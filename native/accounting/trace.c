/* Linux x86_64 stopped-world allocation observer.
 * No malloc/calloc/realloc/free, stdio, dlopen, or worker threads after startup.
 * Metadata slabs are real, retained mmap allocations and are included by the
 * self scan. Two reusable banks bound retention by observed VMA high water,
 * rather than imposing a capacity limit on the service. */
#define _GNU_SOURCE
#include "counter.h"
#include "window.h"
#include "deadline.h"
#include "stage_control.h"
#include <errno.h>
#include <fcntl.h>
#include <linux/audit.h>
#include <linux/sched.h>
#include <linux/io_uring.h>
#include <linux/memfd.h>
#include <linux/openat2.h>
#include <linux/falloc.h>
#include <linux/magic.h>
#include <signal.h>
#include <setjmp.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/ptrace.h>
#include <sys/syscall.h>
#include <sys/stat.h>
#include <sys/sysmacros.h>
#include <sys/types.h>
#include <sys/user.h>
#include <sys/vfs.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error This observer requires Linux x86_64
#endif
#define SLAB_BYTES 65536u
struct slab { struct slab *next; size_t used; };
struct arena { struct slab *first, *cursor, *tail; };
struct account_object;
struct fd_table;
struct region {
  struct region *next;
  uint64_t mm, lo, hi, offset, major, minor, inode;
  struct account_object *object;
  /* A private view retains its file without charging its activation to the
   * shared object. object/part describe charged shared capacity; file_owner
   * is a separate lifetime reference and adds no interval by itself. */
  struct account_object *file_owner;
  uint64_t part;
  bool shared, active;
};
struct space { struct space *next; uint64_t uid, inherit; pid_t representative; bool live; };
struct task {
  struct task *next;
  struct space *space;
  struct fd_table *files;
  pid_t pid, tgid;
  pid_t vfork_child;
  bool stopped, exiting, dead, entry, memory, marker, vfork_wait;
  bool marker_hold_started;
  bool deadline_marker, stage_marker, stage_prepared;
  int stage_error;
  bool group_stop, listening, vanishing;
  bool initial_stop;
  bool open_truncate;
  bool creation_prepared, creation_valid, creation_bound, creation_pending;
  bool creation_pidns_same;
  bool result_known, exit_result_missing, exec_started;
  uint64_t creation_flags;
  int64_t known_result;
  int deliver, event;
  uint64_t nr, args[6];
};
struct pending_stop { struct pending_stop *next; pid_t pid; int status; };
static struct arena persistent, banks[2];
static struct task *tasks;
static struct task *last_stopped;
static struct pending_stop *pending;
static struct pending_stop *pending_tail, *pending_free;
static struct space *spaces;
static struct region *previous, *regions;
static struct arena *building;
static unsigned bank_index;
static uint64_t next_mm, snapshots, syscall_stops;
static uint64_t invalidated_observations, exec_identity_changes, group_stops;
static uint64_t recovered_syscall_results;
static uint64_t unavailable_syscall_stops;
static int report_fd = -1, root_status = 255;
static bool service_window, stage_control;
static struct jaystage_shared *stage_page;
static struct jaystage_receipt stage_receipt;
static bool stage_recovery, stage_terminal;
static struct task *stage_owner;
static struct jaystage_request stage_request;
struct stage_origin {struct stage_origin*next;struct jaystage_request request;};
static struct stage_origin *stage_origins;
static void deadline_rearm(void);
static void stage_publish(void);
static void stage_log(const char*);
static uint64_t stage_pending_flags(void);
static void stage_prepare(struct task*);
static bool stage_finish(struct task*);
static void stage_recovered(void);
static int scan_fd=-1;
static pid_t root_pid;
static pid_t hold_owner;
static struct task *active;
/* Exact transaction actually resumed into exec, not a guess by PPid/TGID. */
static struct task *exec_inflight;
static uint64_t recovered_event_metadata, proc_memory_reads, alternate_fd_reads;
static struct task *deadline_task, *deadline_prior_active;
static __uint128_t deadline_ns, cancellation_ns;
static volatile sig_atomic_t deadline_signalled;
static sigjmp_buf deadline_escape;
static int deadline_timer;
static unsigned deadline_steps;
static uint64_t deadline_cancellations;
static uint64_t deadline_begin_publications;
static bool snapshot_in_progress;
static bool caches_dirty;
static void deadline_tick(void);
static void *counter;
static struct jayacct_snapshot latest;
static struct jayacct_window_snapshot latest_window;
static __uint128_t automatic_stack_bytes, observer_bytes;
static __uint128_t fd_payload_bytes;
static __uint128_t traced_private_bytes, traced_shared_bytes, largest_private_bytes;
static uint64_t live_memory_spaces;
static pid_t largest_private_pid;
static char input_buffer[8192], header[192], output_buffer[2048];
static struct user_regs_struct validation_regs;
/* A successful MAP_FIXED/MREMAP must not inherit activation from the replaced
 * destination. Accessible new mappings activate their entire capacity. */
static uint64_t replace_mm, replace_lo, replace_hi;
static uint64_t remap_mm, remap_old_lo, remap_old_hi, remap_new_lo;
static struct account_object *mapped_object;
static struct account_object *mapped_file_owner;
static uint64_t mapped_part;
static uint64_t mapped_offset;
static bool monitor_failed;
static unsigned lifecycle_depth;
#ifdef JAYACCT_TEST_RACES
static bool test_kill_after_scan;
static bool test_grow_marker_entry;
static bool test_deadline_wait;
static bool test_deadline_scan;
static bool test_kill_uring_exit;
static bool test_kill_open_exit;
static bool test_kill_truncate_exit;
static bool test_kill_uring_info, test_kill_open_info, test_kill_truncate_info;
static bool test_deadline_retained;
static bool test_stage_scan, test_stage_wait, test_stage_commit;
#endif

static size_t string_length(const char *s) { size_t n=0; while (s[n]) ++n; return n; }
static void write_all(int fd, const char *p, size_t n) {
  while (n) { ssize_t r=write(fd,p,n); if(r<0 && errno==EINTR) continue;
    if(r<=0) _exit(125); p+=r; n-=(size_t)r; }
}
static void fail(const char *s) {
  write_all(2,"jayacct: ",9); write_all(2,s,string_length(s)); write_all(2,"\n",1);
  monitor_failed=true;
  if(lifecycle_depth&&stage_control&&
      (stage_receipt.state==JAYSTAGE_ARMED||stage_recovery)) {
    /* No memory fact can be recovered from this critical-data failure. Keep
     * the transaction/real cached result and park this opt-in instance. This
     * is explicitly unresolved, not timeout completion or external failure. */
    stage_terminal=true;stage_receipt.pending_flags|=JAYSTAGE_PENDING_METADATA;
    stage_publish();stage_log("unrecoverable_metadata");
    lifecycle_depth=0;siglongjmp(deadline_escape,2);
  }
  /* EXITKILL retires every attached helper, including changed sessions. */
  _exit(125);
}
static char *decimal(char *p, __uint128_t n) {
  char digits[40]; unsigned k=0;
  do { digits[k++]=(char)('0'+n%10); n/=10; } while(n);
  while(k) *p++=digits[--k]; return p;
}
static char *literal(char *p,const char *s) { while(*s) *p++=*s++; return p; }
static __uint128_t wide(struct jayacct_u128 n) { return ((__uint128_t)n.hi<<64)|n.lo; }
static struct jayacct_u128 words(__uint128_t n) { return (struct jayacct_u128){n,n>>64}; }
static void log_lifecycle(const char*event,pid_t pid,uint64_t detail,uint64_t mm) {
  if(report_fd<0)return;
  char*p=output_buffer;p=literal(p,"{\"type\":\"lifecycle\",\"event\":\"");p=literal(p,event);
  p=literal(p,"\",\"pid\":");p=decimal(p,(unsigned)pid);
  p=literal(p,",\"detail\":\"");p=decimal(p,detail);
  p=literal(p,"\",\"mm\":\"");p=decimal(p,mm);
  p=literal(p,"\"}\n");write_all(report_fd,output_buffer,(size_t)(p-output_buffer));
}
static void log_object(pid_t pid,uint64_t bytes,uint64_t uid) {
  if(report_fd<0)return;
  char*p=output_buffer;p=literal(p,"{\"type\":\"object\",\"event\":\"uring_acquired\",\"pid\":");p=decimal(p,(unsigned)pid);
  p=literal(p,",\"capacity\":\"");p=decimal(p,bytes);
  p=literal(p,"\",\"object\":\"");p=decimal(p,uid);
  p=literal(p,"\"}\n");write_all(report_fd,output_buffer,(size_t)(p-output_buffer));
}
__attribute__((noinline)) static void prepare_observer_stack(void) {
  /* Acquire actual stack backing once. The pinned compiled C callgraph uses
   * less than this touched extent; this is no restriction on tracee stacks. */
  volatile unsigned char bytes[65536];
  for(size_t at=0;at<sizeof bytes;at+=4096)bytes[at]=0;
  __asm__ volatile(""::"r"(bytes):"memory");
}
static void log_snapshot(pid_t pid, uint64_t nr, const char *phase) {
  if(report_fd<0) return;
  char *p=output_buffer;
  p=literal(p,"{\"type\":\"snapshot\",\"pid\":");p=decimal(p,(uint64_t)pid);
  p=literal(p,",\"syscall\":");p=decimal(p,nr);
  p=literal(p,",\"phase\":\"");p=literal(p,phase);
  p=literal(p,"\",\"sequence\":\"");p=decimal(p,wide(latest.sequence));
  p=literal(p,"\",\"current\":\"");p=decimal(p,wide(latest.current));
  p=literal(p,"\",\"peak\":\"");p=decimal(p,wide(latest.peak));
  p=literal(p,"\",\"time_ns\":\"");p=decimal(p,wide(latest.monotonic_ns));
  p=literal(p,"\",\"peak_time_ns\":\"");p=decimal(p,wide(latest.peak_monotonic_ns));
  p=literal(p,"\",\"peak_sequence\":\"");p=decimal(p,wide(latest.peak_sequence));
  p=literal(p,"\",\"automatic_stack_bytes\":\"");p=decimal(p,automatic_stack_bytes);
  p=literal(p,"\",\"observer_bytes\":\"");p=decimal(p,observer_bytes);
  p=literal(p,"\",\"traced_private_bytes\":\"");p=decimal(p,traced_private_bytes);
  p=literal(p,"\",\"traced_shared_bytes\":\"");p=decimal(p,traced_shared_bytes);
  p=literal(p,"\",\"fd_payload_bytes\":\"");p=decimal(p,fd_payload_bytes);
  p=literal(p,"\",\"largest_mm_private_bytes\":\"");p=decimal(p,largest_private_bytes);
  p=literal(p,"\",\"largest_mm_pid\":");p=decimal(p,(unsigned)largest_private_pid);
  p=literal(p,",\"memory_spaces\":");p=decimal(p,live_memory_spaces);
  p=literal(p,",\"peak_flags\":");p=decimal(p,latest.peak_flags);
  p=literal(p,",\"flags\":");p=decimal(p,latest.flags);
  p=literal(p,"}\n");write_all(report_fd,output_buffer,(size_t)(p-output_buffer));
}
static void *allocate(struct arena *a,size_t bytes) {
  bytes=(bytes+15)&~(size_t)15;
  if(bytes>SLAB_BYTES-sizeof(struct slab)) fail("metadata record exceeds slab");
  struct slab *s=a->cursor?a->cursor:a->first;
  while(s && SLAB_BYTES-s->used<bytes) s=s->next;
  if(!s) {
    s=mmap(NULL,SLAB_BYTES,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    if(s==MAP_FAILED) fail("real metadata mmap failure (not memory excess evidence)");
    s->next=NULL;s->used=(sizeof *s+15)&~(size_t)15;
    if(!a->first) a->first=s;
    else a->tail->next=s;
    a->tail=s;
  }
  a->cursor=s;void *p=(char*)s+s->used;s->used+=bytes;memset(p,0,bytes);return p;
}
static void reset(struct arena *a) {
  for(struct slab *s=a->first;s;s=s->next) {deadline_tick();s->used=(sizeof *s+15)&~(size_t)15;}
  a->cursor=a->first;
}
static void unstable(struct task*t);
static uint64_t number(const char **p,unsigned base);
static bool task_path_status(struct task*t,uint64_t address,int dir,uint64_t resolve,
                             uint64_t flags,struct stat*status);
static void bind_creation(struct task*,pid_t);
/* Canonical observer arguments, not modified tracee registers. Linux x86_64
 * wrappers narrow these values before fd lookup, comparison or flag use.
 * Pointer/size_t/unsigned-long/loff_t arguments remain the full 64 bits. */
static void normalize_syscall_args(struct task*t) {
  switch(t->nr) {
  case SYS_dup2:case SYS_dup3:case SYS_close_range:
    t->args[1]=(uint32_t)t->args[1];
    if(t->nr!=SYS_dup2)t->args[2]=(uint32_t)t->args[2];
    t->args[0]=(uint32_t)t->args[0];break;
  case SYS_fcntl:case SYS_fallocate:
    t->args[1]=(uint32_t)t->args[1];
    t->args[0]=(uint32_t)t->args[0];break;
  case SYS_close:case SYS_dup:case SYS_ftruncate:case SYS_lseek:
  case SYS_read:case SYS_readv:case SYS_write:case SYS_writev:
  case SYS_pwrite64:case SYS_pwritev:case SYS_pwritev2:
    t->args[0]=(uint32_t)t->args[0];
    if(t->nr==SYS_lseek)t->args[2]=(uint32_t)t->args[2];
    if(t->nr==SYS_pwritev2)t->args[5]=(uint32_t)t->args[5];
    break;
  case SYS_open:t->args[1]=(uint32_t)t->args[1];break;
  case SYS_openat:case SYS_execveat:
    t->args[t->nr==SYS_openat?2:4]=(uint32_t)t->args[t->nr==SYS_openat?2:4];
    t->args[0]=(uint32_t)t->args[0];break;
  case SYS_openat2:t->args[0]=(uint32_t)t->args[0];break;
  case SYS_memfd_create:t->args[1]=(uint32_t)t->args[1];break;
  case SYS_io_uring_setup:t->args[0]=(uint32_t)t->args[0];break;
  case SYS_io_uring_register:
    t->args[0]=(uint32_t)t->args[0];t->args[1]=(uint32_t)t->args[1];
    t->args[3]=(uint32_t)t->args[3];break;
  case SYS_mmap:t->args[4]=(uint32_t)t->args[4];break;
  case SYS_shmat:t->args[0]=(uint32_t)t->args[0];t->args[2]=(uint32_t)t->args[2];break;
  case SYS_pkey_mprotect:t->args[3]=(uint32_t)t->args[3];break;
  default:break;
  }
}
#include "objects.inc.c"
static struct task *find(pid_t pid) {
  for(struct task *t=tasks;t;t=t->next) {if(snapshot_in_progress)deadline_tick();if(!t->dead && t->pid==pid)return t;}
  return NULL;
}
static void collect(pid_t pid,int status);
static struct space *new_space(void) {
  struct space *s=caches_dirty?NULL:spaces;while(s && s->live)s=s->next;
  if(!s) { s=allocate(&persistent,sizeof *s);s->next=spaces;spaces=s; }
  if(next_mm==UINT64_MAX)fail("address-space identity overflow");
  s->uid=++next_mm;s->inherit=0;s->live=true;return s;
}
static struct task *add_task(pid_t pid,struct space *space,pid_t tgid) {
  struct task *t=find(pid);if(t)return t;
  t=tasks;while(t && !t->dead)t=t->next;
  if(!t) { t=allocate(&persistent,sizeof *t);t->next=tasks;tasks=t; }
  struct task *next=t->next;memset(t,0,sizeof *t);t->next=next;
  t->pid=pid;t->tgid=tgid;t->space=space;t->initial_stop=true;return t;
}
static bool any_alive(void) { for(struct task*t=tasks;t;t=t->next)if(!t->dead)return true;return false; }
static bool queued_work(void) {
  if(hold_owner||active)return false;
  for(struct task*t=tasks;t;t=t->next) {
    deadline_tick();
    if(!t->dead&&t->stopped&&!t->group_stop&&(t->exiting||(t->entry&&t->memory)))return true;
  }
  return false;
}
static bool all_stopped(void) {
  for(struct task*t=tasks;t;t=t->next) {
    deadline_tick();
    if(!t->dead && !t->stopped && !t->vfork_wait && !t->listening)return false;
  }
  return true;
}
static bool stopping_signal(int sig) { return sig==SIGSTOP||sig==SIGTSTP||sig==SIGTTIN||sig==SIGTTOU; }
static bool opening_syscall(uint64_t nr) {
  return nr==SYS_open||nr==SYS_openat||nr==SYS_openat2||nr==SYS_creat;
}
static int path_component_status(struct task*t,int base,const char*name,uint64_t flags,struct stat*status) {
  /* Unscoped pathname calls still evaluate procfs self in the tracee, not
   * in this observer. Walk ordinary symlinks component by component; leave
   * procfs magic links to the kernel so memfd's unlinked name is not guessed
   * from readlink text. No heap allocation, cwd change or helper process. */
  char pending_name[4096],target[4096],component[4096],root_path[96];
  size_t length=string_length(name);if(length>=sizeof pending_name)return -1;
  memcpy(pending_name,name,length+1);
  char*p=root_path;p=literal(p,"/proc/");p=decimal(p,(unsigned)t->pid);p=literal(p,"/root");*p=0;
  int root=open(root_path,O_PATH|O_DIRECTORY|O_CLOEXEC);if(root<0)return -1;
  int current=dup(base);if(current<0){close(root);return -1;}
  struct stat root_status;if(fstat(root,&root_status))goto error;
  unsigned links=0;
  for(;;) {
    char*at=pending_name;while(*at=='/')++at;
    size_t n=0;while(at[n]&&at[n]!='/')++n;
    if(!n) {int result=fstat(current,status);close(current);close(root);return result;}
    memcpy(component,at,n);component[n]=0;
    const char*tail=at+n;while(*tail=='/')++tail;
    size_t remaining=string_length(tail);
    if(!strcmp(component,".")) {memmove(pending_name,tail,remaining+1);continue;}
    if(!strcmp(component,"..")) {
      struct stat here;if(fstat(current,&here))goto error;
      if(here.st_dev==root_status.st_dev&&here.st_ino==root_status.st_ino) {
        memmove(pending_name,tail,remaining+1);continue;
      }
    }
    int fd=openat(current,component,O_PATH|O_NOFOLLOW|O_CLOEXEC);if(fd<0)goto error;
    struct stat found;if(fstat(fd,&found)){close(fd);goto error;}
    if(S_ISLNK(found.st_mode)) {
      /* O_NOFOLLOW applies to the final component only. A trailing slash
       * still requires directory lookup. Intermediate procfs self/fd magic
       * links must retain the tracee's TGID/TID context in either case. */
      if((flags&O_NOFOLLOW)&&!remaining&&at[n]!='/')goto resolved;
      close(fd);if(++links>40)goto error; /* Linux MAXSYMLINKS, not a service cap. */
      struct statfs fs;if(fstatfs(current,&fs))goto error;
      bool proc=fs.f_type==PROC_SUPER_MAGIC;
      if(proc&&(!strcmp(component,"self")||!strcmp(component,"thread-self"))) {
        char*q=target;q=decimal(q,(unsigned)t->tgid);
        if(!strcmp(component,"thread-self")){q=literal(q,"/task/");q=decimal(q,(unsigned)t->pid);}*q=0;
      } else {
        if(proc) {
          struct open_how how={.flags=O_PATH|O_CLOEXEC,.resolve=RESOLVE_NO_MAGICLINKS};
          int ordinary=(int)syscall(SYS_openat2,current,component,&how,sizeof how);
          if(ordinary>=0)close(ordinary);
          else if(errno==ELOOP) {
            fd=openat(current,component,O_PATH|O_CLOEXEC);if(fd<0)goto error;
            if(fstat(fd,&found)){close(fd);goto error;}
            goto resolved;
          } else goto error;
        }
        ssize_t bytes=readlinkat(current,component,target,sizeof target-1);
        if(bytes<0||(size_t)bytes>=sizeof target-1)goto error;target[bytes]=0;
      }
      size_t expanded=string_length(target);
      if(expanded+1+remaining>=sizeof pending_name)goto error;
      memmove(pending_name+expanded+1,tail,remaining+1);
      memcpy(pending_name,target,expanded);pending_name[expanded]='/';
      if(target[0]=='/') {
        int next=dup(root);if(next<0)goto error;close(current);current=next;
      }
      continue;
    }
resolved:
    if(!remaining) {
      *status=found;close(fd);close(current);close(root);return 0;
    }
    if(!S_ISDIR(found.st_mode)){close(fd);goto error;}
    close(current);current=fd;memmove(pending_name,tail,remaining+1);
  }
error:
  close(current);close(root);return -1;
}
static bool task_path_status(struct task*t,uint64_t address,int dir,uint64_t resolve,
                             uint64_t flags,struct stat*status) {
  char name[4096],path[4192];size_t used=0;
  while(used<sizeof name) {
    if(address>UINT64_MAX-used)return false;
    uint64_t at=address+used,aligned=at&~UINT64_C(7);
    errno=0;long word=ptrace(PTRACE_PEEKDATA,t->pid,(void*)(uintptr_t)aligned,NULL);
    if(word==-1&&errno)return false;
    unsigned char bytes[sizeof word];memcpy(bytes,&word,sizeof word);
    for(size_t i=(size_t)(at-aligned);i<sizeof word&&used<sizeof name;i++) {
      name[used++]=(char)bytes[i];if(!bytes[i])goto copied;
    }
  }
  return false; /* The real syscall reports ENAMETOOLONG. */
copied:;
  char*p=path;p=literal(p,"/proc/");p=decimal(p,(unsigned)t->pid);
  bool rooted=(resolve&RESOLVE_IN_ROOT)!=0;
  if(name[0]=='/'&&!rooted) {
    p=literal(p,"/root");
  } else if(dir==AT_FDCWD)p=literal(p,"/cwd");
  else {
    if(dir<0)return false;
    p=literal(p,"/fd/");p=decimal(p,(unsigned)dir);
  }
  *p=0;
  int base;do{base=open(path,O_PATH|O_DIRECTORY|O_CLOEXEC);}while(base<0&&errno==EINTR);
  if(base<0)return false;
  if(!resolve) {
    bool ok=path_component_status(t,base,name,flags,status)==0;close(base);return ok;
  }
  struct open_how how={.flags=O_PATH|O_CLOEXEC|(flags&(O_NOFOLLOW|O_DIRECTORY)),.resolve=resolve};
  /* Crucially, resolve IN_ROOT symlinks and '..' in the kernel with the
   * actual referenced directory, rather than following an observer pathname
   * prefix. O_PATH neither waits for FIFO partners nor truncates backing. */
  const char*lookup=name[0]=='/'&&!rooted?name+1:name;
  int fd;do{fd=(int)syscall(SYS_openat2,base,lookup,&how,sizeof how);}while(fd<0&&errno==EINTR);
  close(base);if(fd<0)return false;
  bool ok=fstat(fd,status)==0;close(fd);return ok;
}
static bool path_backing_known(const struct stat*status) {
  uint64_t device_major=major(status->st_dev),device_minor=minor(status->st_dev);
  if(file_object(device_major,device_minor,status->st_ino,false))return true;
  /* Private/COW views belong to mm capacities rather than shared objects.
   * They still make this a represented backing target: do not bypass the
   * exclusive slot merely because no shared-file object was needed. */
  for(struct region*r=regions;r;r=r->next) {
    deadline_tick();
    if(r->inode&&r->inode==status->st_ino&&r->major==device_major&&r->minor==device_minor)return true;
  }
  return false;
}
static bool open_may_truncate(struct task*t) {
  uint64_t address,flags,resolve=0;int dir=AT_FDCWD;
  if(t->nr==SYS_open||t->nr==SYS_creat) {
    address=t->args[0];flags=t->nr==SYS_creat?O_TRUNC:t->args[1];
  } else {
    dir=(int)t->args[0];address=t->args[1];flags=t->args[2];
    if(t->nr==SYS_openat2) {
      if(t->args[3]<sizeof(struct open_how))return true;
      errno=0;long word=ptrace(PTRACE_PEEKDATA,t->pid,(void*)(uintptr_t)t->args[2],NULL);
      if(word==-1&&errno)return true;flags=(uint64_t)word;
      if(flags&O_TRUNC) {
        if(t->args[2]>UINT64_MAX-16)return true;
        errno=0;word=ptrace(PTRACE_PEEKDATA,t->pid,(void*)(uintptr_t)(t->args[2]+16),NULL);
        if(word==-1&&errno)return true;resolve=(uint64_t)word;
      }
    }
  }
  t->open_truncate=(flags&O_TRUNC)&&!(flags&O_PATH);
  if(!t->open_truncate)return false;
  struct stat status;
  if(!task_path_status(t,address,dir,resolve,flags,&status))return true;
  /* O_TRUNC is ignored by FIFO/devices. For a regular target, only a known
   * accounted object needs exclusive mutation. An ordinary contents-only
   * open may wait for a peer's lease just like truncate(path). Its installed
   * descriptor and any changed identity are still inspected at exit. */
  return S_ISREG(status.st_mode)&&path_backing_known(&status);
}
static bool memory_syscall(struct task*t) {
  switch(t->nr) {
  case SYS_open:case SYS_openat:case SYS_openat2:case SYS_creat:
    return open_may_truncate(t);
  case SYS_truncate: {
    /* An identified ordinary file with no adapted object changes only file
     * contents, not this ledger's acquired userspace backing. In particular,
     * it may wait for a peer's lease handler and must not own the exclusive
     * slot. Known objects (including mapped regular files) and unresolved
     * identities remain serialized. Preflight is not atomic with pathname
     * lookup: concurrent replacement and leases on adapted objects remain
     * explicit coverage obligations, not a complete Linux contract. */
    struct stat status;
    if(!task_path_status(t,t->args[0],AT_FDCWD,0,0,&status))return true;
    return path_backing_known(&status);
  }
  case SYS_fcntl:
    /* Locks (including blocking waits) and queries acquire no userspace
     * backing. Their peers must remain runnable to release the lock. Keep
     * fd lifecycle, write-position flags and possible backing mutations
     * serialized; unknown future commands take the conservative path. */
    switch((unsigned)t->args[1]) {
    case F_GETLK:case F_SETLK:case F_SETLKW:
    case F_OFD_GETLK:case F_OFD_SETLK:case F_OFD_SETLKW:
    case F_GETFD:case F_GETFL:case F_GETOWN:case F_GETOWN_EX:case F_GETSIG:
    case F_GETLEASE:case F_GETPIPE_SZ:case F_GET_SEALS:
    case F_SETOWN:case F_SETOWN_EX:case F_SETSIG:case F_SETLEASE:case F_NOTIFY:
    case F_GET_RW_HINT:case F_SET_RW_HINT:case F_GET_FILE_RW_HINT:case F_SET_FILE_RW_HINT:
    case 1027:case 1028: /* Linux 7.0 F_DUPFD_QUERY / F_CREATED_QUERY */
      return false;
    default:return true;
    }
  case SYS_mmap:case SYS_mprotect:case SYS_munmap:case SYS_mremap:case SYS_brk:
  case SYS_shmat:case SYS_shmdt:case SYS_execve:case SYS_execveat:
  case SYS_clone:case SYS_clone3:case SYS_fork:case SYS_vfork:
  case SYS_exit:case SYS_exit_group:case SYS_remap_file_pages:case SYS_pkey_mprotect:
  case SYS_io_uring_setup:case SYS_io_uring_register:
  case SYS_memfd_create:case SYS_ftruncate:
  case SYS_close:case SYS_close_range:case SYS_dup:case SYS_dup2:case SYS_dup3:case SYS_unshare:
    return true;
  default:return false;
  }
}
static bool creation_syscall(uint64_t nr) {
  return nr==SYS_clone||nr==SYS_clone3||nr==SYS_fork||nr==SYS_vfork;
}
static void prepare_creation(struct task*t) {
  if(t->creation_prepared)return;
  t->creation_prepared=true;
  char path[64],*p=path;p=literal(p,"/proc/");p=decimal(p,(unsigned)t->pid);
  p=literal(p,"/ns/pid");*p=0;
  struct stat parent_namespace,observer_namespace;
  t->creation_pidns_same=!stat(path,&parent_namespace)&&!stat("/proc/self/ns/pid",&observer_namespace)&&
    parent_namespace.st_dev==observer_namespace.st_dev&&parent_namespace.st_ino==observer_namespace.st_ino;
  if(t->nr==SYS_clone3) {
    /* Input is captured while the world is stopped, before the selected
     * syscall executes. An unreadable argument may legitimately fail. */
    if(t->args[1]<sizeof(uint64_t))return;
    t->creation_valid=remote_copy(t,t->args[0],&t->creation_flags,sizeof(uint64_t));
  } else {
    t->creation_flags=t->nr==SYS_clone?t->args[0]:
      t->nr==SYS_vfork?CLONE_VM|CLONE_VFORK:0;
    t->creation_valid=true;
  }
}
static void bind_creation(struct task*t,pid_t child) {
  if(t->creation_bound)return;
  if(!t->creation_valid||child<=0)fail("unrecoverable creation metadata; no observation published");
  uint64_t flags=t->creation_flags;
  struct space*s=(flags&CLONE_VM)?t->space:new_space();
  if(!(flags&CLONE_VM))s->inherit=t->space->uid;
  struct task*c=add_task(child,s,(flags&CLONE_THREAD)?t->tgid:child);
  c->files=(flags&CLONE_FILES)?t->files:files_copy(t->files);
  if(flags&CLONE_VFORK)t->vfork_child=child;
  t->creation_bound=true;t->creation_pending=false;
  log_lifecycle("clone",child,flags,s->uid);
  struct pending_stop**link=&pending,*before=NULL;
  while(*link) {
    struct pending_stop*p=*link;
    if(p->pid!=child){before=p;link=&p->next;continue;}
    *link=p->next;if(pending_tail==p)pending_tail=before;
    int initial=p->status;p->next=pending_free;pending_free=p;
    collect(child,initial);
  }
}
static void record_syscall_result(struct task*t,int64_t result,bool error) {
  t->result_known=true;t->known_result=result;t->exit_result_missing=false;
  if(error&&exec_inflight==t&&(t->nr==SYS_execve||t->nr==SYS_execveat))exec_inflight=NULL;
  if(t->creation_pending) {
    /* A syscall result is in the creator's PID namespace. Never approximate
     * its translation to the observer's wait/ptrace namespace. */
    if(!t->creation_pidns_same||error||result<=0||result>INT32_MAX)
      fail("creation event has no recoverable child result; no observation published");
    bind_creation(t,(pid_t)result);++recovered_event_metadata;
    log_lifecycle("creation_result_recovered",t->pid,(uint64_t)result,t->space->uid);
  }
  t->vfork_wait=false;
  objects_syscall_exit(t,result,error);
  t->entry=false;
  if(!error && (t->nr==SYS_mmap||t->nr==SYS_mremap)) {
    replace_mm=t->space->uid;replace_lo=(uint64_t)result;
    uint64_t size=t->nr==SYS_mmap?t->args[1]:t->args[2];
    if(size>UINT64_MAX-4095)fail("mapping size overflow");
    size=(size+4095)&~UINT64_C(4095);
    if(size>UINT64_MAX-replace_lo)fail("mapping address overflow");
    replace_hi=replace_lo+size;
    mapped_object=NULL;mapped_file_owner=NULL;mapped_part=0;mapped_offset=0;
    if(t->nr==SYS_mmap) {
      uint64_t type=t->args[3]&MAP_TYPE;
      bool shared=type==MAP_SHARED||type==MAP_SHARED_VALIDATE;
      /* MAP_ANONYMOUS ignores fd, even when it names a known object. Choose
       * the real acquisition first; never borrow that fd's identity/size. */
      if(t->args[3]&MAP_ANONYMOUS) {
        if(shared)mapped_object=object_new(OBJECT_SHARED_ANON);
      } else {
        struct fd_entry*entry=files_find(t->files,(int)t->args[4]);
        if(entry) {
          mapped_file_owner=entry->object;
          mapped_offset=entry->object->kind==OBJECT_URING?0:t->args[5];
          if(shared) {
            mapped_object=entry->object;
            mapped_part=entry->object->kind==OBJECT_URING&&t->args[5]==IORING_OFF_SQES?1:0;
          }
        }
      }
    }
    if(t->nr==SYS_mremap) {
      remap_mm=t->space->uid;remap_old_lo=t->args[0];
      if(t->args[1]>UINT64_MAX-4095)fail("old remap size overflow");
      uint64_t old_size=(t->args[1]+4095)&~UINT64_C(4095);
      if(!old_size)old_size=size; /* shared mremap(old_size=0) alias */
      if(old_size>UINT64_MAX-remap_old_lo)fail("old remap range overflow");
      remap_old_hi=remap_old_lo+old_size;remap_new_lo=replace_lo;
    }
  }
  if(!error&&t->nr==SYS_remap_file_pages) {
    /* Linux emulates this with MAP_FIXED at the page-aligned start, with
     * size rounded DOWN and the old VMA's protection. It replaces the view,
     * not the object's previously acquired interval history. */
    replace_mm=t->space->uid;replace_lo=t->args[0]&~UINT64_C(4095);
    uint64_t size=t->args[1]&~UINT64_C(4095);
    if(size>UINT64_MAX-replace_lo||t->args[3]>UINT64_MAX/4096)
      fail("file remap extent overflow");
    replace_hi=replace_lo+size;mapped_object=NULL;mapped_file_owner=NULL;mapped_part=0;
    mapped_offset=t->args[3]*4096;
    for(struct region*r=regions;r;r=r->next)
      if(r->mm==replace_mm&&r->lo<=replace_lo&&replace_lo<r->hi) {
        mapped_object=r->object;mapped_file_owner=r->file_owner;mapped_part=r->part;break;
      }
  }
  /* A marker is delivered only at syscall EXIT. Both metadata banks may
   * have grown during the entry observation; the exit observation must
   * include that real backing before the caller resumes userspace. */
  /* Opens and non-adapted pathname truncation can wait for another service
   * task (FIFO, device, lease). Successful exits remain ownership barriers:
   * collect their real results before observation and userspace resumption. */
  t->memory=t->marker||((opening_syscall(t->nr)||t->nr==SYS_truncate)&&!error);
}
static void collect_impl(pid_t pid,int status) {
  last_stopped=NULL;
  if(WIFSTOPPED(status)&&(status>>16)==PTRACE_EVENT_EXEC) {
    /* The kernel renumbers an execing nonleader to TGID and silently retires
     * its former TID. Keep that task record (and active transaction pointer),
     * retire the other thread records, and create a new mm generation. */
    unsigned long oldtid=0;bool unavailable=false;
    if(ptrace(PTRACE_GETEVENTMSG,pid,0,&oldtid)<0) {
      if(errno!=ESRCH)fail("get exec identity");
      unavailable=true;
      if(!exec_inflight||exec_inflight->dead||exec_inflight->tgid!=pid)
        fail("unrecoverable exec transaction identity; no observation published");
      oldtid=(unsigned long)exec_inflight->pid;++recovered_event_metadata;
      log_lifecycle("exec_transaction_recovered",pid,oldtid,exec_inflight->space->uid);
    }
    struct task*origin=find((pid_t)oldtid);
    if(!origin)fail("exec has no originating task");
    pid_t old_group=origin->tgid;
    for(struct task*other=tasks;other;other=other->next)
      if(other!=origin&&!other->dead&&other->tgid==old_group){other->dead=true;other->stopped=true;}
    if(oldtid!=(unsigned long)pid)++exec_identity_changes;
    origin->pid=pid;origin->tgid=pid;origin->space=new_space();
    origin->files=files_copy(origin->files);
    files_exec(origin->files);
    origin->stopped=true;origin->exiting=false;origin->event=PTRACE_EVENT_EXEC;
    origin->listening=false;origin->group_stop=false;origin->vanishing=false;origin->vfork_wait=false;
    origin->deliver=0;last_stopped=origin;
    exec_inflight=NULL;
    if(unavailable)unstable(origin);
    log_lifecycle("exec",pid,oldtid,origin->space->uid);return;
  }
  struct task*t=find(pid);
  if(!t) {
    /* Auto-attached child's initial stop may be reported before its creator's
     * fork/clone event. Retain it until that event gives the mm identity. */
    /* A new child may reach EXIT before the creator supplies its PID.
     * Queue actual statuses, without inferring parentage or CLONE flags. */
    struct pending_stop*p=pending_free;
    if(p)pending_free=p->next;else p=allocate(&persistent,sizeof *p);
    p->next=NULL;if(pending_tail)pending_tail->next=p;else pending=pending_tail=p;
    pending_tail=p;
    p->pid=pid;p->status=status;return;
  }
  if(WIFEXITED(status)||WIFSIGNALED(status)) {
    if(t->creation_pending||t->exit_result_missing)
      fail("critical lifecycle metadata lost at retirement; no observation published");
    if(exec_inflight==t)exec_inflight=NULL;
    if(pid==root_pid)root_status=WIFEXITED(status)?WEXITSTATUS(status):128+WTERMSIG(status);
    log_lifecycle("retired",pid,(uint64_t)status,t->space->uid);
    t->dead=true;t->stopped=true;return;
  }
  if(!WIFSTOPPED(status))fail("unexpected wait status");
  last_stopped=t;
  t->stopped=true;t->listening=false;t->vanishing=false;t->deliver=0;t->event=status>>16;
  int sig=WSTOPSIG(status);
  if(t->event==PTRACE_EVENT_CLONE||t->event==PTRACE_EVENT_FORK||t->event==PTRACE_EVENT_VFORK) {
    unsigned long child=0;
    if(ptrace(PTRACE_GETEVENTMSG,pid,0,&child)<0) {
      if(errno!=ESRCH)fail("get clone identity");
      t->creation_pending=true;
      log_lifecycle("creation_identity_unavailable",pid,ESRCH,t->space->uid);
      unstable(t);return;
    }
    if(child>INT32_MAX)fail("unsupported child PID representation");
    bind_creation(t,(pid_t)child);
    return;
  }
  if(t->event==PTRACE_EVENT_EXIT) {
    t->exiting=true;
    /* A fatal signal may skip the ordinary syscall-exit notification. On the
     * pinned x86_64 exit path, regs.rax contains the completed syscall result,
     * and this stop precedes exit_mm/exit_files. Recover committed ownership
     * before allowing either resource to disappear. -ENOSYS is the entry
     * sentinel, not evidence that an operation was executed. */
    if(t->entry&&(t->memory||opening_syscall(t->nr)||t->nr==SYS_truncate)&&!t->marker&&t->nr!=SYS_exit&&t->nr!=SYS_exit_group) {
      struct user_regs_struct regs;
      bool cached=false;
      if(ptrace(PTRACE_GETREGS,pid,0,&regs)<0) {
        if(errno!=ESRCH)fail("cannot inspect dying syscall owner");
        if(!t->result_known) {
          t->exit_result_missing=true;
          log_lifecycle("exit_result_unavailable",pid,t->nr,t->space->uid);
          unstable(t);return;
        }
        cached=true;log_lifecycle("exit_cached_result",pid,t->nr,t->space->uid);
      }
      int64_t result=cached?t->known_result:(int64_t)regs.rax;
      if(cached||(regs.orig_rax==t->nr&&result!=-ENOSYS)) {
        record_syscall_result(t,result,result<0&&result>=-4095);
        ++recovered_syscall_results;
        log_lifecycle("syscall_result_recovered",pid,t->nr,t->space->uid);
      }
    }
    t->vfork_wait=false;t->vfork_child=0;t->exiting=true;return;
  }
  if(t->event==PTRACE_EVENT_VFORK_DONE){t->vfork_wait=false;t->vfork_child=0;return;}
  if(t->event==PTRACE_EVENT_STOP) {
    if(t->initial_stop){t->initial_stop=false;t->group_stop=false;return;}
    t->group_stop=stopping_signal(sig);
    if(t->group_stop){++group_stops;log_lifecycle("group_stop",pid,(unsigned)sig,t->space->uid);}
    return;
  }
  if(sig==(SIGTRAP|0x80)) {
    struct __ptrace_syscall_info info;
#ifdef JAYACCT_TEST_RACES
    /* A real SIGKILL after the syscall entry has run, before querying its
     * next stop. No result/errno is injected. EXIT must recover the actual
     * committed allocation/descriptor while its mm/files are still present. */
    bool kill_before_info=t->entry&&
      ((test_kill_uring_info&&t->nr==SYS_io_uring_setup)||
       (test_kill_open_info&&t->nr==SYS_openat2)||
       (test_kill_truncate_info&&t->nr==SYS_truncate));
    if(kill_before_info) {
      test_kill_uring_info=test_kill_open_info=test_kill_truncate_info=false;
      if(kill(pid,SIGKILL))fail("test syscall-info owner signal");
    }
#endif
    long n=ptrace(PTRACE_GET_SYSCALL_INFO,pid,sizeof info,&info);
    if(n<0) {
      if(errno!=ESRCH)fail("cannot read syscall information");
      /* A wait stop does not pin ptrace availability across SIGKILL. Keep
       * the last entry, parameters and owners: an EXIT stop may still need
       * to recover a committed result before mm/files are released. This
       * task is not dead and no replacement observation is published here.
       * stop_world must drain its next real stop/retirement before scanning. */
      ++unavailable_syscall_stops;
      log_lifecycle("syscall_info_unavailable",pid,ESRCH,t->space->uid);
      unstable(t);return;
    }
    if((size_t)n<offsetof(struct __ptrace_syscall_info,entry))fail("short syscall information");
    if(info.arch!=AUDIT_ARCH_X86_64)fail("unsupported syscall architecture");
    if(info.op==PTRACE_SYSCALL_INFO_NONE) {
      /* The reported stop can also have been superseded by EXIT between
       * wait and this request. NONE supplies no entry/result to consume.
       * Preserve the ledger and collect the pending lifecycle event. */
      ++unavailable_syscall_stops;
      log_lifecycle("syscall_stop_superseded",pid,0,t->space->uid);
      unstable(t);return;
    }
    ++syscall_stops;
    if(info.op==PTRACE_SYSCALL_INFO_ENTRY) {
      if((size_t)n<offsetof(struct __ptrace_syscall_info,entry.args)+sizeof info.entry.args)
        fail("short syscall entry information");
      t->entry=true;t->nr=info.entry.nr;
      t->creation_prepared=t->creation_valid=t->creation_bound=t->creation_pending=false;
      t->result_known=t->exit_result_missing=false;
      t->exec_started=false;
      if(t->nr&UINT64_C(0x40000000))fail("x32 ABI is not supported");
      for(unsigned i=0;i<6;i++)t->args[i]=info.entry.args[i];
      normalize_syscall_args(t);t->open_truncate=false;
      t->stage_marker=t->nr==SYS_getpid&&t->args[0]==JAYSTAGE_MARKER&&stage_control;
      t->stage_prepared=false;t->stage_error=0;
      t->marker=t->nr==SYS_getpid && (t->args[0]==JAYACCT_MARKER||t->stage_marker);
      t->deadline_marker=t->marker&&(t->args[2]&JAYACCT_UNTIL_FLAG);
      if(t->deadline_marker)t->args[2]&=~JAYACCT_UNTIL_FLAG;
      t->marker_hold_started=false;
      t->memory=memory_syscall(t)||objects_memory_syscall(t)||t->marker;
    } else if(info.op==PTRACE_SYSCALL_INFO_EXIT) {
      if((size_t)n<offsetof(struct __ptrace_syscall_info,exit.is_error)+sizeof info.exit.is_error)
        fail("short syscall exit information");
      /* Save the actual return before descriptor inspection/lifecycle delay. */
      t->result_known=true;t->known_result=info.exit.rval;
#ifdef JAYACCT_TEST_RACES
      if(test_kill_truncate_exit&&t->nr==SYS_truncate&&!info.exit.is_error) {
        /* A real completed, nonserial truncate must also be recovered if a
         * fatal signal bypasses its normal syscall-result collection. */
        test_kill_truncate_exit=false;
        if(kill(t->pid,SIGKILL))fail("test dying truncate owner signal");
        if(ptrace(PTRACE_CONT,t->pid,0,0)<0&&errno!=ESRCH)fail("test dying truncate owner resume");
        t->stopped=false;return;
      }
      if(test_kill_open_exit&&t->nr==SYS_openat2&&!info.exit.is_error) {
        /* Real delivered fd, real SIGKILL, no normal result collection.
         * EXIT must recover this nontruncating open's installed owner. */
        test_kill_open_exit=false;
        if(kill(t->pid,SIGKILL))fail("test dying open owner signal");
        if(ptrace(PTRACE_CONT,t->pid,0,0)<0&&errno!=ESRCH)fail("test dying open owner resume");
        t->stopped=false;return;
      }
      if(test_kill_uring_exit&&t->nr==SYS_io_uring_setup&&!info.exit.is_error) {
        /* Real completed setup, real SIGKILL, no use of the normal result:
         * force recovery from the later PTRACE_EVENT_EXIT registers/mm. */
        test_kill_uring_exit=false;
        if(kill(t->pid,SIGKILL))fail("test dying ring owner signal");
        if(ptrace(PTRACE_CONT,t->pid,0,0)<0&&errno!=ESRCH)fail("test dying ring owner resume");
        t->stopped=false;return;
      }
#endif
#ifdef JAYACCT_TEST_RACES
      if(test_stage_commit&&stage_receipt.state==JAYSTAGE_ARMED&&
          t->pid!=root_pid&&t->nr==SYS_mmap&&!info.exit.is_error) {
        test_stage_commit=false;stage_log("diagnostic_committed_return");
        /* Actual successful return is saved above. Let the real deadline pass
         * inside this lifecycle transaction: no cancellation may discard the
         * still-to-be-applied ownership. No timestamp/result is substituted. */
        struct timespec time;
        do {
          if(clock_gettime(CLOCK_MONOTONIC,&time))fail("test stage commit clock");
          deadline_tick();
        } while((__uint128_t)time.tv_sec*1000000000u+time.tv_nsec<wide(stage_receipt.deadline_ns));
      }
#endif
      record_syscall_result(t,info.exit.rval,info.exit.is_error);
    } else fail("unexpected syscall information operation");
    return;
  }
  /* First inject a stopping signal at delivery-stop. Its later EVENT_STOP
   * group-stop is parked with LISTEN, preserving SIGCONT semantics. */
  if(sig==SIGCONT){t->group_stop=false;log_lifecycle("continued",pid,0,t->space->uid);}
  t->deliver=sig;
}
static void collect(pid_t pid,int status) {
  /* A stage may expire at any syscall, unlike a marker-only timer. Save and
   * apply its real result/ownership atomically with respect to cancellation.
   * The signal only sets a flag; the next outer safepoint observes expiry. */
  ++lifecycle_depth;collect_impl(pid,status);--lifecycle_depth;
}
static void wait_one(void) {
  int status;pid_t pid;
  if(!stage_control) {
    do{deadline_tick();pid=waitpid(-1,&status,__WALL);}while(pid<0&&errno==EINTR);
  } else {
    /* Avoid a lost one-shot alarm between checking the clock and blocking.
     * Block both wake sources, inspect real wait status, then atomically
     * unblock them in sigsuspend. No polling timeout renews the epoch. */
    sigset_t blocked,prior;
    if(sigemptyset(&blocked)||sigaddset(&blocked,SIGALRM)||sigaddset(&blocked,SIGCHLD)||
        sigprocmask(SIG_BLOCK,&blocked,&prior))fail("stage wait signal mask");
    for(;;) {
      deadline_signalled=1;deadline_tick();
      pid=waitpid(-1,&status,__WALL|WNOHANG);
      if(pid>0|| (pid<0&&errno!=EINTR))break;
      if(pid<0)continue;
      sigset_t wake=prior;
      if(sigdelset(&wake,SIGALRM)||sigdelset(&wake,SIGCHLD))fail("stage wait wake mask");
      (void)sigsuspend(&wake);
    }
    if(sigprocmask(SIG_SETMASK,&prior,NULL))fail("stage wait restore mask");
  }
  if(pid<0)fail("waitpid failed");collect(pid,status);
}
static void stop_world(void) {
  for(struct task*t=tasks;t;t=t->next)if(!t->dead&&t->vfork_wait) {
    deadline_tick();
    struct task*child=find(t->vfork_child);
    if(!child||child->space!=t->space)t->vfork_wait=false;
  }
  for(struct task*t=tasks;t;t=t->next) if(!t->dead&&!t->stopped&&!t->vfork_wait&&!t->vanishing) {
    deadline_tick();
    /* Interrupt LISTEN too: validation needs a real ptrace-stop. EVENT_STOP
     * preserves the group-stop, which resume() restores with LISTEN. */
    if(ptrace(PTRACE_INTERRUPT,t->pid,0,0)<0) {
      if(errno!=ESRCH)fail("interrupt failed");
      t->vanishing=true;t->listening=false;
    } else t->listening=false;
  }
  while(!all_stopped())wait_one();
}
static void resume(struct task*t) {
  if(t->dead||!t->stopped)return;
  if(t->entry&&!t->exiting&&creation_syscall(t->nr)&&!t->creation_prepared) {
    prepare_creation(t);if(!t->stopped)return;
  }
  if(t->entry&&!t->exiting&&!t->exec_started&&(t->nr==SYS_execve||t->nr==SYS_execveat)) {
    if(exec_inflight&&exec_inflight!=t)fail("overlapping exec transactions");
    exec_inflight=t;t->exec_started=true;
  }
  enum __ptrace_request request=t->group_stop?PTRACE_LISTEN:PTRACE_SYSCALL;
  if(ptrace(request,t->pid,0,(void*)(intptr_t)t->deliver)<0) {
    if(errno!=ESRCH)fail("resume failed");
    t->stopped=false;t->listening=false;t->vanishing=true;return;
  }
  t->listening=t->group_stop;
  t->stopped=false;t->event=0;t->deliver=0;
}
static uint64_t number(const char **p,unsigned base) {
  uint64_t n=0;bool got=false;
  for(;;) {
    unsigned d=(*p)[0]>='0'&&(*p)[0]<='9'?(unsigned)((*p)[0]-'0'):
      (*p)[0]>='a'&&(*p)[0]<='f'?(unsigned)((*p)[0]-'a'+10):99;
    if(d>=base)break;
    if(n>(UINT64_MAX-d)/base)fail("proc maps integer overflow");n=n*base+d;++*p;got=true;
  }
  if(!got)fail("malformed proc maps");return n;
}
static void spaces_skip(const char **p){while(**p==' ')++*p;}
static void emit_region(struct region r) {
  struct region*n=allocate(building,sizeof *n);*n=r;n->next=regions;regions=n;
}
static __uint128_t own_extra;
static void parse_header(uint64_t mm,bool own) {
  const char*p=header;struct region r={0};r.mm=mm;
  r.lo=number(&p,16);if(*p++!='-')fail("malformed maps range");r.hi=number(&p,16);spaces_skip(&p);
  char a=*p++,b=*p++,c=*p++,d=*p++;
  r.active=a!='-'||b!='-'||c!='-';r.shared=d=='s';spaces_skip(&p);
  r.offset=number(&p,16);spaces_skip(&p);r.major=number(&p,16);
  if(*p++!=':')fail("malformed maps device");r.minor=number(&p,16);spaces_skip(&p);r.inode=number(&p,10);
  if(r.hi<=r.lo||r.hi-r.lo>UINT64_MAX-r.offset)fail("invalid maps extent");
  spaces_skip(&p);
  if(r.active&&!strncmp(p,"[stack]",7))automatic_stack_bytes+=r.hi-r.lo;
  if(r.shared&&r.inode)r.object=file_object(r.major,r.minor,r.inode,!own);
  if(!own&&r.inode)r.file_owner=file_object(r.major,r.minor,r.inode,false);
  if(own) {
    if(!r.active)return;
    uint64_t cursor=r.offset,end=r.offset+r.hi-r.lo;
    if(r.object)for(struct retained_range*n=retained;n;n=n->next) {
      deadline_tick();
      if(n->object!=r.object||n->uid!=r.object->uid||n->part)continue;
      if(n->hi<=cursor||n->lo>=end)continue;
      if(n->lo>cursor)own_extra+=n->lo-cursor;
      if(n->hi>cursor)cursor=n->hi;if(cursor>=end)return;
    }
    if(cursor<end)own_extra+=end-cursor;return;
  }
  /* Partition at old ownership/activation boundaries and the current syscall
   * result, even for accessible VMAs: a merged VMA is not an object identity. */
  uint64_t at=r.lo;
  uint64_t inherit=0;
  for(struct space*s=spaces;s;s=s->next){deadline_tick();if(s->uid==mm)inherit=s->inherit;}
  while(at<r.hi) {
    deadline_tick();
    uint64_t next=r.hi;bool active=r.active;struct region*match=NULL;uint64_t source_at=at;
    for(struct region*old=previous;old;old=old->next) {
      deadline_tick();
      if(old->mm!=mm&&old->mm!=inherit)continue;
      if(old->lo<=at&&at<old->hi) {match=old;active|=old->active;if(old->hi<next)next=old->hi;}
      else if(at<old->lo&&old->lo<next)next=old->lo;
    }
    if(mm==replace_mm) {
      if(replace_lo<=at&&at<replace_hi){active=r.active;match=NULL;if(replace_hi<next)next=replace_hi;}
      else if(at<replace_lo&&replace_lo<next)next=replace_lo;
    }
    if(mm==remap_mm&&replace_lo<=at&&at<replace_hi) {
      for(struct region*old=previous;old;old=old->next) {
        deadline_tick();
        if(old->mm!=mm)continue;
        uint64_t lo=old->lo>remap_old_lo?old->lo:remap_old_lo;
        uint64_t hi=old->hi<remap_old_hi?old->hi:remap_old_hi;
        if(lo>=hi)continue;
        lo=remap_new_lo+(lo-remap_old_lo);hi=remap_new_lo+(hi-remap_old_lo);
        if(lo<=at&&at<hi){active|=old->active;match=old;source_at=remap_old_lo+at-remap_new_lo;if(hi<next)next=hi;}
        else if(at<lo&&lo<next)next=lo;
      }
    }
    struct region piece=r;piece.lo=at;piece.hi=next;piece.offset=r.offset+at-r.lo;piece.active=active;
    if(match&&(match->object||match->file_owner)) {
      piece.object=match->object;piece.file_owner=match->file_owner;piece.part=match->part;
      piece.offset=match->offset+source_at-match->lo;if(piece.object)piece.shared=true;
    } else if(mm==replace_mm&&replace_lo<=at&&at<replace_hi&&(mapped_object||mapped_file_owner)) {
      piece.object=mapped_object;piece.file_owner=mapped_file_owner;piece.part=mapped_part;
      piece.offset=mapped_offset+at-replace_lo;if(piece.object)piece.shared=true;
    }
    /* Shared activation belongs to object offsets, never to the address of a
     * vanished/reused view. Its retained history is applied after all owners
     * are reconciled, including PROT_NONE aliases and fd-only RAM owners. */
    if(piece.object)piece.active=r.active;
    emit_region(piece);at=next;
  }
}
static void unstable(struct task*t) {
  if(t){t->stopped=false;t->listening=false;t->vanishing=true;}
}
static bool scan_maps(pid_t pid,uint64_t mm,bool own) {
  char path[64],*p=path;p=literal(p,"/proc/");p=decimal(p,(uint64_t)pid);p=literal(p,"/maps");*p=0;
  int fd;
  do{deadline_tick();fd=open(path,O_RDONLY|O_CLOEXEC);}while(fd<0&&errno==EINTR);
  if(fd<0) {
    if(!own&&(errno==ENOENT||errno==ESRCH)){unstable(find(pid));return false;}
    fail("cannot open stopped task maps");
  }
  scan_fd=fd;
#ifdef JAYACCT_TEST_RACES
  if(test_deadline_scan&&deadline_task) {
    /* Test-only CPU scheduling seam, with a genuinely open proc fd and a
     * partially built bank. The real monotonic timer must cancel this scan. */
    test_deadline_scan=false;for(;;)deadline_tick();
  }
#endif
  size_t used=0;bool truncated=false;
  for(;;) {
    deadline_tick();
    ssize_t n=read(fd,input_buffer,sizeof input_buffer);
    if(n<0&&errno==EINTR)continue;
    if(n<0) {
      if(!own&&errno==ESRCH){close(fd);scan_fd=-1;unstable(find(pid));return false;}
      fail("maps read failed");
    }
    if(!n)break;
    for(ssize_t i=0;i<n;i++) {
      deadline_tick();
      char ch=input_buffer[i];
      if(ch=='\n') {header[used]=0;if(used)parse_header(mm,own);used=0;truncated=false;}
      else if(!truncated) {
        if(used+1<sizeof header)header[used++]=ch;else truncated=true;
      }
    }
  }
  if(used)fail("unterminated proc maps");close(fd);scan_fd=-1;return true;
}
static bool snapshot(pid_t cause,uint64_t nr,const char*phase) {
  deadline_tick();
  /* Unbound real child statuses and missing committed metadata cannot be
   * represented by an empty owner. Drain lifecycle before any observation. */
  if(pending)return false;
  for(struct task*t=tasks;t;t=t->next)
    {deadline_tick();if(!t->dead&&(t->creation_pending||t->exit_result_missing))return false;}
  snapshot_in_progress=true;
  automatic_stack_bytes=0;
  previous=regions;regions=NULL;previous_retained=retained;
  bank_index^=1;building=&banks[bank_index];reset(building);
#ifdef JAYACCT_TEST_RACES
  if(test_deadline_wait&&deadline_task) {
    /* All tracees are already stopped: this real waitpid blocks until the
     * observer timer interrupts it. No fake clock or allocation is used. */
    test_deadline_wait=false;wait_one();
  }
#endif
#ifdef JAYACCT_TEST_RACES
  if(stage_receipt.state==JAYSTAGE_ARMED&&cause&&cause!=root_pid&&nr==SYS_mmap) {
    if(test_stage_wait) {
      test_stage_wait=false;stage_log("diagnostic_automatic_wait");wait_one();
    }
    if(test_stage_scan) {
      test_stage_scan=false;stage_log("diagnostic_automatic_scan");for(;;)deadline_tick();
    }
  }
#endif
  for(struct space*s=spaces;s;s=s->next){deadline_tick();s->live=false;s->representative=0;}
  for(struct task*t=tasks;t;t=t->next)if(!t->dead) {
    deadline_tick();
    t->space->live=true;
    /* An EXIT stop still owns its mm until the kernel actually retires it. */
    struct task*prior=find(t->space->representative);
    if(!prior||(!prior->stopped&&t->stopped))t->space->representative=t->pid;
  }
  for(struct space*s=spaces;s;s=s->next)if(s->live) {
    deadline_tick();if(!scan_maps(s->representative,s->uid,false))goto invalidated;
  }
  __uint128_t current=0;
  objects_reconcile();
  for(struct region*r=regions;r;r=r->next) {
    deadline_tick();
    if(r->active&&!r->object&&(!r->shared||!r->inode))current+=r->hi-r->lo;
  }
  traced_private_bytes=current;largest_private_bytes=0;largest_private_pid=0;live_memory_spaces=0;
  for(struct space*s=spaces;s;s=s->next)if(s->live) {
    deadline_tick();
    ++live_memory_spaces;__uint128_t amount=0;
    for(struct region*r=regions;r;r=r->next) {
      deadline_tick();
      if(r->mm==s->uid&&r->active&&!r->object&&(!r->shared||!r->inode))amount+=r->hi-r->lo;
    }
    if(amount>largest_private_bytes){largest_private_bytes=amount;largest_private_pid=s->representative;}
  }
  current+=retained_build();
#ifdef JAYACCT_TEST_RACES
  if(test_deadline_retained&&deadline_task) {
    /* Real timer cancellation after the pending canonical history exists,
     * before it has any validating timestamp or counter publication. */
    test_deadline_retained=false;for(;;)deadline_tick();
  }
#endif
  traced_shared_bytes=current-traced_private_bytes;
  current+=fd_payload_bytes;
  /* No metadata allocation occurs in the own scan, so there is no observer
   * recursion. Slab acquisition is included by this same map snapshot. */
  own_extra=0;(void)scan_maps(getpid(),0,true);observer_bytes=own_extra;current+=own_extra;
#ifdef JAYACCT_TEST_RACES
  if(test_kill_after_scan&&root_pid) {
    /* Test-only scheduling hook: a real SIGKILL and real kernel retirement
     * after maps were read, before validation. Never built into deployment. */
    test_kill_after_scan=false;
    if(kill(root_pid,SIGKILL))fail("test SIGKILL failed");
    while(find(root_pid)) {
      struct task*v=find(root_pid);
      if(v->exiting&&v->stopped) {
        if(ptrace(PTRACE_CONT,v->pid,0,0)<0&&errno!=ESRCH)fail("test exit release failed");
        v->stopped=false;
      }
      wait_one();
    }
  }
#endif
  /* Linearize BEFORE validation: a stopped owner validated later necessarily
   * existed at this earlier instant. A SIGKILL after its individual check
   * cannot falsify that historical observation. Publishing at the end of the
   * validation pass instead would have precisely that race. */
  struct timespec now;
  if(clock_gettime(CLOCK_MONOTONIC,&now)||now.tv_sec<0)fail("observation clock failed");
  struct jayacct_u128 observed=words((__uint128_t)now.tv_sec*1000000000u+now.tv_nsec);
  for(struct space*s=spaces;s;s=s->next)if(s->live) {
    deadline_tick();
    struct task*owner=find(s->representative);
    if(!owner)goto invalidated;
    if(!owner->stopped)fail("mm has no stopped validating owner");
    if(ptrace(PTRACE_GETREGS,owner->pid,0,&validation_regs)<0) {
      if(errno!=ESRCH)fail("stopped-owner validation failed");
      unstable(owner);goto invalidated;
    }
  }
  /* FD tables can differ between tasks sharing one mm. Validate the owners of
   * those tables too; one surviving mm owner does not prove an fd-only object
   * was still owned after another task died. */
  for(struct region*r=regions;r;r=r->next) {
    deadline_tick();if(r->object)r->object->witnessed=true;
    if(r->file_owner)r->file_owner->witnessed=true;
  }
  for(struct fd_table*f=file_tables;f;f=f->next)if(f->live) {
    deadline_tick();
    struct task*owner=NULL;
    for(struct task*t=tasks;t;t=t->next){deadline_tick();if(!t->dead&&t->files==f&&t->stopped){owner=t;break;}}
    if(!owner) {
      /* A vfork parent is parked in the kernel and retains its OWN fd table.
       * The borrower may have closed every corresponding descriptor. Follow
       * the recorded vfork chain, not an arbitrary task sharing this mm.
       * PTRACE_EXIT precedes release of mm/files; we never resumed an EXIT
       * stop for this still non-exiting parent. Fatal signals therefore
       * cannot release its files before a new observed/serialized EXIT. */
      for(struct task*t=tasks;t&&!owner;t=t->next) {
        deadline_tick();if(t->dead||t->files!=f||!t->vfork_wait||t->exiting)continue;
        struct task*borrower=t;
        while(borrower->vfork_wait&&!borrower->stopped&&!borrower->exiting) {
          deadline_tick();struct task*child=find(borrower->vfork_child);
          if(!child||child==borrower||child->space!=borrower->space){borrower=NULL;break;}
          borrower=child;
        }
        if(borrower&&borrower->stopped&&!borrower->dead)owner=borrower;
      }
    }
    if(!owner)goto invalidated;
    if(ptrace(PTRACE_GETREGS,owner->pid,0,&validation_regs)<0) {
      if(errno!=ESRCH)fail("fd-owner validation failed");unstable(owner);goto invalidated;
    }
    for(struct fd_entry*e=f->entries;e;e=e->next){deadline_tick();if(e->fd>=0)e->object->witnessed=true;}
  }
  for(struct account_object*o=objects;o;o=o->next) {
    deadline_tick();
    if(o->live&&!o->witnessed)goto invalidated;
  }
  if(stage_receipt.state==JAYSTAGE_ARMED)deadline_signalled=1;
  deadline_tick();
  int r=jayacct_publish_observation(counter,words(current),observed,
                       JAYACCT_FROZEN|JAYACCT_INCOMPLETE|(hold_owner?JAYACCT_HELD:0),&latest);
  if(r)fail("counter publication failed");
  for(struct space*s=spaces;s;s=s->next)s->inherit=0;
  replace_mm=0;remap_mm=0;mapped_object=NULL;mapped_file_owner=NULL;retention_changed=NULL;retention_shrink=false;retention_hole=false;
  snapshot_in_progress=false;caches_dirty=false;
  ++snapshots;log_snapshot(cause,nr,phase);return true;
invalidated:
  /* Keep activation history from the last committed observation. The failed
   * bank can be reused, while any acquired slabs remain genuinely charged. */
  regions=previous;retained=previous_retained;bank_index^=1;++invalidated_observations;
  snapshot_in_progress=false;caches_dirty=true;
  log_lifecycle("observation_invalidated",cause,invalidated_observations,0);
  return false;
}
static bool copy_snapshot(struct task*t,const void*value,size_t bytes) {
  uintptr_t address=(uintptr_t)t->args[1];
  if(!address)fail("null barrier snapshot destination");
  const unsigned char*p=value;
  _Static_assert(sizeof latest%sizeof(long)==0,"ptrace words");
  _Static_assert(sizeof latest_window%sizeof(long)==0,"window ptrace words");
  for(size_t at=0;at<bytes;at+=sizeof(long)) {
    long word;memcpy(&word,p+at,sizeof word);
    if(ptrace(PTRACE_POKEDATA,t->pid,(void*)(address+at),(void*)(uintptr_t)word)<0) {
      if(errno==ESRCH){unstable(t);return false;}
      fail("barrier destination is not writable");
    }
  }
  return true;
}
static void begin_service_window(void) {
  /* Sole writer, immediately after the first real publication. The existing
   * window operation includes that baseline and allocates no backing. No
   * invented event is used for the pinned monotone static-startup prefix. */
  if(jayacct_window_open(counter,&latest_window))fail("open initial service window");
  if(report_fd<0)return;
  char*p=output_buffer;p=literal(p,"{\"type\":\"service_window_begin\",\"scope_id\":\"");
  p=decimal(p,wide(latest_window.scope_id));p=literal(p,"\",\"begin_sequence\":\"");
  p=decimal(p,wide(latest_window.begin_sequence));p=literal(p,"\",\"begin_time_ns\":\"");
  p=decimal(p,wide(latest_window.begin_monotonic_ns));p=literal(p,"\",\"peak\":\"");
  p=decimal(p,wide(latest_window.peak));p=literal(p,"\",\"peak_sequence\":\"");
  p=decimal(p,wide(latest_window.peak_sequence));p=literal(p,"\",\"peak_time_ns\":\"");
  p=decimal(p,wide(latest_window.peak_monotonic_ns));p=literal(p,"\",\"peak_flags\":");
  p=decimal(p,latest_window.peak_flags);p=literal(p,",\"state\":");p=decimal(p,latest_window.state);
  p=literal(p,"}\n");write_all(report_fd,output_buffer,(size_t)(p-output_buffer));
}
static void finish(void) {
  if(report_fd>=0) {
    char*p=output_buffer;p=literal(p,"{\"type\":\"summary\",\"root_status\":");p=decimal(p,(unsigned)root_status);
    p=literal(p,",\"snapshots\":");p=decimal(p,snapshots);p=literal(p,",\"syscall_stops\":");p=decimal(p,syscall_stops);
    p=literal(p,",\"current\":\"");p=decimal(p,wide(latest.current));p=literal(p,"\",\"peak\":\"");p=decimal(p,wide(latest.peak));
    p=literal(p,"\",\"peak_time_ns\":\"");p=decimal(p,wide(latest.peak_monotonic_ns));
    p=literal(p,"\",\"peak_sequence\":\"");p=decimal(p,wide(latest.peak_sequence));
    p=literal(p,"\",\"invalidated_observations\":");p=decimal(p,invalidated_observations);
    p=literal(p,",\"nonleader_execs\":");p=decimal(p,exec_identity_changes);
    p=literal(p,",\"group_stops\":");p=decimal(p,group_stops);
    p=literal(p,",\"uring_objects_created\":");p=decimal(p,ring_objects_created);
    p=literal(p,",\"unsupported_object_events\":");p=decimal(p,unsupported_object_events);
    p=literal(p,",\"deadline_cancellations\":");p=decimal(p,deadline_cancellations);
    p=literal(p,",\"recovered_syscall_results\":");p=decimal(p,recovered_syscall_results);
    p=literal(p,",\"unavailable_syscall_stops\":");p=decimal(p,unavailable_syscall_stops);
    p=literal(p,",\"recovered_event_metadata\":");p=decimal(p,recovered_event_metadata);
    p=literal(p,",\"proc_memory_reads\":");p=decimal(p,proc_memory_reads);
    p=literal(p,",\"alternate_fd_reads\":");p=decimal(p,alternate_fd_reads);
    p=literal(p,",\"complete\":false,\"observer_included\":true}\n");
    write_all(report_fd,output_buffer,(size_t)(p-output_buffer));
  }
}
#include "deadline.inc.c"
#include "stage.inc.c"
int main(int argc,char**argv) {
  prepare_observer_stack();
  int command=1;
  while(command<argc) {
    if(!strcmp(argv[command],"--stage-control")) {stage_control=true;++command;continue;}
    if(!strcmp(argv[command],"--service-window")) {service_window=true;++command;continue;}
    if(!strcmp(argv[command],"--report")&&command+1<argc) {
      if(report_fd>=0)fail("duplicate report option");
      report_fd=open(argv[command+1],O_WRONLY|O_CREAT|O_TRUNC|O_CLOEXEC,0600);
      if(report_fd<0)fail("open report");command+=2;continue;
    }
    break;
  }
  if(command<argc&&!strcmp(argv[command],"--"))++command;
  if(command>=argc)fail("usage: trace [--report PATH] [--service-window] [--stage-control] -- PROGRAM [ARG...]");
#ifdef JAYACCT_TEST_RACES
  test_kill_after_scan=getenv("JAYACCT_TEST_KILL_AFTER_SCAN")!=NULL;
  test_grow_marker_entry=getenv("JAYACCT_TEST_GROW_MARKER_ENTRY")!=NULL;
  test_deadline_wait=getenv("JAYACCT_TEST_DEADLINE_WAIT")!=NULL;
  test_deadline_scan=getenv("JAYACCT_TEST_DEADLINE_SCAN")!=NULL;
  test_kill_uring_exit=getenv("JAYACCT_TEST_KILL_URING_EXIT")!=NULL;
  test_kill_open_exit=getenv("JAYACCT_TEST_KILL_OPEN_EXIT")!=NULL;
  test_kill_truncate_exit=getenv("JAYACCT_TEST_KILL_TRUNCATE_EXIT")!=NULL;
  test_kill_uring_info=getenv("JAYACCT_TEST_KILL_URING_INFO")!=NULL;
  test_kill_open_info=getenv("JAYACCT_TEST_KILL_OPEN_INFO")!=NULL;
  test_kill_truncate_info=getenv("JAYACCT_TEST_KILL_TRUNCATE_INFO")!=NULL;
  test_deadline_retained=getenv("JAYACCT_TEST_DEADLINE_RETAINED")!=NULL;
  test_stage_scan=getenv("JAYACCT_TEST_STAGE_SCAN")!=NULL;
  test_stage_wait=getenv("JAYACCT_TEST_STAGE_WAIT")!=NULL;
  test_stage_commit=getenv("JAYACCT_TEST_STAGE_COMMIT")!=NULL;
#endif
  int fd=(int)syscall(SYS_memfd_create,"jaydb-allocation-counter",0);
  if(fd<0||ftruncate(fd,JAYACCT_SHARED_BYTES))fail("create shared counter");
  counter=mmap(NULL,JAYACCT_SHARED_BYTES,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);
  if(counter==MAP_FAILED||jayacct_init(counter,JAYACCT_SHARED_BYTES))fail("initialize counter");
  int stage_fd=-1;
  if(stage_control) {
    stage_fd=(int)syscall(SYS_memfd_create,"jaydb-stage-control-v1",0);
    if(stage_fd<0||ftruncate(stage_fd,JAYSTAGE_SHARED_BYTES))fail("create stage control");
    stage_page=mmap(NULL,JAYSTAGE_SHARED_BYTES,PROT_READ|PROT_WRITE,MAP_SHARED,stage_fd,0);
    if(stage_page==MAP_FAILED)fail("map stage control");
    stage_receipt.abi=JAYSTAGE_ABI;stage_publish();
  }
  deadline_initialize();
  /* The first observation already includes image, loader/TLS/libc and counter.
   * Subsequent bootstrap acquisitions are observed before creating the root. */
  if(!snapshot(0,0,"observer_counter_ready"))fail("unstable observer bootstrap");
  if(service_window)begin_service_window();
  char text[32],*end=decimal(text,(unsigned)fd);*end=0;
  if(setenv("JAYDB_ACCOUNTING_FD",text,1))fail("set counter descriptor environment");
  if(stage_control) {
    end=decimal(text,(unsigned)stage_fd);*end=0;
    if(setenv("JAYDB_ACCOUNTING_STAGE_FD",text,1))fail("set stage descriptor environment");
  }
  if(!snapshot(0,0,"observer_environment_ready"))fail("unstable observer environment");
  int gate[2];if(pipe2(gate,O_CLOEXEC))fail("create bootstrap gate");
  (void)allocate(&persistent,16); /* Acquire metadata slab before bootstrap fork. */
  if(!snapshot(0,0,"observer_metadata_ready"))fail("unstable observer metadata");
  root_pid=fork();if(root_pid<0)fail("fork traced root");
  if(!root_pid) {
    close(gate[1]);char ready;
    ssize_t n;do{n=read(gate[0],&ready,1);}while(n<0&&errno==EINTR);
    close(gate[0]);if(n!=1)_exit(126);
    /* The parent retains its wake handler. Restore the captured action in
     * this still-compatible pre-exec image, including flags/handler mask; a
     * real failure must not silently substitute SIG_DFL or launch the root. */
    if(stage_control&&sigaction(SIGCHLD,&stage_root_sigchld,NULL))_exit(126);
    execvp(argv[command],argv+command);_exit(127);
  }
  close(gate[0]);
  struct task*root=add_task(root_pid,new_space(),root_pid);
  root->files=files_copy(NULL);
  unsigned long options=PTRACE_O_TRACESYSGOOD|PTRACE_O_TRACEFORK|PTRACE_O_TRACEVFORK|
      PTRACE_O_TRACECLONE|PTRACE_O_TRACEEXEC|PTRACE_O_TRACEEXIT|PTRACE_O_TRACEVFORKDONE|PTRACE_O_EXITKILL;
  if(ptrace(PTRACE_SEIZE,root_pid,0,(void*)options)<0) {kill(root_pid,SIGKILL);fail("PTRACE_SEIZE denied");}
  if(ptrace(PTRACE_INTERRUPT,root_pid,0,0)<0)fail("initial interrupt");
  wait_one();write_all(gate[1],"1",1);close(gate[1]);
  while(any_alive()) {
    int escaped=sigsetjmp(deadline_escape,1);
    if(escaped) {
      if(escaped==1)deadline_cancel();
      if(!stage_terminal&&!stage_recovery&&any_alive()&&!queued_work())wait_one();
      continue;
    }
    if(stage_terminal) {
      sigset_t alarm,prior;
      if(sigemptyset(&alarm)||sigaddset(&alarm,SIGALRM)||sigprocmask(SIG_BLOCK,&alarm,&prior))fail("terminal signal mask");
      deadline_signalled=1;deadline_tick();(void)sigsuspend(&prior);
      if(sigprocmask(SIG_SETMASK,&prior,NULL))fail("terminal restore mask");
      continue;
    }
    deadline_maybe_arm();
    deadline_tick();
    if(last_stopped&&!last_stopped->dead&&last_stopped->stopped&&last_stopped->marker&&!last_stopped->stage_marker
        &&last_stopped->args[2]==JAYACCT_RELEASE_OPERATION) {
      release_hold(last_stopped);
      if(any_alive()&&!queued_work())wait_one();
      continue;
    }
    if(hold_owner&&!find(hold_owner))hold_owner=0;
    /* Non-memory syscall stops and delayed INTERRUPT stops do not require a
     * new world-stop. Interrupting every other thread again here produces a
     * feedback loop of artificial stops (not service progress). Stack growth
     * between memory barriers is monotone; observe it before the next release.
     * No allocating/freeing syscall is resumed by this fast path. */
    if(!stage_recovery&&!queued_work()&&!active&&last_stopped&&(!hold_owner||last_stopped->pid==hold_owner)
        &&!last_stopped->dead&&last_stopped->stopped
        &&!last_stopped->exiting&&!last_stopped->memory&&!memory_syscall(last_stopped)
        &&(last_stopped->event==0||last_stopped->event==PTRACE_EVENT_STOP)) {
      resume(last_stopped);wait_one();continue;
    }
    /* Do not interrupt an in-flight memory syscall just because another
     * task's queued stop was delivered first. Only its exit (or a defined
     * lifecycle event) tells us how MAP_FIXED/remap ownership changed. */
    if(active&&!active->dead&&!active->stopped) {
      for(struct task*t=tasks;!hold_owner&&t;t=t->next)
        if(t!=active&&t->exiting&&!t->dead)resume(t);
      wait_one();continue;
    }
    if(active&&!active->dead&&active->group_stop)active=NULL;
    if(active&&!active->dead&&active->event==PTRACE_EVENT_STOP) {
      resume(active);wait_one();continue;
    }
    stop_world();
    bool unresolved=pending!=NULL;
    for(struct task*t=tasks;t;t=t->next)
      {deadline_tick();if(!t->dead&&(t->creation_pending||t->exit_result_missing))unresolved=true;}
    if(unresolved){wait_one();continue;}
    if(active&&(active->dead||(!active->entry&&!active->exiting&&!active->marker)))active=NULL;
    /* vfork's parent cannot complete until the child runs. It has no memory
     * mutation after the event until the child execs/exits. */
    if(active&&active->event==PTRACE_EVENT_VFORK) {
      /* TASK_UNINTERRUPTIBLE vfork wait cannot reach a ptrace interrupt until
       * its child releases the borrowed mm. It cannot execute user code and
       * PTRACE_SYSCALL will stop it before returning from vfork. */
      active->vfork_wait=true;resume(active);active=NULL;
    }
    if(!active) {
      if(hold_owner)active=find(hold_owner);
      for(struct task*t=tasks;!active&&t;t=t->next)if(!t->dead&&t->stopped&&
          (t->exiting||(t->memory&&(t->entry||t->marker)))) {active=t;break;}
    }
    /* Establish only the selected owner's hold, before its observation. */
    if(active&&active->entry&&active->marker&&!active->stage_marker&&active->args[2]==1) {
      if(hold_owner&&!active->marker_hold_started)fail("nested accounting hold");
      hold_owner=active->pid;
      active->marker_hold_started=true;
    }
    if(active&&active->stage_marker&&active->entry&&!active->stage_prepared)stage_prepare(active);
    if(!snapshot(active?active->pid:0,active?active->nr:0,"barrier"))continue;
    stage_recovered();
    if(active) {
      bool marker_finished=false,hold_finished=false;
#ifdef JAYACCT_TEST_RACES
      if(test_grow_marker_entry&&active->entry&&active->marker) {
        test_grow_marker_entry=false;
        log_snapshot(active->pid,SYS_getpid,"test_marker_entry_before_growth");
        (void)allocate(&persistent,SLAB_BYTES-sizeof(struct slab)-16);
      }
#endif
      if(!active->entry&&active->marker&&active->stage_marker) {
        if(!stage_finish(active))continue;
        active->marker=false;active->stage_marker=false;active->memory=false;
        marker_finished=true;
      } else if(!active->entry&&active->marker) {
        deadline_tick();
        unsigned operation=(unsigned)active->args[2];
        if(operation>5)fail("unknown barrier operation");
        if(operation==2&&hold_owner!=active->pid)fail("hold_end by non-owner");
        if(operation>=3) {
          int code=operation==4&&stage_control&&
                   stage_receipt.state!=JAYSTAGE_IDLE&&stage_receipt.state!=JAYSTAGE_RETIRED?
                   EBUSY:operation==3?jayacct_window_open(counter,&latest_window):
                   operation==4?jayacct_window_close(counter,&latest_window):
                                jayacct_window_read(counter,&latest_window);
          if(code) {
            if(jayacct_window_read(counter,&latest_window))fail("window state read failed");
            latest_window.error=(unsigned)code;
          }
          if(!copy_snapshot(active,&latest_window,sizeof latest_window))continue;
        } else if(!copy_snapshot(active,&latest,sizeof latest))continue;
        log_snapshot(active->pid,SYS_getpid,operation==1?"hold_begin":operation==2?"hold_end":
                     operation==3?"window_begin":operation==4?"window_end":operation==5?"window_marker":"marker");
        active->marker=false;active->memory=false;active->marker_hold_started=false;
        marker_finished=true;
        if(operation==2){hold_owner=0;hold_finished=true;}
        if(deadline_task==active)deadline_disarm();
      }
      if(active->exiting&&active->nr==SYS_exit_group)
        for(struct task*t=tasks;t;t=t->next)if(t!=active&&!t->dead&&t->tgid==active->tgid)resume(t);
      /* An exec or group exit can require already-doomed siblings to retire. */
      for(struct task*t=tasks;!hold_owner&&t;t=t->next)if(t!=active&&t->exiting&&!t->dead)resume(t);
      resume(active);
      if(hold_finished||(marker_finished&&!hold_owner))for(struct task*t=tasks;t;t=t->next)
        if(t!=active&&!(t->entry&&t->memory)&&!t->exiting)resume(t);
      if(marker_finished)active=NULL;
    } else {
      for(struct task*t=tasks;t;t=t->next)resume(t);
    }
    if(any_alive()&&!queued_work())wait_one();
  }
  if(!snapshot(0,0,"retired"))fail("observer-only retirement was unstable");finish();
  (void)root;(void)monitor_failed;
  return root_status;
}
