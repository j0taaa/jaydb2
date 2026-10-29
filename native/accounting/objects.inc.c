/* Event identities for userspace-owned fd payloads. Included by trace.c after
 * its mmap-only metadata allocator; no libc allocation or new observer. */
enum { OBJECT_URING=1, OBJECT_SHARED_ANON=2, OBJECT_SHARED_FILE=3, OBJECT_MEMFD=4 };
struct account_object {
  struct account_object *next;
  uint64_t uid, kind, capacity[2];
  uint64_t major, minor, inode, size;
  bool live, witnessed;
};
struct fd_entry { struct fd_entry *next; int fd; bool cloexec; struct account_object*object; };
struct fd_table { struct fd_table *next; struct fd_entry*entries; bool live; };
static struct account_object *objects;
static struct fd_table *file_tables;
static uint64_t next_object, ring_objects_created, unsupported_object_events;
static struct io_uring_params ring_parameters;
static struct account_object *object_new(unsigned kind) {
  struct account_object*o=caches_dirty?NULL:objects;while(o&&o->live)o=o->next;
  if(!o){o=allocate(&persistent,sizeof *o);o->next=objects;objects=o;}
  if(next_object==UINT64_MAX)fail("backing identity generation overflow");
  struct account_object*next=o->next;memset(o,0,sizeof *o);o->next=next;
  o->uid=++next_object;o->kind=kind;o->live=true;return o;
}
/* The committed interval history lives in the same immutable scan bank as
 * regions. Syscall changes remain pending until a validated observation. */
struct retained_range {
  struct retained_range *next;
  struct account_object*object;
  uint64_t uid, part, lo, hi;
};
static struct retained_range *retained, *previous_retained;
static struct account_object *retention_changed;
static uint64_t retention_uid, retention_lo, retention_hi, retention_limit;
static bool retention_shrink, retention_hole;
static bool object_referenced(struct account_object*object) {
  for(struct region*r=regions;r;r=r->next){deadline_tick();if(r->object==object||r->file_owner==object)return true;}
  for(struct region*r=previous;r;r=r->next){deadline_tick();if(r->object==object||r->file_owner==object)return true;}
  for(struct retained_range*r=previous_retained;r;r=r->next) {
    deadline_tick();if(r->object==object&&r->uid==object->uid)return true;
  }
  for(struct task*t=tasks;t;t=t->next)if(!t->dead&&t->files)
    for(struct fd_entry*e=t->files->entries;e;e=e->next){deadline_tick();if(e->fd>=0&&e->object==object)return true;}
  return false;
}
static struct account_object*file_object(uint64_t major,uint64_t minor,uint64_t inode,bool create) {
  for(struct account_object*o=objects;o;o=o->next) {
    deadline_tick();
    if((o->kind==OBJECT_SHARED_FILE||o->kind==OBJECT_MEMFD)&&
        o->major==major&&o->minor==minor&&o->inode==inode&&
        (caches_dirty?object_referenced(o):o->live))return o;
  }
  if(!create)return NULL;
  struct account_object*o=object_new(OBJECT_SHARED_FILE);
  o->major=major;o->minor=minor;o->inode=inode;return o;
}
static struct fd_entry*files_find(struct fd_table*f,int fd) {
  if(fd<0)return NULL;
  if(f)for(struct fd_entry*e=f->entries;e;e=e->next)if(e->fd==fd)return e;
  return NULL;
}
static void files_set(struct fd_table*f,int fd,struct account_object*object,bool cloexec) {
  if(!f)return;
  struct fd_entry*e=files_find(f,fd);
  if(!object){if(e)e->fd=-1;return;}
  if(!e) {
    e=f->entries;while(e&&e->fd>=0)e=e->next;
    if(!e){e=allocate(&persistent,sizeof *e);e->next=f->entries;f->entries=e;}
  }
  e->fd=fd;e->object=object;e->cloexec=cloexec;
}
static struct fd_table*files_copy(struct fd_table*old) {
  struct fd_table*f=caches_dirty?NULL:file_tables;while(f&&f->live)f=f->next;
  if(!f){f=allocate(&persistent,sizeof *f);f->next=file_tables;file_tables=f;}
  for(struct fd_entry*e=f->entries;e;e=e->next)e->fd=-1;
  f->live=true;
  if(old)for(struct fd_entry*e=old->entries;e;e=e->next)
    if(e->fd>=0)files_set(f,e->fd,e->object,e->cloexec);
  return f;
}
static void files_exec(struct fd_table*f) {
  if(f)for(struct fd_entry*e=f->entries;e;e=e->next)if(e->fd>=0&&e->cloexec)e->fd=-1;
}
static bool proc_memory_copy(struct task*t,uint64_t address,void*destination,size_t bytes) {
  char path[64],*p=path;p=literal(p,"/proc/");p=decimal(p,(unsigned)t->pid);
  p=literal(p,"/mem");*p=0;
  int fd;do{fd=open(path,O_RDONLY|O_CLOEXEC);}while(fd<0&&errno==EINTR);
  if(fd<0)return false;
  size_t done=0;
  while(done<bytes) {
    ssize_t n=pread(fd,(char*)destination+done,bytes-done,(off_t)(address+done));
    if(n<0&&errno==EINTR)continue;
    if(n<=0)break;done+=(size_t)n;
  }
  close(fd);
  if(done!=bytes)return false;
  ++proc_memory_reads;
  log_lifecycle("proc_memory_descriptor",t->pid,bytes,t->space->uid);return true;
}
static bool remote_copy(struct task*t,uint64_t address,void*destination,size_t bytes) {
  if(bytes>UINT64_MAX-address)return false;
  unsigned char*out=destination;
  /* Try the exact owner first, then only tasks with the recorded same mm.
   * /proc/PID/mem can return real bytes while fatal-pending ptrace freeze
   * refuses PEEKDATA. It does not resurrect an mm or fabricate missing bytes. */
  struct task*reader=t;
  for(;;) {
    bool readable=reader->stopped;
    for(size_t at=0;at<bytes;at+=sizeof(long)) {
      if(!readable)break;
      errno=0;long word=ptrace(PTRACE_PEEKDATA,reader->pid,(void*)(uintptr_t)(address+at),NULL);
      if(word==-1&&errno) {
        if(errno==ESRCH)unstable(reader);
        readable=false;break;
      }
      size_t n=bytes-at<sizeof word?bytes-at:sizeof word;memcpy(out+at,&word,n);
    }
    if(readable)return true;
    if(!reader->dead&&proc_memory_copy(reader,address,destination,bytes))return true;
    struct task*next=reader==t?tasks:reader->next;
    while(next&&(next==t||next->dead||next->space!=t->space))next=next->next;
    if(!next)return false;reader=next;
  }
}
static void fd_path(char*path,struct task*t,int fd,bool info) {
  char*p=path;p=literal(p,"/proc/");p=decimal(p,(unsigned)t->pid);
  p=literal(p,info?"/fdinfo/":"/fd/");p=decimal(p,(unsigned)fd);*p=0;
}
static bool task_fd_status(struct task*t,int fd,struct stat*out) {
  struct task*reader=t;
  for(;;) {
    char path[96];fd_path(path,reader,fd,false);
    if(!stat(path,out)){if(reader!=t)++alternate_fd_reads;return true;}
    struct task*next=reader==t?tasks:reader->next;
    while(next&&(next==t||next->dead||next->files!=t->files))next=next->next;
    if(!next)return false;reader=next;
  }
}
static int task_fdinfo(struct task*t,int fd) {
  struct task*reader=t;
  for(;;) {
    char path[96];fd_path(path,reader,fd,true);
    int out;do{out=open(path,O_RDONLY|O_CLOEXEC);}while(out<0&&errno==EINTR);
    if(out>=0){if(reader!=t)++alternate_fd_reads;return out;}
    struct task*next=reader==t?tasks:reader->next;
    while(next&&(next==t||next->dead||next->files!=t->files))next=next->next;
    if(!next)return -1;reader=next;
  }
}
static uint64_t page_capacity(uint64_t n) {
  if(n>UINT64_MAX-4095)fail("returned allocation capacity overflow");
  return (n+4095)&~UINT64_C(4095);
}
static bool objects_memory_syscall(struct task*t) {
  struct fd_entry*e=files_find(t->files,(int)t->args[0]);
  if(!e||e->object->kind!=OBJECT_MEMFD)return false;
  switch(t->nr) {
  case SYS_write:case SYS_writev:case SYS_pwrite64:case SYS_pwritev:case SYS_pwritev2:
  case SYS_read:case SYS_readv:case SYS_lseek:case SYS_fallocate:return true;
  default:return false;
  }
}
static uint64_t file_position(struct task*t,int fd,bool*append) {
  char buffer[128];int source=task_fdinfo(t,fd);
  if(source<0)fail("cannot inspect completed memfd write position");
  ssize_t n;do{n=read(source,buffer,sizeof buffer-1);}while(n<0&&errno==EINTR);
  close(source);if(n<=0)fail("cannot read completed memfd write position");buffer[n]=0;
  if(strncmp(buffer,"pos:",4))fail("unsupported fdinfo position format");
  const char*s=buffer+4;while(*s==' '||*s=='\t')++s;
  uint64_t pos=0;bool got=false;
  while(*s>='0'&&*s<='9') {
    unsigned digit=(unsigned)(*s++-'0');
    if(pos>(UINT64_MAX-digit)/10)fail("memfd position overflow");pos=pos*10+digit;got=true;
  }
  if(!got)fail("missing memfd position");
  s=strstr(buffer,"\nflags:");if(!s)fail("missing memfd open flags");s+=7;
  while(*s==' '||*s=='\t')++s;
  uint64_t flags=0;got=false;
  while(*s>='0'&&*s<='7'){flags=flags*8+(unsigned)(*s++-'0');got=true;}
  if(!got)fail("missing memfd open flags value");*append=(flags&O_APPEND)!=0;return pos;
}
static void object_resize(struct account_object*o,uint64_t size,bool truncate) {
  if(size<o->size||(truncate&&size==o->size)) {
    retention_changed=o;retention_uid=o->uid;retention_shrink=true;
    retention_hole=false;
    retention_lo=retention_hi=0;retention_limit=page_capacity(size);
  }
  o->size=size;
}
static bool object_fd_status(struct account_object*o,struct stat*status) {
  for(struct task*t=tasks;t;t=t->next)if(!t->dead&&t->files)
    for(struct fd_entry*e=t->files->entries;e;e=e->next)if(e->fd>=0&&e->object==o) {
      char path[96],*p=path;p=literal(p,"/proc/");p=decimal(p,(unsigned)t->pid);
      p=literal(p,"/fd/");p=decimal(p,(unsigned)e->fd);*p=0;
      if(!stat(path,status)&&major(status->st_dev)==o->major&&minor(status->st_dev)==o->minor&&status->st_ino==o->inode)
        return true;
    }
  return false;
}
static void objects_truncated(struct task*t) {
  struct stat status;
  if(task_path_status(t,t->args[0],AT_FDCWD,0,0,&status)) {
    struct account_object*o=file_object(major(status.st_dev),minor(status.st_dev),status.st_ino,false);
    /* Ordinary contents/page cache do not become fd payload. Avoid touching
     * other objects' pending events while such a nonserial call completes.
     * Pathname replacement between preflight and lookup is still incomplete;
     * diagnose an adapted target discovered after nonserial execution. */
    if(!o)return;
    if(!t->memory)++unsupported_object_events;
    if(o&&o->kind==OBJECT_MEMFD) {
      if(status.st_size<0)fail("invalid truncated memfd size");
      object_resize(o,(uint64_t)status.st_size,true);
    }
  } else ++unsupported_object_events;
  /* Size reconciliation uses actual known owners, not a guessed pathname or
   * a size-to-allocation conversion. This also finds a shrink through procfs
   * aliases whose magic self/root cannot be resolved in the observer. A
   * same-size truncate through such an unresolved alias remains incomplete. */
  for(struct account_object*o=objects;o;o=o->next)if(o->live&&o->kind==OBJECT_MEMFD&&object_fd_status(o,&status)) {
    if(status.st_size<0)fail("invalid retained memfd size");
    if((uint64_t)status.st_size!=o->size)object_resize(o,(uint64_t)status.st_size,false);
  }
}
static void objects_fallocated(struct task*t,struct account_object*o) {
  unsigned mode=(unsigned)t->args[1];
  uint64_t start=t->args[2],length=t->args[3];
  if(start>INT64_MAX||length>INT64_MAX||!length||length>INT64_MAX-start)
    fail("invalid successful memfd fallocate extent");
  uint64_t end=start+length;
  if(mode&~(FALLOC_FL_KEEP_SIZE|FALLOC_FL_PUNCH_HOLE)) {
    ++unsupported_object_events;return; /* Never guess newly supported modes. */
  }
  retention_changed=o;retention_uid=o->uid;retention_shrink=false;
  retention_hole=(mode&FALLOC_FL_PUNCH_HOLE)!=0;
  if(retention_hole) {
    /* Only complete base pages are returned. Partial boundary pages are
     * zeroed and retained, and compound-folio kernel padding is not charged. */
    retention_lo=page_capacity(start);retention_hi=end&~UINT64_C(4095);
  } else {
    retention_lo=start&~UINT64_C(4095);retention_hi=page_capacity(end);
    if(!(mode&FALLOC_FL_KEEP_SIZE)&&end>o->size)o->size=end;
  }
}
static void files_opened(struct task*t,int fd) {
  /* The pathname and spelling of /proc links do not establish ownership.
   * Collect the actual returned descriptor at syscall-exit, before a world
   * stop can reconcile/retire owners or the caller resumes userspace. Never create
   * a RAM object from an arbitrary regular-file descriptor. */
  struct stat status;if(!task_fd_status(t,fd,&status))fail("cannot identify opened descriptor");
  struct account_object*o=file_object(major(status.st_dev),minor(status.st_dev),status.st_ino,false);
  if(!o||o->kind!=OBJECT_MEMFD)return;
  /* Read the descriptor's installed flags, also covering openat2 and O_PATH.
   * Do not dereference a caller's open_how after the kernel consumed it. */
  int source=task_fdinfo(t,fd);
  if(source<0)fail("cannot inspect opened descriptor flags");
  char buffer[256];ssize_t n;do{n=read(source,buffer,sizeof buffer-1);}while(n<0&&errno==EINTR);
  close(source);if(n<=0)fail("cannot read opened descriptor flags");buffer[n]=0;
  const char*s=strstr(buffer,"\nflags:");if(!s)fail("missing opened descriptor flags");s+=7;
  while(*s==' '||*s=='\t')++s;
  uint64_t flags=number(&s,8);
  files_set(t->files,fd,o,(flags&O_CLOEXEC)!=0);
  if(status.st_size<0)fail("invalid opened memfd size");
  object_resize(o,(uint64_t)status.st_size,t->open_truncate);
}
static void objects_syscall_exit(struct task*t,int64_t result,bool error) {
  if(!t->files)t->files=files_copy(NULL);
  if(t->nr==SYS_close) {
    /* Linux releases the descriptor before reporting later flush errors. */
    if(!error||result!=-EBADF)files_set(t->files,(int)t->args[0],NULL,false);
    return;
  }
  if(error)return;
  struct fd_entry*target=files_find(t->files,(int)t->args[0]);
  if(t->nr==SYS_truncate) {
    objects_truncated(t);
  } else if(t->nr==SYS_open||t->nr==SYS_openat||t->nr==SYS_openat2||t->nr==SYS_creat) {
    files_opened(t,(int)result);
  } else if(t->nr==SYS_memfd_create) {
    /* A RAM object starts with no acquired intervals. Size/reservation alone
     * is never charged. fd lifecycle keeps later delivered capacity owned. */
    struct account_object*o=object_new(OBJECT_MEMFD);
    struct stat status;if(!task_fd_status(t,(int)result,&status))fail("cannot identify returned memfd");
    o->major=major(status.st_dev);o->minor=minor(status.st_dev);o->inode=status.st_ino;
    if(t->args[1]&MFD_HUGETLB)++unsupported_object_events;
    files_set(t->files,(int)result,o,(t->args[1]&MFD_CLOEXEC)!=0);
  } else if(target&&target->object->kind==OBJECT_MEMFD&&t->nr==SYS_ftruncate) {
    object_resize(target->object,t->args[1],true);
  } else if(target&&target->object->kind==OBJECT_MEMFD&&t->nr==SYS_fallocate) {
    objects_fallocated(t,target->object);
  } else if(target&&target->object->kind==OBJECT_MEMFD&&result>0&&
      (t->nr==SYS_write||t->nr==SYS_writev||t->nr==SYS_pwrite64||t->nr==SYS_pwritev||t->nr==SYS_pwritev2)) {
    uint64_t end,start;bool append;
    uint64_t position=file_position(t,(int)t->args[0],&append);
    bool explicit_append=t->nr==SYS_pwritev2&&(t->args[5]&0x10); /* RWF_APPEND */
    if(t->nr==SYS_pwritev2&&(t->args[5]&0x20))append=false; /* RWF_NOAPPEND */
    if(append||explicit_append) {
      struct stat status;if(!task_fd_status(t,(int)t->args[0],&status)||status.st_size<result)fail("cannot inspect appended memfd extent");
      end=(uint64_t)status.st_size;start=end-(uint64_t)result;
    } else if(t->nr==SYS_write||t->nr==SYS_writev||
        (t->nr==SYS_pwritev2&&t->args[3]==UINT64_MAX)) {
      end=position;
      if(end<(uint64_t)result)fail("invalid completed memfd write extent");start=end-(uint64_t)result;
    } else {
      /* Native x86_64 pos_from_hilo keeps the entire unsigned-long low
       * argument. The 32+32 split belongs to compat syscalls, not this ABI. */
      start=t->args[3];
      if((uint64_t)result>UINT64_MAX-start)fail("memfd write extent overflow");end=start+(uint64_t)result;
    }
    struct account_object*o=target->object;
    if(end>o->size)o->size=end;
    retention_changed=o;retention_uid=o->uid;retention_shrink=false;
    retention_hole=false;
    retention_lo=start&~UINT64_C(4095);retention_hi=page_capacity(end);
  } else if(t->nr==SYS_io_uring_setup) {
    if(!remote_copy(t,t->args[1],&ring_parameters,sizeof ring_parameters))
      fail("allocation descriptor lost with its mm; no observation published");
    struct io_uring_params*p=&ring_parameters;
    if(p->flags&IORING_SETUP_NO_MMAP) {
      /* Caller-provided backing was already acquired by its allocator. */
      ++unsupported_object_events;return;
    }
    uint64_t ring=(uint64_t)p->cq_off.cqes+(uint64_t)p->cq_entries*((p->flags&IORING_SETUP_CQE32)?32:16);
    if(!(p->flags&IORING_SETUP_NO_SQARRAY)) {
      uint64_t sq=(uint64_t)p->sq_off.array+(uint64_t)p->sq_entries*4;if(sq>ring)ring=sq;
    }
    struct account_object*o=object_new(OBJECT_URING);
    o->capacity[0]=page_capacity(ring);
    o->capacity[1]=page_capacity((uint64_t)p->sq_entries*((p->flags&IORING_SETUP_SQE128)?128:64));
    files_set(t->files,(int)result,o,true);++ring_objects_created;
    log_object(t->pid,o->capacity[0]+o->capacity[1],o->uid);
  } else if(t->nr==SYS_dup||t->nr==SYS_dup2||t->nr==SYS_dup3) {
    struct fd_entry*e=files_find(t->files,(int)t->args[0]);
    if(t->nr==SYS_dup2&&t->args[0]==t->args[1])return;
    files_set(t->files,(int)result,e?e->object:NULL,t->nr==SYS_dup3&&(t->args[2]&O_CLOEXEC));
  } else if(t->nr==SYS_fcntl) {
    struct fd_entry*e=files_find(t->files,(int)t->args[0]);
    unsigned command=(unsigned)t->args[1];
    if(command==F_DUPFD||command==F_DUPFD_CLOEXEC)
      files_set(t->files,(int)result,e?e->object:NULL,command==F_DUPFD_CLOEXEC);
    else if(command==F_SETFD&&e)e->cloexec=(t->args[2]&FD_CLOEXEC)!=0;
  } else if(t->nr==SYS_close_range) {
    if(t->args[2]&2)t->files=files_copy(t->files); /* CLOSE_RANGE_UNSHARE */
    for(struct fd_entry*e=t->files->entries;e;e=e->next)
      if(e->fd>=0&&(uint64_t)e->fd>=t->args[0]&&(uint64_t)e->fd<=t->args[1]) {
        if(t->args[2]&4)e->cloexec=true;else e->fd=-1; /* CLOSE_RANGE_CLOEXEC */
      }
  } else if(t->nr==SYS_unshare&&(t->args[0]&CLONE_FILES)) {
    t->files=files_copy(t->files);
  } else if(t->nr==SYS_io_uring_register) {
    /* Actual closure uses no registration. Do not guess ownership for an
     * unexpectedly reached kernel-allocated registration subtype. */
    ++unsupported_object_events;
  }
}
static void objects_reconcile(void) {
  for(struct fd_table*f=file_tables;f;f=f->next){deadline_tick();f->live=false;}
  for(struct account_object*o=objects;o;o=o->next){deadline_tick();o->live=false;o->witnessed=false;}
  for(struct task*t=tasks;t;t=t->next){deadline_tick();if(!t->dead&&t->files)t->files->live=true;}
  for(struct fd_table*f=file_tables;f;f=f->next)if(f->live)
    for(struct fd_entry*e=f->entries;e;e=e->next){deadline_tick();if(e->fd>=0)e->object->live=true;}
  for(struct region*r=regions;r;r=r->next) {
    deadline_tick();if(r->object)r->object->live=true;
    if(r->file_owner)r->file_owner->live=true;
  }
  fd_payload_bytes=0;
  for(struct account_object*o=objects;o;o=o->next){deadline_tick();if(o->live&&o->kind==OBJECT_URING)
    fd_payload_bytes+=(__uint128_t)o->capacity[0]+o->capacity[1];
  }
}
static void retain_interval(struct account_object*object,uint64_t part,uint64_t lo,uint64_t hi) {
  /* Explicit fd preallocation may retain backing beyond i_size (KEEP_SIZE).
   * Only new mapping activations are clamped to i_size, at their call site. */
  if(lo>=hi)return;
  struct retained_range**at=&retained;
  while(*at) {
    deadline_tick();struct retained_range*r=*at;
    if(r->uid>object->uid||(r->uid==object->uid&&r->part>part))break;
    if(r->uid==object->uid&&r->part==part&&r->hi>=lo) {
      if(r->lo>hi)break;
      if(lo<r->lo)r->lo=lo;if(hi>r->hi)r->hi=hi;
      while(r->next&&r->next->uid==r->uid&&r->next->part==part&&r->next->lo<=r->hi) {
        deadline_tick();if(r->next->hi>r->hi)r->hi=r->next->hi;r->next=r->next->next;
      }
      return;
    }
    at=&r->next;
  }
  struct retained_range*r=allocate(building,sizeof *r);
  r->object=object;r->uid=object->uid;r->part=part;r->lo=lo;r->hi=hi;
  r->next=*at;*at=r;
}
static __uint128_t retained_build(void) {
  /* This builds a new bank only. Neither old intervals nor pending syscall
   * changes are destroyed if scan/validation/deadline later fails. */
  retained=NULL;
  for(struct retained_range*r=previous_retained;r;r=r->next) {
    deadline_tick();struct account_object*o=r->object;
    if(!o->live||o->uid!=r->uid)continue;
    uint64_t hi=r->hi;
    if(retention_shrink&&o==retention_changed&&o->uid==retention_uid&&hi>retention_limit)hi=retention_limit;
    if(retention_hole&&o==retention_changed&&o->uid==retention_uid&&retention_lo<retention_hi&&
        r->lo<retention_hi&&hi>retention_lo) {
      if(r->lo<retention_lo)retain_interval(o,r->part,r->lo,hi<retention_lo?hi:retention_lo);
      if(hi>retention_hi)retain_interval(o,r->part,r->lo>retention_hi?r->lo:retention_hi,hi);
      continue;
    }
    retain_interval(o,r->part,r->lo,hi);
  }
  for(struct region*r=regions;r;r=r->next) {
    deadline_tick();
    if(r->active&&r->object&&r->object->kind!=OBJECT_URING) {
      uint64_t hi=r->offset+r->hi-r->lo;
      if(r->object->kind==OBJECT_MEMFD&&hi>page_capacity(r->object->size))hi=page_capacity(r->object->size);
      retain_interval(r->object,r->part,r->offset,hi);
    }
  }
  if(retention_changed&&retention_changed->uid==retention_uid&&retention_changed->live&&!retention_shrink&&!retention_hole)
    retain_interval(retention_changed,0,retention_lo,retention_hi);
  __uint128_t amount=0;
  for(struct retained_range*r=retained;r;r=r->next){deadline_tick();amount+=r->hi-r->lo;}
  return amount;
}
