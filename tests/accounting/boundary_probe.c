#define _GNU_SOURCE
#include "counter.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/openat2.h>
#include <sched.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#define M (1024u*1024u)
static void stage(const char*name) {
  struct jayacct_snapshot s;assert(!jayacct_barrier(&s));
  printf("%s %llu\n",name,(unsigned long long)s.sequence.lo);
}
static int ram(void) {
  int fd=(int)syscall(SYS_memfd_create,"jayacct-boundaries",MFD_CLOEXEC);
  assert(fd>=0&&!ftruncate(fd,4*M));return fd;
}
static void path_for(int fd,char*path,size_t size) {
  assert(snprintf(path,size,"/proc/self/fd/%d",fd)>0);
}
static char*view_at(void*at,int fd,size_t bytes,int prot,off_t offset) {
  char*p=mmap(at,bytes,prot,MAP_SHARED|(at?MAP_FIXED:0),fd,offset);
  assert(p!=MAP_FAILED);return p;
}
static void acquire(int fd) {
  char*p=view_at(NULL,fd,M,PROT_READ|PROT_WRITE,0);p[0]=42;assert(!munmap(p,M));
}
static int reopen_fd(const char*mode,const char*path) {
  if(!strcmp(mode,"open"))return (int)syscall(SYS_open,path,O_RDWR|O_CLOEXEC,0);
  if(!strcmp(mode,"openat")) {
    int dir=open("/proc/self/fd",O_PATH|O_DIRECTORY|O_CLOEXEC);assert(dir>=0);
    const char*relative=strrchr(path,'/');assert(relative);
    int fd=(int)syscall(SYS_openat,dir,relative+1,O_RDWR,0);assert(!close(dir));return fd;
  }
  if(!strcmp(mode,"openat2")) {
    struct open_how how={.flags=O_RDWR|O_CLOEXEC};
    return (int)syscall(SYS_openat2,AT_FDCWD,path,&how,sizeof how);
  }
  if(!strcmp(mode,"path"))return open(path,O_PATH|O_CLOEXEC);
  if(!strcmp(mode,"read"))return open(path,O_RDONLY|O_CLOEXEC);
  if(!strcmp(mode,"truncate"))return open(path,O_RDWR|O_TRUNC|O_CLOEXEC);
  if(!strcmp(mode,"truncate_openat2")) {
    struct open_how how={.flags=O_RDWR|O_TRUNC|O_CLOEXEC};
    return (int)syscall(SYS_openat2,AT_FDCWD,path,&how,sizeof how);
  }
  if(!strcmp(mode,"creat"))return (int)syscall(SYS_creat,path,0600);
  assert(false);return -1;
}
static void opened_owner(const char*mode) {
  int fd=ram();char path[96];path_for(fd,path,sizeof path);stage("baseline");
  acquire(fd);stage("acquired");
  /* Failed open must neither create an owner nor release existing history. */
  errno=0;assert(open(path,O_RDWR|O_NOFOLLOW)<0&&errno==ELOOP);stage("failed_open");
  int reopened=reopen_fd(mode,path);assert(reopened>=0);
  struct stat a,b;assert(!fstat(fd,&a)&&!fstat(reopened,&b));
  assert(a.st_dev==b.st_dev&&a.st_ino==b.st_ino);assert(!close(fd));stage("reopened_only");
  bool truncated=!strncmp(mode,"truncate",8)||!strcmp(mode,"creat");
  if(truncated)assert(!b.st_size);
  else if(strcmp(mode,"path")) {char byte=0;assert(pread(reopened,&byte,1,0)==1&&byte==42);}
  int copy=(int)syscall(SYS_fcntl,reopened,UINT64_C(0x100000000)|F_DUPFD,80);
  assert(copy>=80&&!close(reopened));stage("dup_only");
  int clo=fcntl(copy,F_DUPFD_CLOEXEC,100);assert(clo>=100&&!close(copy));
  assert(fcntl(clo,F_GETFD)==FD_CLOEXEC);stage("dup_cloexec_only");
  assert(!fcntl(clo,F_SETFD,0)&&!fcntl(clo,F_GETFD));
  assert(!fcntl(clo,F_SETFD,FD_CLOEXEC));assert(!close(clo));stage("closed");
}
static void reopened_exec(char*program) {
  int fd=ram(),gate[2];char path[96];path_for(fd,path,sizeof path);assert(!pipe(gate));
  stage("baseline");acquire(fd);
  int reopened=reopen_fd("openat2",path);assert(reopened>=0&&!close(fd));
  int kept=fcntl(reopened,F_DUPFD,80),clo=fcntl(reopened,F_DUPFD_CLOEXEC,100);
  assert(kept>=80&&clo>=100&&!close(reopened));
  /* Exercise both directions of F_SETFD before copying the fd table. */
  assert(!fcntl(kept,F_SETFD,FD_CLOEXEC)&&!fcntl(kept,F_SETFD,0));
  char k[24],c[24];snprintf(k,sizeof k,"%d",kept);snprintf(c,sizeof c,"%d",clo);
  pid_t child=fork();assert(child>=0);
  if(!child) {
    char byte;if(read(gate[0],&byte,1)!=1)_exit(3);
    execl(program,program,"exec_stage",k,c,(char*)NULL);_exit(4);
  }
  assert(!close(kept)&&!close(clo));stage("child_only");
  assert(write(gate[1],"x",1)==1);
  int status;assert(waitpid(child,&status,0)==child&&status==0);stage("retired");
  assert(!close(gate[0])&&!close(gate[1]));
}
static void reopened_exec_direct(char*program,bool cloexec) {
  int fd=ram(),gate[2];char path[96];path_for(fd,path,sizeof path);assert(!pipe(gate));
  stage("baseline");acquire(fd);
  int reopened=reopen_fd(cloexec?"openat2":"openat",path);assert(reopened>=0&&!close(fd));
  char number[24];snprintf(number,sizeof number,"%d",reopened);
  pid_t child=fork();assert(child>=0);
  if(!child) {
    char byte;if(read(gate[0],&byte,1)!=1)_exit(3);
    execl(program,program,"exec_direct_stage",number,cloexec?"1":"0",(char*)NULL);_exit(4);
  }
  assert(!close(reopened));stage("child_only");assert(write(gate[1],"x",1)==1);
  int status;assert(waitpid(child,&status,0)==child&&status==0);stage("retired");
  assert(!close(gate[0])&&!close(gate[1]));
}
static void regular_owner(void) {
  char path[]="/tmp/jayacct-boundary-XXXXXX";int fd=mkstemp(path);assert(fd>=0&&!ftruncate(fd,M));
  stage("baseline");acquire(fd);stage("regular_unmapped");
  char proc[96];path_for(fd,proc,sizeof proc);int reopened=open(proc,O_RDWR|O_CLOEXEC);
  assert(reopened>=0&&!close(fd));stage("regular_reopened");
  char byte=0;assert(pread(reopened,&byte,1,0)==1&&byte==42);
  assert(!close(reopened)&&!unlink(path));stage("closed");
}
static void remap_edges(void) {
  int fd=ram();stage("baseline");
  char*p=view_at(NULL,fd,2*M,PROT_NONE,0);assert(!mprotect(p,M,PROT_READ|PROT_WRITE));
  p[0]=42;stage("first_offset");
  /* Linux rounds both start and size DOWN for remap_file_pages. */
  assert(!syscall(SYS_remap_file_pages,p+17,M+127,0,2*M/4096,0));p[0]=43;stage("new_offset");
  char byte=0;assert(pread(fd,&byte,1,0)==1&&byte==42);
  assert(pread(fd,&byte,1,2*M)==1&&byte==43);
  assert(!syscall(SYS_remap_file_pages,p,M,0,0,0)&&p[0]==42);stage("old_offset_again");
  errno=0;assert(syscall(SYS_remap_file_pages,p,M,PROT_READ,M/4096,0)<0&&errno==EINVAL);
  stage("failed_remap");assert(!mprotect(p,M,PROT_NONE));
  assert(!syscall(SYS_remap_file_pages,p,M,0,M/4096,0));stage("new_reserved_offset");
  assert(!mprotect(p,M/4,PROT_READ|PROT_WRITE));p[0]=44;stage("partial_activation");
  int other=ram();assert(view_at(p,other,M,PROT_NONE,0)==p);
  assert(!syscall(SYS_remap_file_pages,p,M,0,M/4096,0));stage("replacement_reserved");
  assert(!mprotect(p,4096,PROT_READ|PROT_WRITE));p[0]=45;stage("replacement_active");
  assert(!munmap(p,2*M));stage("fds_only");
  assert(!close(fd));stage("second_fd_only");assert(!close(other));stage("closed");
}
static void remap_anon(void) {
  stage("baseline");
  char*p=mmap(NULL,2*M,PROT_NONE,MAP_SHARED|MAP_ANONYMOUS,-1,0);assert(p!=MAP_FAILED);
  assert(!mprotect(p,M,PROT_READ|PROT_WRITE));p[0]=42;stage("first_offset");
  assert(!syscall(SYS_remap_file_pages,p,M,0,M/4096,0));p[0]=43;stage("second_offset");
  assert(!munmap(p,M));stage("reservation_retains");
  assert(!mprotect(p+M,M,PROT_READ|PROT_WRITE)&&p[M]==43);stage("alias_reactivated");
  assert(!munmap(p+M,M));stage("closed");
}
static void query_locks(void) {
  int fd=ram();stage("before_queries");
  assert(fcntl(fd,F_GETFD)==FD_CLOEXEC&&fcntl(fd,F_GETFL)>=0);
  assert(fcntl(fd,F_GETLEASE)>=0&&fcntl(fd,F_GET_SEALS)>=0);
  struct flock lock={.l_type=F_WRLCK,.l_whence=SEEK_SET,.l_len=1};
  assert(!fcntl(fd,F_GETLK,&lock)&&lock.l_type==F_UNLCK);lock.l_type=F_WRLCK;
  assert(!fcntl(fd,F_SETLK,&lock));lock.l_type=F_UNLCK;assert(!fcntl(fd,F_SETLKW,&lock));
  lock.l_type=F_WRLCK;assert(!fcntl(fd,F_OFD_GETLK,&lock)&&lock.l_type==F_UNLCK);
  lock.l_type=F_WRLCK;assert(!fcntl(fd,F_OFD_SETLK,&lock));
  lock.l_type=F_UNLCK;assert(!fcntl(fd,F_OFD_SETLKW,&lock));
  assert(fcntl(fd,1027,fd)==1); /* Linux 7.0 F_DUPFD_QUERY: same open description. */
  stage("after_queries");assert(!close(fd));
}
static void ofd_wait(void) {
  int fd=ram(),ready[2];char path[96];path_for(fd,path,sizeof path);assert(!pipe(ready));
  struct flock lock={.l_type=F_WRLCK,.l_whence=SEEK_SET,.l_len=1};
  assert(!fcntl(fd,F_OFD_SETLK,&lock));pid_t child=fork();assert(child>=0);
  if(!child) {
    int other=open(path,O_RDWR|O_CLOEXEC);assert(other>=0&&!close(fd));
    assert(write(ready[1],"x",1)==1&&!fcntl(other,F_OFD_SETLKW,&lock));_exit(0);
  }
  char byte;assert(read(ready[0],&byte,1)==1);
  struct timespec delay={.tv_nsec=50000000};assert(!nanosleep(&delay,NULL));
  lock.l_type=F_UNLCK;assert(!fcntl(fd,F_OFD_SETLK,&lock));
  int status;assert(waitpid(child,&status,0)==child&&status==0);puts("completed");
  assert(!close(fd)&&!close(ready[0])&&!close(ready[1]));
}
static int fifo_descriptor(const char*method,const char*path,int flags) {
  if(!strcmp(method,"open"))return (int)syscall(SYS_open,path,flags,0);
  if(!strcmp(method,"openat"))return (int)syscall(SYS_openat,AT_FDCWD,path,flags,0);
  const char*name=strrchr(path,'/');assert(name);++name;
  if(!strcmp(method,"cwd")) {
    assert(!chdir("/tmp"));return (int)syscall(SYS_open,name,flags,0);
  }
  if(!strcmp(method,"dirfd")||!strcmp(method,"rooted")) {
    int dir=open("/tmp",O_RDONLY|O_DIRECTORY|O_CLOEXEC);assert(dir>=0);
    int fd;
    if(!strcmp(method,"dirfd"))fd=(int)syscall(SYS_openat,dir,name,flags,0);
    else {
      char absolute[128];assert(snprintf(absolute,sizeof absolute,"/%s",name)>0);
      struct open_how how={.flags=(unsigned)flags,.resolve=RESOLVE_IN_ROOT};
      fd=(int)syscall(SYS_openat2,dir,absolute,&how,sizeof how);
    }
    assert(!close(dir));return fd;
  }
  struct open_how how={.flags=(unsigned)flags};
  return (int)syscall(SYS_openat2,AT_FDCWD,path,&how,sizeof how);
}
static void fifo_wait(const char*method,bool truncate) {
  char path[]="/tmp/jayacct-fifo-XXXXXX";int temp=mkstemp(path);
  assert(temp>=0&&!close(temp)&&!unlink(path)&&!mkfifo(path,0600));
  pid_t child=fork();assert(child>=0);int flags=O_CLOEXEC|(truncate?O_TRUNC:0);
  if(!child) {
    int fd=fifo_descriptor(method,path,O_WRONLY|flags);assert(fd>=0);
    assert(write(fd,"x",1)==1&&!close(fd));_exit(0);
  }
  int fd=fifo_descriptor(method,path,O_RDONLY|flags);assert(fd>=0);
  char byte;assert(read(fd,&byte,1)==1&&byte=='x');assert(!close(fd));
  int status;assert(waitpid(child,&status,0)==child&&status==0);
  assert(!unlink(path));puts("completed");
}
static int dying_opener(void*argument) {
  struct open_how how={.flags=O_RDWR|O_CLOEXEC};
  int fd=(int)syscall(SYS_openat2,AT_FDCWD,argument,&how,sizeof how);
  assert(fd>=0);return 0;
}
static void open_exit_death(void) {
  int fd=ram();char path[96];path_for(fd,path,sizeof path);stage("baseline");acquire(fd);
  int slot=dup(fd);assert(slot>=0&&!close(slot));
  size_t bytes=128*1024;char*stack=mmap(NULL,bytes,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
  assert(stack!=MAP_FAILED);
  pid_t child=clone(dying_opener,stack+bytes,CLONE_FILES|SIGCHLD,path);assert(child>=0);
  int status;assert(waitpid(child,&status,0)==child&&WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL);
  struct stat a,b;assert(!fstat(fd,&a)&&!fstat(slot,&b));
  assert(a.st_dev==b.st_dev&&a.st_ino==b.st_ino);
  assert(!close(fd));stage("recovered_owner_only");
  char byte;assert(pread(slot,&byte,1,0)==1&&byte==42);
  assert(!close(slot));stage("closed");assert(!munmap(stack,bytes));
}
static void special_descriptors(void) {
  stage("baseline");
  for(unsigned i=0;i<2;i++) {
    int fd=open(i?"/dev/zero":"/dev/null",O_RDWR|O_TRUNC|O_CLOEXEC);assert(fd>=0&&!close(fd));
  }
  int dir=open("/tmp",O_PATH|O_DIRECTORY|O_CLOEXEC);assert(dir>=0&&!close(dir));
  char path[]="/tmp/jayacct-symlink-XXXXXX";int temp=mkstemp(path);
  assert(temp>=0&&!close(temp)&&!unlink(path)&&!symlink("missing-target",path));
  int link=open(path,O_PATH|O_NOFOLLOW|O_TRUNC|O_CLOEXEC);assert(link>=0&&!close(link)&&!unlink(path));
  struct open_how how={.flags=O_RDONLY};
  errno=0;assert(syscall(SYS_openat2,AT_FDCWD,"/dev/null",(void*)1,sizeof how)<0&&errno==EFAULT);
  errno=0;assert(syscall(SYS_openat2,AT_FDCWD,"/dev/null",&how,7)<0&&errno==EINVAL);
  stage("special_closed");
}
int main(int argc,char**argv) {
  assert(argc>=2);setbuf(stdout,NULL);
  if(!strcmp(argv[1],"exec_stage")) {
    assert(argc==4);int kept=atoi(argv[2]),clo=atoi(argv[3]);
    assert(fcntl(kept,F_GETFD)==0);errno=0;assert(fcntl(clo,F_GETFD)<0&&errno==EBADF);
    char byte;assert(pread(kept,&byte,1,0)==1&&byte==42);stage("after_exec");
    assert(!close(kept));stage("exec_closed");
  } else if(!strcmp(argv[1],"exec_direct_stage")) {
    assert(argc==4);int fd=atoi(argv[2]);bool closed=atoi(argv[3])!=0;
    if(closed) {errno=0;assert(fcntl(fd,F_GETFD)<0&&errno==EBADF);}
    else {char byte;assert(fcntl(fd,F_GETFD)==0&&pread(fd,&byte,1,0)==1&&byte==42);}
    stage("after_exec");if(!closed)assert(!close(fd));stage("exec_closed");
  } else if(!strcmp(argv[1],"reopen_exec"))reopened_exec(argv[0]);
  else if(!strcmp(argv[1],"reopen_exec_direct")) {assert(argc==3);reopened_exec_direct(argv[0],atoi(argv[2])!=0);}
  else if(!strcmp(argv[1],"regular"))regular_owner();
  else if(!strcmp(argv[1],"remap_edges"))remap_edges();
  else if(!strcmp(argv[1],"remap_anon"))remap_anon();
  else if(!strcmp(argv[1],"queries"))query_locks();
  else if(!strcmp(argv[1],"ofd_wait"))ofd_wait();
  else if(!strcmp(argv[1],"fifo")) {assert(argc==4);fifo_wait(argv[2],atoi(argv[3])!=0);}
  else if(!strcmp(argv[1],"open_exit_death"))open_exit_death();
  else if(!strcmp(argv[1],"special"))special_descriptors();
  else opened_owner(argv[1]);
  return 0;
}
