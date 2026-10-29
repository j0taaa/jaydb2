#define _GNU_SOURCE
#include "counter.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/falloc.h>
#include <linux/openat2.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>
static void stage(const char*n) {
  struct jayacct_snapshot s={0};int e=jayacct_barrier(&s);assert(!e||e==ENOTSUP);
  printf("STAGE %s %llu %llu %llu\n",n,(unsigned long long)s.sequence.lo,
         (unsigned long long)s.current.lo,(unsigned long long)s.flags);
}
static int ram(void) {
  int f=(int)syscall(SYS_memfd_create,"progress-v6",MFD_CLOEXEC);assert(f>=0);
  assert(!syscall(SYS_fallocate,f,FALLOC_FL_KEEP_SIZE,0,8192));return f;
}
static void path_for(int fd,char*p,size_t n) {assert(snprintf(p,n,"/proc/self/fd/%d",fd)>0);}
static void final_link(const char*d) {
  stage("baseline");
  int fd=ram();char direct[128],link[1024],fifo[1024];path_for(fd,direct,sizeof direct);
  assert(snprintf(link,sizeof link,"%s/final",d)>0&&snprintf(fifo,sizeof fifo,"%s/fifo",d)>0);
  assert(!symlink(direct,link));stage("owned");
  errno=0;assert(open(link,O_RDWR|O_NOFOLLOW|O_TRUNC)<0&&errno==ELOOP);stage("failed_keeps");
  int l=open(link,O_PATH|O_NOFOLLOW|O_TRUNC);struct stat s;
  assert(l>=0&&!fstat(l,&s)&&S_ISLNK(s.st_mode)&&!close(l));stage("path_keeps");
  assert(!unlink(link)&&!mkfifo(fifo,0600)&&!symlink(fifo,link));
  errno=0;assert(open(link,O_RDONLY|O_NOFOLLOW|O_TRUNC)<0&&errno==ELOOP);
  assert(!unlink(link)&&!unlink(fifo)&&!close(fd));stage("closed");
}
struct fifo_args {char path[1024];pid_t main_tid;};
static void*writer(void*pointer) {
  struct fifo_args*a=pointer;assert(syscall(SYS_gettid)!=a->main_tid);
  int fd=open(a->path,O_WRONLY|O_NOFOLLOW|O_TRUNC|O_CLOEXEC);
  assert(fd>=0&&write(fd,"k",1)==1&&!close(fd));return NULL;
}
static void thread_fifo(const char*d) {
  char path[1024];assert(snprintf(path,sizeof path,"%s/fifo",d)>0&&!mkfifo(path,0600));
  int low=open(d,O_PATH|O_DIRECTORY|O_CLOEXEC);assert(low>=0);
  int high=fcntl(low,F_DUPFD_CLOEXEC,180);assert(high>=180&&!close(low));
  struct fifo_args a={.main_tid=(pid_t)syscall(SYS_gettid)};
  assert(snprintf(a.path,sizeof a.path,"/proc/thread-self/fd/%d/fifo",high)>0);
  pthread_t thread;assert(!pthread_create(&thread,NULL,writer,&a));
  int fd=open(a.path,O_RDONLY|O_NOFOLLOW|O_TRUNC|O_CLOEXEC);char b;
  assert(fd>=0&&read(fd,&b,1)==1&&b=='k'&&!close(fd)&&!pthread_join(thread,NULL));
  assert(!close(high)&&!unlink(path));puts("FACT completed 1");
}
static void targets(const char*d) {
  char regular[1024],direct[128];assert(snprintf(regular,sizeof regular,"%s/regular",d)>0);
  int disk=open(regular,O_CREAT|O_EXCL|O_RDWR|O_CLOEXEC,0600);assert(disk>=0&&!ftruncate(disk,8192));
  int fd=ram();path_for(fd,direct,sizeof direct);stage("baseline");
  stage("before_ordinary");assert(!syscall(SYS_truncate,regular,4096));stage("after_ordinary");
  void*p=mmap(NULL,4096,PROT_READ,MAP_SHARED,disk,0);assert(p!=MAP_FAILED);stage("before_mapped");
  assert(!syscall(SYS_truncate,regular,4096));stage("after_mapped");assert(!munmap(p,4096));
  p=mmap(NULL,4096,PROT_READ,MAP_PRIVATE,disk,0);assert(p!=MAP_FAILED);stage("before_private");
  assert(!syscall(SYS_truncate,regular,4096));stage("after_private");assert(!munmap(p,4096));
  stage("before_adapted");assert(!syscall(SYS_truncate,direct,0));stage("after_adapted");
  assert(!close(fd)&&!close(disk)&&!unlink(regular));stage("closed");
}
static void truncate_exit(const char*d) {
  char regular[1024];assert(snprintf(regular,sizeof regular,"%s/regular",d)>0);
  int disk=open(regular,O_CREAT|O_EXCL|O_RDWR|O_CLOEXEC,0600);assert(disk>=0&&write(disk,"k",1)==1);
  int fd=ram();stage("baseline");pid_t child=fork();assert(child>=0);
  if(!child){assert(!syscall(SYS_truncate,regular,0));_exit(0);}
  int status;assert(waitpid(child,&status,0)==child&&WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL);
  struct stat s;assert(!fstat(disk,&s)&&s.st_size==0);stage("parent_retains");
  assert(!close(fd)&&!close(disk)&&!unlink(regular));stage("closed");
}
/* This is an executable witness of the remaining obligation, not a fixed
 * progress claim. Control succeeds. Observed adapted-lease runs are recorded
 * separately by replay_v5_review, with bounded harness cleanup. */
static int regular_leased;
static volatile sig_atomic_t regular_released;
static void regular_unlock(int sig) {
  (void)sig;int e=errno;assert(!fcntl(regular_leased,F_SETLEASE,F_UNLCK));regular_released=1;errno=e;
}
static void regular_lease(const char*d,int operation) {
  char path[1024];assert(snprintf(path,sizeof path,"%s/leased",d)>0);
  int fd=open(path,O_CREAT|O_EXCL|O_WRONLY|O_CLOEXEC,0600);assert(fd>=0&&write(fd,"k",1)==1&&!close(fd));
  int ready[2];assert(!pipe(ready));pid_t child=fork();assert(child>=0);
  if(!child) {
    struct sigaction a={.sa_handler=regular_unlock};sigemptyset(&a.sa_mask);
    regular_leased=open(path,O_RDONLY|O_CLOEXEC);assert(regular_leased>=0);
    assert(!sigaction(SIGIO,&a,NULL)&&!fcntl(regular_leased,F_SETOWN,getpid()));
    assert(!fcntl(regular_leased,F_SETLEASE,F_RDLCK)&&write(ready[1],"r",1)==1);
    while(!regular_released)pause();_exit(0);
  }
  char b;assert(read(ready[0],&b,1)==1);
  if(operation==0)fd=(int)syscall(SYS_open,path,O_WRONLY|O_TRUNC|O_CLOEXEC,0);
  else if(operation==1)fd=(int)syscall(SYS_openat,AT_FDCWD,path,O_WRONLY|O_TRUNC|O_CLOEXEC,0);
  else if(operation==2) {
    struct open_how how={.flags=O_WRONLY|O_TRUNC|O_CLOEXEC};
    fd=(int)syscall(SYS_openat2,AT_FDCWD,path,&how,sizeof how);
  } else fd=(int)syscall(SYS_creat,path,0600);
  assert(fd>=0);struct stat st;assert(!fstat(fd,&st)&&st.st_size==0&&!close(fd));
  int status;assert(waitpid(child,&status,0)==child&&status==0&&!unlink(path));puts("FACT completed 1");
}
static volatile sig_atomic_t released;
static int leased;
static void unlock(int sig) {(void)sig;int e=errno;int r=fcntl(leased,F_SETLEASE,F_UNLCK);assert(!r);released=1;errno=e;}
static void adapted_lease(void) {
  int fd=ram();char direct[128];path_for(fd,direct,sizeof direct);
  int ro=open(direct,O_RDONLY|O_CLOEXEC);assert(ro>=0&&!close(fd));path_for(ro,direct,sizeof direct);
  stage("baseline");int ready[2];assert(!pipe(ready));pid_t child=fork();assert(child>=0);
  if(!child) {
    leased=ro;struct sigaction a={.sa_handler=unlock};sigemptyset(&a.sa_mask);
    assert(!sigaction(SIGIO,&a,NULL)&&!fcntl(ro,F_SETOWN,getpid())&&!fcntl(ro,F_SETLEASE,F_RDLCK));
    assert(write(ready[1],"r",1)==1);while(!released)pause();_exit(0);
  }
  char b;assert(read(ready[0],&b,1)==1);puts("FACT adapted_read_lease_installed 1");
  assert(!syscall(SYS_truncate,direct,0));int status;assert(waitpid(child,&status,0)==child&&status==0);
  stage("truncated");assert(!close(ro));stage("closed");puts("FACT completed 1");
}
int main(int argc,char**argv) {
  assert(argc>=2);setbuf(stdout,NULL);
  if(!strcmp(argv[1],"adapted_lease"))adapted_lease();
  else {assert(argc==3);if(!strcmp(argv[1],"final_link"))final_link(argv[2]);
    else if(!strcmp(argv[1],"thread_fifo"))thread_fifo(argv[2]);
    else if(!strcmp(argv[1],"targets"))targets(argv[2]);
    else if(!strncmp(argv[1],"regular_lease",13))regular_lease(argv[2],atoi(argv[1]+13));
    else if(!strcmp(argv[1],"truncate_exit"))truncate_exit(argv[2]);else assert(0);}
  return 0;
}
