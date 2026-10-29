#define _GNU_SOURCE
#include "deadline.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/falloc.h>
#include <linux/memfd.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#define P UINT64_C(4096)
#define M (UINT64_C(1024)*1024)
#define HIGH UINT64_C(0x8000000100000000)
static void stage(const char*name) {
  struct jayacct_snapshot s;assert(!jayacct_barrier(&s));
  printf("%s %llu\n",name,(unsigned long long)s.sequence.lo);
}
static int ram(uint64_t size) {
  int fd=(int)syscall(SYS_memfd_create,"jayacct-mutations",HIGH|MFD_CLOEXEC|MFD_ALLOW_SEALING);
  assert(fd>=0&&!ftruncate(fd,(off_t)size));return fd;
}
static uint64_t raw(int fd) {return (uint32_t)fd|HIGH;}
static void path_for(int fd,char*path,size_t length) {
  assert(snprintf(path,length,"/proc/self/fd/%d",fd)>0);
}
static void allocate(int fd,unsigned mode,uint64_t start,uint64_t length) {
  assert(!syscall(SYS_fallocate,raw(fd),(uint64_t)mode|HIGH,start,length));
}
static void facts(int fd,uint64_t size) {
  struct stat s;assert(!fstat(fd,&s)&&(uint64_t)s.st_size==size);
  printf("FACT size %llu blocks %llu\n",(unsigned long long)s.st_size,(unsigned long long)s.st_blocks);
}
static void extents(void) {
  int fd=ram(4*M);stage("baseline");facts(fd,4*M);
  allocate(fd,0,P-1,2);stage("unaligned");
  allocate(fd,FALLOC_FL_KEEP_SIZE,P+7,19);stage("overlap");
  allocate(fd,0,8*P+5,1);stage("disjoint");
  allocate(fd,FALLOC_FL_KEEP_SIZE|FALLOC_FL_PUNCH_HOLE,0,P);stage("punched_first");
  allocate(fd,FALLOC_FL_KEEP_SIZE|FALLOC_FL_PUNCH_HOLE,P+1,P-2);stage("partial_kept");
  allocate(fd,FALLOC_FL_KEEP_SIZE|FALLOC_FL_PUNCH_HOLE,P+1,7*P+2);stage("boundary_pages_kept");
  allocate(fd,FALLOC_FL_KEEP_SIZE|FALLOC_FL_PUNCH_HOLE,P,P);stage("punched_second");
  allocate(fd,0,5*M+1,3);facts(fd,5*M+4);stage("plain_grows");
  allocate(fd,FALLOC_FL_KEEP_SIZE,8*M+P-1,2);facts(fd,5*M+4);stage("keep_beyond");
  int copy=dup(fd);assert(copy>=0&&!close(fd));stage("dup_retains");
  assert(!ftruncate(copy,5*M+4));stage("same_size_truncate");
  assert(!ftruncate(copy,12*M));stage("virtual_grow");
  assert(!close(copy));stage("closed");
}
static void beyond(void) {
  int fd=ram(0);char path[96];path_for(fd,path,sizeof path);stage("baseline");
  allocate(fd,FALLOC_FL_KEEP_SIZE,4*P+7,P+1);facts(fd,0);stage("beyond_eof");
  char byte=42;assert(!pread(fd,&byte,1,0));stage("read_eof");
  int reopened=open(path,O_RDWR|O_CLOEXEC);assert(reopened>=0&&!close(reopened));stage("reopened_keeps");
  int handle=open(path,O_PATH|O_TRUNC|O_CLOEXEC);assert(handle>=0&&!close(handle));stage("path_keeps");
  assert(!ftruncate(fd,3*P));stage("grow_below_preallocation");
  char link[]="/tmp/jayacct-proc-alias-XXXXXX";int temporary=mkstemp(link);
  assert(temporary>=0&&!close(temporary)&&!unlink(link)&&!symlink(path,link));
  assert(!syscall(SYS_truncate,link,3*P));facts(fd,3*P);stage("path_same_size_releases");
  assert(!unlink(link));
  allocate(fd,0,P+1,P);facts(fd,3*P);stage("plain_inside_size");
  assert(!syscall(SYS_truncate,path,P+1));stage("shrink_partial");
  assert(!syscall(SYS_truncate,path,16*P));stage("path_virtual_grow");
  assert(!close(fd));stage("closed");
}
static void errors(void) {
  int fd=ram(4*M);stage("baseline");allocate(fd,FALLOC_FL_KEEP_SIZE,8*P,1);stage("acquired");
  const unsigned modes[]={FALLOC_FL_ZERO_RANGE,FALLOC_FL_ZERO_RANGE|FALLOC_FL_KEEP_SIZE,
    FALLOC_FL_COLLAPSE_RANGE,FALLOC_FL_INSERT_RANGE,FALLOC_FL_UNSHARE_RANGE,
    FALLOC_FL_PUNCH_HOLE,0x80,0x80000000u};
  for(size_t i=0;i<sizeof modes/sizeof *modes;i++) {
    errno=0;assert(syscall(SYS_fallocate,fd,modes[i],0,P)<0&&errno==EOPNOTSUPP);
  }
  errno=0;assert(syscall(SYS_fallocate,fd,0,0,0)<0&&errno==EINVAL);
  errno=0;assert(syscall(SYS_fallocate,fd,0,UINT64_MAX,P)<0&&errno==EINVAL);
  char path[96];path_for(fd,path,sizeof path);int ro=open(path,O_RDONLY|O_CLOEXEC);assert(ro>=0);
  errno=0;assert(syscall(SYS_fallocate,ro,0,0,P)<0&&errno==EBADF);assert(!close(ro));
  assert(!fcntl(fd,F_ADD_SEALS,F_SEAL_WRITE));
  errno=0;assert(syscall(SYS_fallocate,fd,FALLOC_FL_KEEP_SIZE|FALLOC_FL_PUNCH_HOLE,8*P,P)<0&&errno==EPERM);
  stage("all_errors_keep");assert(!close(fd));stage("closed");
}
static void aliases(void) {
  int fd=ram(M);stage("baseline");allocate(fd,FALLOC_FL_KEEP_SIZE,0,M);stage("allocated");
  char*a=mmap(NULL,M,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);
  char*b=mmap(NULL,M,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);assert(a!=MAP_FAILED&&b!=MAP_FAILED);
  assert(!a[0]&&!b[0]);stage("aliases_union");assert(!munmap(a,M)&&!munmap(b,M));stage("fd_only");
  allocate(fd,FALLOC_FL_KEEP_SIZE|FALLOC_FL_PUNCH_HOLE,0,P);stage("punched");
  a=mmap(NULL,P,PROT_NONE,MAP_SHARED,fd,0);assert(a!=MAP_FAILED);stage("reservation_keeps_hole");
  assert(!mprotect(a,P,PROT_READ|PROT_WRITE));a[0]=42;stage("reactivated");
  assert(!munmap(a,P));stage("unmapped_retains");assert(!close(fd));stage("closed");
}
static void raw_fd(void) {
  int fd=ram(0);uint64_t big=UINT64_C(5)*1024*1024*1024;stage("baseline");
  assert(!syscall(SYS_ftruncate,raw(fd),big+4*P));stage("wide_virtual_size");
  allocate(fd,FALLOC_FL_KEEP_SIZE,big,1);stage("wide_allocation");
  char byte=42;assert(syscall(SYS_pwrite64,raw(fd),&byte,1,big+P)==1);stage("wide_write");
  assert(syscall(SYS_lseek,raw(fd),big,HIGH|SEEK_SET)==(long)big);
  byte=99;assert(syscall(SYS_read,raw(fd),&byte,1)==1&&!byte);stage("raw_read");
  byte=43;struct iovec vector={&byte,1};
  assert(syscall(SYS_pwritev2,raw(fd),&vector,1,big+2*P,0,HIGH)==1);stage("wide_vector");
  assert(!syscall(SYS_fcntl,raw(fd),HIGH|F_SETFL,HIGH|O_RDWR|O_APPEND));
  assert(syscall(SYS_writev,raw(fd),&vector,1)==1);stage("raw_append");
  errno=0;assert(syscall(SYS_close,UINT64_MAX)<0&&errno==EBADF);stage("invalid_close_keeps");
  assert(!syscall(SYS_close_range,raw(fd),UINT64_MAX,HIGH));stage("closed");
}
static void raw_replacement(unsigned operation) {
  int fd=ram(M),other=ram(M);stage("baseline");allocate(fd,0,0,M);allocate(other,0,0,M);stage("two_objects");
  long result=operation==2?syscall(SYS_dup2,raw(fd),raw(other)):
                           syscall(SYS_dup3,raw(fd),raw(other),HIGH|O_CLOEXEC);
  assert(result==other);stage("replacement");
  assert(!syscall(SYS_close,raw(fd)));stage("alias_only");
  errno=0;assert(syscall(SYS_dup3,raw(other),raw(other),HIGH|O_CLOEXEC)<0&&errno==EINVAL);
  assert(!syscall(SYS_close,raw(other)));stage("closed");
}
static void raw_exec(char*program,const char*kind) {
  int fd=ram(M);stage("baseline");allocate(fd,0,0,M);
  int copy=(int)syscall(SYS_fcntl,raw(fd),HIGH|F_DUPFD,HIGH|80);assert(copy>=80&&!close(fd));
  if(!strcmp(kind,"range"))assert(!syscall(SYS_close_range,raw(copy),raw(copy),HIGH|4));
  else {
    assert(!syscall(SYS_fcntl,raw(copy),HIGH|F_SETFD,HIGH|FD_CLOEXEC));
    assert(syscall(SYS_dup2,raw(copy),(unsigned)copy)==copy);
  }
  assert(fcntl(copy,F_GETFD)==FD_CLOEXEC);stage("before_exec");
  char number[24];assert(snprintf(number,sizeof number,"%d",copy)>0);
  execl(program,program,"exec_closed",number,(char*)NULL);assert(0);
}
static int unshare_child(void*argument) {
  int fd=*(int*)argument;
  assert(!syscall(SYS_close_range,raw(fd),raw(fd),HIGH|2));
  errno=0;assert(fcntl(fd,F_GETFD)<0&&errno==EBADF);return 0;
}
static void raw_unshare(void) {
  int fd=ram(M);stage("baseline");allocate(fd,0,0,M);
  size_t size=128*1024;char*stack=mmap(NULL,size,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(stack!=MAP_FAILED);
  pid_t child=clone(unshare_child,stack+size,CLONE_FILES|SIGCHLD,&fd);assert(child>=0);
  int status;assert(waitpid(child,&status,0)==child&&status==0);stage("parent_retains");
  assert(!syscall(SYS_close_range,raw(fd),raw(fd),HIGH));stage("closed");assert(!munmap(stack,size));
}
static void path_truncate(void) {
  int fd=ram(2*M),other=ram(2*M);char path[96];path_for(fd,path,sizeof path);stage("baseline");
  allocate(fd,0,0,M);allocate(other,0,P,1);stage("two_objects");
  assert(!syscall(SYS_truncate,path,P+1));stage("path_partial_shrink");
  assert(!syscall(SYS_truncate,path,4*M));stage("path_grow_only");
  assert(!fcntl(fd,F_ADD_SEALS,F_SEAL_SHRINK));errno=0;
  assert(syscall(SYS_truncate,path,0)<0&&errno==EPERM);stage("failed_path_keeps");
  assert(!close(fd));stage("other_only");assert(!close(other));stage("closed");
}
static void regular_negative(void) {
  int fd=ram(0);char path[]="/tmp/jayacct-regular-falloc-XXXXXX";int file=mkstemp(path);
  assert(file>=0);stage("baseline");allocate(fd,FALLOC_FL_KEEP_SIZE,4*P,1);stage("ram_owned");
  assert(!syscall(SYS_fallocate,file,0,0,M));stage("regular_allocated");
  assert(!syscall(SYS_truncate,path,0));stage("regular_truncated");
  assert(!close(file)&&!unlink(path));stage("regular_closed");assert(!close(fd));stage("closed");
}
static void fork_exec(char*program) {
  int fd=ram(0),gate[2];assert(!pipe(gate));stage("baseline");
  allocate(fd,FALLOC_FL_KEEP_SIZE,4*P,2*P);int copy=fcntl(fd,F_DUPFD,80);assert(copy>=80&&!close(fd));
  char number[24];assert(snprintf(number,sizeof number,"%d",copy)>0);pid_t child=fork();assert(child>=0);
  if(!child) {
    char byte;assert(read(gate[0],&byte,1)==1);
    execl(program,program,"exec_allocated",number,(char*)NULL);_exit(3);
  }
  assert(!close(copy));stage("child_only");assert(write(gate[1],"x",1)==1);
  int status;assert(waitpid(child,&status,0)==child&&status==0);stage("retired");
  assert(!close(gate[0])&&!close(gate[1]));
}
static void cancelled(void) {
  int fd=ram(0);stage("baseline");allocate(fd,FALLOC_FL_KEEP_SIZE,0,3*P);
  allocate(fd,FALLOC_FL_KEEP_SIZE|FALLOC_FL_PUNCH_HOLE,P,P);stage("before_cancel");
  struct jayacct_snapshot s;assert(!jayacct_hold_begin(&s));
  struct jayacct_window_snapshot w;assert(!jayacct_window_begin(&w));
  struct timespec now;assert(!clock_gettime(CLOCK_MONOTONIC,&now));
  struct jayacct_u128 until={(uint64_t)now.tv_sec*1000000000+now.tv_nsec+5000000,0};
  assert(jayacct_window_barrier_until(&w,until)==ETIMEDOUT&&!w.abi);
  assert(!jayacct_hold_release());stage("after_cancel");assert(!jayacct_window_end(&w));
  assert(!close(fd));stage("closed");
}
int main(int argc,char**argv) {
  assert(argc>=2);setbuf(stdout,NULL);
  if(!strcmp(argv[1],"extents"))extents();
  else if(!strcmp(argv[1],"beyond"))beyond();
  else if(!strcmp(argv[1],"errors"))errors();
  else if(!strcmp(argv[1],"aliases"))aliases();
  else if(!strcmp(argv[1],"raw_fd"))raw_fd();
  else if(!strcmp(argv[1],"raw_dup2"))raw_replacement(2);
  else if(!strcmp(argv[1],"raw_dup3"))raw_replacement(3);
  else if(!strcmp(argv[1],"raw_exec")) {assert(argc==3);raw_exec(argv[0],argv[2]);}
  else if(!strcmp(argv[1],"exec_closed")) {
    assert(argc==3);errno=0;assert(fcntl(atoi(argv[2]),F_GETFD)<0&&errno==EBADF);stage("after_exec");
  } else if(!strcmp(argv[1],"raw_unshare"))raw_unshare();
  else if(!strcmp(argv[1],"truncate"))path_truncate();
  else if(!strcmp(argv[1],"regular"))regular_negative();
  else if(!strcmp(argv[1],"fork_exec"))fork_exec(argv[0]);
  else if(!strcmp(argv[1],"exec_allocated")) {
    assert(argc==3);int fd=atoi(argv[2]);assert(!fcntl(fd,F_GETFD));facts(fd,0);
    stage("after_exec");assert(!close(fd));stage("exec_closed");
  }
  else if(!strcmp(argv[1],"cancel"))cancelled();
  else assert(0);
  return 0;
}
