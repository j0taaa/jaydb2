#define _GNU_SOURCE
#include "deadline.h"
#include <assert.h>
#include <fcntl.h>
#include <linux/io_uring.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#define EXTENT (1024u*1024u)
static void stage(const char*name) {
  struct jayacct_snapshot s;assert(!jayacct_barrier(&s));
  printf("%s %llu %llu %llu\n",name,(unsigned long long)s.sequence.lo,
         (unsigned long long)s.current.lo,(unsigned long long)s.peak.lo);
}
static void ring_vfork(const char*mode) {
  struct io_uring_params p={0};p.flags=IORING_SETUP_NO_SQARRAY;
  int fd=(int)syscall(SYS_io_uring_setup,256,&p);assert(fd>=0);stage("ring_before");
  pid_t child=!strcmp(mode,"fork_close")?fork():vfork();assert(child>=0);
  if(!child) {
    if(strcmp(mode,"vfork_no_close"))close(fd);
    if(!strcmp(mode,"vfork_exec"))execl("/bin/true","true",(char*)NULL);
    _exit(0);
  }
  int status;assert(waitpid(child,&status,0)==child&&status==0);
  stage("ring_parent_retains");assert(!close(fd));stage("ring_released");
}
static void killed_vfork_parent(void) {
  int ready[2],gate[2];assert(!pipe(ready)&&!pipe(gate));
  struct io_uring_params p={0};p.flags=IORING_SETUP_NO_SQARRAY;
  int fd=(int)syscall(SYS_io_uring_setup,256,&p);assert(fd>=0);
  pid_t parent=fork();assert(parent>=0);
  if(!parent) {
    pid_t child=vfork();
    if(!child) {
      close(fd);char byte;
      if(write(ready[1],"1",1)!=1||read(gate[0],&byte,1)!=1)_exit(3);
      _exit(0);
    }
    _exit(4);
  }
  assert(!close(fd));char byte;assert(read(ready[0],&byte,1)==1);
  stage("blocked_parent_retains");assert(!kill(parent,SIGKILL));
  int status;assert(waitpid(parent,&status,0)==parent&&WIFSIGNALED(status));
  stage("killed_parent_released");assert(write(gate[1],"1",1)==1);
  close(ready[0]);close(ready[1]);close(gate[0]);close(gate[1]);
}
static int memory_file(void) {
  int fd=(int)syscall(SYS_memfd_create,"jayacct-retention",MFD_CLOEXEC);
  assert(fd>=0&&ftruncate(fd,EXTENT)==0);return fd;
}
static void aliases(const char*mode) {
  bool ram=!strcmp(mode,"memfd"),regular=!strcmp(mode,"regular");int fd=-1;
  if(ram)fd=memory_file();
  if(regular) {
    char path[]="/tmp/jayacct-regular-XXXXXX";fd=mkstemp(path);
    assert(fd>=0&&!unlink(path)&&!ftruncate(fd,EXTENT));
  }
  stage("before_reserve");
  void*a=mmap(NULL,EXTENT,PROT_NONE,MAP_SHARED|(fd<0?MAP_ANONYMOUS:0),fd,0);assert(a!=MAP_FAILED);
  stage("reserved");void*b=mremap(a,0,EXTENT,MREMAP_MAYMOVE);assert(b!=MAP_FAILED);stage("alias_reserved");
  assert(!mprotect(b,EXTENT,PROT_READ|PROT_WRITE));*(char*)b=42;stage("alias_active");
  assert(!munmap(b,EXTENT));stage("alias_removed");
  assert(!mprotect(a,EXTENT,PROT_READ|PROT_WRITE)&&*(char*)a==42);stage("original_reactivated");
  assert(!mprotect(a,EXTENT,PROT_NONE));stage("original_revoked");
  assert(!munmap(a,EXTENT));stage("last_view_removed");
  if(fd>=0) {
    int copy=dup(fd);assert(copy>=0&&!close(fd));stage("fd_copy_retains");
    assert(!close(copy));stage("last_fd_closed");
  }
}
static void memfd_writes(void) {
  char buffer[4096]={1};int fd=memory_file();stage("size_only");
  assert(pwrite(fd,buffer,4096,8192)==4096);stage("pwrite_page");
  assert(pwrite(fd,buffer,4096,10240)==4096);stage("pwrite_overlap");
  assert(!ftruncate(fd,9000));stage("shrink_partial");
  assert(!ftruncate(fd,0));stage("shrink_zero");
  assert(!ftruncate(fd,1u<<30));stage("grow_reservation_only");
  assert(lseek(fd,7*4096+4080,SEEK_SET)==7*4096+4080);
  struct iovec vector[2]={{buffer,16},{buffer,32}};
  assert(writev(fd,vector,2)==48);stage("writev_pages");
  assert(pwritev(fd,vector,2,20*4096)==48);stage("pwritev_page");
  assert(lseek(fd,30*4096,SEEK_SET)==30*4096);
  assert(pwritev2(fd,vector,2,-1,0)==48);stage("pwritev2_current");
  assert(!ftruncate(fd,40*4096));
  assert(fcntl(fd,F_SETFL,O_RDWR|O_APPEND)==0);
  assert(pwrite(fd,buffer,16,0)==16);stage("append_pwrite");
  assert(!close(fd));stage("written_fd_closed");
}
static void partial_alias(void) {
  int fd=memory_file();void*a=mmap(NULL,EXTENT,PROT_NONE,MAP_SHARED,fd,0);assert(a!=MAP_FAILED);
  stage("partial_reserved");
  void*b=mmap(NULL,256*1024,PROT_READ|PROT_WRITE,MAP_SHARED,fd,128*1024);assert(b!=MAP_FAILED);
  *(char*)b=42;stage("partial_active");
  void*c=mremap(b,0,256*1024,MREMAP_MAYMOVE);assert(c!=MAP_FAILED);
  assert(!munmap(b,256*1024));stage("partial_alias_moved");
  assert(!munmap(c,256*1024));stage("partial_only_reservation");
  assert(!mprotect(a,4096,PROT_READ|PROT_WRITE));stage("partial_disjoint");
  assert(!munmap(a,EXTENT));stage("partial_fd_only");
  assert(!ftruncate(fd,192*1024));stage("partial_shrink");
  assert(!ftruncate(fd,EXTENT));stage("partial_extend_none");
  assert(!close(fd));stage("partial_closed");
}
static void fork_activation(void) {
  void*a=mmap(NULL,EXTENT,PROT_NONE,MAP_SHARED|MAP_ANONYMOUS,-1,0);assert(a!=MAP_FAILED);
  stage("fork_reserved");pid_t child=fork();assert(child>=0);
  if(!child) {
    void*b=mremap(a,0,EXTENT,MREMAP_MAYMOVE);assert(b!=MAP_FAILED);
    assert(!mprotect(b,EXTENT,PROT_READ|PROT_WRITE));*(char*)b=42;
    assert(!munmap(b,EXTENT));_exit(0);
  }
  int status;assert(waitpid(child,&status,0)==child&&status==0);stage("fork_child_retired");
  assert(!mprotect(a,EXTENT,PROT_READ|PROT_WRITE)&&*(char*)a==42);
  stage("fork_parent_reactivated");assert(!munmap(a,EXTENT));stage("fork_last_view_removed");
}
static void memfd_fork_exec(void) {
  int fd=memory_file(),gate[2];assert(!pipe(gate));
  void*p=mmap(NULL,EXTENT,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);assert(p!=MAP_FAILED);
  assert(!munmap(p,EXTENT));stage("exec_fd_only");pid_t child=fork();assert(child>=0);
  if(!child) {char byte;if(read(gate[0],&byte,1)!=1)_exit(3);execl("/bin/true","true",(char*)NULL);_exit(4);}
  assert(!close(fd));stage("exec_child_only");assert(write(gate[1],"1",1)==1);
  int status;assert(waitpid(child,&status,0)==child&&status==0);stage("exec_cloexec_released");
  close(gate[0]);close(gate[1]);
}
static void cancelled_retention(void) {
  int fd=memory_file();void*p=mmap(NULL,EXTENT,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);assert(p!=MAP_FAILED);
  *(char*)p=42;assert(!munmap(p,EXTENT));stage("cancel_before");
  struct jayacct_snapshot s;assert(!jayacct_hold_begin(&s));
  struct jayacct_window_snapshot w;assert(!jayacct_window_begin(&w));
  struct timespec now;assert(!clock_gettime(CLOCK_MONOTONIC,&now));
  struct jayacct_u128 until={(uint64_t)now.tv_sec*1000000000+now.tv_nsec+5000000,0};
  assert(jayacct_window_barrier_until(&w,until)==ETIMEDOUT&&!w.abi);
  assert(!jayacct_hold_release());stage("cancel_after");
  assert(!jayacct_window_end(&w));assert(!close(fd));stage("cancel_fd_closed");
}
int main(int argc,char**argv) {
  assert(argc==2);setbuf(stdout,NULL);
  if(!strcmp(argv[1],"vfork_close")||!strcmp(argv[1],"vfork_no_close")||
      !strcmp(argv[1],"fork_close")||!strcmp(argv[1],"vfork_exec"))ring_vfork(argv[1]);
  else if(!strcmp(argv[1],"vfork_kill_parent"))killed_vfork_parent();
  else if(!strcmp(argv[1],"memfd_writes"))memfd_writes();
  else if(!strcmp(argv[1],"partial_alias"))partial_alias();
  else if(!strcmp(argv[1],"fork_activation"))fork_activation();
  else if(!strcmp(argv[1],"memfd_fork_exec"))memfd_fork_exec();
  else if(!strcmp(argv[1],"cancel_retention"))cancelled_retention();
  else aliases(argv[1]);
  return 0;
}
