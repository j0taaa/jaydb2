#define _GNU_SOURCE
#include "deadline.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/falloc.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#define P UINT64_C(4096)
#define B (UINT64_C(5)*1024*1024*1024)
#define HIGH UINT64_C(0xa38107af00000000)
static uint64_t raw(int fd){return HIGH|(unsigned)fd;}
static void stage(const char*n) {
  struct jayacct_snapshot s={0};int e=jayacct_barrier(&s);assert(!e||e==ENOTSUP);
  printf("STAGE %s %llu %llu %llu\n",n,(unsigned long long)s.sequence.lo,
    (unsigned long long)s.current.lo,(unsigned long long)s.flags);
}
static int ram(uint64_t size) {
  int f=(int)syscall(SYS_memfd_create,"ownership-v7",MFD_CLOEXEC);assert(f>=0&&!ftruncate(f,size));return f;
}
static void alloc(int f,uint64_t offset,uint64_t bytes) {assert(!syscall(SYS_fallocate,raw(f),FALLOC_FL_KEEP_SIZE,offset,bytes));}
static char*private_map(int f,uint64_t size,uint64_t offset) {
  char*p=(void*)syscall(SYS_mmap,NULL,size,PROT_NONE,MAP_PRIVATE,raw(f),offset);assert(p!=MAP_FAILED);return p;
}
static void cow(void) {
  stage("baseline");int fd=ram(2*P);alloc(fd,0,2*P);char byte=42;assert(pwrite(fd,&byte,1,0)==1);
  char*a=private_map(fd,2*P,0),*b=private_map(fd,2*P,0);assert(!close(fd));stage("private_views_only");
  assert(!mprotect(a,P,PROT_READ|PROT_WRITE));a[0]=99;assert(a[0]==99);stage("cow_a");
  assert(!mprotect(a,P,PROT_NONE));stage("a_revoked");
  assert(!mprotect(b,P,PROT_READ)&&b[0]==42);stage("original_b");assert(!mprotect(b,P,PROT_NONE));
  assert(mmap(a,2*P,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED,-1,0)==a);stage("a_replaced");
  assert(!munmap(b,2*P));stage("last_file_view_gone");assert(!munmap(a,2*P));stage("closed");
}
static void remap_owner(void) {
  stage("baseline");int fd=ram(B+4*P);alloc(fd,B,P);alloc(fd,B+3*P,P);
  char byte=42;assert(pwrite(fd,&byte,1,B)==1);byte=43;assert(pwrite(fd,&byte,1,B+3*P)==1);
  char*p=private_map(fd,4*P,B);assert(!close(fd));stage("private_view");
  char*reservation=mmap(NULL,6*P,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(reservation!=MAP_FAILED);
  p=mremap(p,4*P,4*P,MREMAP_MAYMOVE|MREMAP_FIXED,reservation+P);assert(p==reservation+P);
  assert(!munmap(reservation,P)&&!munmap(reservation+5*P,P));stage("moved");
  assert(!mprotect(p,P,PROT_READ)&&!mprotect(p+3*P,P,PROT_READ)&&p[0]==42&&p[3*P]==43);
  stage("activated_edges");assert(!mprotect(p,P,PROT_NONE)&&!mprotect(p+3*P,P,PROT_NONE));stage("revoked_edges");
  assert(!munmap(p,P));stage("first_slice_gone");assert(!munmap(p+2*P,2*P));stage("last_unactivated_slice");
  assert(!munmap(p+P,P));stage("closed");
}
static void anonymous_flags(void) {
  stage("baseline");int fd=ram(0);
  char*a=(void*)syscall(SYS_mmap,NULL,P,PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,raw(fd),B);
  char*b=(void*)syscall(SYS_mmap,NULL,P,PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,raw(fd),0);
  assert(a!=MAP_FAILED&&b!=MAP_FAILED);a[0]=42;b[0]=43;stage("two_anonymous_objects");
  assert(!mprotect(a,P,PROT_NONE)&&!close(fd));stage("ignored_fd_closed");
  assert(!munmap(a,P));stage("one_anonymous_object");assert(b[0]==43&&!munmap(b,P));stage("anonymous_gone");
  char*c=(void*)syscall(SYS_mmap,NULL,P,PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,HIGH|UINT32_C(0xfffffffe),B);
  assert(c!=MAP_FAILED);c[0]=44;stage("invalid_fd_ignored");assert(!munmap(c,P));
  fd=ram(P);alloc(fd,0,P);
  c=(void*)syscall(SYS_mmap,NULL,P,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,raw(fd),B);
  assert(c!=MAP_FAILED);c[0]=45;stage("private_anonymous_and_fd");
  assert(!close(fd)&&!mprotect(c,P,PROT_NONE));stage("private_does_not_retain_fd");
  assert(!munmap(c,P));stage("closed");
}
static void exec_owner(const char*self) {
  stage("baseline");int fd=ram(2*P);alloc(fd,0,2*P);char*p=private_map(fd,2*P,0);
  int ready[2],gate[2];assert(!pipe(ready)&&!pipe(gate));pid_t child=fork();assert(child>=0);
  if(!child) {
    assert(!close(fd));char byte=1;assert(write(ready[1],&byte,1)==1&&read(gate[0],&byte,1)==1);
    execl(self,self,"after_exec",NULL);assert(0);
  }
  char byte;assert(read(ready[0],&byte,1)==1&&!close(fd)&&!munmap(p,2*P));stage("child_view_only");
  assert(write(gate[1],&byte,1)==1);int status;assert(waitpid(child,&status,0)==child&&status==0);stage("closed");
}
static void cancel_owner(void) {
  int counter_fd=atoi(getenv("JAYDB_ACCOUNTING_FD"));
  void*page=mmap(NULL,JAYACCT_SHARED_BYTES,PROT_READ|PROT_WRITE,MAP_SHARED,counter_fd,0);assert(page!=MAP_FAILED);
  stage("baseline");int fd=ram(2*P);alloc(fd,0,2*P);char*p=private_map(fd,2*P,0);
  assert(!close(fd));stage("only_private_view");
  struct jayacct_window_snapshot before,failed,after;struct jayacct_snapshot hold;
  assert(!jayacct_window_begin(&before)&&!jayacct_hold_begin(&hold)&&!jayacct_window_barrier(&before));
  struct timespec now;assert(!clock_gettime(CLOCK_MONOTONIC,&now));
  uint64_t end=(uint64_t)now.tv_sec*1000000000+(uint64_t)now.tv_nsec+20000000;
  assert(jayacct_window_barrier_until(&failed,(struct jayacct_u128){end,0})==ETIMEDOUT&&!failed.abi);
  assert(!jayacct_window_read(page,&after)&&after.scope_id.lo==before.scope_id.lo&&after.state==1);
  assert(after.peak.lo==before.peak.lo&&after.peak_sequence.lo==before.peak_sequence.lo&&
    after.peak_monotonic_ns.lo==before.peak_monotonic_ns.lo&&(after.peak_flags&JAYACCT_INCOMPLETE));
  assert(!jayacct_hold_release());stage("after_cancel");
  assert(!mprotect(p,P,PROT_READ));stage("activated_after_cancel");assert(!mprotect(p,P,PROT_NONE));
  assert(!munmap(p,2*P));stage("file_view_gone");assert(!jayacct_window_end(&after));
  stage("closed");assert(!munmap(page,JAYACCT_SHARED_BYTES));
}
int main(int argc,char**argv) {
  assert(argc==2);setbuf(stdout,NULL);
  if(!strcmp(argv[1],"cow"))cow();
  else if(!strcmp(argv[1],"remap"))remap_owner();
  else if(!strcmp(argv[1],"anonymous"))anonymous_flags();
  else if(!strcmp(argv[1],"exec"))exec_owner(argv[0]);
  else if(!strcmp(argv[1],"after_exec"))stage("after_exec");
  else if(!strcmp(argv[1],"cancel"))cancel_owner();else assert(0);
  puts("FACT completed 1");return 0;
}
