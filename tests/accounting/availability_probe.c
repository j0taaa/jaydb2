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
#include <sys/wait.h>
#include <unistd.h>
#define N (1024UL*1024)
#define P 4096UL
static void stage(const char*n) {
  struct jayacct_snapshot s={0};int e=jayacct_barrier(&s);assert(!e||e==ENOTSUP);
  printf("STAGE %s %llu %llu %llu\n",n,(unsigned long long)s.sequence.lo,
    (unsigned long long)s.current.lo,(unsigned long long)s.flags);
}
static int ram(void) {
  int f=memfd_create("availability-v8",MFD_CLOEXEC);assert(f>=0&&!ftruncate(f,N)&&!fallocate(f,FALLOC_FL_KEEP_SIZE,0,N));
  char b=42;assert(pwrite(f,&b,1,0)==1);b=43;assert(pwrite(f,&b,1,N-1)==1);return f;
}
static void cow(char*p) {
  assert(!mprotect(p,P,PROT_READ|PROT_WRITE)&&p[0]==42);p[0]=99;
  assert(!mprotect(p+N-P,P,PROT_READ)&&p[N-1]==43);
  assert(!mprotect(p,P,PROT_NONE)&&!mprotect(p+N-P,P,PROT_NONE));
}
static void retained(int abrupt) {
  stage("baseline");int fd=ram();char*p=mmap(NULL,N,PROT_NONE,MAP_PRIVATE,fd,0);assert(p!=MAP_FAILED);
  int ready[2],gate[2][2];assert(!pipe(ready));pid_t children[2];
  for(int i=0;i<2;i++) {
    assert(!pipe(gate[i]));children[i]=fork();assert(children[i]>=0);
    if(!children[i]) {
      assert(!close(fd));cow(p);char byte=1;
      assert(write(ready[1],&byte,1)==1&&read(gate[i][0],&byte,1)==1);
      if(abrupt)for(;;)pause();_exit(0);
    }
    char byte;assert(read(ready[0],&byte,1)==1);
  }
  assert(!mprotect(p,P,PROT_READ)&&p[0]==42&&!munmap(p,N)&&!close(fd));stage("only_children");
  for(int i=0;i<2;i++) {
    assert(write(gate[i][1],"g",1)==1);if(abrupt)assert(!kill(children[i],SIGKILL));
    int status;assert(waitpid(children[i],&status,0)==children[i]);
    assert(abrupt?(WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL):status==0);
    stage(i?"closed":"other_child_retains");
  }
  puts("FACT independent_cow99_base42_tail43 1");
}
static void hold_death(void) {
  struct jayacct_window_snapshot initial,closed;assert(!jayacct_window_barrier(&initial));
  assert(initial.state==JAYACCT_WINDOW_ACTIVE&&initial.scope_id.lo==1&&initial.begin_sequence.lo==1);
  stage("baseline");int fd=ram();char*p=mmap(NULL,N,PROT_NONE,MAP_PRIVATE,fd,0);assert(p!=MAP_FAILED);
  pid_t child=fork();assert(child>=0);
  if(!child) {
    assert(!close(fd));cow(p);struct jayacct_snapshot held;struct jayacct_window_snapshot failed;
    /* Touch the bounded output stack before hold; this is a protocol probe,
     * not the host's Campo implementation. */
    memset(&held,0,sizeof held);memset(&failed,0,sizeof failed);
    assert(!jayacct_hold_begin(&held));
    assert(jayacct_window_end_until(&failed,(struct jayacct_u128){0,0})==ETIMEDOUT&&!failed.abi);
    assert(!kill(getpid(),SIGKILL));_exit(90);
  }
  int status;assert(waitpid(child,&status,0)==child&&WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL);
  assert(!close(fd));stage("parent_view_retains");
  int code=jayacct_window_barrier(&closed);printf("FACT window_after_death code %d state %llu id %llu expected_id %llu error %llu\n",code,(unsigned long long)closed.state,(unsigned long long)closed.scope_id.lo,(unsigned long long)initial.scope_id.lo,(unsigned long long)closed.error);
  assert(!code&&closed.scope_id.lo==initial.scope_id.lo&&closed.state==JAYACCT_WINDOW_ACTIVE);
  assert(!(closed.snapshot.flags&JAYACCT_HELD));
  assert(!munmap(p,N));stage("closed");assert(!jayacct_window_end(&closed));
  assert(closed.state==JAYACCT_WINDOW_CLOSED&&closed.begin_sequence.lo==1&&(closed.peak_flags&JAYACCT_INCOMPLETE));
  assert(!jayacct_window_begin(&initial)&&initial.scope_id.lo==2&&!jayacct_window_end(&initial));
  puts("FACT dead_hold_owner_reconciled_scope1_closed_scope2 1");
}
int main(int argc,char**argv) {
  assert(argc==2);setbuf(stdout,NULL);
  if(!strcmp(argv[1],"retained_kill"))retained(1);
  else if(!strcmp(argv[1],"retained_exit"))retained(0);
  else if(!strcmp(argv[1],"hold_death"))hold_death();else assert(0);
  return 0;
}
