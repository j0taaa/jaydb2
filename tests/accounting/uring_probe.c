#define _GNU_SOURCE
#include "counter.h"
#include <assert.h>
#include <fcntl.h>
#include <linux/io_uring.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>
static uint64_t amount(void) {
  struct jayacct_snapshot n;assert(!jayacct_barrier(&n));assert(!n.current.hi);return n.current.lo;
}
static uint64_t page(uint64_t n){return (n+4095)&~UINT64_C(4095);}
static void*unshare_worker(void*value) {
  assert(!unshare(CLONE_FILES));assert(!close((int)(intptr_t)value));amount();return NULL;
}
static int dying_ring_owner(void*unused) {
  (void)unused;struct io_uring_params p={0};p.flags=IORING_SETUP_NO_SQARRAY;
  int fd=(int)syscall(SYS_io_uring_setup,256,&p);assert(fd>=0);
  _exit(99); /* The test observer kills at syscall exit before this executes. */
}
int main(int argc,char**argv) {
  assert(argc==2);setbuf(stdout,NULL);
  if(!strcmp(argv[1],"after_exec")){amount();puts("uring_exec_clean");return 0;}
  if(!strcmp(argv[1],"dying_shared_files")) {
    void*stack=mmap(NULL,256*1024,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(stack!=MAP_FAILED);
    pid_t child=clone(dying_ring_owner,(char*)stack+256*1024,CLONE_FILES|SIGCHLD,NULL);assert(child>=0);
    int status;assert(waitpid(child,&status,0)==child);assert(WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL);
    struct jayacct_snapshot n;assert(!jayacct_barrier(&n));
    printf("dying_owner_retained %llu\n",(unsigned long long)n.sequence.lo);
    assert(!syscall(SYS_close_range,3,~0U,0));assert(!jayacct_barrier(&n));
    printf("dying_owner_released %llu\n",(unsigned long long)n.sequence.lo);
    assert(!munmap(stack,256*1024));return 0;
  }
  uint64_t before=amount();struct io_uring_params p={0};p.flags=IORING_SETUP_NO_SQARRAY;
  int fd=(int)syscall(SYS_io_uring_setup,256,&p);assert(fd>=0);
  uint64_t ring=page((uint64_t)p.cq_off.cqes+(uint64_t)p.cq_entries*16);
  uint64_t sq=page((uint64_t)p.sq_entries*64),total=ring+sq;
  assert(amount()==before+total);printf("fd_only %llu\n",(unsigned long long)total);
  if(!strcmp(argv[1],"unshare")) {
    pthread_t thread;assert(!pthread_create(&thread,NULL,unshare_worker,(void*)(intptr_t)fd));
    assert(!pthread_join(thread,NULL));assert(fcntl(fd,F_GETFD)>=0);
    struct jayacct_snapshot n;assert(!jayacct_barrier(&n));
    printf("unshare_retained %llu\n",(unsigned long long)n.sequence.lo);
    assert(!close(fd));assert(!jayacct_barrier(&n));
    printf("unshare_released %llu\n",(unsigned long long)n.sequence.lo);return 0;
  }
  if(!strcmp(argv[1],"exec")) {
    execl(argv[0],argv[0],"after_exec",NULL);return 127;
  }
  void*a=mmap(NULL,ring,PROT_READ|PROT_WRITE,MAP_SHARED,fd,IORING_OFF_SQ_RING);assert(a!=MAP_FAILED);
  void*b=mmap(NULL,ring,PROT_READ|PROT_WRITE,MAP_SHARED,fd,IORING_OFF_CQ_RING);assert(b!=MAP_FAILED);
  void*c=mmap(NULL,sq,PROT_READ|PROT_WRITE,MAP_SHARED,fd,IORING_OFF_SQES);assert(c!=MAP_FAILED);
  assert(amount()==before+total);
  int alias=dup(fd);assert(alias>=0);assert(!close(fd));assert(amount()==before+total);
  assert(!munmap(a,ring));assert(!munmap(b,ring));assert(!munmap(c,sq));assert(amount()==before+total);
  int high=fcntl(alias,F_DUPFD_CLOEXEC,100);assert(high>=100);assert(!close(alias));assert(amount()==before+total);
  pid_t child=fork();assert(child>=0);
  if(!child){execl("/bin/true","true",NULL);_exit(127);}
  int status;assert(waitpid(child,&status,0)==child&&!status);assert(amount()==before+total);
  a=mmap(NULL,ring,PROT_READ|PROT_WRITE,MAP_SHARED,high,IORING_OFF_SQ_RING);assert(a!=MAP_FAILED);
  assert(!syscall(SYS_close_range,100,~0U,0));assert(amount()==before+total); /* mapping still owns whole ring */
  assert(!munmap(a,ring));assert(amount()==before);
  struct io_uring_params q={0};q.flags=IORING_SETUP_NO_SQARRAY;
  int x=(int)syscall(SYS_io_uring_setup,256,&q);assert(x>=0);
  int y=(int)syscall(SYS_io_uring_setup,256,&p);assert(y>=0);
  assert(amount()==before+2*total);assert(!close(x));assert(amount()==before+total);
  assert(!close(y));assert(amount()==before);puts("uring_lifetime_correct");return 0;
}
