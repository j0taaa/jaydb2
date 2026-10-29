#define _GNU_SOURCE
#include "deadline.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/falloc.h>
#include <linux/sched.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>
#define N (1024UL*1024)
#define STACK (128UL*1024)
struct context {int fd,ready[2],gate[2];char*view;};
static void stage(const char*n) {
  struct jayacct_snapshot s={0};int e=jayacct_barrier(&s);assert(!e||e==ENOTSUP);
  printf("STAGE %s %llu %llu %llu\n",n,(unsigned long long)s.sequence.lo,
    (unsigned long long)s.current.lo,(unsigned long long)s.flags);
}
__attribute__((used,noreturn)) static void descendant(void*arg) {
  struct context*c=arg;assert(!close(c->fd));
  assert(!mprotect(c->view,4096,PROT_READ|PROT_WRITE)&&c->view[0]==42);c->view[0]=99;
  assert(!mprotect(c->view,4096,PROT_NONE));
  pid_t pid=getpid();assert(write(c->ready[1],&pid,sizeof pid)==sizeof pid);
  char byte;assert(read(c->gate[0],&byte,1)==1);
  assert(!munmap(c->view,N));_exit(0);
}
/* Only the fixture's raw clone3 entry changes stacks. No compiler-generated
 * frame is used on the child stack. It enters descendant with a SysV frame. */
extern long fixture_clone3(struct clone_args*,size_t);
__asm__(".text\n.type fixture_clone3,@function\nfixture_clone3:\n"
        "mov $435,%eax\nsyscall\ntest %rax,%rax\njnz 1f\n"
        "xor %ebp,%ebp\npop %rdi\ncall descendant\nud2\n1: ret\n"
        ".size fixture_clone3,.-fixture_clone3\n");
static int child_entry(void*p){descendant(p);}
static void creation(const char*kind,int vm,int files) {
  assert(!prctl(PR_SET_CHILD_SUBREAPER,1));
  stage("baseline");int fd=memfd_create("metadata-v9",MFD_CLOEXEC);
  assert(fd>=0&&!ftruncate(fd,N)&&!fallocate(fd,FALLOC_FL_KEEP_SIZE,0,N));
  char b=42;assert(pwrite(fd,&b,1,0)==1);
  char*view=mmap(NULL,N,PROT_NONE,MAP_PRIVATE,fd,0);assert(view!=MAP_FAILED);
  struct context c={.fd=fd,.view=view};assert(!pipe(c.ready)&&!pipe(c.gate));
  pid_t actor=fork();assert(actor>=0);
  if(!actor) {
    char*stack=mmap(NULL,STACK,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(stack!=MAP_FAILED);
    uint64_t flags=(vm?CLONE_VM:0)|(files?CLONE_FILES:0);
    if(!strcmp(kind,"vfork")||!strcmp(kind,"clone3vfork"))flags|=CLONE_VM|CLONE_VFORK;
    long made;
    if(!strncmp(kind,"clone3",6)) {
      *(struct context**)(stack+STACK-16)=&c;
      struct clone_args a={.flags=flags,.exit_signal=SIGCHLD,.stack=(uintptr_t)stack,.stack_size=STACK-16};
      made=fixture_clone3(&a,sizeof a);
    } else if(!strcmp(kind,"fork")) {made=fork();if(!made)descendant(&c);}
    else made=clone(child_entry,stack+STACK,(int)flags|SIGCHLD,&c);
    assert(made>0);for(;;)pause();
  }
  pid_t child;assert(read(c.ready[0],&child,sizeof child)==sizeof child&&child>0);
  /* The diagnostic kills the creator at its real event; the ordinary control
   * kills it only here. Both use actual SIGKILL and the same final owners. */
  assert(!kill(actor,SIGKILL)||errno==ESRCH);int status;
  assert(waitpid(actor,&status,0)==actor&&WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL);
  assert(!mprotect(view,4096,PROT_READ)&&view[0]==42&&!munmap(view,N)&&!close(fd));
  stage("last_descendant");assert(write(c.gate[1],"g",1)==1);
  assert(waitpid(child,&status,0)==child&&status==0);stage("closed");
  puts("FACT creation_actual_pid_base42_cow99 1");
}
static void*execute_thread(void*unused) {
  (void)unused;char*args[]={"true",NULL};execv("/usr/bin/true",args);_exit(91);
}
static void executed(int nonleader) {
  stage("baseline");int fd=memfd_create("exec-metadata-v9",MFD_CLOEXEC);
  assert(fd>=0&&!ftruncate(fd,N)&&!fallocate(fd,FALLOC_FL_KEEP_SIZE,0,N));
  stage("owned");pid_t p=fork();assert(p>=0);
  if(!p){if(nonleader){pthread_t t;assert(!pthread_create(&t,NULL,execute_thread,NULL));for(;;)pause();}execute_thread(NULL);}
  int s;assert(waitpid(p,&s,0)==p);
  assert((WIFEXITED(s)&&WEXITSTATUS(s)==0)||(WIFSIGNALED(s)&&WTERMSIG(s)==SIGKILL));
  stage("parent_retains");assert(!close(fd));stage("closed");
  printf("FACT exec_wait_status %d nonleader %d\n",s,nonleader);
}
int main(int argc,char**argv) {
  setbuf(stdout,NULL);assert(argc==4);
  if(!strcmp(argv[1],"invalid")) {
    stage("baseline");errno=0;assert(syscall(SYS_clone3,(void*)1,88)==-1&&errno==EFAULT);
    errno=0;assert(syscall(SYS_clone3,NULL,0)==-1&&errno==EINVAL);
    stage("closed");puts("FACT invalid_clone3_real_errors 1");return 0;
  }
  if(!strcmp(argv[1],"exec")){executed(atoi(argv[2]));return 0;}
  creation(argv[1],atoi(argv[2]),atoi(argv[3]));return 0;
}
