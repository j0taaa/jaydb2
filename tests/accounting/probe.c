#define _GNU_SOURCE
#include "counter.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>
#define PAGE 4096u
static uint64_t amount(void) {
  struct jayacct_snapshot n;assert(!jayacct_barrier(&n));assert(!n.current.hi);return n.current.lo;
}
static void sample(const char*name) {
  struct jayacct_snapshot n;assert(!jayacct_barrier(&n));
  printf("%s %llu %llu\n",name,(unsigned long long)n.current.lo,(unsigned long long)n.peak.lo);
}
static void *worker(void *unused) {
  (void)unused;void*p=mmap(NULL,8*PAGE,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
  assert(p!=MAP_FAILED);sample("thread_active");assert(!munmap(p,8*PAGE));return NULL;
}
__attribute__((noinline)) static void grow_stack(size_t n) {
  volatile char space[4096];space[0]=(char)n;space[4095]=(char)(n>>8);
  if(n)grow_stack(n-1);
  __asm__ volatile(""::"r"(space):"memory");
}
int main(int argc,char**argv) {
  assert(argc==2);setbuf(stdout,NULL);
  if(!strcmp(argv[1],"mappings")) {
    uint64_t before=amount();
    void*p=mmap(NULL,16*PAGE,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(p!=MAP_FAILED);
    assert(amount()==before);sample("reserved");
    assert(!mprotect(p+4*PAGE,4*PAGE,PROT_READ|PROT_WRITE));assert(amount()==before+4*PAGE);sample("activated");
    assert(!mprotect(p+4*PAGE,4*PAGE,PROT_NONE));assert(amount()==before+4*PAGE);sample("revoked_retained");
    assert(!munmap(p,16*PAGE));assert(amount()==before);sample("unmapped");
    p=(void*)syscall(SYS_mmap,NULL,3*PAGE,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    assert(p!=MAP_FAILED);assert(amount()==before+3*PAGE);sample("direct_syscall");
    void*q=mremap(p,3*PAGE,7*PAGE,MREMAP_MAYMOVE);assert(q!=MAP_FAILED);
    assert(amount()==before+7*PAGE);sample("remapped");
    assert(!munmap(q,7*PAGE));assert(amount()==before);
  } else if(!strcmp(argv[1],"aliases")) {
    int fd=(int)syscall(SYS_memfd_create,"aliases",0);assert(fd>=0);assert(!ftruncate(fd,32*PAGE));
    uint64_t before=amount();
    void*a=mmap(NULL,16*PAGE,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);assert(a!=MAP_FAILED);
    assert(amount()==before+16*PAGE);sample("alias_first");
    void*b=mmap(NULL,16*PAGE,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);assert(b!=MAP_FAILED);
    assert(amount()==before+16*PAGE);sample("alias_same");
    void*c=mmap(NULL,16*PAGE,PROT_READ|PROT_WRITE,MAP_SHARED,fd,8*PAGE);assert(c!=MAP_FAILED);
    assert(amount()==before+24*PAGE);sample("alias_partial");
    assert(!munmap(a,16*PAGE));assert(amount()==before+24*PAGE);
    assert(!munmap(b,16*PAGE));assert(amount()==before+24*PAGE);
    assert(!munmap(c,16*PAGE));assert(amount()==before+24*PAGE);close(fd);
  } else if(!strcmp(argv[1],"retained_remap")) {
    uint64_t before=amount();
    void*p=mmap(NULL,4*PAGE,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(p!=MAP_FAILED);
    assert(!mprotect(p,4*PAGE,PROT_NONE));assert(amount()==before+4*PAGE);
    void*target=mmap(NULL,8*PAGE,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(target!=MAP_FAILED);
    void*q=mremap(p,4*PAGE,8*PAGE,MREMAP_MAYMOVE|MREMAP_FIXED,target);assert(q==target);
    assert(amount()==before+4*PAGE);sample("remapped_retained");
    assert(!mprotect(q+4*PAGE,4*PAGE,PROT_READ|PROT_WRITE));assert(amount()==before+8*PAGE);
    assert(!munmap(q,8*PAGE));assert(amount()==before);
    p=mmap(NULL,4*PAGE,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(p!=MAP_FAILED);
    assert(amount()==before+4*PAGE);
    q=mmap(p,4*PAGE,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED,-1,0);assert(q==p);
    assert(amount()==before);sample("replaced_reservation");assert(!munmap(p,4*PAGE));
  } else if(!strcmp(argv[1],"shared_anon_event")) {
    uint64_t before=amount();
    void*p=mmap(NULL,8*PAGE,PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,-1,0);assert(p!=MAP_FAILED);
    assert(amount()==before+8*PAGE);
    void*q=mremap(p,0,8*PAGE,MREMAP_MAYMOVE);assert(q!=MAP_FAILED);assert(amount()==before+8*PAGE);
    assert(!munmap(p,8*PAGE));assert(amount()==before+8*PAGE);
    assert(!munmap(q,8*PAGE));assert(amount()==before);sample("event_alias_released");
  } else if(!strcmp(argv[1],"malloc")) {
    sample("before_malloc");void*p=malloc(16*1024*1024);assert(p);memset(p,7,16*1024*1024);sample("malloc");
    p=realloc(p,24*1024*1024);assert(p);sample("realloc");free(p);sample("free");
    char*a=malloc(100);assert(a);sample("small");free(a);sample("small_free_retained");
  } else if(!strcmp(argv[1],"brk")) {
    uintptr_t old=(uintptr_t)syscall(SYS_brk,0);uint64_t before=amount();
    uintptr_t next=(uintptr_t)syscall(SYS_brk,old+32*PAGE);assert(next==old+32*PAGE);
    assert(amount()==before+32*PAGE);sample("brk_grown");
    assert((uintptr_t)syscall(SYS_brk,old)==old);assert(amount()==before);sample("brk_released");
  } else if(!strcmp(argv[1],"threads")) {
    sample("thread_before");pthread_t t;assert(!pthread_create(&t,NULL,worker,NULL));assert(!pthread_join(t,NULL));sample("thread_after");
  } else if(!strcmp(argv[1],"stack")) {
    uint64_t before=amount();grow_stack(255);uint64_t after=amount();
    assert(after>before+512*1024);sample("implicit_stack");
  } else if(!strcmp(argv[1],"fork")) {
    sample("fork_before");pid_t child=fork();assert(child>=0);
    if(!child){sample("fork_child");_exit(0);}assert(waitpid(child,NULL,0)==child);sample("fork_after");
  } else if(!strcmp(argv[1],"fork_storm")) {
    pid_t children[8];
    for(unsigned i=0;i<8;i++) {
      children[i]=fork();assert(children[i]>=0);
      if(!children[i]){execl("/bin/true","true",NULL);_exit(127);}
    }
    for(unsigned i=0;i<8;i++){int status;assert(waitpid(children[i],&status,0)==children[i]);assert(!status);}
    sample("all_children_retired");
  } else if(!strcmp(argv[1],"vfork")) {
    pid_t child=vfork();assert(child>=0);
    if(!child){execl("/bin/true","true",NULL);_exit(127);}int status;assert(waitpid(child,&status,0)==child);assert(!status);sample("vfork_after");
  } else if(!strcmp(argv[1],"transient")) {
    sample("transient_before");void*p=mmap(NULL,64*1024*1024,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    assert(p!=MAP_FAILED);assert(!munmap(p,64*1024*1024));sample("transient_after");
  } else if(!strcmp(argv[1],"transient_stack")) {
    sample("transient_stack_before");void*p=mmap(NULL,64*1024*1024,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    assert(p!=MAP_FAILED);grow_stack(255);assert(!munmap(p,64*1024*1024));sample("transient_stack_after");
  } else if(!strcmp(argv[1],"hold")) {
    struct jayacct_snapshot begin,end;
    assert(!jayacct_hold_begin(&begin));assert(begin.flags&JAYACCT_HELD);
    volatile uint64_t field=123;__asm__ volatile(""::"r"(&field):"memory");
    assert(!jayacct_hold_end(&end));assert(end.flags&JAYACCT_HELD);
    assert(begin.current.lo==end.current.lo&&begin.current.hi==end.current.hi);
    sample("held_field_window");
  } else if(!strcmp(argv[1],"exec_fail")) {
    size_t bytes=16*65536;
    char*p=mmap(NULL,bytes,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(p!=MAP_FAILED);
    memset(p,'a',bytes);char*args[17];
    for(unsigned i=0;i<16;i++){args[i]=p+i*65536;args[i][65535]=0;}args[16]=NULL;
    char*env[]={NULL};uint64_t before=amount();sample("exec_before");
    assert(syscall(SYS_execve,"tests/accounting/.build/not-elf",args,env)==-1);
    assert(errno==ENOEXEC);assert(amount()==before);sample("exec_failed_same_visible_maps");
    assert(!munmap(p,bytes));
  } else return 2;
  return 0;
}
