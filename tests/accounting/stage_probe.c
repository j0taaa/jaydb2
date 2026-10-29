#define _GNU_SOURCE
#include "stage_control.h"
#include "window.h"
#include "deadline.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>
#include <sched.h>
#include <fcntl.h>
static __uint128_t wide(struct jayacct_u128 n){return ((__uint128_t)n.hi<<64)|n.lo;}
static struct jayacct_u128 words(__uint128_t n){return (struct jayacct_u128){n,n>>64};}
static __uint128_t now(void){struct timespec t;assert(!clock_gettime(CLOCK_MONOTONIC,&t));return (__uint128_t)t.tv_sec*1000000000u+t.tv_nsec;}
static int vfork_child(void*arg){
  const void*page=arg;usleep(200000);struct jaystage_receipt r;assert(!jaystage_read(page,&r));
  assert(r.state==JAYSTAGE_EXPIRED_PENDING_RECOVERY);assert(r.pending_flags&JAYSTAGE_PENDING_VFORK);_exit(0);
}
#define CHECK_STAGE(call,want) do { \
  int e=(call);uint64_t residue; \
  __asm__ volatile("mov %%rdi,%0":"=r"(residue)::"memory"); \
  pid_t actual=getpid();assert(e==(want)&&residue!=JAYSTAGE_MARKER&&actual==pid); \
} while(0)
static void ordinary(void){long pid;__asm__ volatile("syscall":"=a"(pid):"a"(39):"rcx","r11","memory");assert(pid==getpid());}
static void print_receipt(const char*name,struct jaystage_receipt*r){printf("%s %lu %lu %lu %lu\n",name,r->state,r->pending_flags,r->observed_ns.lo,r->recovery_sequence.lo);fflush(stdout);}
int main(int argc,char**argv){
 assert(argc==2);pid_t pid=getpid();
 struct jaystage_request req={.abi=1,.stage=3};struct jaystage_receipt receipt;
 if(!strcmp(argv[1],"outside")){
   CHECK_STAGE(jaystage_raw_call(&req,&receipt,JAYSTAGE_ARM),ENOTSUP);
   CHECK_STAGE(jaystage_raw_call(&req,&receipt,JAYSTAGE_RETIRE),ENOTSUP);
   CHECK_STAGE(jaystage_raw_call(NULL,&receipt,JAYSTAGE_ARM),EINVAL);
   CHECK_STAGE(jaystage_raw_call((void*)(uintptr_t)JAYSTAGE_MARKER,NULL,JAYSTAGE_ARM),EINVAL);
   return 0;
 }
 if(!strcmp(argv[1],"passive")){
   struct jayacct_window_snapshot before,after;assert(!jayacct_window_barrier(&before));
   const void*page;assert(!jaystage_map(atoi(getenv("JAYDB_ACCOUNTING_STAGE_FD")),&page));
   assert(!jayacct_window_barrier(&after));assert(!jaystage_read(page,&receipt));assert(receipt.state==JAYSTAGE_IDLE);
   printf("page_alias %lu %lu\n",before.snapshot.current.lo,after.snapshot.current.lo);
   assert(!jaystage_unmap(page));assert(!jayacct_window_end(&after));return 0;
 }
 const void*page;assert(!jaystage_map(atoi(getenv("JAYDB_ACCOUNTING_STAGE_FD")),&page));
 struct jayacct_window_snapshot window;assert(!jayacct_window_barrier(&window));req.scope_id=window.scope_id;
 req.generation=words(1);req.start_ns=words(now());
 if(!strcmp(argv[1],"old"))req.deadline_ns=req.start_ns;
 else if(!strcmp(argv[1],"huge"))req.deadline_ns=words((__uint128_t)1<<100);
 else req.deadline_ns=words(wide(req.start_ns)+120000000u);
 CHECK_STAGE(jaystage_raw_call(&req,&receipt,JAYSTAGE_ARM),0);ordinary();print_receipt("armed",&receipt);
 if(!strcmp(argv[1],"huge")){
   assert(receipt.state==JAYSTAGE_ARMED);assert(!jaystage_retire(&req,&receipt));ordinary();
   struct jaystage_request bad=req;bad.generation=words(2);bad.deadline_ns=words(((__uint128_t)1<<100)+1);
   assert(jaystage_arm(&bad,&receipt)==EPERM);ordinary();
   assert(jaystage_arm(&req,&receipt)==ESTALE);ordinary();
   bad=req;bad.generation=words(2);assert(!jaystage_arm(&bad,&receipt));assert(!jaystage_retire(&bad,&receipt));
   assert(!jayacct_window_end(&window));assert(jaystage_arm(&bad,&receipt)==ESTALE);ordinary();
   assert(!jayacct_window_begin(&window));bad.generation=words(3);
   CHECK_STAGE(jaystage_raw_call(&bad,&receipt,JAYSTAGE_ARM),ESTALE);
   bad.scope_id=window.scope_id;assert(!jaystage_arm(&bad,&receipt));assert(!jaystage_retire(&bad,&receipt));
   assert(!jayacct_window_end(&window));
 } else {
   if(!strcmp(argv[1],"hold")) {
     struct jayacct_snapshot s;assert(!jayacct_hold_begin(&s));usleep(200000);
     assert(!jaystage_read(page,&receipt));print_receipt("held_pending",&receipt);
     assert(receipt.state==JAYSTAGE_EXPIRED_PENDING_RECOVERY&&(receipt.pending_flags&JAYSTAGE_PENDING_HOLD));
     CHECK_STAGE(jaystage_raw_call(&req,&receipt,JAYSTAGE_RETIRE),EBUSY);ordinary();
     assert(jayacct_window_end(&window)==EBUSY);assert(window.state==JAYACCT_WINDOW_ACTIVE);
     assert(!jayacct_hold_release());ordinary();
   } else if(!strcmp(argv[1],"vfork")) {
     char*stack=mmap(NULL,1048576,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(stack!=MAP_FAILED);
     pid_t child=clone(vfork_child,stack+1048576,CLONE_VM|CLONE_VFORK|SIGCHLD,(void*)page);assert(child>0);
     int s;assert(waitpid(child,&s,0)==child&&WIFEXITED(s)&&WEXITSTATUS(s)==0);assert(!munmap(stack,1048576));
   } else if(!strcmp(argv[1],"auth")) {
     pid_t child=fork();assert(child>=0);
     if(!child){struct jaystage_request bad=req;bad.generation=words(2);assert(jaystage_arm(&bad,&receipt)==EPERM);ordinary();_exit(0);}
     int s;assert(waitpid(child,&s,0)==child&&WIFEXITED(s)&&WEXITSTATUS(s)==0);
     usleep(150000);
   } else if(strcmp(argv[1],"old")){
    int p[2];assert(!pipe(p));pid_t child=fork();assert(child>=0);
    if(!child){close(p[0]);void*m=mmap(NULL,1048576,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(m!=MAP_FAILED);*(char*)m=42;assert(write(p[1],"x",1)==1);for(;;)pause();}
    close(p[1]);char c;assert(read(p[0],&c,1)==1&&c=='x');close(p[0]);
    do{assert(!jaystage_read(page,&receipt));if(receipt.state==JAYSTAGE_ARMED)usleep(1000);}while(receipt.state==JAYSTAGE_ARMED);
    assert(!kill(child,SIGKILL));int status;assert(waitpid(child,&status,0)==child);assert(WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL);
   }
   assert(!jayacct_window_barrier(&window));assert(!jaystage_read(page,&receipt));
   print_receipt("expired",&receipt);assert(receipt.state==JAYSTAGE_EXPIRED_RECOVERED);
   assert(wide(receipt.observed_ns)>=wide(req.deadline_ns));assert(wide(receipt.recovery_sequence)>wide(receipt.arm_sequence));
   assert(window.state==JAYACCT_WINDOW_ACTIVE&&(window.snapshot.flags&JAYACCT_INCOMPLETE));
   struct jaystage_receipt saved=receipt;assert(!jayacct_barrier(&window.snapshot));assert(!jaystage_read(page,&receipt));assert(!memcmp(&saved,&receipt,sizeof saved));
   assert(!jaystage_retire(&req,&receipt));ordinary();assert(receipt.state==JAYSTAGE_RETIRED);
   CHECK_STAGE(jaystage_raw_call(&req,&receipt,JAYSTAGE_RETIRE),EBUSY);ordinary();
   assert(!jayacct_window_end(&window));assert(window.state==JAYACCT_WINDOW_CLOSED);
 }
 assert(!jaystage_unmap(page));return 0;
}
