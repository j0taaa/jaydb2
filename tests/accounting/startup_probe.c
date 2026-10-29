#define _GNU_SOURCE
#include "window.h"
#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
#define MIB (UINT64_C(1024)*1024)
_Static_assert(sizeof(struct jayacct_snapshot)==120,"legacy ABI changed");
_Static_assert(sizeof(struct jayacct_window_snapshot)==280,"window ABI changed");
__attribute__((constructor)) static void before_main(void) {
  void*p=mmap(NULL,64*MIB,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
  assert(p!=MAP_FAILED);((volatile char*)p)[0]=1;assert(!munmap(p,64*MIB));
}
static void emit(const char*name,const struct jayacct_window_snapshot*n) {
  printf("WINDOW %s %llu %llu %llu %llu %llu %llu %llu %llu %llu\n",name,
    (unsigned long long)n->scope_id.lo,(unsigned long long)n->state,
    (unsigned long long)n->begin_sequence.lo,(unsigned long long)n->end_sequence.lo,
    (unsigned long long)n->peak.lo,(unsigned long long)n->peak_sequence.lo,
    (unsigned long long)n->peak_monotonic_ns.lo,(unsigned long long)n->peak_flags,
    (unsigned long long)n->snapshot.current.lo);
}
int main(int argc,char**argv) {
  assert(argc==2);setbuf(stdout,NULL);
  const char*text=getenv("JAYDB_ACCOUNTING_FD");assert(text);
  void*shared=mmap(NULL,JAYACCT_SHARED_BYTES,PROT_READ|PROT_WRITE,MAP_SHARED,atoi(text),0);
  assert(shared!=MAP_FAILED);struct jayacct_window_snapshot first,closed,late,request;
  assert(!jayacct_window_read(shared,&first));emit("initial",&first);
  if(!strcmp(argv[1],"default")) {
    assert(first.state==JAYACCT_WINDOW_NONE&&!first.scope_id.lo);
    assert(!jayacct_window_begin(&late)&&!jayacct_window_end(&late));emit("late",&late);
    assert(late.peak.lo+32*MIB<late.snapshot.peak.lo);
  } else {
    assert(first.state==JAYACCT_WINDOW_ACTIVE&&first.scope_id.lo==1&&first.begin_sequence.lo==1);
    assert(first.peak.lo>first.snapshot.current.lo+32*MIB&&(first.peak_flags&JAYACCT_INCOMPLETE));
    if(!strcmp(argv[1],"unclosed")){puts("FACT completed 1");return 0;}
    assert(!strcmp(argv[1],"service"));
    assert(jayacct_window_begin(&late)==EBUSY&&late.scope_id.lo==first.scope_id.lo);
    assert(!jayacct_window_end(&closed)&&closed.state==JAYACCT_WINDOW_CLOSED);emit("closed",&closed);
    assert(closed.peak.lo==first.peak.lo&&closed.peak_sequence.lo==first.peak_sequence.lo);
    assert(!jayacct_window_begin(&request)&&request.scope_id.lo==2);
    void*p=mmap(NULL,4*MIB,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    assert(p!=MAP_FAILED&&!munmap(p,4*MIB)&&!jayacct_window_end(&request));emit("request",&request);
    assert(request.peak.lo+32*MIB<closed.peak.lo);
    assert(request.peak_sequence.lo>=request.begin_sequence.lo&&request.peak_flags&JAYACCT_INCOMPLETE);
  }
  assert(!munmap(shared,JAYACCT_SHARED_BYTES));puts("FACT completed 1");return 0;
}
