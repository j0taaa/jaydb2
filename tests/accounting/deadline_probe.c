#define _GNU_SOURCE
#include "deadline.h"
#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>
#include <unistd.h>
static _Atomic uint64_t progress;
static _Atomic int done;
static void*worker(void*unused) {
  (void)unused;while(!atomic_load(&done))atomic_fetch_add(&progress,1);return NULL;
}
static uint64_t now(void) {
  struct timespec t;assert(!clock_gettime(CLOCK_MONOTONIC,&t));return (uint64_t)t.tv_sec*1000000000+t.tv_nsec;
}
static struct jayacct_u128 future(void) {return(struct jayacct_u128){now()+1000000000,0};}
int main(int argc,char**argv) {
  assert(argc==2);setbuf(stdout,NULL);
  struct jayacct_snapshot s;
  if(!strcmp(argv[1],"past")) {
    assert(jayacct_barrier_until(&s,(struct jayacct_u128){0,0})==ETIMEDOUT);
    assert(!s.abi);
    assert(jayacct_hold_begin_until(&s,(struct jayacct_u128){1,0})==ETIMEDOUT);
    assert(jayacct_hold_release()==EPERM);
    assert(!jayacct_barrier_until(&s,(struct jayacct_u128){UINT64_MAX,UINT64_MAX}));
    struct jayacct_window_snapshot w;
    assert(!jayacct_hold_begin_until(&s,future()));assert(!jayacct_window_begin_until(&w,future()));
    assert(jayacct_window_begin_until(&w,future())==EBUSY);
    assert(!jayacct_window_end_until(&w,future()));assert(!jayacct_hold_release());
    puts("past_deadline_and_unreachable_future_ok");return 0;
  }
  void*shared=mmap(NULL,JAYACCT_SHARED_BYTES,PROT_READ|PROT_WRITE,MAP_SHARED,atoi(getenv("JAYDB_ACCOUNTING_FD")),0);
  assert(shared!=MAP_FAILED);
  pthread_t thread;assert(!pthread_create(&thread,NULL,worker,NULL));while(!atomic_load(&progress)){}
  assert(!jayacct_hold_begin(&s));
  struct jayacct_window_snapshot opened,failed,reading,closed;
  assert(!jayacct_window_begin(&opened));
  uint64_t frozen=atomic_load(&progress),start=now(),until=start+5000000;
  assert(jayacct_window_end_until(&failed,(struct jayacct_u128){until,0})==ETIMEDOUT);
  uint64_t elapsed=now()-start;assert(elapsed>=5000000&&elapsed<1000000000);
  assert(!failed.abi);
  for(unsigned i=0;i<100000;i++)assert(atomic_load(&progress)==frozen);
  assert(!jayacct_window_read(shared,&reading));
  assert(reading.state==JAYACCT_WINDOW_ACTIVE&&reading.scope_id.lo==opened.scope_id.lo);
  assert(!jayacct_hold_release());
  while(atomic_load(&progress)==frozen){}
  atomic_store(&done,1);assert(!pthread_join(thread,NULL));
  assert(!jayacct_window_end_until(&closed,future()));
  assert(closed.state==JAYACCT_WINDOW_CLOSED&&closed.scope_id.lo==opened.scope_id.lo);
  printf("cancelled_%s %llu %llu\n",argv[1],(unsigned long long)elapsed,(unsigned long long)reading.scope_id.lo);
  assert(!munmap(shared,JAYACCT_SHARED_BYTES));return 0;
}
