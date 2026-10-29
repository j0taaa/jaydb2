#define _GNU_SOURCE
#include "counter.h"
#include <assert.h>
#include <errno.h>
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>
static void*shared;
static void *worker(void*unused) {
  (void)unused;
  for(unsigned i=0;i<200;i++) {
    struct jayacct_transaction tx;struct jayacct_snapshot n;
    assert(!jayacct_begin(shared,&tx));
    void*p=mmap(NULL,4096,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);assert(p!=MAP_FAILED);
    assert(!jayacct_commit(&tx,(struct jayacct_u128){0},(struct jayacct_u128){4096,0},&n));
    assert(!jayacct_begin(shared,&tx));assert(!munmap(p,4096));
    assert(!jayacct_commit(&tx,(struct jayacct_u128){4096,0},(struct jayacct_u128){0},&n));
  }
  return NULL;
}
static void*died(void*unused) {
  (void)unused;struct jayacct_transaction tx;assert(!jayacct_begin(shared,&tx));
  return NULL; /* robust mutex reports an abandoned allocation transaction */
}
int main(void) {
  shared=mmap(NULL,JAYACCT_SHARED_BYTES,PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,-1,0);
  assert(shared!=MAP_FAILED);assert(!jayacct_init(shared,JAYACCT_SHARED_BYTES));
  struct jayacct_snapshot n;struct jayacct_transaction tx;
  assert(!jayacct_change(shared,(struct jayacct_u128){0},(struct jayacct_u128){4096,0},&n));
  pthread_t threads[4];for(unsigned i=0;i<4;i++)assert(!pthread_create(threads+i,NULL,worker,NULL));
  for(unsigned i=0;i<4;i++)assert(!pthread_join(threads[i],NULL));
  pid_t children[3];
  for(unsigned i=0;i<3;i++) {
    children[i]=fork();assert(children[i]>=0);
    if(!children[i]){worker(NULL);_exit(0);}
  }
  for(unsigned i=0;i<3;i++){int s;assert(waitpid(children[i],&s,0)==children[i]);assert(!s);}
  assert(!jayacct_read(shared,&n));assert(n.current.lo==4096&&!n.current.hi);
  assert(n.peak.lo>=8192);assert(n.peak_monotonic_ns.lo<=n.monotonic_ns.lo);
  assert(n.peak_sequence.lo<=n.sequence.lo);
  assert(!jayacct_begin(shared,&tx));pid_t child=fork();assert(child>=0);
  if(!child){assert(jayacct_cancel(&tx)==EPERM);_exit(0);}
  int s;assert(waitpid(child,&s,0)==child&&!s);assert(!jayacct_cancel(&tx));
  assert(!pthread_create(threads,NULL,died,NULL));assert(!pthread_join(threads[0],NULL));
  assert(jayacct_begin(shared,&tx)==EOWNERDEAD);assert(jayacct_read(shared,&n)==EOWNERDEAD);
  assert(jayacct_begin(shared,&tx)==EOWNERDEAD);
  assert(!munmap(shared,JAYACCT_SHARED_BYTES));
  return 0;
}
