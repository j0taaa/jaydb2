#define _GNU_SOURCE
#include "window.h"
#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>
#define MIB (UINT64_C(1024)*1024)
_Static_assert(sizeof(struct jayacct_snapshot)==120,"legacy ABI changed");
_Static_assert(sizeof(struct jayacct_window_snapshot)==280,"window ABI changed");
static void emit(const char*name,const struct jayacct_window_snapshot*n) {
  printf("%s %llu %llu %llu %llu %llu %llu %llu %llu %llu %llu\n",name,
         (unsigned long long)n->scope_id.lo,(unsigned long long)n->peak.lo,
         (unsigned long long)n->peak_sequence.lo,(unsigned long long)n->peak_monotonic_ns.lo,
         (unsigned long long)n->snapshot.peak.lo,(unsigned long long)n->snapshot.current.lo,
         (unsigned long long)n->begin_sequence.lo,(unsigned long long)n->end_sequence.lo,
         (unsigned long long)n->peak_flags,(unsigned long long)n->state);
}
int main(void) {
  setbuf(stdout,NULL);
  int fd=atoi(getenv("JAYDB_ACCOUNTING_FD"));
  void*shared=mmap(NULL,JAYACCT_SHARED_BYTES,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);
  assert(shared!=MAP_FAILED);
  void*arena=mmap(NULL,4*MIB,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
  assert(arena!=MAP_FAILED);
  struct jayacct_snapshot base;assert(!jayacct_barrier(&base));assert(!jayacct_barrier(&base));
  uint64_t ceiling=base.current.lo+MIB;
  struct jayacct_window_snapshot one,two,three,reading,nested;
  assert(!jayacct_window_begin(&one));assert(one.state==JAYACCT_WINDOW_ACTIVE);
  assert(jayacct_window_begin(&nested)==EBUSY);
  arena=mremap(arena,4*MIB,10*MIB,MREMAP_MAYMOVE);assert(arena!=MAP_FAILED);
  arena=mremap(arena,10*MIB,4*MIB,MREMAP_MAYMOVE);assert(arena!=MAP_FAILED);
  assert(!jayacct_window_end(&one));assert(one.state==JAYACCT_WINDOW_CLOSED);emit("one",&one);
  assert(!jayacct_window_read(shared,&reading));assert(reading.peak.lo==one.peak.lo);
  assert(jayacct_window_end(&nested)==EALREADY);
  assert(!jayacct_window_begin(&two));
  arena=mremap(arena,4*MIB,6*MIB,MREMAP_MAYMOVE);assert(arena!=MAP_FAILED);
  assert(!jayacct_window_barrier(&reading));assert(reading.peak.lo==two.peak.lo+2*MIB);
  arena=mremap(arena,6*MIB,4*MIB,MREMAP_MAYMOVE);assert(arena!=MAP_FAILED);
  assert(!jayacct_window_end(&two));emit("two",&two);
  assert(!jayacct_window_begin(&three));
  arena=mremap(arena,4*MIB,5*MIB,MREMAP_MAYMOVE);assert(arena!=MAP_FAILED);
  arena=mremap(arena,5*MIB,4*MIB,MREMAP_MAYMOVE);assert(arena!=MAP_FAILED);
  assert(!jayacct_window_end(&three));emit("three",&three);
  assert(one.peak.lo==base.current.lo+6*MIB);
  assert(two.peak.lo==base.current.lo+2*MIB);
  assert(three.peak.lo==ceiling);
  assert(one.snapshot.peak.lo==two.snapshot.peak.lo&&two.snapshot.peak.lo==three.snapshot.peak.lo);
  assert(one.peak_sequence.lo<two.begin_sequence.lo&&two.peak_sequence.lo<three.begin_sequence.lo);
  assert(!munmap(arena,4*MIB));assert(!jayacct_barrier(&base));
  assert(!jayacct_window_read(shared,&reading));
  assert(reading.scope_id.lo==three.scope_id.lo&&reading.state==JAYACCT_WINDOW_CLOSED);
  assert(reading.peak.lo==three.peak.lo&&reading.peak_sequence.lo==three.peak_sequence.lo);
  assert(reading.peak_monotonic_ns.lo==three.peak_monotonic_ns.lo);
  assert(reading.end_sequence.lo==three.end_sequence.lo&&base.sequence.lo>reading.end_sequence.lo);
  assert(reading.snapshot.current.lo==base.current.lo);emit("closed_later",&reading);
  printf("ceiling %llu\n",(unsigned long long)ceiling);
  assert(!munmap(shared,JAYACCT_SHARED_BYTES));return 0;
}
