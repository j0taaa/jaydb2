#define _GNU_SOURCE
#include "deadline.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>
#include <unistd.h>

/* These exported functions also make optimized emission inspectable. They
 * exercise the effective inline helper, including the receipt comparison
 * against MARKER for op6, rather than only counter.c's out-of-line wrappers. */
#define LEAF(name,op) __attribute__((noinline,used)) int name(void *p) { \
  return jayacct_raw_marker(p,op,(struct jayacct_u128){UINT64_MAX,UINT64_MAX}); }
LEAF(emission_barrier,0)
LEAF(emission_window,5)
LEAF(emission_release,6)
LEAF(emission_until,JAYACCT_UNTIL_FLAG|4)
__attribute__((noinline,used)) int emission_dynamic(void*p,uint64_t op,struct jayacct_u128 t) {
  return jayacct_raw_marker(p,op,t);
}

/* No function with an argument is allowed between the marker and getpid:
 * that would mask an RDI token left by the wrapper. The register capture is
 * also checked outside the tracer, where an ordinary getpid cannot replay a
 * marker and an unsupported receipt must still remove the token. */
#define CHECK(call,want) do { \
  int error=(call);uint64_t residue; \
  __asm__ volatile("mov %%rdi,%0":"=r"(residue)::"memory"); \
  pid_t actual=getpid(); \
  assert(error==(want)&&residue!=JAYACCT_MARKER&&actual==pid); \
  ++checks; \
} while(0)
static uint64_t clock_ns(void) {
  struct timespec t;assert(!clock_gettime(CLOCK_MONOTONIC,&t));
  return (uint64_t)t.tv_sec*1000000000+(uint64_t)t.tv_nsec;
}
int main(void) {
  setbuf(stdout,NULL);pid_t pid=getpid();unsigned checks=0;
  struct jayacct_snapshot s,read;
  struct jayacct_window_snapshot w,failed;
  uint64_t receipt=0;
  memset(&s,0,sizeof s);memset(&read,0,sizeof read);
  memset(&w,0,sizeof w);memset(&failed,0,sizeof failed);
  char*fd=getenv("JAYDB_ACCOUNTING_FD");
  if(!fd) {
    CHECK(jayacct_barrier(&s),ENOTSUP);
    CHECK(jayacct_window_barrier(&w),ENOTSUP);
    CHECK(jayacct_hold_release(),ENOTSUP);
    CHECK(emission_barrier(&s),ENOTSUP);
    CHECK(emission_window(&w),ENOTSUP);
    CHECK(emission_release(&receipt),ENOTSUP);
    CHECK(emission_until(&w),ENOTSUP);
    CHECK(emission_dynamic(&w,5,(struct jayacct_u128){0,0}),ENOTSUP);
    printf("FACT unsupported_cleanup_checks %u\n",checks);return 0;
  }
  void*page=mmap(NULL,JAYACCT_SHARED_BYTES,PROT_READ|PROT_WRITE,MAP_SHARED,atoi(fd),0);
  assert(page!=MAP_FAILED&&!jayacct_read(page,&read));
  (void)clock_ns(); /* resolve libc/vDSO before the bounded held section */
  CHECK(jayacct_hold_begin(&s),0);
  CHECK(jayacct_barrier(&s),0);
  assert(!jayacct_read(page,&read)&&read.sequence.lo==s.sequence.lo);
  CHECK(jayacct_window_begin(&w),0);
  CHECK(jayacct_window_barrier(&w),0);
  assert(!jayacct_read(page,&read)&&read.sequence.lo==w.snapshot.sequence.lo);
  CHECK(jayacct_raw_marker(&w,5,(struct jayacct_u128){0,0}),0);
  CHECK(jayacct_raw_marker(&w,5,(struct jayacct_u128){0,0}),0);
  assert(!jayacct_read(page,&read)&&read.sequence.lo==w.snapshot.sequence.lo);
  uint64_t before=read.sequence.lo;
  CHECK(jayacct_window_end_until(&failed,(struct jayacct_u128){0,0}),ETIMEDOUT);
  assert(!failed.abi&&!jayacct_read(page,&read)&&read.sequence.lo==before);
  assert(!jayacct_window_read(page,&w)&&w.state==JAYACCT_WINDOW_ACTIVE);
  /* Host C-clock validation belongs before a public time-limit fact. This
   * probe only checks ordering and preserved scope; it publishes no Campo. */
  uint64_t checked=clock_ns();assert(checked>=w.snapshot.monotonic_ns.lo);
  CHECK(jayacct_raw_marker(&receipt,6,(struct jayacct_u128){0,0}),0);
  assert(!jayacct_read(page,&read)&&read.sequence.lo==before);
  CHECK(jayacct_hold_release(),EPERM);
  assert(!jayacct_read(page,&read)&&read.sequence.lo==before);
  CHECK(jayacct_window_end(&w),0);assert(w.state==JAYACCT_WINDOW_CLOSED);
  CHECK(jayacct_window_end(&w),EALREADY);
  CHECK(jayacct_barrier_until(&s,(struct jayacct_u128){0,0}),ETIMEDOUT);
  CHECK(jayacct_hold_begin_until(&s,(struct jayacct_u128){UINT64_MAX,UINT64_MAX}),0);
  CHECK(jayacct_hold_release(),0);
  CHECK(jayacct_hold_release(),EPERM);
  CHECK(emission_barrier(&s),0);
  CHECK(emission_window(&w),0);
  CHECK(emission_release(&receipt),EPERM);
  CHECK(jayacct_hold_begin(&s),0);
  CHECK(jayacct_hold_end(&s),0);
  assert(!munmap(page,JAYACCT_SHARED_BYTES));
  printf("FACT marker_cleanup_checks %u clock_checked_before_cleanup %llu\n",checks,
         (unsigned long long)checked);return 0;
}
