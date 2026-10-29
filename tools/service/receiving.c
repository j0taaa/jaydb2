#include "receiving.h"
#include <stddef.h>
#ifndef JAYDB_RECEIVING_BUILD_ID
#error "The builder must identify the loaded receiving artifact"
#endif
#if !defined(__linux__) || !defined(__x86_64__)
#error "The selected receiving environment is Linux x86_64"
#endif
static inline long raw5(long nr,long a,long b,long c,long d,long e) {
  register long r10 __asm__("r10")=d;
  register long r8 __asm__("r8")=e;
  long result;
  __asm__ volatile("syscall":"=a"(result):"a"(nr),"D"(a),"S"(b),"d"(c),
    "r"(r10),"r"(r8):"rcx","r11","memory");
  return result;
}
static inline __uint128_t nat(struct jayacct_u128 n) {
  return ((__uint128_t)n.hi<<64)|n.lo;
}
static inline struct jayacct_u128 words(__uint128_t n) {
  return (struct jayacct_u128){(uint64_t)n,(uint64_t)(n>>64)};
}
static inline void zero(void *p,size_t n) {
  volatile unsigned char *b=p;
  for(size_t i=0;i<n;++i)b[i]=0;
}
static inline long sample(struct jayacct_u128 *out) {
  long ts[2]={0,0};
  long e=raw5(228,1,(long)ts,0,0,0); /* CLOCK_MONOTONIC */
  if(e<0)return -e;
  if(ts[0]<0||ts[1]<0||ts[1]>=1000000000L)return EINVAL;
  *out=words((__uint128_t)(unsigned long)ts[0]*1000000000u+(unsigned long)ts[1]);
  return 0;
}
#ifdef JAYDB_RECEIVING_TEST
extern int jaydb_receiving_test_open(struct jayacct_window_snapshot*);
#endif
static inline int open_window(struct jayacct_window_snapshot *out,struct jayacct_u128 until) {
#ifdef JAYDB_RECEIVING_TEST
  (void)until;
  return jaydb_receiving_test_open(out);
#else
  return jayacct_raw_marker(out,3|JAYACCT_UNTIL_FLAG,until);
#endif
}
const struct jaydb_receiving_descriptor *jaydb_receiving_describe(void) {
  static const struct jaydb_receiving_descriptor d={JAYDB_RECEIVING_ABI,
    sizeof(struct jaydb_receiving_result),
#ifdef JAYDB_RECEIVING_TEST
    1,
#else
    0,
#endif
    JAYDB_RECEIVING_BUILD_ID};
  return &d;
}
uint64_t jaydb_receiving_begin(int fd,struct jayacct_u128 duration,
    struct jayacct_u128 instrument_deadline,struct jaydb_receiving_result *r) {
  if(!r)return JAYDB_RECEIVING_ARGUMENT;
  zero(r,sizeof *r);r->abi=JAYDB_RECEIVING_ABI;r->status=JAYDB_RECEIVING_ARGUMENT;
  if(fd<0||!nat(duration)||!nat(instrument_deadline))return r->status;
  /* All native locals/result backing are active before waiting. ppoll's
   * kernel-internal temporaries are excluded by the selected memory measure. */
  struct {int fd;short events,revents;} ready={fd,1,0};
  unsigned char byte=0;
  for(;;) {
    ready.revents=0;
    long p=raw5(271,(long)&ready,1,0,0,8); /* ppoll, no idle timeout */
    if(p<0) {
      r->system_error=(uint64_t)-p;
      r->status=p==-EINTR?JAYDB_RECEIVING_INTERRUPTED:JAYDB_RECEIVING_IO;
      return r->status;
    }
    long ce=sample(&r->started_ns);
    if(ce){r->system_error=(uint64_t)ce;r->status=JAYDB_RECEIVING_IO;return r->status;}
    long n=raw5(0,fd,(long)&byte,1,0,0);
    if(n==0) {zero(&r->started_ns,sizeof r->started_ns);r->status=JAYDB_RECEIVING_EOF;return r->status;}
    if(n<0) {
      zero(&r->started_ns,sizeof r->started_ns);
      if(n==-EAGAIN)continue; /* no byte was consumed, no stage began */
      r->system_error=(uint64_t)-n;
      r->status=n==-EINTR?JAYDB_RECEIVING_INTERRUPTED:JAYDB_RECEIVING_IO;
      return r->status;
    }
    r->received=1;r->first_byte=byte;
    __uint128_t start=nat(r->started_ns),span=nat(duration);
    __uint128_t end=start+span;
    r->deadline_ns=words(end<start?~(__uint128_t)0:end);
    ce=sample(&r->received_ns);
    int e=open_window(&r->window,instrument_deadline);
    if(e) {r->system_error=(uint64_t)e;r->status=JAYDB_RECEIVING_INSTRUMENT;return r->status;}
    const struct jayacct_window_snapshot *w=&r->window;
    if(w->abi!=JAYACCT_WINDOW_ABI||w->snapshot.abi!=JAYACCT_ABI||w->error
        ||w->state!=JAYACCT_WINDOW_ACTIVE||!nat(w->scope_id)||!nat(w->begin_sequence)
        ||nat(w->begin_sequence)!=nat(w->snapshot.sequence)
        ||nat(w->begin_monotonic_ns)!=nat(w->snapshot.monotonic_ns)
        ||nat(w->begin_monotonic_ns)<nat(r->received_ns)
        ||nat(w->peak_sequence)!=nat(w->begin_sequence)
        ||nat(w->peak_monotonic_ns)!=nat(w->begin_monotonic_ns)
        ||nat(w->peak)!=nat(w->snapshot.current)) {
      r->system_error=EINVAL;r->status=JAYDB_RECEIVING_INSTRUMENT;return r->status;
    }
    if(!(w->snapshot.flags&JAYACCT_FROZEN)||!(w->peak_flags&JAYACCT_FROZEN)
        ||(w->snapshot.flags&(JAYACCT_INCOMPLETE|JAYACCT_OWNER_DIED))
        ||(w->peak_flags&(JAYACCT_INCOMPLETE|JAYACCT_OWNER_DIED))) {
      r->status=JAYDB_RECEIVING_COVERAGE;return r->status;
    }
    if(ce){r->system_error=(uint64_t)ce;r->status=JAYDB_RECEIVING_IO;return r->status;}
    r->status=JAYDB_RECEIVING_STARTED;return r->status;
  }
}
