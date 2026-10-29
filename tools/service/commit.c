#include "commit.h"
#include <stddef.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error "The fixed commit environment is Linux x86_64"
#endif
#ifndef JAYDB_COMMIT_STACK_BYTES
#error "The builder must supply its audited stack extent"
#endif
#ifndef JAYDB_COMMIT_BUILD_ID
#error "The builder must bind the loaded artifact to its inputs"
#endif

_Static_assert(sizeof(struct jayacct_snapshot) == 120, "snapshot ABI");
_Static_assert(sizeof(struct jayacct_window_snapshot) == 280, "window ABI");
_Static_assert(sizeof(void *) == 8, "pointer domain");

static __attribute__((always_inline)) inline long raw4(long nr, long a,
    long b, long c, long d) {
  register long r10 __asm__("r10") = d;
  long result;
  __asm__ volatile("syscall" : "=a"(result) : "a"(nr), "D"(a), "S"(b),
    "d"(c), "r"(r10) : "rcx", "r11", "memory");
  return result;
}
static __attribute__((always_inline)) inline void clear(void *p, size_t n) {
  volatile unsigned char *b = p;
  for (size_t i=0; i<n; ++i) b[i]=0;
}
static __attribute__((always_inline)) inline __uint128_t nat(struct jayacct_u128 n) {
  return ((__uint128_t)n.hi << 64) | n.lo;
}
static __attribute__((always_inline)) inline struct jayacct_u128 words(__uint128_t n) {
  return (struct jayacct_u128){(uint64_t)n, (uint64_t)(n>>64)};
}

#ifdef JAYDB_COMMIT_TEST
/* Unit-test-only symbols are absent from every production build. The fixture
 * supplies observations; no such fixture is a real allocation measurement. */
extern int jaydb_commit_test_marker(void *, unsigned);
extern long jaydb_commit_test_clock(long *);
#endif
static __attribute__((always_inline)) inline int marker(void *out, unsigned op,
    struct jayacct_u128 until) {
  clear(out, op>=3 ? sizeof(struct jayacct_window_snapshot) : sizeof(struct jayacct_snapshot));
#ifdef JAYDB_COMMIT_TEST
  (void)until;
  return jaydb_commit_test_marker(out, op);
#else
  int e=jayacct_raw_marker(out,op|JAYACCT_UNTIL_FLAG,until);
  if(e)return e;
  return op>=3 ? (int)((const struct jayacct_window_snapshot *)out)->error : 0;
#endif
}
static __attribute__((always_inline)) inline int release_hold(void *out) {
#ifdef JAYDB_COMMIT_TEST
  return jaydb_commit_test_marker(out,2);
#else
  return jayacct_raw_marker(out,JAYACCT_RELEASE_OPERATION,(struct jayacct_u128){0,0});
#endif
}
static __attribute__((always_inline)) inline long clock_now(long *ts) {
#ifdef JAYDB_COMMIT_TEST
  return jaydb_commit_test_clock(ts);
#else
  return raw4(228, 1, (long)ts, 0, 0); /* clock_gettime(CLOCK_MONOTONIC) */
#endif
}
struct context {
  struct jaydb_root *root;
  const struct jaydb_prepared *prepared;
  const struct jaydb_prepared *limited;
  struct jaydb_commit_result *result;
  struct jayacct_u128 scope, ceiling, deadline, instrument_deadline;
};
/* In production this function is a leaf: fixed-size loops, raw syscalls and
 * stores only. The builder checks LLVM IR and the emitted stack-usage file. */
static __attribute__((noinline)) void critical(void *arg) {
  struct context *c=arg;
  struct jaydb_commit_result *r=c->result;
  const struct jaydb_prepared *chosen=c->prepared;
  struct jayacct_snapshot held;
  volatile long ts[2];
  ts[0]=0; ts[1]=0;
  int e=marker(&held,1,c->instrument_deadline);
  if(e) { r->instrument_error=(uint64_t)e; goto release; }
  e=marker(&r->window,5,c->instrument_deadline);
  if(e) { r->instrument_error=(uint64_t)e; goto release; }
  if(r->window.state!=JAYACCT_WINDOW_ACTIVE || nat(r->window.scope_id)!=nat(c->scope)) {
    r->instrument_error=22; goto release;
  }
  e=marker(&r->window,4,c->instrument_deadline); /* final barrier and close exact scope */
  if(e) { r->instrument_error=(uint64_t)e; goto release; }
  if(r->window.abi!=JAYACCT_WINDOW_ABI || r->window.snapshot.abi!=JAYACCT_ABI
      || r->window.state!=JAYACCT_WINDOW_CLOSED || nat(r->window.scope_id)!=nat(c->scope)
      || !nat(r->window.begin_sequence)
      || nat(r->window.end_sequence)!=nat(r->window.snapshot.sequence)
      || nat(r->window.end_monotonic_ns)!=nat(r->window.snapshot.monotonic_ns)
      || nat(r->window.peak_sequence)<nat(r->window.begin_sequence)
      || nat(r->window.peak_sequence)>nat(r->window.end_sequence)
      || nat(r->window.peak_monotonic_ns)<nat(r->window.begin_monotonic_ns)
      || nat(r->window.peak_monotonic_ns)>nat(r->window.end_monotonic_ns)
      || nat(r->window.snapshot.current)>nat(r->window.peak)) {
    r->instrument_error=22; goto release;
  }
  uint64_t flags=r->window.snapshot.flags;
  if((flags & (JAYACCT_FROZEN|JAYACCT_HELD))!=(JAYACCT_FROZEN|JAYACCT_HELD)
      || !(r->window.peak_flags & JAYACCT_FROZEN)
      || (flags & (JAYACCT_INCOMPLETE|JAYACCT_OWNER_DIED))
      || (r->window.peak_flags & (JAYACCT_INCOMPLETE|JAYACCT_OWNER_DIED))) {
    r->status=JAYDB_COMMIT_COVERAGE; goto release;
  }
  if(nat(r->window.peak)>nat(c->ceiling)) {
    r->status=JAYDB_COMMIT_MEMORY;
    if(!c->limited) goto release;
    chosen=c->limited; goto complete;
  }
  long ce=clock_now((long *)ts);
  if(ce<0 || ts[0]<0 || ts[1]<0 || ts[1]>=1000000000L) {
    r->clock_error=(uint64_t)(ce<0?-ce:22); goto release;
  }
  __uint128_t now=(__uint128_t)(unsigned long)ts[0]*1000000000u+(unsigned long)ts[1];
  r->checked_ns=words(now);
  if(now>=nat(c->deadline)) {
    r->status=JAYDB_COMMIT_TIME;
    if(!c->limited) goto release;
    chosen=c->limited; goto complete;
  }
  r->status=JAYDB_COMMITTED;
complete:
  /* Sole publication point. Both records and all byte buffers are retained.
   * Release cannot revoke this store, even on an FFI return exception. */
  if(chosen->publish) __atomic_store_n(&c->root->published,chosen,__ATOMIC_RELEASE);
  __atomic_store_n(&c->root->completed,chosen,__ATOMIC_RELEASE);
release:
  /* A cancelled scan produces no observation. Only this caller's real clock
   * may establish that the stage deadline was reached. */
  if(r->status==JAYDB_COMMIT_INSTRUMENT && r->instrument_error==ETIMEDOUT) {
    long ce=clock_now((long *)ts);
    if(!ce && ts[0]>=0 && ts[1]>=0 && ts[1]<1000000000L) {
      __uint128_t now=(__uint128_t)(unsigned long)ts[0]*1000000000u+(unsigned long)ts[1];
      r->checked_ns=words(now);
      if(now>=nat(c->deadline)) r->status=JAYDB_COMMIT_TIME;
    }
  }
  e=release_hold(&held);
  if(e) r->release_error=(uint64_t)e;
}

extern void jaydb_commit_on_stack(void (*)(void *), void *, void *);
const struct jaydb_commit_descriptor *jaydb_commit_describe(void) {
  static const struct jaydb_commit_descriptor d={JAYDB_COMMIT_ABI,
    sizeof(struct jaydb_prepared),sizeof(struct jaydb_root),sizeof(struct jaydb_commit_result),
    JAYDB_COMMIT_STACK_BYTES,
#ifdef JAYDB_COMMIT_TEST
    1,
#else
    0,
#endif
    JAYDB_COMMIT_BUILD_ID};
  return &d;
}
uint64_t jaydb_commit_stack_bytes(void) { return JAYDB_COMMIT_STACK_BYTES; }
static uint64_t finish(struct jaydb_root *root, const struct jaydb_prepared *p,
    const struct jaydb_prepared *limited,
    struct jayacct_u128 scope, struct jayacct_u128 ceiling,
    struct jayacct_u128 deadline, struct jayacct_u128 instrument_deadline,
    void *stack, uint64_t bytes,
    struct jaydb_commit_result *r) {
  if(!r) return JAYDB_COMMIT_ARGUMENT;
  clear(r,sizeof *r);
  r->status=JAYDB_COMMIT_ARGUMENT;
  if(!root || root->abi!=JAYDB_COMMIT_ABI || !root->published || !p
      || p->abi!=JAYDB_COMMIT_ABI || p->publish>1 || !p->state || !p->state_bytes
      || !p->response || !p->response_bytes || !nat(scope)
      || !stack || ((uintptr_t)stack&15u) || bytes<JAYDB_COMMIT_STACK_BYTES
      || bytes>UINTPTR_MAX-(uintptr_t)stack) return r->status;
  if(limited && (limited->abi!=JAYDB_COMMIT_ABI || limited->publish
      || limited->state!=root->published->state
      || limited->state_bytes!=root->published->state_bytes
      || !limited->response || !limited->response_bytes)) return r->status;
  struct context c={root,p,limited,r,scope,ceiling,deadline,instrument_deadline};
  /* Linux rt_sigprocmask uses an 8-byte kernel set on this target. Blocking
   * handlers is done before the final barrier; pending handlers run only
   * after hold_end and restoration, when completed already has its value. */
  uint64_t all=UINT64_MAX, previous=0;
  long e=raw4(14,0,(long)&all,(long)&previous,8); /* SIG_BLOCK */
  r->status=JAYDB_COMMIT_INSTRUMENT;
  if(e<0) { r->instrument_error=(uint64_t)-e; return r->status; }
  jaydb_commit_on_stack(critical,&c,(char *)stack+bytes);
  e=raw4(14,2,(long)&previous,0,8); /* SIG_SETMASK */
  if(e<0) r->release_error=(uint64_t)-e;
  return r->status;
}

uint64_t jaydb_commit_finish(struct jaydb_root *root, const struct jaydb_prepared *p,
    struct jayacct_u128 scope, struct jayacct_u128 ceiling,
    struct jayacct_u128 deadline, void *stack, uint64_t bytes,
    struct jaydb_commit_result *r) {
  return finish(root,p,NULL,scope,ceiling,deadline,deadline,stack,bytes,r);
}

uint64_t jaydb_commit_resolve(struct jaydb_root *root, const struct jaydb_prepared *p,
    const struct jaydb_prepared *limited,
    struct jayacct_u128 scope, struct jayacct_u128 ceiling,
    struct jayacct_u128 decision_deadline, struct jayacct_u128 instrument_deadline,
    void *stack, uint64_t bytes, struct jaydb_commit_result *r) {
  if(!limited) {
    if(r) { clear(r,sizeof *r); r->status=JAYDB_COMMIT_ARGUMENT; }
    return JAYDB_COMMIT_ARGUMENT;
  }
  return finish(root,p,limited,scope,ceiling,decision_deadline,instrument_deadline,stack,bytes,r);
}
