#define _GNU_SOURCE
#include "counter.h"
#include "window.h"
#include "deadline.h"
#include <errno.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <string.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

struct shared_counter {
  uint64_t magic;
  pthread_mutex_t mutex;
  _Atomic uint64_t epoch, seq_lo, seq_hi;
  _Atomic uint64_t current_lo, current_hi, peak_lo, peak_hi, ns_lo, ns_hi, flags;
  _Atomic uint64_t peak_ns_lo, peak_ns_hi, peak_seq_lo, peak_seq_hi, peak_flags;
  _Atomic uint64_t window_state, window_id_lo, window_id_hi;
  _Atomic uint64_t window_begin_seq_lo, window_begin_seq_hi, window_begin_ns_lo, window_begin_ns_hi;
  _Atomic uint64_t window_end_seq_lo, window_end_seq_hi, window_end_ns_lo, window_end_ns_hi;
  _Atomic uint64_t window_peak_lo, window_peak_hi, window_peak_ns_lo, window_peak_ns_hi;
  _Atomic uint64_t window_peak_seq_lo, window_peak_seq_hi, window_peak_flags;
};
_Static_assert(sizeof(struct shared_counter) <= JAYACCT_SHARED_BYTES, "counter page");
_Static_assert(ATOMIC_LLONG_LOCK_FREE == 2, "shared counter requires lock-free words");
_Static_assert(sizeof(time_t) <= sizeof(int64_t) && (time_t)-1 < 0, "wide monotonic clock domain");
static __uint128_t wide(struct jayacct_u128 n) { return ((__uint128_t)n.hi << 64) | n.lo; }
static struct jayacct_u128 words(__uint128_t n) { return (struct jayacct_u128){n, n >> 64}; }
size_t jayacct_shared_size(void) { return JAYACCT_SHARED_BYTES; }
int jayacct_init(void *memory, size_t size) {
  if (!memory || size < JAYACCT_SHARED_BYTES) return EINVAL;
  struct shared_counter *s = memory;
  memset(s, 0, sizeof *s);
  pthread_mutexattr_t attr;
  int r = pthread_mutexattr_init(&attr);
  if (r) return r;
  if (!(r = pthread_mutexattr_setpshared(&attr, PTHREAD_PROCESS_SHARED)) &&
      !(r = pthread_mutexattr_setrobust(&attr, PTHREAD_MUTEX_ROBUST)))
    r = pthread_mutex_init(&s->mutex, &attr);
  pthread_mutexattr_destroy(&attr);
  if (r) return r;
  s->magic = JAYACCT_MARKER;
  atomic_store(&s->flags, JAYACCT_INCOMPLETE);
  return 0;
}
static int lock(struct shared_counter *s) {
  if (!s || s->magic != JAYACCT_MARKER) return EINVAL;
  int r = pthread_mutex_lock(&s->mutex);
  if (r == EOWNERDEAD) {
    atomic_fetch_or(&s->flags, JAYACCT_OWNER_DIED | JAYACCT_INCOMPLETE);
    pthread_mutex_consistent(&s->mutex);
    pthread_mutex_unlock(&s->mutex);
  }
  if (!r && (atomic_load(&s->flags) & JAYACCT_OWNER_DIED)) {
    pthread_mutex_unlock(&s->mutex); return EOWNERDEAD;
  }
  return r;
}
static int store(struct shared_counter *s, __uint128_t current,
                 const struct jayacct_u128 *observed, uint64_t flags, struct jayacct_snapshot *out) {
  struct timespec ts;
  if (clock_gettime(CLOCK_MONOTONIC, &ts) || ts.tv_sec < 0 || ts.tv_nsec < 0
      || ts.tv_nsec >= 1000000000L) return EIO;
  /* Same wide monotonic clock domain as V3; no u64 deadline clipping. */
  __uint128_t ns = (__uint128_t)ts.tv_sec * 1000000000u + ts.tv_nsec;
  if (observed) {
    if (wide(*observed) > ns) return EINVAL;
    ns = wide(*observed);
  }
  __uint128_t previous_ns = ((__uint128_t)atomic_load(&s->ns_hi) << 64) | atomic_load(&s->ns_lo);
  if (ns < previous_ns) return EIO;
  __uint128_t seq = ((__uint128_t)atomic_load(&s->seq_hi) << 64) | atomic_load(&s->seq_lo);
  if (seq == ~(__uint128_t)0) return EOVERFLOW;
  ++seq;
  __uint128_t peak = ((__uint128_t)atomic_load(&s->peak_hi) << 64) | atomic_load(&s->peak_lo);
  struct jayacct_u128 peak_ns = {atomic_load(&s->peak_ns_lo), atomic_load(&s->peak_ns_hi)};
  struct jayacct_u128 peak_seq = {atomic_load(&s->peak_seq_lo), atomic_load(&s->peak_seq_hi)};
  uint64_t peak_flags = atomic_load(&s->peak_flags);
  if (current > peak || seq == 1) {
    peak = current; peak_ns = words(ns); peak_seq = words(seq); peak_flags = flags;
  }
  uint64_t epoch = atomic_load(&s->epoch);
  atomic_store(&s->epoch, epoch + 1);
  atomic_store(&s->seq_lo, (uint64_t)seq);
  atomic_store(&s->seq_hi, (uint64_t)(seq >> 64));
  atomic_store(&s->current_lo, (uint64_t)current);
  atomic_store(&s->current_hi, (uint64_t)(current >> 64));
  atomic_store(&s->peak_lo, (uint64_t)peak);
  atomic_store(&s->peak_hi, (uint64_t)(peak >> 64));
  atomic_store(&s->ns_lo, (uint64_t)ns);
  atomic_store(&s->ns_hi, (uint64_t)(ns >> 64));
  atomic_store(&s->peak_ns_lo, peak_ns.lo);
  atomic_store(&s->peak_ns_hi, peak_ns.hi);
  atomic_store(&s->peak_seq_lo, peak_seq.lo);
  atomic_store(&s->peak_seq_hi, peak_seq.hi);
  atomic_store(&s->peak_flags, peak_flags);
  atomic_store(&s->flags, flags);
  if (atomic_load(&s->window_state) == JAYACCT_WINDOW_ACTIVE) {
    __uint128_t scoped = ((__uint128_t)atomic_load(&s->window_peak_hi) << 64) | atomic_load(&s->window_peak_lo);
    if (current > scoped) {
      atomic_store(&s->window_peak_lo, (uint64_t)current);
      atomic_store(&s->window_peak_hi, (uint64_t)(current >> 64));
      atomic_store(&s->window_peak_ns_lo, (uint64_t)ns);
      atomic_store(&s->window_peak_ns_hi, (uint64_t)(ns >> 64));
      atomic_store(&s->window_peak_seq_lo, (uint64_t)seq);
      atomic_store(&s->window_peak_seq_hi, (uint64_t)(seq >> 64));
      atomic_store(&s->window_peak_flags, flags);
    }
  }
  atomic_store(&s->epoch, epoch + 2);
  if (out) *out = (struct jayacct_snapshot){JAYACCT_ABI, words(seq),
      words(current), words(peak), words(ns), peak_ns, peak_seq, peak_flags, flags};
  return 0;
}
int jayacct_begin(void *memory, struct jayacct_transaction *tx) {
  if (!tx) return EINVAL;
  int r = lock(memory); if (r) return r;
  *tx = (struct jayacct_transaction){memory, (uint64_t)getpid(), (uint64_t)syscall(SYS_gettid)};
  return 0;
}
static bool owned(const struct jayacct_transaction *tx) {
  return tx && tx->shared && tx->pid == (uint64_t)getpid()
      && tx->tid == (uint64_t)syscall(SYS_gettid);
}
int jayacct_cancel(struct jayacct_transaction *tx) {
  if (!owned(tx)) return EPERM;
  struct shared_counter *s = tx->shared;
  tx->shared = NULL;
  return pthread_mutex_unlock(&s->mutex);
}
int jayacct_commit(struct jayacct_transaction *tx, struct jayacct_u128 released,
                   struct jayacct_u128 acquired, struct jayacct_snapshot *out) {
  if (!owned(tx)) return EPERM;
  struct shared_counter *s = tx->shared;
  int r = 0;
  __uint128_t current = ((__uint128_t)atomic_load(&s->current_hi) << 64) | atomic_load(&s->current_lo);
  if (wide(released) > current || ~(__uint128_t)0 - (current - wide(released)) < wide(acquired)) r = ERANGE;
  else {
    current = current - wide(released) + wide(acquired);
    r = store(s, current, NULL, atomic_load(&s->flags), out);
  }
  jayacct_cancel(tx);
  return r;
}
int jayacct_change(void *memory, struct jayacct_u128 released,
                   struct jayacct_u128 acquired, struct jayacct_snapshot *out) {
  struct jayacct_transaction tx;
  int r = jayacct_begin(memory, &tx);
  return r ? r : jayacct_commit(&tx, released, acquired, out);
}
int jayacct_publish(void *memory, struct jayacct_u128 current, uint64_t flags,
                    struct jayacct_snapshot *out) {
  struct shared_counter *s = memory;
  int r = lock(s); if (r) return r;
  /* Coverage cannot silently improve in the lifetime of this ABI. */
  flags |= atomic_load(&s->flags) & (JAYACCT_INCOMPLETE | JAYACCT_OWNER_DIED);
  r = store(s, wide(current), NULL, flags, out);
  pthread_mutex_unlock(&s->mutex);
  return r;
}
int jayacct_publish_observation(void *memory, struct jayacct_u128 current,
                    struct jayacct_u128 observed_ns, uint64_t flags,
                    struct jayacct_snapshot *out) {
  struct shared_counter *s = memory;
  int r = lock(s); if (r) return r;
  flags |= atomic_load(&s->flags) & (JAYACCT_INCOMPLETE | JAYACCT_OWNER_DIED);
  r = store(s, wide(current), &observed_ns, flags, out);
  pthread_mutex_unlock(&s->mutex);
  return r;
}
int jayacct_read(const void *memory, struct jayacct_snapshot *out) {
  const struct shared_counter *s = memory;
  if (!s || !out || s->magic != JAYACCT_MARKER) return EINVAL;
  if (atomic_load(&s->flags) & JAYACCT_OWNER_DIED) return EOWNERDEAD;
  /* A dead writer must never turn an odd epoch into an infinite reader loop.
   * EAGAIN means retry at a caller-controlled deadline, not a fake measure. */
  uint64_t before = atomic_load(&s->epoch);
  if (before & 1) return EAGAIN;
  struct jayacct_u128 sequence = {atomic_load(&s->seq_lo), atomic_load(&s->seq_hi)};
  *out = (struct jayacct_snapshot){JAYACCT_ABI, sequence,
    {atomic_load(&s->current_lo), atomic_load(&s->current_hi)},
    {atomic_load(&s->peak_lo), atomic_load(&s->peak_hi)},
    {atomic_load(&s->ns_lo), atomic_load(&s->ns_hi)},
    {atomic_load(&s->peak_ns_lo), atomic_load(&s->peak_ns_hi)},
    {atomic_load(&s->peak_seq_lo), atomic_load(&s->peak_seq_hi)},
    atomic_load(&s->peak_flags), atomic_load(&s->flags)};
  if (sequence.lo != atomic_load(&s->seq_lo) || sequence.hi != atomic_load(&s->seq_hi)
      || before != atomic_load(&s->epoch)) return EAGAIN;
  if (out->flags & JAYACCT_OWNER_DIED) return EOWNERDEAD;
  return 0;
}
int jayacct_window_read(const void *memory, struct jayacct_window_snapshot *out) {
  const struct shared_counter *s=memory;
  if(!s||!out||s->magic!=JAYACCT_MARKER)return EINVAL;
  uint64_t epoch=atomic_load(&s->epoch);
  if(epoch&1)return EAGAIN;
  struct jayacct_snapshot global;
  int r=jayacct_read(memory,&global);if(r)return r;
#define PAIR(NAME) {atomic_load(&s->NAME##_lo),atomic_load(&s->NAME##_hi)}
  *out=(struct jayacct_window_snapshot){JAYACCT_WINDOW_ABI,atomic_load(&s->window_state),0,global,
    PAIR(window_id),PAIR(window_begin_seq),PAIR(window_begin_ns),PAIR(window_end_seq),PAIR(window_end_ns),
    PAIR(window_peak),PAIR(window_peak_ns),PAIR(window_peak_seq),atomic_load(&s->window_peak_flags)};
#undef PAIR
  if(epoch!=atomic_load(&s->epoch)||out->scope_id.lo!=atomic_load(&s->window_id_lo)
      ||out->scope_id.hi!=atomic_load(&s->window_id_hi))return EAGAIN;
  return 0;
}
static void pair_store(_Atomic uint64_t *lo,_Atomic uint64_t *hi,struct jayacct_u128 n) {
  atomic_store(lo,n.lo);atomic_store(hi,n.hi);
}
int jayacct_window_open(void *memory, struct jayacct_window_snapshot *out) {
  struct shared_counter*s=memory;
  if(!out)return EINVAL;
  int r=lock(s);if(r)return r;
  struct jayacct_snapshot global;
  r=jayacct_read(s,&global);
  if(!r&&!wide(global.sequence))r=ENODATA;
  if(!r&&atomic_load(&s->window_state)==JAYACCT_WINDOW_ACTIVE)r=EBUSY;
  __uint128_t id=((__uint128_t)atomic_load(&s->window_id_hi)<<64)|atomic_load(&s->window_id_lo);
  if(!r&&id==~(__uint128_t)0)r=EOVERFLOW;
  if(!r) {
    uint64_t epoch=atomic_load(&s->epoch);atomic_store(&s->epoch,epoch+1);
#define SAVE(NAME,VALUE) pair_store(&s->NAME##_lo,&s->NAME##_hi,(VALUE))
    SAVE(window_id,words(id+1));SAVE(window_begin_seq,global.sequence);SAVE(window_begin_ns,global.monotonic_ns);
    SAVE(window_end_seq,words(0));SAVE(window_end_ns,words(0));
    SAVE(window_peak,global.current);SAVE(window_peak_ns,global.monotonic_ns);SAVE(window_peak_seq,global.sequence);
    atomic_store(&s->window_peak_flags,global.flags);atomic_store(&s->window_state,JAYACCT_WINDOW_ACTIVE);
    atomic_store(&s->epoch,epoch+2);
    r=jayacct_window_read(s,out);
  }
  pthread_mutex_unlock(&s->mutex);return r;
}
int jayacct_window_close(void *memory, struct jayacct_window_snapshot *out) {
  struct shared_counter*s=memory;
  if(!out)return EINVAL;
  int r=lock(s);if(r)return r;
  uint64_t state=atomic_load(&s->window_state);
  if(state!=JAYACCT_WINDOW_ACTIVE)r=state==JAYACCT_WINDOW_CLOSED?EALREADY:ENOENT;
  struct jayacct_snapshot global;
  if(!r)r=jayacct_read(s,&global);
  if(!r) {
    uint64_t epoch=atomic_load(&s->epoch);atomic_store(&s->epoch,epoch+1);
    SAVE(window_end_seq,global.sequence);SAVE(window_end_ns,global.monotonic_ns);
    atomic_store(&s->window_state,JAYACCT_WINDOW_CLOSED);atomic_store(&s->epoch,epoch+2);
    r=jayacct_window_read(s,out);
  }
#undef SAVE
  pthread_mutex_unlock(&s->mutex);return r;
}
static int marker(struct jayacct_snapshot *out, unsigned operation) {
#if defined(__linux__) && defined(__x86_64__)
  if (!out) return EINVAL;
  memset(out, 0, sizeof *out);
  long result=syscall(SYS_getpid, JAYACCT_MARKER, out, operation);
  int error=result==-1?errno:
            out->abi==JAYACCT_ABI&&(out->flags&JAYACCT_FROZEN)?0:ENOTSUP;
  /* Finish validation before removing the protocol token from caller-saved
   * RDI, including errno and unsupported-receipt paths. */
  __asm__ volatile("xor %%edi,%%edi":"+a"(error)::"rdi","cc","memory");
  return error;
#else
  (void)out; (void)operation; return ENOTSUP;
#endif
}
int jayacct_barrier(struct jayacct_snapshot *out) { return marker(out, 0); }
int jayacct_hold_begin(struct jayacct_snapshot *out) { return marker(out, 1); }
int jayacct_hold_end(struct jayacct_snapshot *out) { return marker(out, 2); }
static int window_marker(struct jayacct_window_snapshot *out,unsigned operation) {
#if defined(__linux__) && defined(__x86_64__)
  if(!out)return EINVAL;
  memset(out,0,sizeof *out);
  long result=syscall(SYS_getpid,JAYACCT_MARKER,out,operation);
  int error=result==-1?errno:out->abi!=JAYACCT_WINDOW_ABI?ENOTSUP:(int)out->error;
  __asm__ volatile("xor %%edi,%%edi":"+a"(error)::"rdi","cc","memory");
  return error;
#else
  (void)out;(void)operation;return ENOTSUP;
#endif
}
int jayacct_window_begin(struct jayacct_window_snapshot *out){return window_marker(out,3);}
int jayacct_window_end(struct jayacct_window_snapshot *out){return window_marker(out,4);}
int jayacct_window_barrier(struct jayacct_window_snapshot *out){return window_marker(out,5);}
int jayacct_barrier_until(struct jayacct_snapshot*out,struct jayacct_u128 t) {
  return out?jayacct_raw_marker(out,JAYACCT_UNTIL_FLAG,t):EINVAL;
}
int jayacct_hold_begin_until(struct jayacct_snapshot*out,struct jayacct_u128 t) {
  return out?jayacct_raw_marker(out,JAYACCT_UNTIL_FLAG|1,t):EINVAL;
}
int jayacct_hold_end_until(struct jayacct_snapshot*out,struct jayacct_u128 t) {
  return out?jayacct_raw_marker(out,JAYACCT_UNTIL_FLAG|2,t):EINVAL;
}
int jayacct_window_begin_until(struct jayacct_window_snapshot*out,struct jayacct_u128 t) {
  return out?jayacct_raw_marker(out,JAYACCT_UNTIL_FLAG|3,t):EINVAL;
}
int jayacct_window_end_until(struct jayacct_window_snapshot*out,struct jayacct_u128 t) {
  return out?jayacct_raw_marker(out,JAYACCT_UNTIL_FLAG|4,t):EINVAL;
}
int jayacct_window_barrier_until(struct jayacct_window_snapshot*out,struct jayacct_u128 t) {
  return out?jayacct_raw_marker(out,JAYACCT_UNTIL_FLAG|5,t):EINVAL;
}
int jayacct_hold_release(void) {
  uint64_t receipt;return jayacct_raw_marker(&receipt,JAYACCT_RELEASE_OPERATION,(struct jayacct_u128){0,0});
}
