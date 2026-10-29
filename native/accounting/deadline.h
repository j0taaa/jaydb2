#ifndef JAYDB_ACCOUNTING_DEADLINE_H
#define JAYDB_ACCOUNTING_DEADLINE_H
#include "window.h"
#include <errno.h>
#define JAYACCT_UNTIL_FLAG UINT64_C(0x100)
#define JAYACCT_RELEASE_OPERATION 6u
/* Absolute CLOCK_MONOTONIC, same u128 clock domain as snapshots. No memory
 * budget is installed. now >= deadline expires (distinct from memory's strict
 * bytes > ceiling). ETIMEDOUT invalidates this marker's output; the host
 * must check its own clock before producing any public time-limit fact.
 * A timeout before window_close leaves the active window unchanged. */
int jayacct_barrier_until(struct jayacct_snapshot*,struct jayacct_u128);
int jayacct_hold_begin_until(struct jayacct_snapshot*,struct jayacct_u128);
int jayacct_hold_end_until(struct jayacct_snapshot*,struct jayacct_u128);
int jayacct_window_begin_until(struct jayacct_window_snapshot*,struct jayacct_u128);
int jayacct_window_end_until(struct jayacct_window_snapshot*,struct jayacct_u128);
int jayacct_window_barrier_until(struct jayacct_window_snapshot*,struct jayacct_u128);
/* Release an owned hold without scanning or claiming a fresh measurement.
 * For cleanup after timeout, and after the host has committed its root store. */
int jayacct_hold_release(void);

#if defined(__linux__) && defined(__x86_64__)
/* Leaf raw protocol for audited critical callers. dst points to 120/280
 * bytes, or an 8-byte receipt for RELEASE. Its backing must already be active.
 * op is 0..5, optionally ORed with UNTIL_FLAG, or RELEASE. No libc, allocator,
 * errno store, loop, or timestamp restamping. The assembly clobbers memory.
 * Nonnegative syscall result + ABI/receipt means success. Negative kernel
 * errno is returned as positive errno. Output is unusable on any error. */
static inline int jayacct_raw_marker(void *dst,uint64_t op,struct jayacct_u128 until) {
  *(uint64_t*)dst=0;
  register uint64_t a4 __asm__("r10")=until.lo;
  register uint64_t a5 __asm__("r8")=until.hi;
  register uint64_t a6 __asm__("r9")=0;
  register long result __asm__("rax")=39; /* __NR_getpid, x86_64 */
  __asm__ volatile("syscall":"+a"(result):"D"(JAYACCT_MARKER),"S"(dst),"d"(op),
                   "r"(a4),"r"(a5),"r"(a6):"rcx","r11","cc","memory");
  uint64_t base=op&~JAYACCT_UNTIL_FLAG;
  uint64_t expected=base==JAYACCT_RELEASE_OPERATION?JAYACCT_MARKER:
                    base>=3&&base<=5?JAYACCT_WINDOW_ABI:JAYACCT_ABI;
  int error=result<0&&result>=-4095?(int)-result:
            *(uint64_t*)dst!=expected?ENOTSUP:
            base>=3&&base<=5?(int)((struct jayacct_window_snapshot*)dst)->error:0;
  /* Receipt/error validation can itself materialize the marker constant.
   * Clear RDI last: a following ordinary getpid has no argument to replace
   * it. The return-value dependency orders validation before this cleanup;
   * the clobber also forces a later inlined marker to reload its token.
   * RDI is caller-saved. This does not promise anything about a caller's own
   * later register use, nor about a separate, private raw-syscall wrapper. */
  __asm__ volatile("xor %%edi,%%edi":"+a"(error)::"rdi","cc","memory");
  return error;
}
#endif
#endif
