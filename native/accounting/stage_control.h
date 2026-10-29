#ifndef JAYDB_ACCOUNTING_STAGE_CONTROL_H
#define JAYDB_ACCOUNTING_STAGE_CONTROL_H
#include "counter.h"
#include <errno.h>
#include <stdatomic.h>
/* Additive protocol, opt-in --stage-control. No change to counter/window ABI.
 * All instants are absolute CLOCK_MONOTONIC u128, never rounded budgets.
 * observed_ns is valid only after a real expiry (cancellations != 0).
 * A receipt is control state; it is not a memory observation or MedicaoReal. */
#define JAYSTAGE_ABI 1u
#define JAYSTAGE_SHARED_BYTES 4096u
#define JAYSTAGE_MARKER UINT64_C(0x4a41595354414731)
#define JAYSTAGE_ARM 1u
#define JAYSTAGE_RETIRE 2u
#define JAYSTAGE_IDLE 0u
#define JAYSTAGE_ARMED 1u
#define JAYSTAGE_EXPIRED_PENDING_RECOVERY 2u
#define JAYSTAGE_EXPIRED_RECOVERED 3u
#define JAYSTAGE_RETIRED 4u
#define JAYSTAGE_PENDING_INFLIGHT 1u
#define JAYSTAGE_PENDING_VFORK 2u
#define JAYSTAGE_PENDING_METADATA 4u
#define JAYSTAGE_PENDING_HOLD 8u
#define JAYSTAGE_PENDING_SCAN 16u
#define JAYSTAGE_PENDING_STOP 32u
struct jaystage_request {
  uint64_t abi, stage;
  struct jayacct_u128 scope_id, generation, start_ns, deadline_ns;
};
struct jaystage_receipt {
  uint64_t abi, error, state, stage;
  struct jayacct_u128 scope_id, generation, start_ns, deadline_ns, observed_ns;
  struct jayacct_u128 arm_sequence, recovery_sequence;
  uint64_t owner_pid, owner_mm, pending_flags, cancellations;
};
#define JAYSTAGE_RECEIPT_WORDS 22u
struct jaystage_shared {
  _Atomic uint64_t sequence;
  _Atomic uint64_t receipt[JAYSTAGE_RECEIPT_WORDS];
};
_Static_assert(sizeof(struct jaystage_request)==80,"stage request ABI1");
_Static_assert(sizeof(struct jaystage_receipt)==176,"stage receipt ABI1");
_Static_assert(sizeof(struct jaystage_shared)==184,"stage shared ABI1");
_Static_assert(ATOMIC_LONG_LOCK_FREE==2,"stage uint64 atomics must be lock free");
int jaystage_arm(const struct jaystage_request*,struct jaystage_receipt*);
int jaystage_retire(const struct jaystage_request*,struct jaystage_receipt*);
int jaystage_read(const void*,struct jaystage_receipt*);
int jaystage_map(int,const void**);
int jaystage_unmap(const void*);
#if defined(__linux__) && defined(__x86_64__)
static inline int jaystage_raw_call(const struct jaystage_request *request,
    struct jaystage_receipt *out,uint64_t operation) {
  if(!request||!out) {
    int error=EINVAL;
    __asm__ volatile("xor %%edi,%%edi":"+a"(error)::"rdi","cc","memory");
    return error;
  }
  out->abi=0;
  register uint64_t a4 __asm__("r10")=(uintptr_t)request;
  register uint64_t a5 __asm__("r8")=0;
  register uint64_t a6 __asm__("r9")=0;
  register long result __asm__("rax")=39;
  __asm__ volatile("syscall":"+a"(result):"D"(JAYSTAGE_MARKER),"S"(out),"d"(operation),
                   "r"(a4),"r"(a5),"r"(a6):"rcx","r11","cc","memory");
  int error=result<0&&result>=-4095?(int)-result:
            out->abi!=JAYSTAGE_ABI?ENOTSUP:(int)out->error;
  /* Validation can materialize a constant. Clear the caller-saved token last,
   * including error/outside-observer paths and effective inlined code. */
  __asm__ volatile("xor %%edi,%%edi":"+a"(error)::"rdi","cc","memory");
  return error;
}
#endif
#endif
