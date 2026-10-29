#ifndef JAYDB_NATIVE_ABI_V3_H
#define JAYDB_NATIVE_ABI_V3_H
#include "abi.h"

#define JAYDB_NATIVE_ABI_OWNED 3u

/* Unsigned 128-bit ns encoded as two words, without compiler-specific ABI.
 * CLOCK_MONOTONIC with a nonnegative <=64-bit signed time_t has <2^93 ns.
 * Host may encode min(public_Nat, 2^128-1): every valid observed elapsed time
 * is strictly smaller, so this never invents an earlier timeout. No deadline
 * addition/saturation is used. Zero duration is invalid. */
struct jaydb_native_ns128 { uint64_t lo, hi; };

struct jaydb_native_request_v3 {
  uint32_t abi_version; /* exactly 3 */
  uint32_t flags; /* exactly CPU1_GPU_OFF */
  const uint8_t *input;
  uint64_t input_len;
  uint64_t output_limit; /* logical byte ceiling; never preallocated/charged */
  uint64_t memory_bytes; /* ceiling on actual charged allocation capacities */
  uint64_t term_stack_bytes;
  uint64_t native_stack_bytes;
  struct jaydb_native_ns128 setup_timeout_ns;
  struct jaydb_native_ns128 execution_timeout_ns;
  struct jaydb_native_ns128 preparation_timeout_ns;
};

struct jaydb_native_result_v3 {
  uint32_t status;
  uint32_t runtime_code;
  uint32_t stage;
  uint32_t reserved;
  const uint8_t *output; /* only byte storage; NULL for empty output/failure */
  uint64_t output_len; /* zero on failure */
  uint64_t output_capacity; /* actual mapped capacity, zero for empty output */
  uint64_t lease; /* nonzero on every success, including empty output */
  uint64_t charged_bytes; /* peak of actual charged capacities during run */
  struct jaydb_native_ns128 elapsed_ns;
  struct jaydb_native_ns128 stage_elapsed_ns[3];
  struct jaydb_native_ns128 preparation_started_ns; /* absolute epoch or zero */
};

/* Additional interface. V1/V2, effects and their layouts remain unchanged.
 * One synchronous CPU1 worker, same process, no callbacks or Term/DB pointers.
 * A successful run retains its byte storage and occupies this DSO until release.
 * Copy exactly output_len bytes before releasing the current lease ONCE. Keep
 * the DSO loaded through release. Do not retain/reuse expired lease values.
 * Failure retains no storage and requires no release. Input is borrowed until
 * run returns. It need not remain valid while a successful output lease lives.
 * Host may clip memory/output Nat ceilings to UINT64_MAX: no addressable byte
 * extent on this target is larger. This does not allocate those ceiling bytes.
 */
const struct jaydb_native_descriptor *jaydb_native_describe_v3(void);
uint32_t jaydb_native_run_v3(const struct jaydb_native_request_v3 *, struct jaydb_native_result_v3 *);
uint32_t jaydb_native_release_v3(uint64_t lease);
#endif
