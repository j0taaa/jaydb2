#ifndef JAYDB_NATIVE_SIMPLE_H
#define JAYDB_NATIVE_SIMPLE_H
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <setjmp.h>
#include <stdatomic.h>
#include <errno.h>

#define JAYDB_NATIVE_ABI_SIMPLE 6u
#define JAYDB_CPU1_GPU_OFF 1u
enum jaydb_simple_status {
  JAYDB_OK=0, JAYDB_ARGUMENT=1, JAYDB_BUSY=2, JAYDB_SYSTEM=5,
  JAYDB_EFFECT=6, JAYDB_OUTPUT=7, JAYDB_NAT_REPRESENTATION=8,
  JAYDB_ARRAY_REPRESENTATION=9, JAYDB_REFCOUNT_REPRESENTATION=10,
  JAYDB_RUNTIME=11, JAYDB_INVARIANT=12, JAYDB_CAPTURED_STEP=13
};
enum jaydb_simple_stage { JAYDB_SETUP=0, JAYDB_EXECUTION=1, JAYDB_PREPARATION=2 };

struct jaydb_simple_request {
  uint32_t abi_version, size;
  const uint8_t *input;
  uint64_t input_len, output_capacity;
};
struct jaydb_simple_result {
  uint32_t status, runtime_code, stage, reserved;
  const uint8_t *output;
  uint64_t output_len, output_capacity, lease;
};
struct jaydb_simple_descriptor {
  uint32_t abi_version, size, request_bytes, result_bytes;
  uint32_t flags, term_bytes;
  char source_sha256[64], build_identity_sha256[64];
};
_Static_assert(sizeof(struct jaydb_simple_request)==32, "ABI6 request");
_Static_assert(sizeof(struct jaydb_simple_result)==48, "ABI6 result");
_Static_assert(offsetof(struct jaydb_simple_result, output)==16, "output prefix");
_Static_assert(offsetof(struct jaydb_simple_result, lease)==40, "lease prefix");
_Static_assert(sizeof(struct jaydb_simple_descriptor)==152, "ABI6 descriptor");

/* One synchronous evaluator in the caller's process and thread. The host
 * establishes the Linux main grow-down stack profile before calling. */
static jmp_buf jaydb_escape;
static uint32_t jaydb_status, jaydb_runtime_code, jaydb_stage;
static bool jaydb_cleanup_failed;
static _Noreturn void jaydb_abort(uint32_t status, uint32_t code) {
  jaydb_status=status; jaydb_runtime_code=code; longjmp(jaydb_escape, 1);
}
static void jaydb_enter_stage(uint32_t stage) {
  if (stage > JAYDB_PREPARATION || stage <= jaydb_stage)
    jaydb_abort(JAYDB_INVARIANT, 0);
  jaydb_stage=stage;
}
static void jaydb_unmap(void *pointer, uint64_t bytes);
static void jaydb_resize(void *owner, uint64_t *capacity, uint64_t bytes);

const struct jaydb_simple_descriptor *jaydb_native_describe_v6(void);
uint32_t jaydb_native_run_v6(const struct jaydb_simple_request *, struct jaydb_simple_result *);
uint32_t jaydb_native_release_v6(uint64_t lease);
#endif
