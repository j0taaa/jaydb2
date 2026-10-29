#ifndef JAYDB_NATIVE_ABI_H
#define JAYDB_NATIVE_ABI_H
#include <stdint.h>
#include <stddef.h>

#define JAYDB_NATIVE_ABI 1u
#define JAYDB_NATIVE_ABI_STAGES 2u
#define JAYDB_CPU1_GPU_OFF 1u
enum jaydb_native_status {
  JAYDB_OK = 0, JAYDB_ARGUMENT = 1, JAYDB_BUSY = 2,
  JAYDB_TIME = 3, JAYDB_MEMORY = 4, JAYDB_SYSTEM = 5,
  JAYDB_EFFECT = 6, JAYDB_OUTPUT = 7,
  JAYDB_NAT_REPRESENTATION = 8, JAYDB_ARRAY_REPRESENTATION = 9,
  JAYDB_REFCOUNT_REPRESENTATION = 10, JAYDB_RUNTIME = 11,
  JAYDB_INVARIANT = 12, JAYDB_CAPTURED_STEP = 13
};

enum jaydb_native_stage { JAYDB_SETUP = 0, JAYDB_EXECUTION = 1, JAYDB_PREPARATION = 2 };

struct jaydb_native_request {
  uint32_t abi_version;
  uint32_t flags; /* exactly CPU1_GPU_OFF; environment/argv are never read */
  const uint8_t *input;
  uint64_t input_len;
  uint8_t *output; /* staging storage, never the published database */
  uint64_t output_capacity;
  uint64_t memory_bytes; /* charged image + mappings + input/output; see README */
  uint64_t timeout_ns; /* monotonic wall time, starts before pthread creation */
  uint64_t term_stack_bytes;
  uint64_t native_stack_bytes;
};

struct jaydb_native_result {
  uint32_t status;
  uint32_t runtime_code; /* official ERR_* number when applicable */
  uint64_t output_len; /* zero unless OK; ignore output buffer on any failure */
  uint64_t elapsed_ns;
  uint64_t charged_bytes;
};

/* ABI v1 remains binary compatible. ABI v2 adds budgets fixed by the host.
 * base.timeout_ns covers setup until enter(EXECUTION) or Native.loop.
 * Stage transitions are monotonic and allowed once; no client can extend them.
 */
struct jaydb_native_request_v2 {
  struct jaydb_native_request base; /* base.abi_version = 2 */
  uint64_t execution_timeout_ns;
  uint64_t preparation_timeout_ns;
};
struct jaydb_native_result_v2 {
  struct jaydb_native_result base;
  uint32_t stage;
  uint32_t reserved;
  uint64_t setup_ns;
  uint64_t execution_ns;
  uint64_t preparation_ns;
};

struct jaydb_native_descriptor {
  uint32_t abi_version;
  uint32_t flags;
  uint32_t generic_nat_array;
  uint32_t immortal_refcounts;
  uint64_t image_bytes;
  uint64_t maximum_c_frame_bytes;
  const char *generated_c_sha256;
};

/* One active call per loaded module. Distinct modules have separate state.
 * Run is synchronous, on ONE CPU worker in the SAME process. No Term escapes.
 * Host must keep the module loaded until run returns, including failed calls.
 * Buffer extents must be valid, disjoint, and stable throughout the call.
 * No database pointers/callbacks are accepted. Publish only after status OK.
 */
const struct jaydb_native_descriptor *jaydb_native_describe_v1(void);
uint32_t jaydb_native_run_v1(const struct jaydb_native_request *, struct jaydb_native_result *);
const struct jaydb_native_descriptor *jaydb_native_describe_v2(void);
uint32_t jaydb_native_run_v2(const struct jaydb_native_request_v2 *, struct jaydb_native_result_v2 *);
/* Absolute CLOCK_MONOTONIC ns at enter(2) in the last accepted run. Zero if
 * that run was V1 or never entered preparation. Read after run, before dlclose;
 * serialized use per DSO. ARGUMENT/BUSY rejections leave the prior run intact.
 * Struct layouts and the V1/V2 call signatures remain unchanged.
 */
uint64_t jaydb_native_preparation_started_v2(void);
#endif
