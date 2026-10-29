#ifndef JAYDB_NATIVE_ACCOUNTED_H
#define JAYDB_NATIVE_ACCOUNTED_H
#include "abi_deadline.h"
#include "field_recipe.h"
#include <stddef.h>
#define JAYDB_ACCOUNTED_ABI 1u
#define JAYDB_FIELD_REFUSAL_CODE 0x4649454cu
#define JAYDB_ACCOUNTED_STAGE_OBSERVED 1u
#define JAYDB_ACCOUNTED_RETURN_OBSERVED 2u
#define JAYDB_ACCOUNTED_ARTIFACT_FIXTURE 1u
/* Additional PRIVATE host ABI. No layout of V1/V2/V3 changes. A live ACTIVE
 * service scope and original setup epoch are supplied by the host, never Bend.
 * Nonzero execution/preparation epochs are original host epochs. Zero binds
 * that stage once at its native transition using the V3 duration; never per decode.
 * Local memory bookkeeping is diagnostic; it cannot refuse this mode. */
struct jaydb_native_accounted {
  uint64_t abi;
  struct jayacct_u128 scope,ceiling,deadline_ns[3]; /* SETUP, EXECUTION, PREPARATION */
};
struct jaydb_native_accounted_result {
  struct jaydb_native_result_v3 native;
  uint64_t decoder_calls,decoder_completed,field_calls,field_completed;
  uint64_t decode_id,constructor_id,site_id,logical_claims;
  struct jaydb_field_result field;
  /* Final/interrupted native stage. Bit 0: stage start observed; bit 1:
   * returned_ns observed. These epochs survive failure and cleanup. The
   * decision deadline is the ORIGINAL bound, including an already past epoch;
   * it is never reconstructed from elapsed time or renewed on FFI return. */
  uint64_t timing_flags;
  struct jaydb_native_ns128 stage_started_ns,decision_deadline_ns,returned_ns;
};
struct jaydb_native_accounted_descriptor {
  uint64_t abi,host_bytes,result_bytes,lowering_version,recipe_version,term_bytes,artifact_flags;
  const char *generated_c_sha256;
};
/* Frozen private ABI 1, Linux x86_64. Extend through a new ABI, never by
 * changing these layouts or the legacy V1/V2/V3 prefixes. */
_Static_assert(sizeof(struct jaydb_native_accounted)==88,"accounted host ABI 1");
_Static_assert(sizeof(struct jaydb_native_accounted_result)==656,"accounted result ABI 1");
_Static_assert(sizeof(struct jaydb_native_accounted_descriptor)==64,"accounted descriptor ABI 1");
_Static_assert(offsetof(struct jaydb_native_accounted_result,field)==200,"field receipt ABI 1");
_Static_assert(offsetof(struct jaydb_native_accounted_result,decision_deadline_ns)==624,"epoch ABI 1");
const struct jaydb_native_accounted_descriptor *jaydb_native_describe_accounted_v3(void);
uint32_t jaydb_native_run_accounted_v3(const struct jaydb_native_request_v3 *,
  const struct jaydb_native_accounted *,struct jaydb_native_accounted_result *);

/* Independent optional progress ABI 1. Does NOT extend frozen host/result.
 * Metadata prefixes, never AlocouCampo/MedicaoReal by themselves. Last accepted
 * accounted call, retained until the next; read only after synchronous return.
 * sampled_ns is the last real runtime poll, not an invented UTF8 timestamp. */
enum jaydb_decode_phase {
  JAYDB_DECODE_IDLE=0,JAYDB_DECODE_COUNT=1,JAYDB_DECODE_COPY=2,
  JAYDB_DECODE_PARSE=3,JAYDB_DECODE_UTF8=4,JAYDB_DECODE_FIELD=5,
  JAYDB_DECODE_DONE=6,JAYDB_DECODE_REJECTED=7
};
struct jaydb_native_accounted_progress {
  uint64_t abi,phase,decode_id,stage,wire_size,wire_copied,cursor;
  uint64_t scalar_start,utf8_consumed,utf8_value,utf8_needed;
  struct jaydb_native_ns128 sampled_ns;
};
_Static_assert(sizeof(struct jaydb_native_accounted_progress)==104,"progress ABI 1");
uint32_t jaydb_native_progress_accounted_v1(struct jaydb_native_accounted_progress *);
#endif
