/* Explicit consumer fixture. Epochs/status are injected; malloc/free and
 * destructor effects are real. This is not Bend or MedicaoReal evidence. */
#define jaydb_native_run_accounted_v3 completion_v4_fixture_accounted
#include "lifecycle_consumer_fixture.c"
#undef jaydb_native_run_accounted_v3
static struct jaydb_native_ns128 decision_epoch;
static uint64_t timing = 3;
static uint32_t decision_stage = 2;
void completion_v5_epoch(uint64_t lo, uint64_t hi, uint32_t stage, uint64_t flags) {
  decision_epoch.lo = lo; decision_epoch.hi = hi;
  decision_stage = stage; timing = flags;
}
uint32_t jaydb_native_run_accounted_v3(const struct jaydb_native_request_v3 *req,
  const struct jaydb_native_accounted *host, struct jaydb_native_accounted_result *out) {
  uint32_t status = completion_v4_fixture_accounted(req, host, out);
  out->decision_deadline_ns = decision_epoch;
  out->native.stage = decision_stage; out->timing_flags = timing;
  return status;
}
