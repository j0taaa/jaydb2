/* Consumer-only ABI fixture: real malloc/free/destructor, no Bend certificate
 * or claim of complete measurement. Shares the worker's instrumented payload. */
#include "lifecycle_native_fixture.c"
#include <time.h>
#include "../../native/abi_accounted.h"
static const char source_hash[] = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
#define DEFINE_DESC(n) const struct jaydb_native_descriptor *jaydb_native_describe_v##n(void) { \
  static const struct jaydb_native_descriptor d={n,1,1,1,4096,0,source_hash};return &d;}
DEFINE_DESC(1) DEFINE_DESC(2) DEFINE_DESC(3)
uint32_t jaydb_native_run_v1(const struct jaydb_native_request *a,struct jaydb_native_result *b){(void)a;(void)b;return 5;}
uint32_t jaydb_native_run_v2(const struct jaydb_native_request_v2 *a,struct jaydb_native_result_v2 *b){(void)a;(void)b;return 5;}
uint64_t jaydb_native_preparation_started_v2(void){return 0;}
uint32_t jaydb_native_run_v3(const struct jaydb_native_request_v3 *a,struct jaydb_native_result_v3 *b){
  return lifecycle_fixture_run((void*)a,(struct result*)b);}
uint32_t jaydb_native_run_deadline_v3(const struct jaydb_native_request_v3 *a,
  struct jaydb_native_result_v3 *b,const struct jaydb_native_ns128 *c){
  return lifecycle_fixture_run3((void*)a,(struct result*)b,(void*)c);
}
const struct jaydb_native_accounted_descriptor *jaydb_native_describe_accounted_v3(void){
  static const struct jaydb_native_accounted_descriptor d={1,88,656,1,3,24,0,source_hash};
  return &d;
}
uint32_t jaydb_native_run_accounted_v3(const struct jaydb_native_request_v3 *req,
  const struct jaydb_native_accounted *host,struct jaydb_native_accounted_result *out){
  memset(out,0,sizeof *out);
  uint32_t status=lifecycle_fixture_accounted((void*)req,(void*)host,(struct result*)&out->native);
  struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);
  uint64_t now=(uint64_t)t.tv_sec*1000000000u+(uint64_t)t.tv_nsec;
  out->native.stage=2;out->timing_flags=3;
  out->stage_started_ns.lo=now;out->returned_ns.lo=now;
  out->decision_deadline_ns.lo=host->deadline_ns[0].lo;
  out->decision_deadline_ns.hi=host->deadline_ns[0].hi;
  return status;
}
