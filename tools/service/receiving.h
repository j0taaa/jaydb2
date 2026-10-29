#ifndef JAYDB_SERVICE_RECEIVING_H
#define JAYDB_SERVICE_RECEIVING_H
#include "../../native/accounting/deadline.h"

#define JAYDB_RECEIVING_ABI 1u
enum jaydb_receiving_status {
  JAYDB_RECEIVING_STARTED=0, JAYDB_RECEIVING_EOF=1,
  JAYDB_RECEIVING_INTERRUPTED=2, JAYDB_RECEIVING_IO=3,
  JAYDB_RECEIVING_INSTRUMENT=4, JAYDB_RECEIVING_COVERAGE=5,
  JAYDB_RECEIVING_ARGUMENT=6
};
struct jaydb_receiving_result {
  uint64_t abi,status,system_error,received,first_byte;
  struct jayacct_u128 started_ns,received_ns,deadline_ns;
  struct jayacct_window_snapshot window;
};
struct jaydb_receiving_descriptor {
  uint64_t abi,result_bytes,flags;
  const char *build_identity_sha256;
};
const struct jaydb_receiving_descriptor *jaydb_receiving_describe(void);
/* The selected channel has exactly one reader. After readiness, started_ns is
 * sampled immediately BEFORE the successful one-byte read attempt. It includes
 * processing/preemption during that read; idle waits are outside the stage.
 * No allocation/callback occurs between that sample, receipt and window open.
 * The scope begins at the subsequent exact barrier and includes its baseline.
 * The retained first-byte record survives an exception at the FFI return.
 *
 * duration is the original framing duration, not a retry budget. The distinct
 * absolute instrument epoch only bounds the observer's marker. On failure no
 * observation is fabricated. A successfully opened scope remains ACTIVE for
 * the decoder, helpers and completion; this function never closes a scope. */
uint64_t jaydb_receiving_begin(int fd,struct jayacct_u128 duration,
  struct jayacct_u128 instrument_deadline,struct jaydb_receiving_result *);
_Static_assert(sizeof(struct jaydb_receiving_result)==368,"receiving result ABI 1");
#endif
