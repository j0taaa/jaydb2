#ifndef JAYDB_SERVICE_COMMIT_H
#define JAYDB_SERVICE_COMMIT_H
#include <stdint.h>
#include "../../native/accounting/deadline.h"

#define JAYDB_COMMIT_ABI 1u
enum jaydb_commit_status {
  JAYDB_COMMITTED = 0, JAYDB_COMMIT_MEMORY = 1, JAYDB_COMMIT_TIME = 2,
  JAYDB_COMMIT_COVERAGE = 3, JAYDB_COMMIT_INSTRUMENT = 4,
  JAYDB_COMMIT_ARGUMENT = 5
};
/* The host retains every record and both immutable byte buffers before entry.
 * No reference count, allocation or callback is performed in the critical
 * region. These are trusted host records, never values supplied by Bend. */
struct jaydb_prepared {
  uint64_t abi, publish;
  const void *state;
  uint64_t state_bytes;
  const void *response;
  uint64_t response_bytes;
};
struct jaydb_root {
  uint64_t abi;
  const struct jaydb_prepared *published;
  const struct jaydb_prepared *completed;
};
struct jaydb_commit_result {
  uint64_t status, instrument_error, release_error, clock_error;
  struct jayacct_window_snapshot window;
  struct jayacct_u128 checked_ns;
};
struct jaydb_commit_descriptor {
  uint64_t abi, prepared_bytes, root_bytes, result_bytes, stack_bytes, flags;
  const char *build_identity_sha256;
};
const struct jaydb_commit_descriptor *jaydb_commit_describe(void);
/* required_stack_bytes is derived from this build's finite, leaf callgraph.
 * It is not a request quota. The host supplies that many already active bytes,
 * aligned to 16; no automatic-stack extension is permitted after the barrier.
 * Signals with user handlers are blocked before entering that stack and
 * restored after release. SIGKILL/SIGSTOP remain external events.
 *
 * A complete FROZEN|HELD observation for the exact active scope is required.
 * A successful finish closes the measurement window, checks its own peak
 * strictly against ceiling and time inclusively against the absolute epoch,
 * then performs at most one state pointer store. A non-success prepared
 * response (publish=0) never writes root.published.
 *
 * root.completed is the durable completion indicator even if Python dispatches
 * an exception at the FFI return. Once set, release/return errors cannot turn
 * the response into a rollback or a different response. Inspect it first. */
uint64_t jaydb_commit_stack_bytes(void);
uint64_t jaydb_commit_finish(struct jaydb_root *, const struct jaydb_prepared *,
  struct jayacct_u128 scope, struct jayacct_u128 ceiling,
  struct jayacct_u128 deadline, void *stack, uint64_t stack_bytes,
  struct jaydb_commit_result *);

/* Resolve the already prepared candidate OR the already prepared fixed limite
 * response in this same critical region. limited must retain the published
 * state and must never publish. Complete coverage remains mandatory.
 *
 * decision_deadline is the original public-stage epoch. instrument_deadline
 * only bounds observer cleanup; it never extends time available to the
 * candidate. MEMORY/TIME may accompany root.completed==limited: that durable
 * pointer identifies a completed error, rather than an unfinished candidate.
 * A cancelled/incomplete observation still cannot complete either record. */
uint64_t jaydb_commit_resolve(struct jaydb_root *, const struct jaydb_prepared *,
  const struct jaydb_prepared *limited,
  struct jayacct_u128 scope, struct jayacct_u128 ceiling,
  struct jayacct_u128 decision_deadline, struct jayacct_u128 instrument_deadline,
  void *stack, uint64_t stack_bytes, struct jaydb_commit_result *);
#endif
