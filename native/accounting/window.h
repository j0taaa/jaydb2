#ifndef JAYDB_ACCOUNTING_WINDOW_H
#define JAYDB_ACCOUNTING_WINDOW_H
#include "counter.h"

#define JAYACCT_WINDOW_ABI 1u
#define JAYACCT_WINDOW_NONE 0u
#define JAYACCT_WINDOW_ACTIVE 1u
#define JAYACCT_WINDOW_CLOSED 2u
/* Separate ABI: counter.h's legacy snapshot remains exactly 120 bytes.
 * snapshot is the latest global publication; peak belongs ONLY to scope_id.
 * A closed scope preserves its peak and end provenance even when subsequent
 * global publications change snapshot. A new begin replaces the one retained
 * scope record; callers retain the returned closed value for earlier scopes. */
struct jayacct_window_snapshot {
  uint64_t abi, state, error;
  struct jayacct_snapshot snapshot;
  struct jayacct_u128 scope_id, begin_sequence, begin_monotonic_ns;
  struct jayacct_u128 end_sequence, end_monotonic_ns;
  struct jayacct_u128 peak, peak_monotonic_ns, peak_sequence;
  uint64_t peak_flags;
};
/* O(1) shared-page operations. Sole-writer/cooperative integration only:
 * open/close must immediately follow an exact publication under the same
 * acquisition serialization. They never scan processes or allocate backing.
 * One active scope per counter; EBUSY on nested open. ENODATA before any real
 * publication. Opening includes current as the scope's baseline observation. */
int jayacct_window_open(void *shared, struct jayacct_window_snapshot *out);
int jayacct_window_close(void *shared, struct jayacct_window_snapshot *out);
/* O(1), no retry loop: the last published observation, not current memory at
 * read time. EAGAIN on concurrent publication, EOWNERDEAD on owner death. */
int jayacct_window_read(const void *shared, struct jayacct_window_snapshot *out);
/* Synchronous tracee markers. Each first takes a syscall-EXIT global barrier,
 * then opens/closes/reads the scope without acquiring backing. The scan is
 * proportional to owners/mappings; only the scope operation is O(1).
 * No hold is implied: combine hold_begin, acquisition, window_begin/final
 * barrier and the bounded Campo construction as required by the host. */
int jayacct_window_begin(struct jayacct_window_snapshot *out);
int jayacct_window_end(struct jayacct_window_snapshot *out);
int jayacct_window_barrier(struct jayacct_window_snapshot *out);
#endif
