#ifndef JAYDB_ACCOUNTING_COUNTER_H
#define JAYDB_ACCOUNTING_COUNTER_H
#include <stddef.h>
#include <stdint.h>

#define JAYACCT_ABI 1u
#define JAYACCT_MARKER UINT64_C(0x4a41594143435431)
/* A barrier snapshot is a measurement of the declared allocation semantics.
 * The flags deliberately do not claim full executable/contract certification. */
#define JAYACCT_FROZEN 1u
#define JAYACCT_INCOMPLETE 2u
#define JAYACCT_OWNER_DIED 4u
#define JAYACCT_HELD 8u
#define JAYACCT_SHARED_BYTES 4096u
struct jayacct_u128 { uint64_t lo, hi; };
struct jayacct_snapshot {
  uint64_t abi;
  struct jayacct_u128 sequence;
  struct jayacct_u128 current, peak;
  struct jayacct_u128 monotonic_ns, peak_monotonic_ns, peak_sequence;
  uint64_t peak_flags, flags;
};
struct jayacct_transaction { void *shared; uint64_t pid, tid; };
size_t jayacct_shared_size(void);
int jayacct_init(void *shared, size_t size);
/* Take the global lock BEFORE the actual backing operation. An adapter must
 * publish its owner, commit the actual successful capacity and unlock before
 * a callback/longjmp/cancellation point. Never fork/exec inside a transaction.
 * A transaction copied by fork cannot be committed by its inheritor. */
int jayacct_begin(void *shared, struct jayacct_transaction *tx);
int jayacct_commit(struct jayacct_transaction *tx, struct jayacct_u128 released,
                  struct jayacct_u128 acquired, struct jayacct_snapshot *out);
int jayacct_cancel(struct jayacct_transaction *tx);
/* Cooperative counter. Successful backing acquisition must precede acquired;
 * real release must precede released. Serialize acquisition, owner publication,
 * commit and cleanup as one trusted critical section using begin/commit.
 * change alone updates bookkeeping; it cannot serialize earlier acquisitions.
 * Never mix cooperative writers with the tracer's sole-writer mode. */
int jayacct_change(void *shared, struct jayacct_u128 released,
                   struct jayacct_u128 acquired, struct jayacct_snapshot *out);
int jayacct_read(const void *shared, struct jayacct_snapshot *out);
/* Tracer sole-writer primitive; all mutating tracees must be stopped. */
int jayacct_publish(void *shared, struct jayacct_u128 current, uint64_t flags,
                    struct jayacct_snapshot *out);
/* Same sole-writer operation with an observation time captured BEFORE a
 * stopped-task validation pass. Validation after that time must prove that
 * every mm used by current still existed at the observation instant. */
int jayacct_publish_observation(void *shared, struct jayacct_u128 current,
                    struct jayacct_u128 observed_ns, uint64_t flags,
                    struct jayacct_snapshot *out);
/* x86_64 Linux synchronous marker. ENOTSUP outside the accounting tracer.
 * No memory is allocated by this function. The returned timestamp is that of
 * the stopped-world syscall-EXIT observation, not syscall entry or the time
 * the caller later consumes it. Observer metadata acquisition precedes it. */
int jayacct_barrier(struct jayacct_snapshot *out);
/* Keep all other tracees stopped until hold_end. An acquisition phase may
 * acquire backing through observed syscalls, then call barrier again. After
 * that FINAL barrier and until the Campo event, the owner must perform only
 * bounded, nonblocking work on already active explicit stack/backing: no new
 * backing acquisition, automatic stack growth, allocating signal handlers or
 * nonlocal escape without hold_end. The observer waits without acquiring any
 * backing until another tracee event. These obligations are NOT inferred by
 * the tracer and NOT a proof of AlocouCampo. */
int jayacct_hold_begin(struct jayacct_snapshot *out);
int jayacct_hold_end(struct jayacct_snapshot *out);
#endif
