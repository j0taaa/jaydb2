#ifndef JAYDB_NATIVE_FIELD_H
#define JAYDB_NATIVE_FIELD_H
#include "accounting/deadline.h"

/* PRIVATE trusted-decoder ABI; never a Bend primitive or a client capability.
 * This is additional to constructor_bridge.h and all native V1/V2/V3 layouts.
 * Public Nats above u128 may be clamped to UINT128_MAX for comparisons only.
 * The host owns the ACTIVE scope and supplies the ORIGINAL absolute deadline.
 */
#define JAYDB_FIELD_ABI 2u
enum jaydb_field_status {
  JAYDB_FIELD_CONSTRUCTED=0, JAYDB_FIELD_MEMORY=1, JAYDB_FIELD_TIME=2,
  JAYDB_FIELD_COVERAGE=3, JAYDB_FIELD_INSTRUMENT=4, JAYDB_FIELD_ARGUMENT=5,
  JAYDB_FIELD_BACKING=6, JAYDB_FIELD_INPUT=7, JAYDB_FIELD_LENGTH=8
};
/* One backing owner, shared by any number of suballocation spans. An empty
 * owner acquires exactly page_round(maximum span end), never the ceiling or
 * the wire count. Existing backing is retained; suballocations add no charge.
 * The host may supply an already active arena leaf or explicit-stack extent.
 * Nonempty owners must be stable and wholly active (not PROT_NONE/revoked).
 * Acquisitions remain owned even on refusal; cleanup is explicit after return.
 */
struct jaydb_field_owner { void *address; uint64_t capacity; };
struct jaydb_field_span {
  uint64_t owner, offset;
  const void *source;
  uint64_t bytes;
};
/* position is the actual tag offset in immutable wire. name=1 admits only a
 * nonempty text/name of <=64 bytes, as Codec.abrir_nome. pending_minimum is
 * the trusted decoder's checked minimum of pending siblings/ancestors, from
 * Codec.minimo_pilha; it is not storage bytes or a client length token.
 * The bridge READS the u64 BE header itself and performs the effective minimum
 * versus remaining body/limit check BEFORE raw backing acquisition or stores.
 * Fixed tags 0..2 check quantity 0; integer checks its fixed quantity 8.
 * Only variable tags apply pending_minimum, matching concluir_palavra;
 * fixed primitives must not preempt a later header's error or construction.
 * Variable tags 4/5/6 retain the DECLARED quantity, including record arity.
 * This check is necessary, not a proof of decoder cursor/prefix provenance.
 */
struct jaydb_field_wire {
  const unsigned char *bytes;
  uint64_t size, limit, position, name;
  struct jayacct_u128 pending_minimum;
};
struct jaydb_field_request {
  uint64_t abi, constructor_id, site_id;
  struct jaydb_field_wire wire;
  struct jayacct_u128 scope, ceiling, deadline;
  struct jaydb_field_owner *owners;
  uint64_t owner_count;
  const struct jaydb_field_span *spans;
  uint64_t span_count;
};
struct jaydb_field_result {
  uint64_t status, length_checked, construction_started, constructed;
  uint64_t instrument_error, release_error, clock_error, backing_error;
  uint64_t position, quantity, tag, acquired_bytes, stores_completed;
  struct jayacct_window_snapshot window;
  struct jayacct_u128 checked_ns;
};
/* All request/owner/span/source/result records and the explicit stack are
 * active and retained before entry. Destinations are disjoint from those
 * records, sources and stack. This implementation validates those aliases.
 * Source bytes are representation-ready, NOT a previously constructed copy of
 * the very wire Campo whose first construction this boundary is to protect.
 *
 * Production critical is an audited leaf. Signals are blocked, peers held,
 * required backing acquired, window_barrier_until performed, complete local
 * window provenance/peak checked, own clock checked, then stores to the
 * prepared active destinations plus raw nonallocating clock syscalls. No
 * window_end and no library/FFI/callback.
 * Op6 cleanup precedes mask restoration and return on every held path.
 * construction_started precedes the FIRST destination store; constructed is a
 * durable completion receipt, not a way to erase partial real constructions.
 * Neither receipt alone proves AlocouCampo/Lei2 or runtime correspondence.
 */
uint64_t jaydb_field_stack_bytes_v2(void);
uint64_t jaydb_field_construct_v2(const struct jaydb_field_request *,
  void *active_stack, uint64_t active_stack_bytes, struct jaydb_field_result *);
#endif
