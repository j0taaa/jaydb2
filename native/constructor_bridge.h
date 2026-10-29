#ifndef JAYDB_TRUSTED_CONSTRUCTOR_BRIDGE_H
#define JAYDB_TRUSTED_CONSTRUCTOR_BRIDGE_H
#include "accounting/deadline.h"

/* Experimental PRIVATE trusted C bridge, not a Bend primitive or the public
 * byte-only native ABI. No callback, Term representation or client closure is
 * supplied here. It is not yet linked into emitted native modules.
 *
 * The trusted emitter/adapter must check the real wire length FIRST, acquire
 * raw arena backing without constructing the object, prepare immutable source
 * values, acquire/activate all destinations, metadata and explicit stack, then
 * call this bridge. In particular rfc_seal and sparse-leaf lookup/allocation
 * happen before entry. Destinations may span already acquired arena leaves.
 * Source snapshots, spans, receipts and stack must not alias destinations.
 * No allocating signal handler may run between final barrier and construction;
 * this implementation blocks handlers until after releasing its hold.
 *
 * Every actual destination store, including partial construction, takes place
 * after the final barrier while held. constructed records TRANSFER COMPLETION
 * immediately after the final store; it does not define AlocouCampo and must
 * never be used to erase actual partial constructions from the environment.
 * A complete frozen/held global measurement must have current<=ceiling.
 * Strict excess returns MEMORY with the authentic PRE-construction snapshot,
 * without any destination store or construction event. INCOMPLETE is refused
 * as COVERAGE, never relabelled as memory excess. Equality is accepted.
 *
 * Length provenance, emitted-site completeness (including flattened/packed
 * constructors), observational event binding and global counter completeness
 * are separate pending obligations. Setting length.checked is not a proof
 * of them. This bridge must not be presented as a completed Lei2 integration.
 */
#define JAYDB_CONSTRUCTOR_ABI 1u
enum jaydb_constructor_status {
  JAYDB_CONSTRUCTED=0, JAYDB_CONSTRUCTOR_MEMORY=1, JAYDB_CONSTRUCTOR_TIME=2,
  JAYDB_CONSTRUCTOR_COVERAGE=3, JAYDB_CONSTRUCTOR_INSTRUMENT=4,
  JAYDB_CONSTRUCTOR_ARGUMENT=5
};
struct jaydb_length_checked {
  uint64_t abi, checked, position, quantity;
};
struct jaydb_constructor_span {
  void *destination;
  const void *source;
  uint64_t bytes;
};
struct jaydb_constructor_result {
  uint64_t status, constructed, instrument_error, release_error, clock_error;
  uint64_t constructor_id, site_id, position, quantity;
  struct jayacct_snapshot memory;
  struct jayacct_u128 checked_ns;
};
uint64_t jaydb_constructor_stack_bytes(void);
uint64_t jaydb_constructor_transfer(uint64_t constructor_id, uint64_t site_id,
  const struct jaydb_length_checked *, const struct jaydb_constructor_span *,
  uint64_t span_count, struct jayacct_u128 ceiling, struct jayacct_u128 deadline,
  void *active_stack, uint64_t active_stack_bytes, struct jaydb_constructor_result *);
#endif
