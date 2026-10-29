#ifndef JAYDB_NATIVE_ABSOLUTE_DEADLINE_H
#define JAYDB_NATIVE_ABSOLUTE_DEADLINE_H
#include "abi_v3.h"

/* Additional entry, unchanged V1/V2/V3 layouts. setup_absolute_ns is an epoch
 * on CLOCK_MONOTONIC, not a duration sampled again at the FFI boundary.
 * This entry ignores request.setup_timeout_ns. An epoch <= the first native
 * clock sample returns TIME at SETUP before charging or allocating anything.
 * Execution/preparation budgets still start at their native enter transitions.
 * All pointers are borrowed for this synchronous call. Lease rules are V3. */
uint32_t jaydb_native_run_deadline_v3(const struct jaydb_native_request_v3 *,
                                    struct jaydb_native_result_v3 *,
                                    const struct jaydb_native_ns128 *setup_absolute_ns);
#endif
