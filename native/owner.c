/* A dynamic TLS lookup can allocate and enter the loader. CPU1 needs only an
 * owner test, so use the Linux x86_64 thread pointer without DTV allocation.
 * All methods are bounded, uncovered and allocation-free. */
#include "owner.h"
#include <stdint.h>
#include <stdatomic.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error Invocation owner requires the audited Linux x86_64 thread ABI
#endif

static _Atomic uintptr_t jaydb_owner_thread;
static _Atomic(struct jaydb_guard *) jaydb_owner_guard;

struct jaydb_guard *jaydb_owner_get(void) {
  if (atomic_load(&jaydb_owner_thread) != (uintptr_t)__builtin_thread_pointer()) return 0;
  return atomic_load(&jaydb_owner_guard);
}

void jaydb_owner_set(struct jaydb_guard *guard) {
  if (guard) {
    atomic_store(&jaydb_owner_guard, guard);
    atomic_store(&jaydb_owner_thread, (uintptr_t)__builtin_thread_pointer());
  } else {
    atomic_store(&jaydb_owner_thread, 0);
    atomic_store(&jaydb_owner_guard, 0);
  }
}
