#ifndef JAYDB_GUARD_OWNER_H
#define JAYDB_GUARD_OWNER_H
struct jaydb_guard;
/* CPU1 invocation ownership. Caller holds this DSO's BUSY flag. A different
 * host thread sees NULL without dereferencing the invocation's guard. */
struct jaydb_guard *jaydb_owner_get(void);
void jaydb_owner_set(struct jaydb_guard *);
#endif
