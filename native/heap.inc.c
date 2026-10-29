/* The CPU1 allocator uses ordinary constructor blocks and machine-word classes.
 * V1/V2 use a fixed mapped arena; V3 maps stable leaves only as blocks grow.
 * Generic Arrays have ALeaf/ANode constructors; their depth is not a class.
 */
static uint64_t jaydb_heap_next, jaydb_heap_words;
static uint64_t jaydb_free[64];

INLINE u32 cls_fit(u64 words) {
  return words > 1 ? 64 - (u32)__builtin_clzll(words - 1) : 0;
}

INLINE u64 heap_alloc(Env e, u32 cls) {
  jaydb_poll();
  /* A class >=64 needs at least 2^64 slots and cannot be addressed by this
   * process. Smaller classes fail only if the actual arena is insufficient. */
  if (cls >= 64) jaydb_abort(JAYDB_MEMORY, 0);
  u64 words = 1ull << cls;
  u64 loc = jaydb_free[cls];
  if (loc) {
    jaydb_free[cls] = e.mem[loc];
    return loc;
  }
  if (words > jaydb_heap_words - jaydb_heap_next) jaydb_abort(JAYDB_MEMORY, 0);
  loc = jaydb_heap_next;
  jaydb_arena_ensure(loc, words);
  jaydb_heap_next += words;
  return loc;
}

INLINE void heap_free(Env e, u32 cls, u64 loc) {
  if (cls >= 64 || loc < HEAP_OFF || loc >= jaydb_heap_next) jaydb_abort(JAYDB_RUNTIME, 0);
  e.mem[loc] = jaydb_free[cls];
  jaydb_free[cls] = loc;
}

INLINE void spare_free(Env e, u32 cls, u64 loc) {
  if (loc >= HEAP_OFF) heap_free(e, cls, loc);
}
