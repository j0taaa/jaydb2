/* Logical Term-stack indices. Automatic V3 storage has stable pages; neither
 * continuation depth nor the register bank requires a contiguous reservation.
 * Nonzero explicit capacities preserve the V1/V2/fixed-mode storage contract. */
struct jaydb_term_store {
  bool automatic;
  Term *fixed;
  u64 words;
  struct jaydb_pages pages;
};
static struct jaydb_term_store jaydb_term_stack;
static Term *jaydb_effect_fields;
static u64 jaydb_effect_fields_capacity;

static _Noreturn void jaydb_stack_capacity(void) {
  struct jaydb_guard *g = jaydb_active;
  jaydb_abort(g && g->wide_time ? JAYDB_RUNTIME : JAYDB_MEMORY,
              g && g->wide_time ? JAYDB_STACK_CAPACITY_CODE : 0);
}

static u64 jaydb_stack_move(u64 index, int64_t offset, bool one_past) {
  u64 limit = jaydb_term_stack.automatic ? UINT64_MAX / sizeof(Term) : jaydb_term_stack.words;
  u64 result;
  if (offset < 0) {
    u64 subtract = (u64)(-(offset + 1)) + 1;
    if (subtract > index) jaydb_abort(JAYDB_RUNTIME, 0);
    result = index - subtract;
  } else {
    if (index > limit || (u64)offset > limit - index) {
      if (!jaydb_term_stack.automatic) jaydb_stack_capacity();
      jaydb_abort(JAYDB_MEMORY, 0);
    }
    result = index + (u64)offset;
  }
  if (result > limit || (!one_past && result == limit)) {
    if (!jaydb_term_stack.automatic) jaydb_stack_capacity();
    jaydb_abort(JAYDB_MEMORY, 0);
  }
  return result;
}

static Term *jaydb_term_cell(struct jaydb_term_store *store, u64 index) {
  if (!store->automatic) {
    if (index >= store->words) jaydb_stack_capacity();
    return store->fixed + index;
  }
  if (index >= UINT64_MAX / sizeof(Term)) jaydb_abort(JAYDB_MEMORY, 0);
  u64 page = index >> JAYDB_LEAF_BITS;
  u32 slot = page & (JAYDB_LEAF_CACHE_ENTRIES - 1);
  Term *leaf = store->pages.cache[slot];
  bool missing = (leaf == NULL) | (store->pages.cache_index[slot] != page);
  if (missing) leaf = jaydb_pages_leaf(&store->pages, page, true);
  return leaf + (index & (JAYDB_LEAF_WORDS - 1));
}

static Term *jaydb_fields_storage(u64 words) {
  if (!jaydb_term_stack.automatic) {
    if (words > jaydb_term_stack.words) jaydb_stack_capacity();
    return jaydb_term_stack.fixed;
  }
  if (words > (SIZE_MAX - (JAYDB_PAGE_BYTES - 1)) / sizeof(Term)) jaydb_abort(JAYDB_MEMORY, 0);
  u64 bytes = (words * sizeof(Term) + JAYDB_PAGE_BYTES - 1) & ~(JAYDB_PAGE_BYTES - 1);
  if (bytes > jaydb_effect_fields_capacity) {
    /* No caller retains fields across the next jaydb_fields invocation. The
     * worker has no active evaluator while this buffer is filled/consumed. */
    uint32_t status = jaydb_mapping_resize(jaydb_active, &jaydb_effect_fields,
                                            &jaydb_effect_fields_capacity, bytes);
    if (status) jaydb_abort(status, 0);
  }
  return jaydb_effect_fields;
}

static void jaydb_term_stack_clear(void) {
  jaydb_pages_clear(&jaydb_term_stack.pages);
  if (jaydb_effect_fields) munmap(jaydb_effect_fields, jaydb_effect_fields_capacity);
  jaydb_effect_fields = NULL;
  jaydb_effect_fields_capacity = 0;
  jaydb_term_stack.automatic = false;
  jaydb_term_stack.fixed = NULL;
  jaydb_term_stack.words = 0;
}
