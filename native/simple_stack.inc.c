/* Sparse continuation stack; numeric bounds are machine addressability only. */
struct jaydb_term_store { struct jaydb_pages pages; };
static struct jaydb_term_store jaydb_term_stack;
static Term *jaydb_effect_fields;
static u64 jaydb_effect_fields_capacity;

static u64 jaydb_stack_move(u64 index, int64_t offset, bool one_past) {
  const u64 addressable = SIZE_MAX / sizeof(Term);
  u64 result;
  if (offset < 0) {
    u64 subtract = (u64)(-(offset + 1)) + 1;
    if (subtract > index) jaydb_abort(JAYDB_RUNTIME, 0);
    result = index - subtract;
  } else {
    if (index > addressable || (u64)offset > addressable - index)
      jaydb_abort(JAYDB_SYSTEM, EOVERFLOW);
    result = index + (u64)offset;
  }
  if (result > addressable || (!one_past && result == addressable))
    jaydb_abort(JAYDB_SYSTEM, EOVERFLOW);
  return result;
}

static Term *jaydb_term_cell(struct jaydb_term_store *store, u64 index) {
  if (index >= SIZE_MAX / sizeof(Term)) jaydb_abort(JAYDB_SYSTEM, EOVERFLOW);
  u64 page = index >> JAYDB_LEAF_BITS;
  u32 slot = page & (JAYDB_LEAF_CACHE_ENTRIES - 1);
  Term *leaf = store->pages.cache[slot];
  if (!leaf || store->pages.cache_index[slot] != page)
    leaf = jaydb_pages_leaf(&store->pages, page, true);
  return leaf + (index & (JAYDB_LEAF_WORDS - 1));
}

static Term *jaydb_fields_storage(u64 words) {
  if (words > (SIZE_MAX - (JAYDB_PAGE_BYTES - 1)) / sizeof(Term))
    jaydb_abort(JAYDB_SYSTEM, EOVERFLOW);
  u64 bytes = (words * sizeof(Term) + JAYDB_PAGE_BYTES - 1) & ~(JAYDB_PAGE_BYTES - 1);
  if (bytes > jaydb_effect_fields_capacity)
    jaydb_resize((void **)&jaydb_effect_fields, &jaydb_effect_fields_capacity, bytes);
  return jaydb_effect_fields;
}

static void jaydb_term_stack_clear(void) {
  jaydb_pages_clear(&jaydb_term_stack.pages);
  if (jaydb_effect_fields) jaydb_unmap(jaydb_effect_fields, jaydb_effect_fields_capacity);
  jaydb_effect_fields = NULL;
  jaydb_effect_fields_capacity = 0;
}
