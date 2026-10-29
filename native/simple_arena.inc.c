/* Stable sparse arena. Logical indices remain full machine words.
 * Leaves contain 512 Terms; directory pages hold 256 pointers. Seven radix
 * levels cover all 64-bit indices (9 leaf bits + 7*8 >= 64). No huge virtual
 * reservation or moving heap allocation is required. */
#define JAYDB_PAGE_BYTES 4096ull
#define JAYDB_LEAF_BITS 9u
#define JAYDB_LEAF_WORDS (1ull << JAYDB_LEAF_BITS)
#define JAYDB_LEAF_BYTES (JAYDB_LEAF_WORDS * sizeof(Term))
#define JAYDB_DIR_BITS 8u
#define JAYDB_DIR_ENTRIES (1u << JAYDB_DIR_BITS)
#define JAYDB_DIR_LEVELS 7u
_Static_assert(JAYDB_LEAF_BITS + JAYDB_DIR_LEVELS * JAYDB_DIR_BITS >= 64,
               "Arena radix must cover every machine-word index");
_Static_assert(JAYDB_DIR_ENTRIES * sizeof(void *) <= JAYDB_PAGE_BYTES,
               "Directory page must fit its pointers");
_Static_assert(JAYDB_LEAF_BYTES % JAYDB_PAGE_BYTES == 0,
               "Term leaves must consist of whole mapped pages");

#define JAYDB_LEAF_CACHE_ENTRIES 64u
/* This cache changes lookup cost only. Collisions fall back to the complete
 * radix, so cache size is never a bound on the accessible heap. */
struct jaydb_pages {
  void **root;
  Term *cache[JAYDB_LEAF_CACHE_ENTRIES];
  u64 cache_index[JAYDB_LEAF_CACHE_ENTRIES];
};
static struct jaydb_pages jaydb_heap_pages;
#define jaydb_arena_root jaydb_heap_pages.root
#define jaydb_leaf_cache jaydb_heap_pages.cache
#define jaydb_leaf_cache_index jaydb_heap_pages.cache_index
static uint8_t *jaydb_owned_output;
static u64 jaydb_owned_capacity;

static void jaydb_arena_map(void *owner, u64 bytes) {
  void *mapped = mmap(NULL, bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (mapped == MAP_FAILED) jaydb_abort(JAYDB_SYSTEM, errno);
  memcpy(owner, &mapped, sizeof mapped);
}

FAR Term *jaydb_pages_leaf(struct jaydb_pages *pages, u64 page, bool create) {
  u32 slot = page & (JAYDB_LEAF_CACHE_ENTRIES - 1);
  if (pages->cache[slot] && pages->cache_index[slot] == page) return pages->cache[slot];
  if (!pages->root) {
    if (!create) jaydb_abort(JAYDB_RUNTIME, 0);
    jaydb_arena_map(&pages->root, JAYDB_PAGE_BYTES);
  }
  void **directory = pages->root;
  for (u32 level = JAYDB_DIR_LEVELS - 1; level; --level) {
    u32 index = (page >> (level * JAYDB_DIR_BITS)) & (JAYDB_DIR_ENTRIES - 1);
    if (!directory[index]) {
      if (!create) jaydb_abort(JAYDB_RUNTIME, 0);
      jaydb_arena_map(&directory[index], JAYDB_PAGE_BYTES);
    }
    directory = directory[index];
  }
  u32 index = page & (JAYDB_DIR_ENTRIES - 1);
  if (!directory[index]) {
    if (!create) jaydb_abort(JAYDB_RUNTIME, 0);
    jaydb_arena_map(&directory[index], JAYDB_LEAF_BYTES);
  }
  pages->cache_index[slot] = page;
  pages->cache[slot] = directory[index];
  return pages->cache[slot];
}

FAR Term *jaydb_leaf(u64 page, bool create) { return jaydb_pages_leaf(&jaydb_heap_pages, page, create); }

static Term *jaydb_heap_cell(Term *base, u64 index) {
  u64 page = index >> JAYDB_LEAF_BITS;
  u32 slot = page & (JAYDB_LEAF_CACHE_ENTRIES - 1);
  Term *mapped = jaydb_leaf_cache[slot];
  /* Cache collisions fall back to the full radix directory. */
  bool missing = (mapped == NULL) | (jaydb_leaf_cache_index[slot] != page);
  (void)base;
  if (missing) mapped = jaydb_leaf(page, false);
  return mapped + (index & (JAYDB_LEAF_WORDS - 1));
}

static void jaydb_arena_ensure(u64 start, u64 words) {
  if (!words) return;
  if (start > UINT64_MAX / sizeof(Term) || words > UINT64_MAX / sizeof(Term) - start)
    jaydb_abort(JAYDB_SYSTEM, 0);
  u64 last = (start + words - 1) >> JAYDB_LEAF_BITS;
  for (u64 page = start >> JAYDB_LEAF_BITS;; ++page) {
    (void)jaydb_leaf(page, true);
    if (page == last) break;
  }
}

/* Depth is bounded by the physical address width, not the client object tree.
 * Cleanup walks only directory/leaf mappings actually created by this call. */
static void jaydb_arena_destroy(void **directory, u32 level) {
  if (!directory) return;
  /* Directory depth follows address width. An explicit traversal avoids a
   * recursive C call cycle, including in the host-side cleanup callgraph. */
  void **path[JAYDB_DIR_LEVELS];
  u32 index[JAYDB_DIR_LEVELS] = {0};
  u32 depth = 0;
  path[0] = directory;
  for (;;) {
    if (index[depth] == JAYDB_DIR_ENTRIES) {
      jaydb_unmap(path[depth], JAYDB_PAGE_BYTES);
      if (!depth) break;
      --depth;
    } else {
      void *child = path[depth][index[depth]++];
      if (child) {
        if (depth == level) jaydb_unmap(child, JAYDB_LEAF_BYTES);
        else { ++depth; path[depth] = child; index[depth] = 0; }
      }
    }
  }
}

static void jaydb_pages_clear(struct jaydb_pages *pages) {
  jaydb_arena_destroy(pages->root, JAYDB_DIR_LEVELS - 1);
  pages->root = NULL;
  memset(pages->cache, 0, sizeof pages->cache);
}

static void jaydb_arena_clear(void) {
  jaydb_pages_clear(&jaydb_heap_pages);
}

static void jaydb_owned_byte(u64 index, uint8_t value) {
  if (index > jaydb_owned_capacity) jaydb_abort(JAYDB_RUNTIME, 0);
  if (index == jaydb_owned_capacity) {
    if (index > SIZE_MAX - JAYDB_PAGE_BYTES) jaydb_abort(JAYDB_SYSTEM, EOVERFLOW);
    u64 minimum = (index + JAYDB_PAGE_BYTES) & ~(JAYDB_PAGE_BYTES - 1);
    u64 capacity = jaydb_owned_capacity <= SIZE_MAX / 2 ? jaydb_owned_capacity * 2 : minimum;
    if (capacity < minimum) capacity = minimum;
    jaydb_resize((void **)&jaydb_owned_output, &jaydb_owned_capacity, capacity);
  }
  jaydb_owned_output[index] = value;
}
