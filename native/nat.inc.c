/* Compact boxed Nat. Little-endian base-2^32 limbs in linked 64-word chunks.
 * All storage comes from the charged arena; every loop is coverage audited.
 * No limb-count/numeric ceiling is added. Small values are immediate; larger
 * values promote transparently and use the normal saturating RFC wrapper.
 */
#define JAYDB_NAT_MASK ((1ull << 56) - 1)
#define JAYDB_NAT_SMALL(n) term_make(TAG_NAT_SMALL, 0, n)
#define JAYDB_NAT_ZERO JAYDB_NAT_SMALL(0)
#define JAYDB_NAT_CHUNK 63ull

static bool jaydb_nat_is_zero(Term n) { return n == JAYDB_NAT_ZERO; }
static bool jaydb_nat_immediate(Term n) { return term_tag(n) == TAG_NAT_SMALL; }

static void jaydb_nat_free(Env e, Term n) {
  u64 header = term_loc(n), chunk = e.mem[header + 1];
  while (chunk) {
    u64 next = e.mem[chunk + JAYDB_NAT_CHUNK];
    heap_free(e, 6, chunk);
    chunk = next;
  }
  heap_free(e, 1, header);
}

static u64 jaydb_nat_length(Env e, Term n) {
  if (jaydb_nat_immediate(n)) return (n & JAYDB_NAT_MASK) > UINT32_MAX ? 2 : 1;
  if (term_tag(n) != TAG_NAT_BIG) jaydb_abort(JAYDB_RUNTIME, ERR_TAGS);
  return e.mem[term_peek(e.mem, n)];
}

static u64 jaydb_nat_chunk(Env e, Term n, u64 index) {
  u64 chunk = e.mem[term_peek(e.mem, n) + 1];
  for (u64 i = index / JAYDB_NAT_CHUNK; i; --i)
    chunk = e.mem[chunk + JAYDB_NAT_CHUNK];
  return chunk + index % JAYDB_NAT_CHUNK;
}

static u32 jaydb_nat_get(Env e, Term n, u64 index) {
  if (jaydb_nat_immediate(n))
    return index < 2 ? (u32)((n & JAYDB_NAT_MASK) >> (index * 32)) : 0;
  return (u32)e.mem[jaydb_nat_chunk(e, n, index)];
}

static void jaydb_nat_put(Env e, Term n, u64 index, u32 value) {
  e.mem[jaydb_nat_chunk(e, n, index)] = value;
}

static Term jaydb_nat_new(Env e, u64 length) {
  /* This is a necessary physical capacity condition, not a number quota. */
  if (!length || length > jaydb_heap_words) jaydb_abort(JAYDB_MEMORY, 0);
  u64 header = heap_alloc(e, 1);
  Term *hole = &e.mem[header + 1];
  e.mem[header] = length;
  *hole = 0;
  for (u64 left = length; left;) {
    u64 chunk = heap_alloc(e, 6);
    *hole = chunk;
    for (u64 i = 0; i <= JAYDB_NAT_CHUNK; ++i) e.mem[chunk + i] = 0;
    hole = &e.mem[chunk + JAYDB_NAT_CHUNK];
    left -= left > JAYDB_NAT_CHUNK ? JAYDB_NAT_CHUNK : left;
  }
  return term_make(TAG_NAT_BIG, 0, header);
}

static Term jaydb_nat_finish(Env e, Term n) {
  u64 length = jaydb_nat_length(e, n);
  while (length > 1 && !jaydb_nat_get(e, n, length - 1)) --length;
  if (length <= 2) {
    u64 small = jaydb_nat_get(e, n, 0);
    if (length == 2) small |= (u64)jaydb_nat_get(e, n, 1) << 32;
    if (small <= JAYDB_NAT_MASK) {
      jaydb_nat_free(e, n);
      return JAYDB_NAT_SMALL(small);
    }
  }
  /* Release trailing chunks, including when subtraction shrinks a value. */
  u64 chunk = e.mem[term_loc(n) + 1];
  for (u64 i = (length - 1) / JAYDB_NAT_CHUNK; i; --i)
    chunk = e.mem[chunk + JAYDB_NAT_CHUNK];
  u64 rest = e.mem[chunk + JAYDB_NAT_CHUNK];
  e.mem[chunk + JAYDB_NAT_CHUNK] = 0;
  while (rest) {
    u64 next = e.mem[rest + JAYDB_NAT_CHUNK];
    heap_free(e, 6, rest);
    rest = next;
  }
  e.mem[term_loc(n)] = length;
  return n;
}

static int jaydb_nat_compare(Env e, Term a, Term b) {
  if (jaydb_nat_immediate(a) && jaydb_nat_immediate(b))
    return (a > b) - (a < b);
  u64 an = jaydb_nat_length(e, a), bn = jaydb_nat_length(e, b);
  if (an != bn) return an > bn ? 1 : -1;
  int order = 0;
  for (u64 i = 0; i < an; ++i) {
    u32 x = jaydb_nat_get(e, a, i), y = jaydb_nat_get(e, b, i);
    if (x != y) order = x > y ? 1 : -1;
  }
  return order;
}

static Term jaydb_nat_add(Env e, Term a, Term b) {
  if (jaydb_nat_immediate(a) && jaydb_nat_immediate(b)) {
    u64 sum = (a & JAYDB_NAT_MASK) + (b & JAYDB_NAT_MASK);
    if (sum <= JAYDB_NAT_MASK) return JAYDB_NAT_SMALL(sum);
  }
  u64 an = jaydb_nat_length(e, a), bn = jaydb_nat_length(e, b);
  u64 length = an > bn ? an : bn, carry = 0;
  Term out = jaydb_nat_new(e, length + 1);
  for (u64 i = 0; i < length; ++i) {
    u64 sum = carry + (i < an ? jaydb_nat_get(e, a, i) : 0)
      + (u64)(i < bn ? jaydb_nat_get(e, b, i) : 0);
    jaydb_nat_put(e, out, i, (u32)sum);
    carry = sum >> 32;
  }
  jaydb_nat_put(e, out, length, (u32)carry);
  term_sink(e, a); term_sink(e, b);
  return jaydb_nat_finish(e, out);
}

static Term jaydb_nat_sub(Env e, Term a, Term b) {
  if (jaydb_nat_immediate(a) && jaydb_nat_immediate(b))
    return a < b ? JAYDB_NAT_ZERO : JAYDB_NAT_SMALL(a - b);
  if (jaydb_nat_compare(e, a, b) <= 0) {
    term_sink(e, a); term_sink(e, b);
    return JAYDB_NAT_ZERO;
  }
  u64 an = jaydb_nat_length(e, a), bn = jaydb_nat_length(e, b), borrow = 0;
  Term out = jaydb_nat_new(e, an);
  for (u64 i = 0; i < an; ++i) {
    u64 x = jaydb_nat_get(e, a, i), y = borrow + (u64)(i < bn ? jaydb_nat_get(e, b, i) : 0);
    jaydb_nat_put(e, out, i, (u32)(x - y));
    borrow = x < y;
  }
  term_sink(e, a); term_sink(e, b);
  return jaydb_nat_finish(e, out);
}

static Term jaydb_nat_succ(Env e, Term n) { return jaydb_nat_add(e, n, JAYDB_NAT_SMALL(1)); }
static Term jaydb_nat_pred(Env e, Term n) { return jaydb_nat_sub(e, n, JAYDB_NAT_SMALL(1)); }
static Term jaydb_nat_double(Env e, Term n) {
  n = term_keep(e, n, 1);
  return jaydb_nat_add(e, n, n);
}

static Term jaydb_nat_mul(Env e, Term a, Term b) {
  if (jaydb_nat_is_zero(a) || jaydb_nat_is_zero(b)) {
    term_sink(e, a); term_sink(e, b);
    return JAYDB_NAT_ZERO;
  }
  if (jaydb_nat_immediate(a) && jaydb_nat_immediate(b)) {
    u64 x = a & JAYDB_NAT_MASK, y = b & JAYDB_NAT_MASK;
    if (x <= JAYDB_NAT_MASK / y) return JAYDB_NAT_SMALL(x * y);
  }
  u64 an = jaydb_nat_length(e, a), bn = jaydb_nat_length(e, b);
  Term out = jaydb_nat_new(e, an + bn);
  for (u64 i = 0; i < an; ++i) {
    u64 carry = 0, x = jaydb_nat_get(e, a, i);
    for (u64 j = 0; j < bn; ++j) {
      u64 sum = x * jaydb_nat_get(e, b, j) + jaydb_nat_get(e, out, i + j) + carry;
      jaydb_nat_put(e, out, i + j, (u32)sum);
      carry = sum >> 32;
    }
    jaydb_nat_put(e, out, i + bn, (u32)carry);
  }
  term_sink(e, a); term_sink(e, b);
  return jaydb_nat_finish(e, out);
}

static u64 jaydb_nat_cmp(Env e, Term a, Term b) {
  int order = jaydb_nat_compare(e, a, b);
  term_sink(e, a); term_sink(e, b);
  return (u64)(order + 1);
}
static u64 jaydb_nat_lt(Env e, Term a, Term b) { return jaydb_nat_cmp(e, a, b) == 0; }
static Term jaydb_nat_minmax(Env e, Term a, Term b, bool maximum) {
  bool choose_a = maximum ? jaydb_nat_compare(e, a, b) >= 0 : jaydb_nat_compare(e, a, b) <= 0;
  term_sink(e, choose_a ? b : a);
  return choose_a ? a : b;
}

static void jaydb_nat_divmod(Env e, Term a, Term b, Term *quotient, Term *remainder) {
  if (jaydb_nat_is_zero(b)) {
    *quotient = JAYDB_NAT_ZERO; *remainder = a;
    return;
  }
  if (jaydb_nat_immediate(a) && jaydb_nat_immediate(b)) {
    u64 x = a & JAYDB_NAT_MASK, y = b & JAYDB_NAT_MASK;
    *quotient = JAYDB_NAT_SMALL(x / y); *remainder = JAYDB_NAT_SMALL(x % y);
    return;
  }
  if (jaydb_nat_compare(e, a, b) < 0) {
    term_sink(e, b);
    *quotient = JAYDB_NAT_ZERO; *remainder = a;
    return;
  }
  u64 an = jaydb_nat_length(e, a), bn = jaydb_nat_length(e, b);
  Term q = jaydb_nat_new(e, an), r = jaydb_nat_new(e, bn + 1);
  for (u64 bit = an * 32; bit; --bit) {
    u64 carry = (jaydb_nat_get(e, a, (bit - 1) / 32) >> ((bit - 1) % 32)) & 1;
    int order = 0;
    for (u64 i = 0; i <= bn; ++i) {
      u64 shifted = ((u64)jaydb_nat_get(e, r, i) << 1) | carry;
      u32 x = (u32)shifted, y = i < bn ? jaydb_nat_get(e, b, i) : 0;
      carry = shifted >> 32;
      jaydb_nat_put(e, r, i, x);
      if (x != y) order = x > y ? 1 : -1;
    }
    if (order >= 0) {
      u64 borrow = 0;
      for (u64 i = 0; i <= bn; ++i) {
        u64 x = jaydb_nat_get(e, r, i), y = borrow + (u64)(i < bn ? jaydb_nat_get(e, b, i) : 0);
        jaydb_nat_put(e, r, i, (u32)(x - y));
        borrow = x < y;
      }
      u64 index = (bit - 1) / 32;
      jaydb_nat_put(e, q, index, jaydb_nat_get(e, q, index) | (1u << ((bit - 1) % 32)));
    }
  }
  term_sink(e, a); term_sink(e, b);
  *quotient = jaydb_nat_finish(e, q); *remainder = jaydb_nat_finish(e, r);
}

static Term jaydb_nat_div(Env e, Term a, Term b, bool modulo) {
  Term q, r;
  jaydb_nat_divmod(e, a, b, &q, &r);
  term_sink(e, modulo ? q : r);
  return modulo ? r : q;
}

static u32 jaydb_nat_to_u32(Env e, Term n) {
  u32 value = jaydb_nat_get(e, n, 0);
  term_sink(e, n);
  return value;
}

static Term jaydb_nat_pow(Env e, Term a, Term b) {
  if (jaydb_nat_is_zero(b)) { term_sink(e, a); return JAYDB_NAT_SMALL(1); }
  if (jaydb_nat_is_zero(a) || a == JAYDB_NAT_SMALL(1)) { term_sink(e, b); return a; }
  u64 length = jaydb_nat_length(e, b);
  u64 bits = (length - 1) * 32 + 32 - CLZ(jaydb_nat_get(e, b, length - 1));
  Term result = JAYDB_NAT_SMALL(1), base = a;
  for (u64 bit = 0; bit < bits; ++bit) {
    if ((jaydb_nat_get(e, b, bit / 32) >> (bit % 32)) & 1) {
      base = term_keep(e, base, 1);
      result = jaydb_nat_mul(e, result, base);
    }
    if (bit + 1 < bits) {
      base = term_keep(e, base, 1);
      base = jaydb_nat_mul(e, base, base);
    }
  }
  term_sink(e, base); term_sink(e, b);
  return result;
}

static u32 jaydb_nat_u32_pow(Env e, u32 base, Term n) {
  u64 length = jaydb_nat_length(e, n);
  u32 result = 1;
  for (u64 i = 0; i < length; ++i) {
    u32 limb = jaydb_nat_get(e, n, i);
    for (unsigned bit = 0; bit < 32; ++bit) {
      if ((limb >> bit) & 1) result *= base;
      base *= base;
    }
  }
  term_sink(e, n);
  return result;
}

static u32 jaydb_nat_u32_shift(Env e, u32 value, Term n, bool right) {
  u32 out = 0;
  if (jaydb_nat_immediate(n) && (n & JAYDB_NAT_MASK) < 32) {
    unsigned shift = (unsigned)(n & JAYDB_NAT_MASK);
    out = right ? value >> shift : value << shift;
  }
  term_sink(e, n);
  return out;
}
