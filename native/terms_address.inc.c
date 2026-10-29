/* Independent machine words for location, ID and tag. The scalar has spare
 * bits for pointer-reversal frames, not a packed-address/numeric quota.
 * Each slot is sizeof(Term)=24 bytes; uint64 offsets cover every addressable
 * slot in a 64-bit process. Only bytes cross the ABI.
 */
_Static_assert(sizeof(Term) == 24, "address-word carrier layout");
_Static_assert(UINT64_MAX / sizeof(Term) < (1ull << 60), "GC counts cover every physically addressable slot");
#define JAYDB_GC_COUNT_MASK ((1ull << 60) - 1)
#define term_make(tag, aux, loc) \
  (((Term)(tag) << 128) | ((Term)(u64)(aux) << 64) | (Term)(u64)(loc))
#define term_ctr(cid, loc) term_make(TAG_CTR, cid, loc)
#define term_pak(cid, loc) term_make(TAG_PAK, cid, loc)
#define term_clo(fid, loc) term_make(TAG_CLO, fid, loc)
#define term_tsk(fid, loc) term_make(TAG_TSK, fid, loc)
INLINE Term term_blk(bool arr, u32 cls, u64 loc) {
  return term_make(arr ? TAG_ARR : TAG_BUF, cls, loc);
}
INLINE u64 term_tag(Term t) { return (u64)(t >> 128) & 0x7f; }
INLINE bool term_rfc(Term t) { return (t & RFC_BIT) != 0; }
INLINE u64 term_aux(Term t) { return (u64)(t >> 64); }
INLINE u64 term_loc(Term t) { return (u64)t; }
