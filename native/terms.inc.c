/* CPU1 Terms have independent metadata and payload words. Every addressable
 * CID/FID table index fits u64: even a one-byte entry cannot have 2^64 elements
 * in this 64-bit process. There is no 16-bit (or configurable) ID quota.
 * The payload/tag/RFC layout is retained for compact Nat and legacy offsets.
 * Heap slots and the Term stack store the WHOLE Term, including static Terms.
 * No Term crosses the public bytes-only ABI.
 */
#define term_make(tag, aux, loc) \
  (((Term)(u64)(aux) << 64) | ((Term)(tag) << 56) | (Term)(loc))

#define term_ctr(cid, loc) term_make(TAG_CTR, cid, loc)
#define term_pak(cid, loc) term_make(TAG_PAK, cid, loc)
#define term_clo(fid, loc) term_make(TAG_CLO, fid, loc)
#define term_tsk(fid, loc) term_make(TAG_TSK, fid, loc)

INLINE Term term_blk(bool arr, u32 cls, u64 loc) {
  return term_make(arr ? TAG_ARR : TAG_BUF, cls, loc);
}

INLINE u64 term_tag(Term t) { return (u64)(t >> 56) & 0x7f; }
INLINE bool term_rfc(Term t) { return (t & RFC_BIT) != 0; }
INLINE u64 term_aux(Term t) { return (u64)(t >> 64); }
INLINE u64 term_loc(Term t) { return (u64)t & LOC_MASK; }
