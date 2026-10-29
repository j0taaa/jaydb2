/* CPU1 pointer-reversal collector with actual field counts, not arity bytes or
 * the old 240+log2 encoding. A frame fits one Term: loc/i/n use 40 bits each
 * and class uses 6. Those counts cover every node in the CURRENT offset40
 * arena. The offset limitation remains explicit and is addressed separately.
 * No collector stack allocation or new resource quota is introduced.
 */
FAR void term_drop(Env e, Term t) {
  Term *H = e.mem, cur = 0, first = 0;
  for (;;) {
    if (!term_triv(t) && term_rfc(t)) {
      u64 r = term_loc(t), count = (u64)H[r] & RFC_CNT;
      if (count == RFC_CNT || count > 1) {
        if (count != RFC_CNT) H[r] -= 1;
        t = 0;
      } else {
        t = (t & ~(Term)(RFC_BIT | LOC_MASK)) | (H[r] >> 24);
        heap_free(e, 0, r);
      }
    }
    if (!term_triv(t)) {
      u64 tag = term_tag(t);
      if (tag == TAG_NAT_BIG) {
        jaydb_nat_free(e, t);
      } else if (tag == TAG_BUF) {
        heap_free(e, blk_span(t), term_loc(t));
      } else {
        u64 aux = term_aux(t), loc = term_loc(t);
        u64 n = tag == TAG_ARR ? (1ull << blk_cls(t))
          : tag == TAG_CTR ? cid_arity(aux) : fid_arity(aux) - (tag == TAG_CLO);
        u32 cls = cls_fit(tag == TAG_TSK ? n + 2 : n);
        u64 spine = tag == TAG_CTR ? CID_T[aux].spine : 0;
        if (spine) {
          Term last = H[loc + n - 1];
          H[loc + n - 1] = H[loc + n - 1 - spine];
          H[loc + n - 1 - spine] = last;
        }
        u64 live = n;
        while (live && term_triv(H[loc + live - 1])) --live;
        first = live ? H[loc] : 0;
        H[loc] = cur;
        cur = (Term)loc | ((Term)live << 80) | ((Term)cls << 120);
      }
    }
    for (;;) {
      if (!cur) return;
      u64 loc = (u64)cur & LOC_MASK, i = (u64)(cur >> 40) & LOC_MASK;
      u64 n = (u64)(cur >> 80) & LOC_MASK;
      u32 cls = (u32)(cur >> 120);
      Term child = i == 0 ? first : H[loc + i];
      if (i + 1 >= n) {
        cur = H[loc];
        heap_free(e, cls, loc);
      } else cur += (Term)1 << 40;
      if (!term_triv(child)) { t = child; break; }
    }
  }
}
