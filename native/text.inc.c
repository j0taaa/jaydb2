/* Only F32.show uses this helper. Its numeric buffer is ASCII, <=40 bytes. */
static Term io_str(Env e, const char *bytes, u64 n) {
  Term s = term_pak(CID_SNil, 0);
  // f32_text produces ASCII only (including nan/inf/exponents).
  while (n) {
    u64 at = heap_alloc(e, 1);
    e.mem[at] = (uint8_t)bytes[--n];
    e.mem[at + 1] = cid_hot(CID_SCon) ? rfc_seal(e, s) : s;
    s = term_ctr(CID_SCon, at);
  }
  return s;
}
