/* JayDB application effects, registered through Bend 2's official foreign API.
 * The compiler and its emitted runtime are used verbatim.
 */
#ifdef CID(read)
static Term jaydb_read(Env e, Term* fields, IoWork* work) {
  (void)fields; (void)work;
  size_t used = 0, capacity = 65536;
  char* data = io_mem(malloc(capacity));
  for (;;) {
    if (used == capacity) {
      if (capacity > SIZE_MAX / 2) err_fail("JayDB input is not addressable");
      capacity *= 2;
      data = io_mem(realloc(data, capacity));
    }
    size_t n = fread(data + used, 1, capacity - used, stdin);
    used += n;
    if (!n) {
      if (ferror(stdin)) err_fail("JayDB input read failed");
      break;
    }
  }
  Term result = io_list(e, data, used);
  free(data);
  return result;
}
static void __attribute__((constructor)) jaydb_read_use(void) {
  io_eff(CID(read), jaydb_read);
}
#endif

#ifdef CID(Con)
static Term jaydb_output(Env e, Term bytes) {
  uint64_t n = 0;
  char* data = io_cbuf(e, bytes, &n, CID(Con));
  if (!data) err_fail("JayDB output contains a non-octet");
  io_out(stdout, data, n);
  free(data);
  return term_pak(CID(Unit), 0);
}
#endif

#ifdef CID(write)
static Term jaydb_write(Env e, Term* fields, IoWork* work) {
  (void)work;
  return jaydb_output(e, fields[0]);
}
static void __attribute__((constructor)) jaydb_write_use(void) {
  io_eff(CID(write), jaydb_write);
}
#endif

// JayDB iteration effect (only the execution entry imports this section).
#ifdef CID(loop)
static Term jaydb_loop_run(Env e, Term* fields, IoWork* work) {
  (void)work;
  Term step = fields[0], state = fields[1];
  if (term_tag(step) != TAG_CLO || term_loc(step) != 0 || term_rfc(step)
      || fid_arity((u32)term_aux(step)) != 1)
    err_fail("JayDB iteration step must be closed");
  for (;;) {
    u64 at = task_node(e, FID(Clo~apply), TERM_HOLE, 0, 0);
    e.mem[at] = step;
    e.mem[at + 1] = state;
    Term result = corpus_eval(e.mem, term_tsk(FID(Clo~apply), at));
    u32 cid = (u32)term_aux(result), n = cid_arity(cid);
    if (cid == CID(Inconsistent) || n != 1 || term_tag(result) != TAG_CTR)
      err_fail("JayDB iteration result is invalid");
    Term value;
    spare_free(e, cls_fit(1), ctr_take(e, result, 1, &value));
    if (cid == CID(Continue) || cid == CID(Prepare)) {
      state = value;
    } else if (cid == CID(FinishOutput)) {
      return jaydb_output(e, value);
    } else {
      err_fail("JayDB iteration constructor is invalid");
    }
  }
}
static void __attribute__((constructor)) jaydb_loop_use(void) {
  io_eff(CID(loop), jaydb_loop_run);
}
#endif

// JayDB framed execution effect.
#ifdef CID(serve)
static bool jaydb_read_frame(Env e, Term* bytes, bool request) {
  unsigned char header[8];
  size_t got = fread(header, 1, sizeof(header), stdin);
  if (got == 0 && request && feof(stdin) && !ferror(stdin)) return false;
  if (got != sizeof(header)) err_fail("JayDB truncated live frame header");

  uint64_t remaining = 0;
  for (size_t i = 0; i < sizeof(header); ++i)
    remaining = (remaining << 8) | header[i];
  if (remaining > SIZE_MAX) err_fail("JayDB live frame is not addressable");

  // Grow only as bytes arrive. An incomplete frame cannot force allocation
  // of the size declared in its header.
  char chunk[65536];
  char* data = NULL;
  size_t length = 0, capacity = 0, total = (size_t)remaining;
  while (remaining) {
    size_t part = remaining < sizeof(chunk) ? (size_t)remaining : sizeof(chunk);
    if (fread(chunk, 1, part, stdin) != part)
      err_fail("JayDB truncated live frame body");
    if (part > capacity - length) {
      capacity = capacity <= total / 2 ? capacity * 2 : total;
      if (capacity < length + part) capacity = length + part;
      data = io_mem(realloc(data, capacity));
    }
    memcpy(data + length, chunk, part);
    length += part;
    remaining -= part;
  }
  *bytes = io_list(e, data, length);
  free(data);
  return true;
}

static void jaydb_write_frame(Env e, Term bytes) {
  u64 length;
  char* data = io_cbuf(e, bytes, &length, CID(Con));
  if (!data) err_fail("JayDB live frame contains a non-octet");
  char header[8];
  for (size_t i = 0; i < sizeof(header); ++i)
    header[i] = (char)(length >> (8 * (sizeof(header) - 1 - i)));
  io_out(stdout, header, sizeof(header));
  io_out(stdout, data, length);
  io_sync();
  free(data);
}

static Term jaydb_apply(Env e, Term function, Term argument) {
  u64 at = task_node(e, FID(Clo~apply), TERM_HOLE, 0, 0);
  e.mem[at] = function;
  e.mem[at + 1] = argument;
  return corpus_eval(e.mem, term_tsk(FID(Clo~apply), at));
}

static Term jaydb_serve(Env e, Term* fields, IoWork* work) {
  (void)work;
  Term entry = fields[0], bytes;
  bool single = term_aux(fields[1]) == CID(True);
  if (term_tag(entry) != TAG_CLO || term_loc(entry) != 0 || term_rfc(entry)
      || fid_arity((u32)term_aux(entry)) != 1)
    err_fail("JayDB live entry must be closed");
  while (jaydb_read_frame(e, &bytes, true)) {
    Term result = jaydb_apply(e, entry, io_box(e, CID(RequestFrame), bytes));
    while (term_tag(result) == TAG_CTR && term_aux(result) == CID(AskFrame)) {
      Term ask[2], reply;
      spare_free(e, cls_fit(2), ctr_take(e, result, 2, ask));
      jaydb_write_frame(e, ask[0]);
      jaydb_read_frame(e, &reply, false);
      result = jaydb_apply(e, entry, io_node(e, CID(ReplyFrame), ask[1], reply));
    }
    if (term_tag(result) != TAG_CTR || term_aux(result) != CID(FinalFrame))
      err_fail("JayDB live iteration is inconsistent");
    spare_free(e, cls_fit(1), ctr_take(e, result, 1, &bytes));
    jaydb_write_frame(e, bytes);
    if (single) break;
  }
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) jaydb_serve_use(void) {
  io_eff(CID(serve), jaydb_serve);
}
#endif
