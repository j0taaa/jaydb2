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
    if (cid == CID(Inconsistente) || n != 1 || term_tag(result) != TAG_CTR)
      err_fail("JayDB iteration result is invalid");
    Term value;
    spare_free(e, cls_fit(1), ctr_take(e, result, 1, &value));
    if (cid == CID(Continuar) || cid == CID(Preparar)) {
      state = value;
    } else if (cid == CID(Encerrar)) {
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
