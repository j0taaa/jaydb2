/* Only interprets Exchange/Stop. Decisions and continuations belong to Bend.
 * Binary RPC uses the controller's private pipes, never client stdout. */
static void host_exact(FILE* f, char* p, size_t n, int writing) {
  while (n) {
    size_t k = writing ? fwrite(p, 1, n, f) : fread(p, 1, n, f);
    if (!k) err_fail("Bend host adapter pipe failed");
    p += k; n -= k;
  }
}
static Term host_apply(Env e, Term f, Term x) {
  u64 at = task_node(e, FID(Clo~apply), TERM_HOLE, 0, 0);
  e.mem[at] = f; e.mem[at + 1] = x;
  return corpus_eval(e.mem, term_tsk(FID(Clo~apply), at));
}
static Term host_drive(Env e, Term* fields, IoWork* work) {
  (void)work;
  Term step = fields[0], state = fields[1];
  for (;;) {
    Term task = host_apply(e, step, state), values[2];
    u32 cid = (u32)term_aux(task);
    if (term_tag(task) != TAG_CTR && term_tag(task) != TAG_PAK) err_fail("Bend host invalid task");
    // The checked step returns Tasks.Task: its unary constructor is Stop,
    // its binary constructor is Exchange. No compiler ID/namespace guessing.
    u32 arity = cid_arity(cid);
    if (arity == 1) {
      if (term_tag(task) == TAG_PAK) values[0] = term_loc(task);
      else spare_free(e, cls_fit(1), ctr_take(e, task, 1, values));
      exit((int)(u32)values[0]);
    }
    if (arity != 2) err_fail("Bend host unknown task");
    spare_free(e, cls_fit(2), ctr_take(e, task, 2, values));
    uint64_t size = 0;
    char* data = io_cbuf(e, values[0], &size, CID(Con));
    if (!data) err_fail("Bend host non-byte command");
    unsigned char header[8];
    for (int i = 0; i < 8; ++i) header[7-i] = (unsigned char)(size >> (8*i));
    host_exact(stdout, (char*)header, 8, 1);
    host_exact(stdout, data, size, 1); free(data);
    if (fflush(stdout)) err_fail("Bend host adapter flush failed");
    host_exact(stdin, (char*)header, 8, 0);
    size = 0;
    for (int i = 0; i < 8; ++i) size = (size << 8) | header[i];
    if (size > SIZE_MAX) err_fail("Bend host reply not addressable");
    data = io_mem(malloc(size ? size : 1));
    host_exact(stdin, data, size, 0);
    Term reply = io_list(e, data, size); free(data);
    state = host_apply(e, values[1], reply);
  }
}
static void __attribute__((constructor)) host_drive_use(void) {
  io_eff(CID(drive), host_drive);
}
