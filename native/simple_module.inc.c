/* Synchronous CPU1 evaluation on the caller's main grow-down stack. */
static Term *jaydb_terms;
static u64 jaydb_register_capacity;
static atomic_flag jaydb_busy = ATOMIC_FLAG_INIT;
static atomic_bool jaydb_poisoned;
static _Atomic uint64_t jaydb_live_lease;
static uint64_t jaydb_lease_sequence;

static void jaydb_unmap(void *pointer, uint64_t bytes) {
  if (munmap(pointer, bytes)) {
    jaydb_cleanup_failed = true;
    jaydb_runtime_code = errno;
  }
}

static void jaydb_resize(void *owner, uint64_t *capacity, uint64_t bytes) {
  void *previous, *mapped;
  memcpy(&previous, owner, sizeof previous);
  if (!bytes || bytes % 4096 || bytes < *capacity)
    jaydb_abort(JAYDB_RUNTIME, 0);
  if (previous)
    mapped = mremap(previous, *capacity, bytes, MREMAP_MAYMOVE);
  else
    mapped = mmap(NULL, bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (mapped == MAP_FAILED) jaydb_abort(JAYDB_SYSTEM, errno);
  memcpy(owner, &mapped, sizeof mapped);
  *capacity = bytes;
}

static Term corpus_eval(Term *H, Term t) {
  Env e = { H, ALC[0] };
  Term result[WL_RESW];
  do {
    t = work_loop(e, jaydb_terms, t, 1);
    if (t && (u64)H[task_tail(t) + 1]) jaydb_abort(JAYDB_RUNTIME, 0);
  } while (t);
  if (!root_done(H)) jaydb_abort(JAYDB_RUNTIME, 0);
  u32 n = root_take(H, result);
  if (n != 1) jaydb_abort(JAYDB_RUNTIME, 0);
  return result[0];
}

static Term jaydb_node(Env e, uint64_t cid, Term a, Term b) {
  uint64_t loc = heap_alloc(e, 1);
  e.mem[loc] = cid_hot(cid) ? rfc_seal(e, a) : a;
  e.mem[loc + 1] = cid_hot(cid) ? rfc_seal(e, b) : b;
  return term_ctr(cid, loc);
}

static Term jaydb_input(Env e, const struct jaydb_simple_request *r) {
  Term xs = term_pak(CID_Nil, 0);
  for (uint64_t i = r->input_len; i; --i) xs = jaydb_node(e, CID_Con, r->input[i - 1], xs);
  return xs;
}

static uint64_t jaydb_output(Env e, Term xs, const struct jaydb_simple_request *r) {
  uint64_t n = 0;
  while (term_aux(xs) == CID_Con) {
    Term f[2];
    spare_free(e, 1, ctr_take(e, xs, 2, f));
    if (f[0] > 255) jaydb_abort(JAYDB_RUNTIME, 0);
    if (n == r->output_capacity) jaydb_abort(JAYDB_OUTPUT, 0);
    jaydb_owned_byte(n++, (uint8_t)f[0]);
    xs = f[1];
  }
  if (term_aux(xs) != CID_Nil) jaydb_abort(JAYDB_RUNTIME, 0);
  term_sink(e, xs);
  return n;
}

static Term jaydb_apply(Env e, Term function, Term argument) {
  u64 at = task_node(e, FID_Clo_apply, TERM_HOLE, 0, 0);
  e.mem[at] = function;
  e.mem[at + 1] = argument;
  return corpus_eval(e.mem, term_tsk(FID_Clo_apply, at));
}

/* No evaluator is active here. Its register-bank prefix contains only stale
 * temporaries, so temporary storage can hold effect/iteration fields.
 * The fields are consumed before the next apply resets the bank. */
static Term *jaydb_fields(Env e, Term value, u64 n) {
  Term *fields = jaydb_fields_storage(n);
  if (term_tag(value) == TAG_PAK) fields[0] = term_loc(value);
  else spare_free(e, cls_fit(n), ctr_take(e, value, n, fields));
  return fields;
}

#if JAYDB_LOOP_ENABLED
static Term jaydb_state(Env e, Term *fields, u64 n) {
  // EstadoExecucao is a product. The official emitter flattens its fields in
  // effect/iteration constructors, but Clo_apply takes a BOX argument.
  if (n == 1) return fields[0]; /* generic Native.Iteracao<A> stores a BOX */
#if JAYDB_STATE_ENABLED
  if (n != cid_arity(JAYDB_STATE_CID) || n < 2) jaydb_abort(JAYDB_INVARIANT, 0);
  u64 at = heap_alloc(e, cls_fit(n));
  for (u64 i = 0; i < n; ++i)
    e.mem[at + i] = cid_hot(JAYDB_STATE_CID) ? rfc_seal(e, fields[i]) : fields[i];
  return term_ctr(JAYDB_STATE_CID, at);
#else
  jaydb_abort(JAYDB_INVARIANT, 0);
#endif
}

static uint64_t jaydb_loop(Env e, Term step, Term initial, const struct jaydb_simple_request *r) {
  u64 fid = term_aux(step);
  if (term_tag(step) != TAG_CLO || term_rfc(step) || term_loc(step) != 0
      || fid >= sizeof FID_T / sizeof *FID_T || fid_arity(fid) != 1)
    jaydb_abort(JAYDB_CAPTURED_STEP, 0);
  if (jaydb_stage == JAYDB_SETUP) jaydb_enter_stage(JAYDB_EXECUTION);
  if (jaydb_stage != JAYDB_EXECUTION) jaydb_abort(JAYDB_INVARIANT, 0);
  Term state = initial;
  for (;;) {
    // Reusing this token duplicates no affine capture: its environment is zero.
    // The state is transferred once into the apply task, never kept/copied here.
    Term iteration = jaydb_apply(e, step, state);
    u64 cid = term_aux(iteration);
    u64 n = cid_arity(cid);
    if (cid == JAYDB_INCONSISTENT_CID) jaydb_abort(JAYDB_INVARIANT, 0);
    if (term_tag(iteration) != TAG_CTR || !n) jaydb_abort(JAYDB_INVARIANT, 0);
    Term *fields = jaydb_fields(e, iteration, n);
    if (cid == JAYDB_CONTINUE_CID) {
      state = jaydb_state(e, fields, n);
#if JAYDB_PREPARE_ENABLED
    } else if (cid == JAYDB_PREPARE_CID) {
      state = jaydb_state(e, fields, n);
      jaydb_enter_stage(JAYDB_PREPARATION);
#endif
    } else if (cid == JAYDB_FINISH_CID && n == 1) {
      return jaydb_output(e, fields[0], r);
    } else jaydb_abort(JAYDB_INVARIANT, 0);
  }
}
#endif

static uint64_t jaydb_evaluate(const struct jaydb_simple_request *r) {
  Env e = { CORPUS, ALC[0] };
  if (cid_arity(CID_Con) != 2 || cid_arity(CID_Nil) != 0) jaydb_abort(JAYDB_RUNTIME, 0);
  Term cont = corpus_eval(CORPUS, term_tsk(MAIN_FID, task_node(e, MAIN_FID, TERM_HOLE, 0, 0)));
  Term item = term_clo(FID_IO_emit, 0);
  uint64_t length = 0;
  bool written = false;
  bool loop_used = false;
  for (;;) {
    uint64_t loc = task_node(e, FID_Clo_apply, TERM_HOLE, 0, 0);
    e.mem[loc] = cont;
    e.mem[loc + 1] = item;
    Term req = corpus_eval(CORPUS, term_tsk(FID_Clo_apply, loc));
    uint64_t cid = term_aux(req);
    if (cid == CID_Emit) {
      term_sink(e, req);
      if (!written) jaydb_abort(JAYDB_EFFECT, 0);
      return length;
    }
    uint64_t n = cid_arity(cid);
    if (!n) jaydb_abort(JAYDB_EFFECT, 0);
    Term *fields = jaydb_fields(e, req, n);
    cont = fields[n - 1];
    if (JAYDB_INPUT_ENABLED && cid == JAYDB_INPUT_CID && n == 1) {
      item = jaydb_input(e, r);
    } else if (JAYDB_OUTPUT_ENABLED && cid == JAYDB_OUTPUT_CID && n == 2 && !written) {
      length = jaydb_output(e, fields[0], r);
      written = true;
      item = term_pak(CID_Unit, 0);
#if JAYDB_ENTER_ENABLED
    } else if (cid == JAYDB_ENTER_CID && n == 2 && fields[0] <= JAYDB_PREPARATION) {
      jaydb_enter_stage(fields[0]);
      item = term_pak(CID_Unit, 0);
#endif
#if JAYDB_LOOP_ENABLED
    } else if (cid == JAYDB_LOOP_CID && n >= 3 && !written && !loop_used) {
      loop_used = true;
      Term state = jaydb_state(e, fields + 1, n - 2);
      length = jaydb_loop(e, fields[0], state, r);
      written = true;
      item = term_pak(CID_Unit, 0);
#endif
    } else jaydb_abort(JAYDB_EFFECT, 0);
  }
}

#include <sys/resource.h>
#include <sys/syscall.h>

static void jaydb_execute(const struct jaydb_simple_request *request,
                          struct jaydb_simple_result *result) {
  if (JAYDB_REGISTER_WORDS > (SIZE_MAX - 4095) / sizeof(Term))
    jaydb_abort(JAYDB_SYSTEM, EOVERFLOW);
  u64 register_bytes = (JAYDB_REGISTER_WORDS * sizeof(Term) + 4095) & ~4095ull;
  jaydb_resize(&jaydb_terms, &jaydb_register_capacity, register_bytes);
  memset(ALC, 0, sizeof ALC);
  memset(jaydb_free, 0, sizeof jaydb_free);
  jaydb_heap_words = SIZE_MAX / sizeof(Term); /* address arithmetic, no resource quota */
  jaydb_arena_ensure(0, HEAP_OFF);
  CORPUS = jaydb_heap_cell(NULL, 0);
  jaydb_heap_next = HEAP_OFF;
  for (u64 i = 0; i < STAT_LEN; ++i) CORPUS[STAT_OFF + i] = STAT_IMG[i];
  result->output_len = jaydb_evaluate(request);
}

static const struct jaydb_simple_descriptor jaydb_descriptor_v6 = {
  6, sizeof(struct jaydb_simple_descriptor), sizeof(struct jaydb_simple_request),
  sizeof(struct jaydb_simple_result), JAYDB_CPU1_GPU_OFF, sizeof(Term),
  JAYDB_SOURCE_HASH, JAYDB_BUILD_ID
};

__attribute__((visibility("default")))
const struct jaydb_simple_descriptor *jaydb_native_describe_v6(void) { return &jaydb_descriptor_v6; }

__attribute__((visibility("default")))
uint32_t jaydb_native_run_v6(const struct jaydb_simple_request *request,
                            struct jaydb_simple_result *result) {
  if (!result) return JAYDB_ARGUMENT;
  *result = (struct jaydb_simple_result){ .status=JAYDB_ARGUMENT };
  if (!request || request->abi_version != 6 || request->size != sizeof *request
      || (request->input_len && !request->input) || request->input_len > SIZE_MAX)
    return result->status;
  struct rlimit stack;
  if (syscall(SYS_gettid) != getpid() || getrlimit(RLIMIT_STACK, &stack)
      || stack.rlim_cur != RLIM_INFINITY) {
    result->runtime_code=EPERM;
    return result->status;
  }
  if (atomic_flag_test_and_set(&jaydb_busy)) return result->status=JAYDB_BUSY;
  if (atomic_load(&jaydb_poisoned)) {
    atomic_flag_clear(&jaydb_busy);
    return result->status=JAYDB_SYSTEM;
  }
  jaydb_status=JAYDB_OK; jaydb_runtime_code=0; jaydb_stage=JAYDB_SETUP;
  jaydb_cleanup_failed=false;
  if (!setjmp(jaydb_escape)) jaydb_execute(request, result);
  jaydb_arena_clear();
  jaydb_term_stack_clear();
  if (jaydb_terms) jaydb_unmap(jaydb_terms, jaydb_register_capacity);
  jaydb_terms=NULL; jaydb_register_capacity=0; CORPUS=NULL;
  if (jaydb_cleanup_failed) jaydb_status=JAYDB_SYSTEM;
  if (!jaydb_status && jaydb_lease_sequence == UINT64_MAX)
    { jaydb_status=JAYDB_SYSTEM; jaydb_runtime_code=EOVERFLOW; }
  if (jaydb_status) {
    if (jaydb_owned_output) jaydb_unmap(jaydb_owned_output, jaydb_owned_capacity);
    jaydb_owned_output=NULL; jaydb_owned_capacity=0;
    if (jaydb_cleanup_failed) jaydb_status=JAYDB_SYSTEM;
    result->output_len=0;
    if (jaydb_status != JAYDB_OUTPUT) atomic_store(&jaydb_poisoned, true);
    atomic_flag_clear(&jaydb_busy);
  } else {
    result->output=jaydb_owned_output;
    result->output_capacity=jaydb_owned_capacity;
    result->lease=++jaydb_lease_sequence;
    atomic_store(&jaydb_live_lease, result->lease);
  }
  result->status=jaydb_status;
  result->runtime_code=jaydb_runtime_code;
  result->stage=jaydb_stage;
  return result->status;
}

__attribute__((visibility("default")))
uint32_t jaydb_native_release_v6(uint64_t lease) {
  if (!lease || !atomic_compare_exchange_strong(&jaydb_live_lease, &lease, 0))
    return JAYDB_ARGUMENT;
  if (jaydb_owned_output && munmap(jaydb_owned_output, jaydb_owned_capacity)) {
    atomic_store(&jaydb_live_lease, lease);
    atomic_store(&jaydb_poisoned, true);
    return JAYDB_SYSTEM;
  }
  jaydb_owned_output=NULL; jaydb_owned_capacity=0;
  atomic_flag_clear(&jaydb_busy);
  return JAYDB_OK;
}
