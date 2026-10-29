/* Appended to the official emitted segments; never includes foreign C effects.
 * All evaluation is sequential (seq=1), including Bend's parallel lets.
 */
#include "guard.h"
#include <errno.h>
#include <limits.h>

static Term *jaydb_terms;
static uint64_t jaydb_terms_words;
static atomic_flag jaydb_busy = ATOMIC_FLAG_INIT;
static _Atomic uint64_t jaydb_last_preparation_started;

static Term *jaydb_stack_at(Term *p, int64_t offset, bool one_past) {
  uintptr_t base = (uintptr_t)jaydb_terms, at = (uintptr_t)p;
  uint64_t size = jaydb_terms_words * sizeof(Term);
  if (at < base || at - base > size) jaydb_abort(JAYDB_RUNTIME, 0);
  int64_t index = (int64_t)((at - base) / sizeof(Term));
  if (offset < -index || offset > (int64_t)jaydb_terms_words - index)
    jaydb_abort(JAYDB_MEMORY, 0);
  uint64_t result = (uint64_t)(index + offset);
  if (!one_past && result == jaydb_terms_words) jaydb_abort(JAYDB_MEMORY, 0);
  return jaydb_terms + result;
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

static Term jaydb_input(Env e, const struct jaydb_native_request *r) {
  Term xs = term_pak(CID_Nil, 0);
  for (uint64_t i = r->input_len; i; --i) xs = jaydb_node(e, CID_Con, r->input[i - 1], xs);
  return xs;
}

static uint64_t jaydb_output(Env e, Term xs, const struct jaydb_native_request *r) {
  uint64_t n = 0;
  while (term_aux(xs) == CID_Con) {
    Term f[2];
    spare_free(e, 1, ctr_take(e, xs, 2, f));
    if (f[0] > 255) jaydb_abort(JAYDB_OUTPUT, 0);
    if (n == r->output_capacity) jaydb_abort(JAYDB_OUTPUT, 0);
    if (jaydb_segmented) jaydb_owned_byte(n++, (uint8_t)f[0]);
    else r->output[n++] = (uint8_t)f[0];
    xs = f[1];
  }
  if (term_aux(xs) != CID_Nil) jaydb_abort(JAYDB_OUTPUT, 0);
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
 * temporaries, so the same charged mapping can hold effect/iteration fields.
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

static uint64_t jaydb_loop(Env e, Term step, Term initial, const struct jaydb_native_request *r) {
  u64 fid = term_aux(step);
  if (term_tag(step) != TAG_CLO || term_rfc(step) || term_loc(step) != 0
      || fid >= sizeof FID_T / sizeof *FID_T || fid_arity(fid) != 1)
    jaydb_abort(JAYDB_CAPTURED_STEP, 0);
  if (jaydb_active->stage == JAYDB_SETUP) jaydb_enter_stage(JAYDB_EXECUTION);
  if (jaydb_active->stage != JAYDB_EXECUTION) jaydb_abort(JAYDB_INVARIANT, 0);
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

static uint64_t jaydb_evaluate(const struct jaydb_native_request *r) {
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
      if (!written) jaydb_abort(JAYDB_OUTPUT, 0);
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

struct jaydb_call {
  struct jaydb_native_request request;
  struct jaydb_native_result result;
  struct jaydb_guard guard;
  void *heap;
  uint64_t heap_size;
  bool owned;
};

static void *jaydb_worker(void *arg) {
  struct jaydb_call *call = arg;
  jaydb_guard_bind(&call->guard);
  if (!setjmp(call->guard.escape)) {
    jaydb_poll();
    memset(ALC, 0, sizeof ALC);
    memset(jaydb_free, 0, sizeof jaydb_free);
    jaydb_segmented = call->owned;
    if (call->owned) {
      jaydb_heap_words = UINT64_MAX / sizeof(Term);
      jaydb_arena_ensure(0, HEAP_OFF);
      CORPUS = jaydb_heap_cell(NULL, 0);
    } else {
      CORPUS = call->heap;
      jaydb_heap_words = call->heap_size / sizeof(Term);
    }
    jaydb_heap_next = HEAP_OFF;
    // A fresh anonymous arena is zero initialized. Static constructors are
    // immutable; terms referencing these retain the official static lifetime.
    for (uint64_t i = 0; i < STAT_LEN; ++i) CORPUS[STAT_OFF + i] = STAT_IMG[i];
    call->result.output_len = jaydb_evaluate(&call->request);
    jaydb_poll();
  }
  call->result.status = call->guard.status;
  call->result.runtime_code = call->guard.runtime_code;
  if (call->result.status) call->result.output_len = 0;
  jaydb_guard_bind(NULL);
  return NULL;
}

static const struct jaydb_native_descriptor jaydb_descriptor = {
  JAYDB_NATIVE_ABI, JAYDB_CPU1_GPU_OFF, JAYDB_GENERIC, 1,
  JAYDB_IMAGE_BYTES, JAYDB_MAX_FRAME, JAYDB_SOURCE_HASH
};
static const struct jaydb_native_descriptor jaydb_descriptor_v2 = {
  JAYDB_NATIVE_ABI_STAGES, JAYDB_CPU1_GPU_OFF, JAYDB_GENERIC, 1,
  JAYDB_IMAGE_BYTES, JAYDB_MAX_FRAME, JAYDB_SOURCE_HASH
};

__attribute__((visibility("default")))
const struct jaydb_native_descriptor *jaydb_native_describe_v1(void) { return &jaydb_descriptor; }

__attribute__((visibility("default")))
const struct jaydb_native_descriptor *jaydb_native_describe_v2(void) { return &jaydb_descriptor_v2; }

static uint32_t jaydb_run(const struct jaydb_native_request *request, struct jaydb_native_result *result,
                         uint32_t version, uint64_t execution_ns, uint64_t preparation_ns,
                         struct jaydb_native_result_v2 *stages) {
  if (!result) return JAYDB_ARGUMENT;
  *result = (struct jaydb_native_result){ .status = JAYDB_ARGUMENT };
  if (!request || request->abi_version != version || request->flags != JAYDB_CPU1_GPU_OFF
      || !request->timeout_ns || !request->memory_bytes
      || (request->input_len && !request->input) || (request->output_capacity && !request->output)
      || request->input_len > SIZE_MAX || request->output_capacity > SIZE_MAX) return result->status;
  if (atomic_flag_test_and_set(&jaydb_busy)) return result->status = JAYDB_BUSY;
  struct jaydb_call call = { .request = *request };
  uint64_t now = jaydb_clock(), page = 4096;
  void *heap = MAP_FAILED, *terms = MAP_FAILED, *stack = MAP_FAILED;
  uint64_t tsize = request->term_stack_bytes, ssize = request->native_stack_bytes;
  uint64_t fixed = JAYDB_IMAGE_BYTES;
  call.result.status = JAYDB_ARGUMENT;
  if (!now) { call.result.status = JAYDB_SYSTEM; goto done; }
  call.guard.start = now;
  call.guard.deadline = request->timeout_ns > UINT64_MAX - now ? UINT64_MAX : now + request->timeout_ns;
  call.guard.stage_started = now;
  call.guard.execution_timeout_ns = execution_ns;
  call.guard.preparation_timeout_ns = preparation_ns;
  if (tsize < page || tsize > INT64_MAX || tsize % page || ssize % page
      || ssize < 2 * JAYDB_STACK_MARGIN + PTHREAD_STACK_MIN || ssize > INT64_MAX) goto done;
  // Overflow-safe accounting includes the caller's borrowed byte buffers.
  uint64_t charges[] = { request->input_len, request->output_capacity, tsize, ssize, 2 * page };
  for (size_t i = 0; i < sizeof charges / sizeof *charges; ++i) {
    if (charges[i] > request->memory_bytes || fixed > request->memory_bytes - charges[i]) {
      call.result.status = JAYDB_MEMORY;
      goto done;
    }
    fixed += charges[i];
  }
  call.heap_size = (request->memory_bytes - fixed) & ~(page - 1);
  if (call.heap_size < HEAP_OFF * sizeof(Term) || call.heap_size / sizeof(Term) > LOC_MASK) {
    call.result.status = call.heap_size / sizeof(Term) > LOC_MASK ? JAYDB_RUNTIME : JAYDB_MEMORY;
    goto done;
  }
  call.result.charged_bytes = fixed + call.heap_size;
  heap = mmap(NULL, call.heap_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  terms = mmap(NULL, tsize, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  stack = mmap(NULL, ssize + 2 * page, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (heap == MAP_FAILED || terms == MAP_FAILED || stack == MAP_FAILED) { call.result.status = JAYDB_SYSTEM; goto done; }
  if (mprotect((char *)stack + page, ssize, PROT_READ | PROT_WRITE)) { call.result.status = JAYDB_SYSTEM; goto done; }
  call.heap = heap;
  jaydb_terms = terms;
  jaydb_terms_words = tsize / sizeof(Term);
  jaydb_term_stack.fixed = terms;
  jaydb_term_stack.words = jaydb_terms_words;
  jaydb_term_stack.automatic = false;
  call.guard.stack_low = (uintptr_t)stack + page + JAYDB_STACK_MARGIN;
  call.guard.stack_high = (uintptr_t)stack + page + ssize;
  pthread_attr_t attributes;
  pthread_t worker;
  if (pthread_attr_init(&attributes)) { call.result.status = JAYDB_SYSTEM; goto done; }
  int error = pthread_attr_setguardsize(&attributes, 0);
  if (!error) error = pthread_attr_setstack(&attributes, (char *)stack + page, ssize);
  if (!error) error = pthread_create(&worker, &attributes, jaydb_worker, &call);
  pthread_attr_destroy(&attributes);
  if (error) { call.result.status = JAYDB_SYSTEM; goto done; }
  // No cancellation, process signals, process limits, environment changes, IO,
  // or heap pointers cross the module boundary. The worker exits cooperatively.
  if (pthread_join(worker, NULL)) abort(); /* impossible for this owned thread */
done:
  if (heap != MAP_FAILED) munmap(heap, call.heap_size);
  if (terms != MAP_FAILED) munmap(terms, tsize);
  if (stack != MAP_FAILED) munmap(stack, ssize + 2 * page);
  CORPUS = NULL;
  jaydb_terms = NULL;
  uint64_t end = jaydb_clock();
  call.result.elapsed_ns = now ? end - now : 0;
  // Setup/teardown time belongs to this stage too. Report only elapsed time
  // actually observed; a representation error is never relabelled a timeout.
  if (!call.result.status && end >= call.guard.deadline) {
    call.result.status = JAYDB_TIME;
    call.result.output_len = 0;
  }
  if (stages) {
    if (call.guard.stage_started) call.guard.stage_elapsed[call.guard.stage] += end - call.guard.stage_started;
    stages->stage = call.guard.stage;
    stages->setup_ns = call.guard.stage_elapsed[JAYDB_SETUP];
    stages->execution_ns = call.guard.stage_elapsed[JAYDB_EXECUTION];
    stages->preparation_ns = call.guard.stage_elapsed[JAYDB_PREPARATION];
  }
  *result = call.result;
  atomic_store(&jaydb_last_preparation_started,
    version == JAYDB_NATIVE_ABI_STAGES && call.guard.stage == JAYDB_PREPARATION
      ? call.guard.stage_started : 0);
  atomic_flag_clear(&jaydb_busy);
  return result->status;
}

__attribute__((visibility("default")))
uint64_t jaydb_native_preparation_started_v2(void) {
  return atomic_load(&jaydb_last_preparation_started);
}

__attribute__((visibility("default")))
uint32_t jaydb_native_run_v1(const struct jaydb_native_request *request, struct jaydb_native_result *result) {
  return jaydb_run(request, result, JAYDB_NATIVE_ABI, 0, 0, NULL);
}

__attribute__((visibility("default")))
uint32_t jaydb_native_run_v2(const struct jaydb_native_request_v2 *request, struct jaydb_native_result_v2 *result) {
  if (!result) return JAYDB_ARGUMENT;
  *result = (struct jaydb_native_result_v2){ .base.status = JAYDB_ARGUMENT };
  if (!request || !request->execution_timeout_ns || !request->preparation_timeout_ns) return JAYDB_ARGUMENT;
  return jaydb_run(&request->base, &result->base, JAYDB_NATIVE_ABI_STAGES,
                   request->execution_timeout_ns, request->preparation_timeout_ns, result);
}
