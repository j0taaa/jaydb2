/* Additional owned-byte interface. No Term crosses the boundary. */
#include "abi_accounted.h"
static const struct jaydb_native_descriptor jaydb_descriptor_v3 = {
  JAYDB_NATIVE_ABI_OWNED, JAYDB_CPU1_GPU_OFF, JAYDB_GENERIC, 1,
  JAYDB_IMAGE_BYTES, JAYDB_MAX_FRAME, JAYDB_SOURCE_HASH
};
static _Atomic uint64_t jaydb_live_lease;
static uint64_t jaydb_lease_sequence;

static jaydb_ns jaydb_unpack_ns(struct jaydb_native_ns128 value) {
  return ((jaydb_ns)value.hi << 64) | value.lo;
}
static struct jaydb_native_ns128 jaydb_pack_ns(jaydb_ns value) {
  return (struct jaydb_native_ns128){ (uint64_t)value, (uint64_t)(value >> 64) };
}

__attribute__((visibility("default")))
const struct jaydb_native_descriptor *jaydb_native_describe_v3(void) { return &jaydb_descriptor_v3; }

static uint32_t jaydb_run_owned(const struct jaydb_native_request_v3 *request,
                               struct jaydb_native_result_v3 *result,
                               const struct jaydb_native_ns128 *setup_absolute,
                               const struct jaydb_native_accounted *accounted,
                               struct jaydb_native_accounted_result *accounted_result) {
  if (!result) return JAYDB_ARGUMENT;
  *result = (struct jaydb_native_result_v3){ .status = JAYDB_ARGUMENT };
  if (!request || request->abi_version != JAYDB_NATIVE_ABI_OWNED
      || request->flags != JAYDB_CPU1_GPU_OFF || !JAYDB_GENERIC
      || (!accounted && !request->memory_bytes) || (request->input_len && !request->input)
      || request->input_len > SIZE_MAX
      || (!setup_absolute && !jaydb_unpack_ns(request->setup_timeout_ns))
      || !jaydb_unpack_ns(request->execution_timeout_ns)
      || !jaydb_unpack_ns(request->preparation_timeout_ns)) return result->status;
  uint64_t page = JAYDB_PAGE_BYTES;
  uint64_t tsize = request->term_stack_bytes, ssize = request->native_stack_bytes;
  bool os_main_stack = !ssize;
  if ((tsize && tsize < page) || (!tsize && !JAYDB_LOGICAL_TERMS)
      || tsize > INT64_MAX || tsize % page || ssize % page
      || (!os_main_stack && ssize < 2 * JAYDB_STACK_MARGIN + PTHREAD_STACK_MIN)
      || ssize > INT64_MAX) return result->status;
  if (atomic_flag_test_and_set(&jaydb_busy)) return result->status = JAYDB_BUSY;

  bool automatic_terms = !tsize;
#if JAYDB_LOGICAL_TERMS
  if (automatic_terms) {
    /* The pointer bank has a finite Book-derived extent, independent of the
     * public memory ceiling and continuation depth. It never moves. */
    if (JAYDB_REGISTER_WORDS > (SIZE_MAX - (page - 1)) / sizeof(Term)) {
      atomic_flag_clear(&jaydb_busy);
      return result->status = accounted ? JAYDB_SYSTEM : JAYDB_MEMORY;
    }
    tsize = (JAYDB_REGISTER_WORDS * sizeof(Term) + page - 1) & ~(page - 1);
  }
#endif

  struct jaydb_call call = { .owned = true, .request = {
    .abi_version = JAYDB_NATIVE_ABI_OWNED, .flags = JAYDB_CPU1_GPU_OFF,
    .input = request->input, .input_len = request->input_len,
    .output_capacity = request->output_limit,
    .term_stack_bytes = tsize, .native_stack_bytes = ssize
  } };
  struct jaydb_guard *g = &call.guard;
  void *terms = MAP_FAILED, *stack = MAP_FAILED;
  bool clock_started = false;
  g->accounted=accounted;g->accounted_result=accounted_result;
  if(accounted) {
    jaydb_decoder_progress=(struct jaydb_native_accounted_progress){.abi=1};
    g->accounted_progress=&jaydb_decoder_progress;
  }
  g->wide_time = 1;
  g->os_main_stack = os_main_stack;
  g->stack_error_status = JAYDB_RUNTIME;
  g->stack_error_code = JAYDB_STACK_CAPACITY_CODE;
  g->memory_limit = request->memory_bytes;
  g->stage_budget_wide[JAYDB_SETUP] = jaydb_unpack_ns(request->setup_timeout_ns);
  g->stage_budget_wide[JAYDB_EXECUTION] = jaydb_unpack_ns(request->execution_timeout_ns);
  g->stage_budget_wide[JAYDB_PREPARATION] = jaydb_unpack_ns(request->preparation_timeout_ns);
  jaydb_owned_output = NULL;
  jaydb_owned_capacity = 0;
  if (!jaydb_clock_wide(&g->start_wide)) { call.result.status = JAYDB_SYSTEM; goto done; }
  clock_started = true;
  g->stage_started_wide = g->start_wide;
  if(accounted)jaydb_decoder_progress.sampled_ns=jaydb_pack_ns(g->start_wide);
  jaydb_ns budget=g->stage_budget_wide[JAYDB_SETUP];
  g->stage_deadline_wide[JAYDB_SETUP]=budget>~(jaydb_ns)0-g->start_wide
    ?~(jaydb_ns)0:g->start_wide+budget;
  if (setup_absolute) {
    jaydb_ns absolute = jaydb_unpack_ns(*setup_absolute);
    g->stage_deadline_wide[JAYDB_SETUP]=absolute;
    if (absolute <= g->start_wide) { call.result.status = JAYDB_TIME; goto done; }
    g->stage_budget_wide[JAYDB_SETUP] = absolute - g->start_wide;
  }
  if (os_main_stack) {
    int ready = jaydb_os_main_stack_ready();
    if (ready != 1) {
      call.result.status = ready < 0 ? JAYDB_SYSTEM : JAYDB_ARGUMENT;
      goto done;
    }
  }
  uint64_t borrowed[] = { JAYDB_IMAGE_BYTES, request->input_len };
  for (size_t i = 0; i < sizeof borrowed / sizeof *borrowed; ++i) {
    if (!jaydb_can_charge(g, borrowed[i])) { call.result.status = JAYDB_MEMORY; goto done; }
    jaydb_record_charge(g, borrowed[i]);
  }
  if (tsize) {
    terms = jaydb_map_charged(g, tsize, PROT_READ | PROT_WRITE);
    if (terms == MAP_FAILED) { call.result.status = g->status; goto done; }
  }
  if (!os_main_stack) {
    stack = jaydb_map_charged(g, ssize + 2 * page, PROT_NONE);
    if (stack == MAP_FAILED) { call.result.status = g->status; goto done; }
    if (mprotect((char *)stack + page, ssize, PROT_READ | PROT_WRITE)) {
      call.result.status = JAYDB_SYSTEM;
      goto done;
    }
  }
  jaydb_terms = tsize ? terms : NULL;
  jaydb_terms_words = tsize / sizeof(Term);
  jaydb_term_stack.automatic = automatic_terms;
  jaydb_term_stack.fixed = jaydb_terms;
  jaydb_term_stack.words = jaydb_terms_words;
  if (os_main_stack) {
    /* The trusted host calls on its Linux main grow-down stack with unlimited
     * RLIMIT_STACK. No private C mapping, thread or capacity partition exists.
     * setjmp/longjmp completes inside this synchronous C call before the FFI
     * returns. Global accounting owns observation of actual OS stack growth;
     * local mapping charges do not pretend to include that backing. */
    jaydb_worker(&call);
  } else {
    g->stack_low = (uintptr_t)stack + page + JAYDB_STACK_MARGIN;
    g->stack_high = (uintptr_t)stack + page + ssize;
    pthread_attr_t attributes;
    pthread_t worker;
    if (pthread_attr_init(&attributes)) { call.result.status = JAYDB_SYSTEM; goto done; }
    int error = pthread_attr_setguardsize(&attributes, 0);
    if (!error) error = pthread_attr_setstack(&attributes, (char *)stack + page, ssize);
    if (!error) error = pthread_create(&worker, &attributes, jaydb_worker, &call);
    pthread_attr_destroy(&attributes);
    if (error) { call.result.status = JAYDB_SYSTEM; goto done; }
    if (pthread_join(worker, NULL)) abort();
  }

done:
  /* Existing heap cells and Nat-local pointers remain stable until this point.
   * Cleanup belongs to the last stage; successful output alone survives. */
  jaydb_decoder_cleanup();
  jaydb_arena_clear();
  jaydb_term_stack_clear();
  if (terms != MAP_FAILED) munmap(terms, tsize);
  if (stack != MAP_FAILED) munmap(stack, ssize + 2 * page);
  CORPUS = NULL;
  jaydb_terms = NULL;
  jaydb_ns end = 0;
  bool clock_ended = clock_started && jaydb_clock_wide(&end)
    && end >= g->stage_started_wide && end >= g->start_wide;
  if (clock_started && !clock_ended) call.result.status = JAYDB_SYSTEM;
  if (clock_ended && !call.result.status
      && end - g->stage_started_wide >= g->stage_budget_wide[g->stage])
    call.result.status = JAYDB_TIME;
  if (call.result.status && jaydb_owned_output) {
    munmap(jaydb_owned_output, jaydb_owned_capacity);
    jaydb_owned_output = NULL;
    jaydb_owned_capacity = 0;
    clock_ended = clock_started && jaydb_clock_wide(&end)
      && end >= g->stage_started_wide && end >= g->start_wide;
    if (clock_started && !clock_ended) call.result.status = JAYDB_SYSTEM;
  }
  result->status = call.result.status;
  result->runtime_code = call.result.runtime_code;
  result->stage = g->stage;
  result->charged_bytes = g->memory_peak;
  if (clock_ended) {
    result->elapsed_ns = jaydb_pack_ns(end - g->start_wide);
    g->stage_elapsed_wide[g->stage] += end - g->stage_started_wide;
    for (uint32_t i = 0; i < 3; ++i) result->stage_elapsed_ns[i] = jaydb_pack_ns(g->stage_elapsed_wide[i]);
  }
  if (g->stage == JAYDB_PREPARATION)
    result->preparation_started_ns = jaydb_pack_ns(g->stage_started_wide);
  if(accounted_result && clock_started) {
    accounted_result->timing_flags=1|(clock_ended?2:0);
    accounted_result->stage_started_ns=jaydb_pack_ns(g->stage_started_wide);
    accounted_result->decision_deadline_ns=jaydb_pack_ns(g->stage_deadline_wide[g->stage]);
    if(clock_ended)accounted_result->returned_ns=jaydb_pack_ns(end);
  }
  atomic_store(&jaydb_last_preparation_started, 0);
  if (!result->status) {
    /* A lease occupies the DSO even for an empty output. No allocation is
     * needed to represent an empty buffer. Legal callers release once. */
    if (!++jaydb_lease_sequence) ++jaydb_lease_sequence;
    result->output = jaydb_owned_output;
    result->output_len = call.result.output_len;
    result->output_capacity = jaydb_owned_capacity;
    result->lease = jaydb_lease_sequence;
    atomic_store(&jaydb_live_lease, result->lease);
  } else {
    atomic_flag_clear(&jaydb_busy);
  }
  return result->status;
}

__attribute__((visibility("default")))
uint32_t jaydb_native_run_v3(const struct jaydb_native_request_v3 *request,
                            struct jaydb_native_result_v3 *result) {
  return jaydb_run_owned(request, result, NULL, NULL, NULL);
}

__attribute__((visibility("default")))
uint32_t jaydb_native_run_deadline_v3(const struct jaydb_native_request_v3 *request,
                                    struct jaydb_native_result_v3 *result,
                                    const struct jaydb_native_ns128 *setup_absolute) {
  if (!setup_absolute) {
    if (result) *result = (struct jaydb_native_result_v3){ .status = JAYDB_ARGUMENT };
    return JAYDB_ARGUMENT;
  }
  return jaydb_run_owned(request, result, setup_absolute, NULL, NULL);
}

__attribute__((visibility("default")))
uint32_t jaydb_native_release_v3(uint64_t lease) {
  if (!lease || !atomic_compare_exchange_strong(&jaydb_live_lease, &lease, 0)) return JAYDB_ARGUMENT;
  if (jaydb_owned_output && munmap(jaydb_owned_output, jaydb_owned_capacity)) {
    atomic_store(&jaydb_live_lease, lease);
    return JAYDB_SYSTEM;
  }
  jaydb_owned_output = NULL;
  jaydb_owned_capacity = 0;
  atomic_flag_clear(&jaydb_busy);
  return JAYDB_OK;
}

__attribute__((visibility("default")))
uint32_t jaydb_native_run_accounted_v3(const struct jaydb_native_request_v3 *request,
    const struct jaydb_native_accounted *host,struct jaydb_native_accounted_result *out) {
  if(!out)return JAYDB_ARGUMENT;
  *out=(struct jaydb_native_accounted_result){0};
  out->native.status=JAYDB_ARGUMENT;
  if(!host || host->abi!=JAYDB_ACCOUNTED_ABI || !(host->scope.lo|host->scope.hi)
      || !JAYDB_ACCOUNTED_ENTRY_COVERAGE)return out->native.status;
  struct jaydb_native_ns128 epoch={host->deadline_ns[0].lo,host->deadline_ns[0].hi};
  return jaydb_run_owned(request,&out->native,&epoch,host,out);
}

__attribute__((visibility("default")))
const struct jaydb_native_accounted_descriptor *jaydb_native_describe_accounted_v3(void) {
  static const struct jaydb_native_accounted_descriptor d={JAYDB_ACCOUNTED_ABI,
    sizeof(struct jaydb_native_accounted),sizeof(struct jaydb_native_accounted_result),
    JAYDB_ACCOUNTED_ENTRY_COVERAGE,3,sizeof(Term),JAYDB_ACCOUNTED_TEST_FIXTURE,JAYDB_SOURCE_HASH};
  return &d;
}

__attribute__((visibility("default")))
uint32_t jaydb_native_progress_accounted_v1(struct jaydb_native_accounted_progress *out) {
  if(!out)return JAYDB_ARGUMENT;
  *out=jaydb_decoder_progress;
  return JAYDB_OK;
}
