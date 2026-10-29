/* Compiled separately WITHOUT coverage. The generated module is instrumented. */
#define _GNU_SOURCE
#include "guard.h"
#include "abi_accounted.h"
#include <time.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include "leaves_alias.h"

#if !defined(JAYDB_LOCAL_LEAVES) || !JAYDB_LOCAL_LEAVES
_Thread_local struct jaydb_guard *jaydb_active;
#endif

uint64_t jaydb_clock(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC, &t)) return 0;
  return (uint64_t)t.tv_sec * 1000000000ull + t.tv_nsec;
}

_Static_assert(sizeof(time_t) <= sizeof(int64_t) && (time_t)-1 < 0,
               "V3 clock domain requires signed time_t of at most 64 bits");

bool jaydb_clock_wide(jaydb_ns *value) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC, &t) || t.tv_sec < 0
      || t.tv_nsec < 0 || t.tv_nsec >= 1000000000L) return false;
  *value = (jaydb_ns)(uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec;
  return true;
}

static void record_accounted_clock(struct jaydb_guard *g,jaydb_ns now) {
  if(g->accounted_progress) {
    g->accounted_progress->stage=g->stage;
    g->accounted_progress->sampled_ns=(struct jaydb_native_ns128){now,now>>64};
  }
}

uint32_t jaydb_map_publish(struct jaydb_guard *g, void *owner, uint64_t bytes, int protection) {
  if (!bytes || bytes > SIZE_MAX || (!g->accounted && (g->memory_current > g->memory_limit
      || bytes > g->memory_limit - g->memory_current))) return JAYDB_MEMORY;
  void *mapped = mmap(NULL, (size_t)bytes, protection, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (mapped == MAP_FAILED) return JAYDB_SYSTEM;
  /* No coverage callback may occur between acquiring the mapping and these
   * stores. Its owner is already reachable by cleanup when the caller polls. */
  memcpy(owner, &mapped, sizeof mapped);
  g->memory_current += bytes;
  if (g->memory_current > g->memory_peak) g->memory_peak = g->memory_current;
  return JAYDB_OK;
}

uint32_t jaydb_output_resize(struct jaydb_guard *g, uint8_t **owner,
                             uint64_t *capacity, uint64_t bytes) {
  return jaydb_mapping_resize(g, owner, capacity, bytes);
}

uint32_t jaydb_mapping_resize(struct jaydb_guard *g, void *owner,
                              uint64_t *capacity, uint64_t bytes) {
  if (bytes < *capacity || bytes > SIZE_MAX || (!g->accounted && (g->memory_current > g->memory_limit
      || bytes - *capacity > g->memory_limit - g->memory_current))) return JAYDB_MEMORY;
  void *previous;
  memcpy(&previous, owner, sizeof previous);
  void *mapped = *capacity
    ? mremap(previous, *capacity, bytes, MREMAP_MAYMOVE)
    : mmap(NULL, (size_t)bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (mapped == MAP_FAILED) return JAYDB_SYSTEM;
  memcpy(owner, &mapped, sizeof mapped);
  g->memory_current += bytes - *capacity;
  *capacity = bytes;
  if (g->memory_current > g->memory_peak) g->memory_peak = g->memory_current;
  return JAYDB_OK;
}

_Noreturn void jaydb_abort(uint32_t status, uint32_t code) {
  /* Only module code running inside a live synchronous invocation calls this. */
  struct jaydb_guard *g = jaydb_active;
  if (!g) abort();
  if (g->accounted && status==JAYDB_MEMORY)status=JAYDB_SYSTEM;
  g->status = status;
  g->runtime_code = code;
  /* The longjmp destination is instrumented too. Disarm BEFORE jumping so
   * its cleanup blocks cannot repeatedly abort an already expired request. */
  jaydb_guard_bind(NULL);
  longjmp(g->escape, 1);
}

void jaydb_poll(void) {
  struct jaydb_guard *g = jaydb_active;
  if (!g) return;
  uintptr_t here;
  __asm__ volatile("mov %%rsp, %0" : "=r"(here));
  if (!g->os_main_stack && (here < g->stack_low || here >= g->stack_high))
    jaydb_abort(g->stack_error_status ? g->stack_error_status : JAYDB_MEMORY, g->stack_error_code);
  if (g->wide_time) {
    jaydb_ns now;
    if (!jaydb_clock_wide(&now) || now < g->stage_started_wide) jaydb_abort(JAYDB_SYSTEM, 0);
    record_accounted_clock(g,now);
    if (now - g->stage_started_wide >= g->stage_budget_wide[g->stage]) jaydb_abort(JAYDB_TIME, 0);
    return;
  }
  uint64_t now = jaydb_clock();
  if (!now) jaydb_abort(JAYDB_SYSTEM, 0);
  if (now >= g->deadline) jaydb_abort(JAYDB_TIME, 0);
}

void jaydb_enter_stage(uint32_t stage) {
  jaydb_poll(); /* An expired stage cannot be revived by a transition. */
  struct jaydb_guard *g = jaydb_active;
  if (!g || (!g->wide_time && (!g->execution_timeout_ns || !g->preparation_timeout_ns)))
    jaydb_abort(JAYDB_ARGUMENT, 0);
  if (stage != g->stage + 1 || stage > JAYDB_PREPARATION)
    jaydb_abort(JAYDB_INVARIANT, 0);
  if (g->wide_time) {
    jaydb_ns now;
    if (!jaydb_clock_wide(&now) || now < g->stage_started_wide) jaydb_abort(JAYDB_SYSTEM, 0);
    if (now - g->stage_started_wide >= g->stage_budget_wide[g->stage]) jaydb_abort(JAYDB_TIME, 0);
    g->stage_elapsed_wide[g->stage] += now - g->stage_started_wide;
    g->stage = stage;
    g->stage_started_wide = now;
    record_accounted_clock(g,now);
    jaydb_ns budget=g->stage_budget_wide[stage];
    g->stage_deadline_wide[stage]=budget>~(jaydb_ns)0-now?~(jaydb_ns)0:now+budget;
    if(g->accounted) {
      struct jayacct_u128 words=g->accounted->deadline_ns[stage];
      jaydb_ns epoch=((jaydb_ns)words.hi<<64)|words.lo;
      if(epoch) {
        g->stage_deadline_wide[stage]=epoch;
        g->stage_budget_wide[stage]=epoch>now?epoch-now:0;
        if(epoch<=now)jaydb_abort(JAYDB_TIME,0);
      }
    }
    return;
  }
  uint64_t now = jaydb_clock();
  uint64_t budget = stage == JAYDB_EXECUTION ? g->execution_timeout_ns : g->preparation_timeout_ns;
  if (!now) jaydb_abort(JAYDB_SYSTEM, 0);
  if (now >= g->deadline) jaydb_abort(JAYDB_TIME, 0);
  g->stage_elapsed[g->stage] += now - g->stage_started;
  g->stage = stage;
  g->stage_started = now;
  g->deadline = budget > UINT64_MAX - now ? UINT64_MAX : now + budget;
}

void __sanitizer_cov_trace_pc_guard(uint32_t *guard) {
  (void)guard;
#if defined(JAYDB_LOCAL_LEAVES) && JAYDB_LOCAL_LEAVES
  struct jaydb_guard *g = jaydb_active;
  if (!g) return;
  uintptr_t here;
  __asm__ volatile("mov %%rsp, %0" : "=r"(here));
  if (!g->os_main_stack && (here < g->stack_low || here >= g->stack_high))
    jaydb_abort(g->stack_error_status ? g->stack_error_status : JAYDB_MEMORY, g->stack_error_code);
  /* Sampling cadence, never a step quota: no counter value refuses a call.
   * Every callback still checks stack capacity. Explicit jaydb_poll(), stage
   * entry and final result checks always sample the real monotonic clock.
   * The first callback samples, then at most15 callbacks separate samples. */
  if (g->coverage_clock_ticks++ % 16) return;
#endif
  jaydb_poll();
}

void __sanitizer_cov_trace_pc_guard_init(uint32_t *begin, uint32_t *end) {
  while (begin != end) *begin++ = 1;
}
