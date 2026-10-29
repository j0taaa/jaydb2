#ifndef JAYDB_GUARD_H
#define JAYDB_GUARD_H
#include "abi_v3.h"
#include <setjmp.h>
#include <stdatomic.h>
#include <stdbool.h>

typedef __uint128_t jaydb_ns;
#define JAYDB_STACK_CAPACITY_CODE 0x5354414bu /* STAK: internal fixed-capacity refusal */

struct jaydb_guard {
  jmp_buf escape;
  uint64_t deadline, start, charged;
  uintptr_t stack_low, stack_high;
  uint32_t status, runtime_code;
  uint32_t stage;
  uint64_t stage_started, stage_elapsed[3];
  uint64_t execution_timeout_ns, preparation_timeout_ns;
  uint32_t wide_time;
  jaydb_ns start_wide, stage_started_wide;
  jaydb_ns stage_budget_wide[3], stage_elapsed_wide[3];
  jaydb_ns stage_deadline_wide[3];
  uint64_t memory_limit, memory_current, memory_peak;
  uint32_t stack_error_status, stack_error_code;
  uint32_t coverage_clock_ticks;
  uint32_t os_main_stack;
  const struct jaydb_native_accounted *accounted;
  struct jaydb_native_accounted_result *accounted_result;
  volatile struct jaydb_native_accounted_progress *accounted_progress;
};
#if defined(JAYDB_LOCAL_LEAVES) && JAYDB_LOCAL_LEAVES
#include "owner.h"
#define jaydb_active (jaydb_owner_get())
#define jaydb_guard_bind jaydb_owner_set
#else
extern _Thread_local struct jaydb_guard *jaydb_active;
static inline void jaydb_guard_bind(struct jaydb_guard *guard) { jaydb_active = guard; }
#endif
uint64_t jaydb_clock(void);
bool jaydb_clock_wide(jaydb_ns *value);
/* Trusted O(1) allocation critical sections, compiled without coverage.
 * A successful mapping is charged and published before any poll can longjmp.
 * owner points to a data-pointer object; memcpy avoids pointer-type aliasing.
 */
uint32_t jaydb_map_publish(struct jaydb_guard *, void *owner, uint64_t bytes, int protection);
uint32_t jaydb_output_resize(struct jaydb_guard *, uint8_t **owner, uint64_t *capacity, uint64_t bytes);
uint32_t jaydb_mapping_resize(struct jaydb_guard *, void *owner, uint64_t *capacity, uint64_t bytes);
void jaydb_poll(void);
void jaydb_enter_stage(uint32_t stage);
_Noreturn void jaydb_abort(uint32_t status, uint32_t runtime_code);
#endif
