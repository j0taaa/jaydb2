/* Differential oracle is the exact Bend 2.0.39 C predicate. Test only. */
#include "guard.h"
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "f32_parse.inc.c"

/* Make consumption observable even on rejected input. Otherwise Clang can
 * correctly erase a pure byte reader's drain loop (the real String cursor
 * releases arena nodes and has observable effects on subsequent allocations).
 */
struct bytes_reader { const unsigned char *bytes; volatile uint64_t at; uint64_t length; };
static int bytes_next(void *context) {
  struct bytes_reader *r = context;
  return r->at < r->length ? r->bytes[r->at++] : -1;
}
static uint64_t bits(float f) {
  uint32_t result;
  memcpy(&result, &f, sizeof result);
  return (1ull << 32) | result;
}

uint64_t reference(const char *text, uint64_t n) {
  char *end;
  float f = strtof(text, &end);
  return n > 0 && (uint64_t)(end - text) == n && strpbrk(text, "xX(") == NULL
    ? bits(f) : 0;
}

uint64_t streaming(const unsigned char *text, uint64_t n) {
  struct bytes_reader reader = { text, 0, n };
  float f;
  return jaydb_f32_parse(bytes_next, &reader, &f) ? bits(f) : 0;
}

static uint32_t timed_guard(struct jaydb_guard *guard, const unsigned char *text, uint64_t n) {
  jaydb_active = guard;
  if (!setjmp(guard->escape)) {
    (void)streaming(text, n);
    jaydb_poll();
  }
  jaydb_active = NULL;
  return guard->status;
}

uint32_t timed(const unsigned char *text, uint64_t n, uint64_t timeout) {
  /* The object modified across longjmp belongs to the caller's frame. */
  struct jaydb_guard guard = { .stack_low = 0, .stack_high = UINTPTR_MAX };
  guard.deadline = jaydb_clock() + timeout;
  return timed_guard(&guard, text, n);
}
