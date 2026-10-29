/* Compile without coverage: bounded leafs contain a single raw syscall. In
 * particular, allocation cannot poll between acquiring and publishing owner. */
#define _GNU_SOURCE
#include "leaves.h"
#include <sys/syscall.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error Local leafs require the audited Linux x86_64 ABI
#endif

static __attribute__((always_inline)) inline long jaydb_syscall6(
    long number, long a, long b, long c, long d, long e, long f) {
  register long r10 __asm__("r10") = d;
  register long r8 __asm__("r8") = e;
  register long r9 __asm__("r9") = f;
  long result;
  __asm__ volatile("syscall" : "=a"(result)
      : "a"(number), "D"(a), "S"(b), "d"(c), "r"(r10), "r"(r8), "r"(r9)
      : "rcx", "r11", "memory", "cc");
  return result;
}

static int jaydb_syscall_failed(long result) {
  return (unsigned long)result >= (unsigned long)-4095;
}

int jaydb_os_clock_gettime(clockid_t clock, struct timespec *time) {
  return (int)jaydb_syscall6(SYS_clock_gettime, clock, (long)time, 0, 0, 0, 0);
}

void *jaydb_os_mmap(void *address, size_t length, int protection,
                    int flags, int descriptor, off_t offset) {
  long result = jaydb_syscall6(SYS_mmap, (long)address, length, protection,
                             flags, descriptor, offset);
  return jaydb_syscall_failed(result) ? MAP_FAILED : (void *)result;
}

void *jaydb_os_mremap(void *previous, size_t old_length, size_t new_length, int flags) {
  long result = jaydb_syscall6(SYS_mremap, (long)previous, old_length, new_length, flags, 0, 0);
  return jaydb_syscall_failed(result) ? MAP_FAILED : (void *)result;
}

int jaydb_os_munmap(void *address, size_t length) {
  return (int)jaydb_syscall6(SYS_munmap, (long)address, length, 0, 0, 0, 0);
}

int jaydb_os_mprotect(void *address, size_t length, int protection) {
  return (int)jaydb_syscall6(SYS_mprotect, (long)address, length, protection, 0, 0, 0);
}

int jaydb_os_main_stack_ready(void) {
  long pid = jaydb_syscall6(SYS_getpid, 0, 0, 0, 0, 0, 0);
  if (jaydb_syscall_failed(pid)) return (int)pid;
  long tid = jaydb_syscall6(SYS_gettid, 0, 0, 0, 0, 0, 0);
  if (jaydb_syscall_failed(tid)) return (int)tid;
  if (tid != pid) return 0;
  struct { uint64_t current, maximum; } stack;
  /* Linux x86_64 UAPI RLIMIT_STACK=3, RLIM64_INFINITY=UINT64_MAX. */
  long status = jaydb_syscall6(SYS_prlimit64, 0, 3, 0, (long)&stack, 0, 0);
  if (jaydb_syscall_failed(status)) return (int)status;
  return stack.current == UINT64_MAX;
}
