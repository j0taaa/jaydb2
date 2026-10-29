#ifndef JAYDB_LOCAL_LEAVES_H
#define JAYDB_LOCAL_LEAVES_H
#include <stddef.h>
#include <stdint.h>
#include <sys/mman.h>
#include <time.h>

/* Private Linux x86_64 leafs. Negative syscall results are returned as failure
 * without setting libc errno; runtime callers inspect only success/failure.
 * No client primitive, libc interposition, allocation callback or VDSO call. */
int jaydb_os_clock_gettime(clockid_t, struct timespec *);
void *jaydb_os_mmap(void *, size_t, int, int, int, off_t);
void *jaydb_os_mremap(void *, size_t, size_t, int);
int jaydb_os_munmap(void *, size_t);
int jaydb_os_mprotect(void *, size_t, int);
/* 1: Linux main thread with unlimited soft RLIMIT_STACK; 0: environment does
 * not provide that mode; negative: actual syscall error. Does not change any
 * process limit or allocate backing. */
int jaydb_os_main_stack_ready(void);
#endif
