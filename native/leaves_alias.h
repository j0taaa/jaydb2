#ifndef JAYDB_LOCAL_LEAVES_ALIAS_H
#define JAYDB_LOCAL_LEAVES_ALIAS_H
/* Include after system declarations. Diagnostic standalone probes can retain
 * their explicit libc/fault-injection hooks by not enabling the production
 * local-leaf binding. The builder always enables it. */
#if defined(JAYDB_LOCAL_LEAVES) && JAYDB_LOCAL_LEAVES
#include "leaves.h"
#define clock_gettime jaydb_os_clock_gettime
#define mmap jaydb_os_mmap
#define mremap jaydb_os_mremap
#define munmap jaydb_os_munmap
#define mprotect jaydb_os_mprotect
#endif
#endif
