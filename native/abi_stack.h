#ifndef JAYDB_NATIVE_MAIN_STACK_H
#define JAYDB_NATIVE_MAIN_STACK_H
#include "abi_v3.h"

/* Additional V3 mode; every public layout and entry name is unchanged.
 * A builder reporting automaticNativeStackV3 and mode linux-main-growdown
 * accepts native_stack_bytes=0 in run_v3 and run_deadline_v3. The trusted host
 * must call on the ordinary Linux main grow-down stack, gettid==getpid, with
 * soft RLIMIT_STACK=RLIM_INFINITY. The runtime checks identity and the limit
 * without changing either. Missing conditions return ARGUMENT, actual check
 * syscall failure returns SYSTEM. An already expired absolute setup epoch
 * still returns TIME first, with no local mapping charge or live lease.
 *
 * The evaluator, setjmp/longjmp and cleanup complete inside the synchronous C
 * call, before returning to FFI. No private C-stack mapping or worker pthread
 * is created in this mode. Coverage and explicit deadline checks stay active;
 * only the check against an explicit private stack capacity is disabled.
 * Clang stack-clash probes traverse each newly needed page. Locals and bank
 * pointers never move. Linux can fail actual stack growth; no such event is
 * fabricated as an observed memory-limit violation by this ABI.
 *
 * OS stack backing is part of global accounting. charged_bytes is only the
 * local mapping peak and must not be added to a global total or claimed to
 * include this OS stack. No counter completeness or complete Contrato is
 * implied. A Campo critical section still needs its own bounded, already
 * active stack and backing after the final global barrier.
 * Positive native_stack_bytes retains the old explicit pthread stack path.
 * V1/V2 remain unchanged. */
#endif
