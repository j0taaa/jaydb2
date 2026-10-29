/** Only the generated process entrypoint changes; _lean_main is untouched. */
export function useGrowingMainStack(source) {
  const dispatch = '    lean_init_task_manager();\n    res = lean_run_main(&run_main, argc, argv);';
  const entry = 'int main(int argc, char ** argv) {';
  if (source.split(dispatch).length !== 2 || source.split(entry).length !== 2) throw new Error('Lean 4.34 generated main anchor changed');
  return `#if !defined(__linux__) || !defined(__x86_64__)
#error "JayDB growing verifier stack requires Linux x86_64"
#endif
extern long syscall(long, ...);
#include <lean/mimalloc.h>
/* This pinned CLI uses only synchronous FILE IO, never libuv operations.
   Do not start an unused asynchronous loop with a preallocated pthread stack. */
void __wrap_initialize_libuv(void) {}
` + source.replace(dispatch, '    res = run_main(argc, argv);')
    .replace(entry, entry + `
  /* Linux x86_64 UAPI: __NR_prlimit64=302, RLIMIT_STACK=3.
     Lean's bundled C sysroot omits sys/resource.h. Both fields are u64. */
  struct { unsigned long long soft, hard; } growing_stack = { ~0ULL, ~0ULL };
  _Static_assert(sizeof(growing_stack) == 16, "Linux rlimit64 ABI");
  if (syscall(302L, 0, 3, &growing_stack, (void *)0) != 0) {
    const char growing_error[] = "BENDTT INFRASTRUCTURE: cannot enable growing OS stack\\n";
    syscall(1L, 2, growing_error, sizeof(growing_error) - 1);
    return 2;
  }
  /* Reserve address space freely; commit only the allocator pages in use.
     These options change commitment policy, never total heap capacity. */
  mi_option_set(mi_option_arena_eager_commit, 0);
  mi_option_set(mi_option_deprecated_eager_commit, 0);`);
}
