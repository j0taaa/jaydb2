#ifndef JAYDB_SERVICE_LIFECYCLE_H
#define JAYDB_SERVICE_LIFECYCLE_H
#include <stdint.h>
#include <stdatomic.h>

/* Private, additive Linux/glibc ABI. All memory is caller-owned and prearmed.
 * outcome is ONE atomic pair {returned:u32,status:u32}, little endian.
 * Never reset/reuse receipts. No other waiter/reaper may own these children.
 * C non-local exits, thread cancellation and process death are not recovered.
 */
#define JAYDB_LIFECYCLE_ABI 1u
#define JAYDB_LIFECYCLE_FLAGS 15ull /* NODELETE, setsid, invoke gate, core0 profile */
enum jaydb_lifecycle_code { JAYLC_OK, JAYLC_ERROR, JAYLC_ABI, JAYLC_UNCERTAIN,
    JAYLC_CLOSED, JAYLC_BINDING, JAYLC_RESULT };
enum jaydb_lifecycle_call_state { JAYLC_READY, JAYLC_CALLING, JAYLC_RETURNED, JAYLC_CANCELLED };
#define JAYLC_TERMINAL 1u
#define JAYLC_EXIT_OBSERVED 2u

typedef struct {
    uint32_t abi;
    _Atomic uint32_t entered;
    union { _Atomic uint64_t outcome; struct { uint32_t returned, status; }; };
} jaydb_lifecycle_receipt_v1;
typedef struct {
    jaydb_lifecycle_receipt_v1 receipt;
    int32_t pid;
    uint32_t reserved;
} jaydb_lifecycle_spawn_v1;
typedef struct {
    jaydb_lifecycle_receipt_v1 receipt;
    int32_t wait_status;
    uint32_t kill_error;
} jaydb_lifecycle_finish_v1;
typedef struct {
    uint32_t abi, size;
    jaydb_lifecycle_receipt_v1 prepare;
    jaydb_lifecycle_spawn_v1 spawn;
    jaydb_lifecycle_finish_v1 finish;
    int32_t fds[4]; /* stdout read/write, stderr read/write; initial -1 */
    _Atomic uint32_t gate;
    _Atomic uint32_t flags;
    int32_t observed_status;
    uint32_t io_error;
} jaydb_lifecycle_process_v1;
typedef struct {
    uint32_t abi;
    _Atomic uint32_t state;
    _Atomic uint64_t outcome;
    uintptr_t function;
    uint32_t arity, reserved;
} jaydb_lifecycle_call_v1;
typedef struct {
    jaydb_lifecycle_receipt_v1 receipt;
    uintptr_t function;
    uint64_t lease;
} jaydb_lifecycle_release_v1;
typedef struct {
    uint32_t abi, size, process_bytes, receipt_bytes, spawn_bytes, finish_bytes;
    uint32_t call_bytes, release_bytes, pointer_bytes, reserved;
    uint64_t flags;
    char build_identity[64];
} jaydb_lifecycle_descriptor_v1;

#define JAYLC_EXPORT __attribute__((visibility("default")))
JAYLC_EXPORT const jaydb_lifecycle_descriptor_v1 *jaydb_lifecycle_describe_v1(void);
JAYLC_EXPORT int jaydb_lifecycle_process_prepare_v1(jaydb_lifecycle_process_v1 *);
JAYLC_EXPORT int jaydb_lifecycle_process_start_v1(jaydb_lifecycle_process_v1 *,
    char *const argv[], char *const envp[]);
JAYLC_EXPORT int jaydb_lifecycle_process_poll_v1(jaydb_lifecycle_process_v1 *);
JAYLC_EXPORT int jaydb_lifecycle_process_stop_v1(jaydb_lifecycle_process_v1 *);
JAYLC_EXPORT int jaydb_lifecycle_process_close_v1(jaydb_lifecycle_process_v1 *);
/* Existing native entry signatures are uint32(pointer,pointer[,pointer]). The
 * arity enumerates those ABIs, not an arity restriction on the Bend fragment.
 * All pointers/function addresses are supplied by the trusted host, not clients.
 */
JAYLC_EXPORT int jaydb_lifecycle_invoke_v3(uintptr_t function, uint32_t arity,
    void *a, void *b, void *c, jaydb_lifecycle_call_v1 *);
JAYLC_EXPORT int jaydb_lifecycle_cancel_v1(jaydb_lifecycle_call_v1 *);
JAYLC_EXPORT int jaydb_lifecycle_release_v3(uintptr_t function, uint64_t lease,
    jaydb_lifecycle_release_v1 *);
#endif
