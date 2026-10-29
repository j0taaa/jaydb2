#define _GNU_SOURCE
#include "lifecycle.h"
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <spawn.h>
#include <stddef.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

#ifndef JAYDB_LIFECYCLE_BUILD_ID
#error "Use the explicit offline builder"
#endif
_Static_assert(sizeof(void *) == 8 && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "Linux ABI");
_Static_assert(sizeof(pid_t) == sizeof(int32_t), "glibc pid ABI");
_Static_assert(ATOMIC_INT_LOCK_FREE == 2 && ATOMIC_LLONG_LOCK_FREE == 2, "lock-free receipts");
_Static_assert(sizeof(jaydb_lifecycle_receipt_v1) == 16, "receipt ABI");
_Static_assert(sizeof(jaydb_lifecycle_spawn_v1) == 24, "spawn ABI");
_Static_assert(sizeof(jaydb_lifecycle_finish_v1) == 24, "finish ABI");
_Static_assert(sizeof(jaydb_lifecycle_process_v1) == 104, "process ABI");
_Static_assert(sizeof(jaydb_lifecycle_call_v1) == 32, "call ABI");
_Static_assert(sizeof(jaydb_lifecycle_release_v1) == 32, "release ABI");
_Static_assert(sizeof(jaydb_lifecycle_descriptor_v1) == 112, "descriptor ABI");
_Static_assert(offsetof(jaydb_lifecycle_receipt_v1, outcome) == 8, "atomic pair alignment");

static const jaydb_lifecycle_descriptor_v1 descriptor = {
    1, 112, 104, 16, 24, 24, 32, 32, 8, 0, JAYDB_LIFECYCLE_FLAGS, JAYDB_LIFECYCLE_BUILD_ID
};
const jaydb_lifecycle_descriptor_v1 *jaydb_lifecycle_describe_v1(void) { return &descriptor; }
static uint64_t outcome(uint32_t status) { return ((uint64_t)status << 32) | 1; }
static int record(jaydb_lifecycle_receipt_v1 *r, uint32_t status) {
    atomic_store_explicit(&r->outcome, outcome(status), memory_order_release);
    return status ? JAYLC_ERROR : JAYLC_OK;
}
/* Internal DONE distinguishes an already successful receipt from a new claim.
 * Failed retries compare the WHOLE pair, so success cannot be confused with a
 * previous failure by a concurrent/reentrant claimant (no outcome ABA).
 */
#define DONE 7
static int claim(jaydb_lifecycle_receipt_v1 *r, int retry) {
    if (r->abi != 1) return JAYLC_ABI;
    uint32_t expected = 0;
    if (atomic_compare_exchange_strong(&r->entered, &expected, 1)) return JAYLC_OK;
    uint64_t prior = atomic_load_explicit(&r->outcome, memory_order_acquire);
    if (!(uint32_t)prior) return JAYLC_UNCERTAIN;
    if (!(uint32_t)(prior >> 32)) return DONE;
    if (!retry) return JAYLC_ERROR;
    if (!atomic_compare_exchange_strong(&r->outcome, &prior, 0)) return JAYLC_UNCERTAIN;
    return JAYLC_OK;
}

static int lock_process(jaydb_lifecycle_process_v1 *p) {
    if (!p || p->abi != 1 || p->size != sizeof *p || p->prepare.abi != 1 ||
        p->spawn.receipt.abi != 1 || p->finish.receipt.abi != 1) return JAYLC_ABI;
    uint32_t expected = 0;
    return atomic_compare_exchange_strong(&p->gate, &expected, 1) ? JAYLC_OK : JAYLC_UNCERTAIN;
}
static int unlock(jaydb_lifecycle_process_v1 *p, int code) {
    atomic_store_explicit(&p->gate, 0, memory_order_release);
    return code;
}
static void close_fd(jaydb_lifecycle_process_v1 *p, unsigned int i) {
    if (p->fds[i] < 0) return;
    int error = close(p->fds[i]) ? errno : 0;
    /* Linux close consumes a valid descriptor even on EINTR. No retry of the
     * old number is permitted; the host must not close/reuse these descriptors.
     */
    p->fds[i] = -1;
    if (error && !p->io_error) p->io_error = (uint32_t)error;
}
static void close_all(jaydb_lifecycle_process_v1 *p) {
    for (unsigned int i = 0; i < 4; ++i) close_fd(p, i);
}
static int prepare_pipe(jaydb_lifecycle_process_v1 *p, unsigned int i) {
    if (pipe2(&p->fds[i], O_CLOEXEC)) return errno;
    /* A parent with a closed stdio slot must not accidentally use that slot as
     * an action source/destination. Dup sources are always >=3, without a cap.
     */
    for (unsigned int j = i; j < i + 2; ++j) {
        if (p->fds[j] < 3) {
            int fd = fcntl(p->fds[j], F_DUPFD_CLOEXEC, 3);
            if (fd < 0) return errno;
            close_fd(p, j);
            p->fds[j] = fd;
        }
    }
    int flags = fcntl(p->fds[i], F_GETFL);
    if (flags < 0 || fcntl(p->fds[i], F_SETFL, flags | O_NONBLOCK)) return errno;
    return 0;
}
int jaydb_lifecycle_process_prepare_v1(jaydb_lifecycle_process_v1 *p) {
    int code = lock_process(p);
    if (code) return code;
    if (atomic_load(&p->flags) & JAYLC_TERMINAL) return unlock(p, JAYLC_CLOSED);
    code = claim(&p->prepare, 0);
    if (code) return unlock(p, code == DONE ? JAYLC_OK : code);
    int error = prepare_pipe(p, 0);
    if (!error) error = prepare_pipe(p, 2);
    if (error) close_all(p);
    return unlock(p, record(&p->prepare, (uint32_t)error));
}

int jaydb_lifecycle_process_start_v1(jaydb_lifecycle_process_v1 *p,
                                     char *const argv[], char *const envp[]) {
    int code = lock_process(p);
    if (code) return code;
    if (atomic_load(&p->flags) & JAYLC_TERMINAL) return unlock(p, JAYLC_CLOSED);
    if (atomic_load(&p->prepare.outcome) != 1 || !argv || !argv[0] || !envp)
        return unlock(p, JAYLC_BINDING);
    code = claim(&p->spawn.receipt, 0);
    if (code) return unlock(p, code == DONE ? JAYLC_OK : code);
    struct rlimit core;
    struct sigaction chld;
    int error = getrlimit(RLIMIT_CORE, &core) ? errno : 0;
    if (!error && core.rlim_cur != 0) error = EPERM;
    if (!error && sigaction(SIGCHLD, NULL, &chld)) error = errno;
    if (!error && (chld.sa_handler == SIG_IGN || (chld.sa_flags & SA_NOCLDWAIT))) error = EINVAL;
    posix_spawn_file_actions_t actions;
    posix_spawnattr_t attributes;
    int have_actions = 0, have_attributes = 0;
    if (!error) {
        error = posix_spawn_file_actions_init(&actions);
        have_actions = !error;
    }
    if (!error) {
        error = posix_spawnattr_init(&attributes);
        have_attributes = !error;
    }
    if (!error) error = posix_spawn_file_actions_adddup2(&actions, p->fds[1], STDOUT_FILENO);
    if (!error) error = posix_spawn_file_actions_adddup2(&actions, p->fds[3], STDERR_FILENO);
    if (!error) error = posix_spawn_file_actions_addclosefrom_np(&actions, 3);
    sigset_t defaults, mask;
    sigemptyset(&defaults);
    sigaddset(&defaults, SIGPIPE);
#ifdef SIGXFZ
    sigaddset(&defaults, SIGXFZ);
#endif
#ifdef SIGXFSZ
    sigaddset(&defaults, SIGXFSZ);
#endif
    if (!error && sigprocmask(SIG_SETMASK, NULL, &mask)) error = errno;
    if (!error) error = posix_spawnattr_setsigmask(&attributes, &mask);
    if (!error) error = posix_spawnattr_setsigdefault(&attributes, &defaults);
    if (!error) error = posix_spawnattr_setflags(&attributes,
        POSIX_SPAWN_SETSID | POSIX_SPAWN_SETSIGMASK | POSIX_SPAWN_SETSIGDEF);
    /* glibc returns an exec/setup error without a waitable child. On success it
     * writes the PID straight into durable owner memory, before any Python.
     */
    if (!error) error = posix_spawnp(&p->spawn.pid, argv[0], &actions, &attributes, argv, envp);
    if (have_actions) (void)posix_spawn_file_actions_destroy(&actions);
    if (have_attributes) (void)posix_spawnattr_destroy(&attributes);
    close_fd(p, 1);
    close_fd(p, 3);
    code = record(&p->spawn.receipt, (uint32_t)error);
    return unlock(p, code ? code : (p->io_error ? JAYLC_ERROR : JAYLC_OK));
}

static int check_child(jaydb_lifecycle_process_v1 *p) {
    uint64_t spawned = atomic_load_explicit(&p->spawn.receipt.outcome, memory_order_acquire);
    if (!(uint32_t)spawned)
        return atomic_load(&p->spawn.receipt.entered) ? JAYLC_UNCERTAIN : JAYLC_BINDING;
    if ((uint32_t)(spawned >> 32) || p->spawn.pid <= 0) return JAYLC_BINDING;
    return JAYLC_OK;
}
static int observe(jaydb_lifecycle_process_v1 *p) {
    siginfo_t info = {0};
    int status;
    do { status = waitid(P_PID, (id_t)p->spawn.pid, &info, WEXITED | WNOHANG | WNOWAIT); }
    while (status && errno == EINTR);
    if (status) return errno; /* ECHILD: never kill a possibly reused PID */
    if (info.si_pid) {
        p->observed_status = info.si_code == CLD_EXITED ? info.si_status << 8 :
            info.si_status | (info.si_code == CLD_DUMPED ? 128 : 0);
        atomic_fetch_or(&p->flags, JAYLC_EXIT_OBSERVED);
    }
    return 0;
}
int jaydb_lifecycle_process_poll_v1(jaydb_lifecycle_process_v1 *p) {
    int code = lock_process(p);
    if (code) return code;
    if (atomic_load(&p->finish.receipt.outcome) == 1) return unlock(p, JAYLC_OK);
    code = check_child(p);
    if (code) return unlock(p, code);
    int error = observe(p);
    if (error) p->io_error = (uint32_t)error;
    return unlock(p, error ? JAYLC_ERROR : JAYLC_OK);
}
static int stop(jaydb_lifecycle_process_v1 *p) {
    int code = check_child(p);
    if (code) return code;
    code = claim(&p->finish.receipt, 1);
    if (code) return code == DONE ? JAYLC_OK : code;
    int error = observe(p); /* leader is still our child and remains unreaped */
    p->finish.kill_error = 0;
    if (!error && kill(-p->spawn.pid, SIGKILL)) {
        p->finish.kill_error = (uint32_t)errno;
        if (errno != ESRCH) error = errno;
    }
    if (!error) {
        pid_t child;
        do { child = waitpid(p->spawn.pid, &p->finish.wait_status, 0); }
        while (child < 0 && errno == EINTR);
        if (child != p->spawn.pid) error = child < 0 ? errno : ECHILD;
    }
    return record(&p->finish.receipt, (uint32_t)error);
}
int jaydb_lifecycle_process_stop_v1(jaydb_lifecycle_process_v1 *p) {
    int code = lock_process(p);
    if (code) return code;
    return unlock(p, stop(p));
}
int jaydb_lifecycle_process_close_v1(jaydb_lifecycle_process_v1 *p) {
    int code = lock_process(p);
    if (code) return code;
    if (atomic_load(&p->flags) & JAYLC_TERMINAL) return unlock(p, JAYLC_OK);
    uint64_t spawned = atomic_load(&p->spawn.receipt.outcome);
    if (atomic_load(&p->spawn.receipt.entered)) {
        if (!(uint32_t)spawned) return unlock(p, JAYLC_UNCERTAIN);
        if (!(uint32_t)(spawned >> 32)) {
            code = stop(p);
            if (code) return unlock(p, code);
        }
    }
    close_all(p);
    atomic_fetch_or_explicit(&p->flags, JAYLC_TERMINAL, memory_order_release);
    return unlock(p, p->io_error ? JAYLC_ERROR : JAYLC_OK);
}

int jaydb_lifecycle_invoke_v3(uintptr_t fn, uint32_t arity, void *a, void *b, void *c,
                             jaydb_lifecycle_call_v1 *r) {
    if (!r || r->abi != 1) return JAYLC_ABI;
    if (!fn || (arity != 2 && arity != 3)) return JAYLC_BINDING;
    uint32_t expected = JAYLC_READY;
    if (!atomic_compare_exchange_strong(&r->state, &expected, JAYLC_CALLING))
        return expected == JAYLC_CALLING ? JAYLC_UNCERTAIN : JAYLC_CLOSED;
    r->function = fn;
    r->arity = arity;
    uint32_t status = arity == 2 ? ((uint32_t (*)(void *, void *))fn)(a, b) :
                                  ((uint32_t (*)(void *, void *, void *))fn)(a, b, c);
    atomic_store_explicit(&r->outcome, outcome(status), memory_order_release);
    atomic_store_explicit(&r->state, JAYLC_RETURNED, memory_order_release);
    return JAYLC_OK;
}
int jaydb_lifecycle_cancel_v1(jaydb_lifecycle_call_v1 *r) {
    if (!r || r->abi != 1) return JAYLC_ABI;
    uint32_t expected = JAYLC_READY;
    if (atomic_compare_exchange_strong(&r->state, &expected, JAYLC_CANCELLED) ||
        expected == JAYLC_CANCELLED) return JAYLC_OK;
    return expected == JAYLC_CALLING ? JAYLC_UNCERTAIN : JAYLC_CLOSED;
}
int jaydb_lifecycle_release_v3(uintptr_t fn, uint64_t lease, jaydb_lifecycle_release_v1 *r) {
    if (!r || r->receipt.abi != 1) return JAYLC_ABI;
    if (!fn || !lease) return JAYLC_BINDING;
    uint32_t expected = 0;
    if (atomic_compare_exchange_strong(&r->receipt.entered, &expected, 1)) {
        r->function = fn;
        r->lease = lease;
    } else {
        /* Binding is immutable after its FIRST publication. Check it after an
         * acquire, including when the first operation completed while another
         * caller was entering this function. Never redirect a retry to a new
         * lease or function. The outcome CAS also distinguishes success from
         * failure, even across multiple failed retries.
         */
        uint64_t prior = atomic_load_explicit(&r->receipt.outcome, memory_order_acquire);
        if (!(uint32_t)prior) return JAYLC_UNCERTAIN;
        if (r->function != fn || r->lease != lease) return JAYLC_BINDING;
        if (!(uint32_t)(prior >> 32)) return JAYLC_OK;
        if (!atomic_compare_exchange_strong(&r->receipt.outcome, &prior, 0)) return JAYLC_UNCERTAIN;
    }
    uint32_t status = ((uint32_t (*)(uint64_t))fn)(lease);
    return record(&r->receipt, status);
}
