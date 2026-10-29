#define _DEFAULT_SOURCE
/* Test-only target DSO. It is NOT linked into the production loader. The log
 * survives real unloading, and lets subprocess tests observe each acquisition
 * generation and destructor without ever dereferencing an unloaded pointer.
 */
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <unistd.h>

static const char *log_path;
static uint64_t *destroyed;
static int close_signal;
static unsigned int close_delay;

#ifdef JAYDB_LOADING_WRAP_DLCLOSE
/* Explicit non-consuming error fixture, NOT a real libdl error witness. */
static unsigned int close_calls;
int __real_dlclose(void *handle);
int __wrap_dlclose(void *handle) {
    if (++close_calls == 1)
        return -1;
    return __real_dlclose(handle);
}
unsigned int loading_fixture_close_calls(void) { return close_calls; }
#endif

#if defined(JAYDB_LOADING_SIGNAL_OPEN) || defined(JAYDB_LOADING_OPEN_DELAY)
__attribute__((constructor)) static void start(void) {
#ifdef JAYDB_LOADING_OPEN_DELAY
    usleep(JAYDB_LOADING_OPEN_DELAY);
#endif
#ifdef JAYDB_LOADING_SIGNAL_OPEN
    (void)raise(SIGALRM);
#endif
}
#endif

void loading_fixture_configure(const char *path, uint64_t *counter, int signal_number,
                               unsigned int delay) {
    log_path = path;
    destroyed = counter;
    close_signal = signal_number;
    close_delay = delay;
}

int loading_fixture_value(void) {
    return 73;
}

__attribute__((destructor)) static void finish(void) {
    if (close_delay)
        usleep(close_delay);
    if (destroyed)
        ++*destroyed;
    const char *path = log_path;
#ifdef JAYDB_LOADING_FIXED_LOG
    path = JAYDB_LOADING_FIXED_LOG;
#endif
    if (path) {
        int fd = open(path, O_WRONLY | O_CREAT | O_APPEND, 0600);
        if (fd >= 0) {
            (void)write(fd, "closed\n", 7);
            (void)close(fd);
        }
    }
    if (close_signal)
        (void)raise(close_signal);
}
