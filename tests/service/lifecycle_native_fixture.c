/* Explicit native ABI fixture: real malloc/free and destructor effects. No
 * checked Bend semantics, real resource failure, or accounting coverage claim.
 */
#define _DEFAULT_SOURCE
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <unistd.h>
#include <fcntl.h>
struct ns { uint64_t lo, hi; };
struct result {
    uint32_t status, runtime_code, stage, reserved;
    void *output;
    uint64_t output_len, output_capacity, lease, charged_bytes;
    struct ns elapsed, stages[3], preparation;
};
_Static_assert(sizeof(struct result) == 136, "unchanged native prefix");
struct stats { uint64_t runs, allocations, releases, release_calls, destructors, live_at_destructor; };
static struct stats *stats;
static const char *log_path;
static void *owned;
static uint64_t live, next = 17;
static uint32_t release_error, run_error;
static int signal_release, signal_run;
static unsigned int release_delay;

void lifecycle_fixture_configure(struct stats *s, const char *path, uint32_t re, uint32_t run,
                                  int sr, int sn, unsigned int delay) {
    stats = s; log_path = path; release_error = re; run_error = run;
    signal_release = sr; signal_run = sn; release_delay = delay;
}
uint32_t lifecycle_fixture_run(void *request, struct result *out) {
    (void)request;
    ++stats->runs;
    *out = (struct result){0};
    if (run_error && run_error != UINT32_MAX) { out->status = run_error; return run_error; }
    if (live) { out->status = 2; return 2; }
    if (run_error == UINT32_MAX) { out->lease = live = next++; return 0; } /* empty success fixture */
    owned = malloc(7);
    if (!owned) { out->status = 5; return 5; }
    ++stats->allocations;
    memcpy(owned, "leased!", 7);
    out->output = owned;
    out->output_len = out->output_capacity = 7;
    out->lease = live = next++;
    if (signal_run) (void)raise(signal_run);
    return 0;
}
uint32_t lifecycle_fixture_run3(void *request, struct result *out, void *unused) {
    (void)unused;
    return lifecycle_fixture_run(request, out);
}
uint32_t lifecycle_fixture_accounted(void *request, void *host, struct result *out) {
    (void)host;
    return lifecycle_fixture_run(request, out);
}
uint32_t jaydb_native_release_v3(uint64_t lease) {
    ++stats->release_calls;
    if (release_error) { uint32_t error = release_error; release_error = 0; return error; }
    if (!live || live != lease) return 1;
    if (release_delay) usleep(release_delay);
    free(owned); owned = NULL; live = 0;
    ++stats->releases;
    if (signal_release) (void)raise(signal_release);
    return 0;
}
__attribute__((destructor)) static void finish(void) {
    if (stats) { ++stats->destructors; stats->live_at_destructor = !!live; }
    if (log_path) {
        int fd = open(log_path, O_WRONLY | O_CREAT | O_APPEND, 0600);
        if (fd >= 0) { (void)write(fd, live ? "LIVE\n" : "released\n", live ? 5 : 9); (void)close(fd); }
    }
    /* Prevent a test failure from leaking its deliberately synthetic malloc. */
    free(owned); owned = NULL; live = 0;
}
