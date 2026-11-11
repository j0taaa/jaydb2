/* Opt-in diagnostic observer only; never linked into a JayDB2 worker.
 * Compile as a shared library and enable with paper/bench/diagnose.py.
 * Endpoint sysfs frequency samples are not an integrated cycle counter.
 */
#define _GNU_SOURCE
#include <fcntl.h>
#include <sched.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>
#include <unistd.h>

static long long started_wall, started_cpu;
static int started_core, started_frequency, enabled;
static char executable[4096];

static long long nanoseconds(clockid_t clock) {
  struct timespec time;
  clock_gettime(clock, &time);
  return time.tv_sec * 1000000000LL + time.tv_nsec;
}

static int frequency(int core) {
  char path[160];
  snprintf(path, sizeof path,
    "/sys/devices/system/cpu/cpu%d/cpufreq/scaling_cur_freq", core);
  FILE* file = fopen(path, "r");
  int khz = 0;
  if (file) {
    if (fscanf(file, "%d", &khz) != 1) khz = 0;
    fclose(file);
  }
  return khz;
}

__attribute__((constructor)) static void start(void) {
  ssize_t size = readlink("/proc/self/exe", executable, sizeof executable - 1);
  if (size < 0 || !getenv("JAYDB_WORKER_CLOCK")) return;
  executable[size] = 0;
  if (!strstr(executable, ".program")) return;
  enabled = 1;
  started_core = sched_getcpu();
  started_frequency = frequency(started_core);
  started_wall = nanoseconds(CLOCK_MONOTONIC);
  started_cpu = nanoseconds(CLOCK_PROCESS_CPUTIME_ID);
}

__attribute__((destructor)) static void finish(void) {
  if (!enabled) return;
  long long cpu = nanoseconds(CLOCK_PROCESS_CPUTIME_ID) - started_cpu;
  long long wall = nanoseconds(CLOCK_MONOTONIC) - started_wall;
  struct rusage usage;
  getrusage(RUSAGE_SELF, &usage);
  int core = sched_getcpu();
  char line[4600];
  int size = snprintf(line, sizeof line,
    "{\"pid\":%d,\"exe\":\"%s\",\"wall_ns\":%lld,\"cpu_ns\":%lld,"
    "\"cpu_start\":%d,\"cpu_end\":%d,\"khz_start\":%d,\"khz_end\":%d,"
    "\"minor_faults\":%ld,\"major_faults\":%ld,\"voluntary_cs\":%ld,"
    "\"involuntary_cs\":%ld}\n",
    getpid(), executable, wall, cpu, started_core, core, started_frequency,
    frequency(core), usage.ru_minflt, usage.ru_majflt, usage.ru_nvcsw,
    usage.ru_nivcsw);
  if (size < 0 || (size_t)size >= sizeof line) return;
  int file = open(getenv("JAYDB_WORKER_CLOCK"), O_WRONLY | O_CREAT | O_APPEND, 0600);
  if (file >= 0) {
    // One append per child, after the observed body has completed.
    if (write(file, line, (size_t)size) < 0) { /* Diagnostic only. */ }
    close(file);
  }
}
