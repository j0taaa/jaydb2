#define _GNU_SOURCE
/* TEST ONLY: link with --wrap to position real signals inside C and inject
 * explicitly labelled syscall errors. Never part of the production builder.
 */
#include <errno.h>
#include <signal.h>
#include <spawn.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
static int mode;
static unsigned int pipe_calls, kill_calls;
void lifecycle_syscall_fixture_mode(int value) { mode = value; pipe_calls = kill_calls = 0; }
unsigned int lifecycle_syscall_fixture_kills(void) { return kill_calls; }
int __real_posix_spawnp(pid_t *, const char *, const posix_spawn_file_actions_t *,
                       const posix_spawnattr_t *, char *const [], char *const []);
int __wrap_posix_spawnp(pid_t *pid, const char *file, const posix_spawn_file_actions_t *actions,
                        const posix_spawnattr_t *attributes, char *const argv[], char *const env[]) {
    int result = __real_posix_spawnp(pid, file, actions, attributes, argv, env);
    if (!result && mode == 1) (void)raise(SIGALRM);
    return result;
}
int __real_pipe2(int [2], int);
int __wrap_pipe2(int fds[2], int flags) {
    if (++pipe_calls == 2 && mode == 5) { errno = ENOMEM; return -1; }
    int result = __real_pipe2(fds, flags);
    if (!result && mode == 2) (void)raise(SIGALRM);
    return result;
}
pid_t __real_waitpid(pid_t, int *, int);
pid_t __wrap_waitpid(pid_t pid, int *status, int options) {
    pid_t result = __real_waitpid(pid, status, options);
    if (result > 0 && mode == 3) (void)raise(SIGALRM);
    return result;
}
int __real_close(int);
int __wrap_close(int fd) {
    int result = __real_close(fd);
    if (!result && mode == 4) (void)raise(SIGALRM);
    return result;
}
int __real_waitid(idtype_t, id_t, siginfo_t *, int);
int __wrap_waitid(idtype_t type, id_t id, siginfo_t *info, int options) {
    if (mode == 6) { errno = ECHILD; return -1; }
    return __real_waitid(type, id, info, options);
}
int __real_kill(pid_t, int);
int __wrap_kill(pid_t pid, int sig) {
    ++kill_calls;
    return __real_kill(pid, sig);
}
