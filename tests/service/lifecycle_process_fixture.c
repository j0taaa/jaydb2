#define _GNU_SOURCE
/* Ordinary helper for real spawn/pipe/group tests; it never escapes its group. */
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>

int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "profile";
    if (!strcmp(mode, "sleep")) { for (;;) pause(); }
    if (!strcmp(mode, "exit")) return argc > 2 ? atoi(argv[2]) : 0;
    if (!strcmp(mode, "descendant")) {
        pid_t child = fork();
        if (child < 0) return 4;
        if (!child) { for (;;) pause(); }
        printf("%d\n", child); fflush(stdout);
        return 0; /* leave a same-group child, with the leader still waitable */
    }
    if (!strcmp(mode, "many")) {
        char out[8192], err[8192];
        memset(out, 'o', sizeof out); memset(err, 'e', sizeof err);
        for (unsigned int i = 0; i < 80; ++i) {
            if (write(1, out, sizeof out) != sizeof out || write(2, err, sizeof err) != sizeof err) return 3;
        }
        return 0;
    }
    struct rlimit core;
    struct stat input;
    if (getrlimit(RLIMIT_CORE, &core) || fstat(0, &input)) return 5;
    int inherited = argc > 2 ? atoi(argv[2]) : -1;
    int fd_closed = inherited < 0 || (fcntl(inherited, F_GETFD) < 0 && errno == EBADF);
    printf("pid=%d pgid=%d sid=%d core=%llu hard=%llu fd_closed=%d stdin_dev=%llu stdin_ino=%llu telemetry=%s extra=%s\n",
        getpid(), getpgrp(), getsid(0), (unsigned long long)core.rlim_cur,
        (unsigned long long)core.rlim_max, fd_closed, (unsigned long long)input.st_dev,
        (unsigned long long)input.st_ino, getenv("BEND_NO_TELEMETRY"), getenv("LIFECYCLE_TEST_EXTRA"));
    fprintf(stderr, "stderr captured\n");
    return 0;
}
