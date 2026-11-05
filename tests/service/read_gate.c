/* Test-only OS fault/schedule adapter. The checked C/runtime are untouched.
 * Gate the first stdin fread in explicitly listed prepared executables. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>
#include <fcntl.h>

size_t fread(void *ptr, size_t size, size_t count, FILE *stream) {
  static _Atomic int entered;
  size_t (*real_fread)(void *, size_t, size_t, FILE *) = dlsym(RTLD_NEXT, "fread");
  const char *gate = getenv("JAYDB_TEST_READ_GATE"), *targets = getenv("JAYDB_TEST_READ_TARGETS");
  if (stream == stdin && gate && targets && !atomic_exchange(&entered, 1)) {
    char exe[4096], list[16384];
    ssize_t n = readlink("/proc/self/exe", exe, sizeof(exe)-2);
    int fd = open(targets, O_RDONLY);
    ssize_t got = fd < 0 ? -1 : read(fd, list, sizeof(list)-1);
    if (fd >= 0) close(fd);
    if (n > 0 && got > 0) {
      exe[n] = '\n'; exe[n+1] = 0; list[got] = 0;
      if (strstr(list, exe)) {
        int sock = socket(AF_UNIX, SOCK_STREAM, 0);
        struct sockaddr_un address = {.sun_family=AF_UNIX};
        if (strlen(gate) >= sizeof(address.sun_path)) _exit(93);
        strcpy(address.sun_path, gate);
        if (connect(sock, (void *)&address, sizeof(address))) _exit(94);
        char message[4200];
        int length = snprintf(message, sizeof(message), "%ld %s", (long)getpid(), exe);
        if (write(sock, message, length) != length) _exit(95);
        char command;
        if (read(sock, &command, 1) != 1) _exit(96);
        close(sock);
        if (command == 'f') _exit(91);
      }
    }
  }
  return real_fread(ptr, size, count, stream);
}
