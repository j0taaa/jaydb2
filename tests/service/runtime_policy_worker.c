// Test fixture only; production still compiles literal official emitted C.
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
int main(int argc, char **argv) {
  unsigned char bytes[65536];
  size_t count;
  int received = 0;
  while ((count = fread(bytes, 1, sizeof(bytes), stdin))) {
    received = 1;
    if (fwrite(bytes, 1, count, stdout) != count) return 2;
  }
  if (ferror(stdin)) return 3;
  if (!received) {
    printf("%s\n", getenv("BENDRTS") ? getenv("BENDRTS") : "unset");
    for (int i = 1; i < argc; ++i) printf("%s\n", argv[i]);
  }
  return 0;
}
