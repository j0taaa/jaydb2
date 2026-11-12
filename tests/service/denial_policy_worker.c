// Test fixture for exact denial forwarding, independently of the checked worker.
#include <stdio.h>
#ifndef TEST_DIRECTORY
#error TEST_DIRECTORY is required
#endif
int main(void) {
  unsigned char bytes[65536];
  size_t count;
  FILE *input = fopen(TEST_DIRECTORY "/input", "wb");
  if (!input) return 2;
  while ((count = fread(bytes, 1, sizeof(bytes), stdin)))
    if (fwrite(bytes, 1, count, input) != count) return 3;
  if (fclose(input) || ferror(stdin)) return 4;
  FILE *reply = fopen(TEST_DIRECTORY "/reply", "rb");
  if (!reply) return 5;
  while ((count = fread(bytes, 1, sizeof(bytes), reply)))
    if (fwrite(bytes, 1, count, stdout) != count) return 6;
  return ferror(reply) || fclose(reply);
}
