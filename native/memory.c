/* Compile with -fno-builtin and the same coverage as the module. Defining the
 * hidden standard symbols also resolves compiler-lowered memory intrinsics.
 * No heap allocation, recursion, VLA, libc call or input-sized C frame. */
#include <stddef.h>
#include <stdint.h>
#define LOCAL __attribute__((visibility("hidden")))

LOCAL void *memcpy(void *restrict destination, const void *restrict source, size_t bytes) {
  unsigned char *to = destination;
  const unsigned char *from = source;
  for (size_t i = 0; i < bytes; ++i) to[i] = from[i];
  return destination;
}

LOCAL void *memmove(void *destination, const void *source, size_t bytes) {
  unsigned char *to = destination;
  const unsigned char *from = source;
  if ((uintptr_t)to < (uintptr_t)from) {
    for (size_t i = 0; i < bytes; ++i) to[i] = from[i];
  } else if (to != from) {
    while (bytes) { --bytes; to[bytes] = from[bytes]; }
  }
  return destination;
}

LOCAL void *memset(void *destination, int value, size_t bytes) {
  unsigned char *to = destination;
  for (size_t i = 0; i < bytes; ++i) to[i] = (unsigned char)value;
  return destination;
}

LOCAL int memcmp(const void *left, const void *right, size_t bytes) {
  const unsigned char *a = left, *b = right;
  for (size_t i = 0; i < bytes; ++i) {
    if (a[i] != b[i]) return (int)a[i] - (int)b[i];
  }
  return 0;
}

LOCAL size_t strlen(const char *text) {
  size_t length = 0;
  while (text[length]) ++length;
  return length;
}

LOCAL char *strchr(const char *text, int value) {
  for (;;) {
    unsigned char c = (unsigned char)*text;
    if (c == (unsigned char)value) return (char *)text;
    if (!c) return NULL;
    ++text;
  }
}
