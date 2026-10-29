/* Streaming equivalent of Bend 2.0.39's whole-string strtof predicate.
 * See F32_READ.md for the rounding argument. This translation unit is covered
 * and CFG-audited just like the emitted program. No input-sized libc calls or
 * allocations: strtof sees at most 201 bytes, regardless of input length.
 */
#include <ctype.h>
#include <float.h>
#include <locale.h>

_Static_assert(FLT_RADIX == 2 && FLT_MANT_DIG == 24 && FLT_MIN_EXP == -125
               && FLT_MAX_EXP == 128, "F32 parser requires IEEE binary32");

#define JAYDB_F32_DIGITS 192

static bool jaydb_f32_digit(int c) { return c >= '0' && c <= '9'; }

/* next returns unsigned UTF-8 bytes, including embedded zero, or -1 at EOF.
 * Even rejected strings are consumed completely, preserving affine ownership.
 * locale state must be stable during evaluation, as for the original strtof.
 */
static bool jaydb_f32_parse(int (*next)(void *), void *reader, float *value) {
  int c = next(reader);
  char token[JAYDB_F32_DIGITS + 16];
  unsigned n = 0, digits = 0;
  bool negative = false, point = false, any = false, sticky = false;
  __int128 scale = 0, exponent = 0;
  while (c >= 0 && isspace((unsigned char)c)) c = next(reader);
  if (c == '+' || c == '-') {
    negative = c == '-';
    c = next(reader);
  }
  if (negative) token[n++] = '-';
  if (c == 'i' || c == 'I' || c == 'n' || c == 'N') {
    const char *word = (c == 'i' || c == 'I') ? "infinity" : "nan";
    unsigned length = word[0] == 'i' ? 8 : 3;
    for (unsigned i = 0; i < length; ++i) {
      if (i == 3 && length == 8 && c == -1) break; /* inf */
      if (c < 0 || (c | 32) != word[i]) goto invalid;
      c = next(reader);
    }
    if (c != -1) goto invalid; /* includes forbidden NaN payloads */
    for (unsigned i = 0; i < 3; ++i) token[n++] = word[i];
    token[n] = 0;
    *value = strtof(token, NULL);
    return true;
  }
  /* The canonical output has no radix character. Only the input uses the
   * current locale's radix; this also works with a multibyte decimal point. */
  const unsigned char *radix = (const unsigned char *)localeconv()->decimal_point;
  while (c >= 0) {
    if (jaydb_f32_digit(c)) {
      unsigned digit = (unsigned)(c - '0');
      any = true;
      if (!digits) {
        if (point) --scale;
        if (digit) token[n++] = (char)c, ++digits;
      } else {
        if (!point) ++scale;
        if (digits < JAYDB_F32_DIGITS) token[n++] = (char)c, ++digits;
        else sticky |= digit != 0;
      }
      c = next(reader);
    } else if (!point && c == radix[0]) {
      for (unsigned i = 0; radix[i]; ++i) {
        /* Bend explicitly rejects x, X, ( anywhere in the UTF-8 text. */
        if (c != radix[i] || c == 'x' || c == 'X' || c == '(') goto invalid;
        c = next(reader);
      }
      point = true;
    } else break;
  }
  if (!any) goto invalid;
  if (c == 'e' || c == 'E') {
    c = next(reader);
    bool minus = c == '-';
    if (c == '+' || c == '-') c = next(reader);
    if (!jaydb_f32_digit(c)) goto invalid;
    /* Beyond this value no remaining exponent digits can cancel the decimal
     * position into binary32's range. This is arithmetic saturation, never
     * rejection of an exponent, precision or string length. Native list
     * lengths fit in uint64_t; signed 128-bit positions cannot overflow. */
    __int128 limit = (scale < 0 ? -scale : scale) + 512;
    do {
      exponent = exponent * 10 + c - '0';
      if (exponent > limit) exponent = limit;
      c = next(reader);
    } while (jaydb_f32_digit(c));
    if (minus) exponent = -exponent;
  }
  if (c != -1) goto invalid;
  if (!digits) {
    token[n++] = '0'; /* exact signed zero, even with an enormous exponent */
  } else {
    if (sticky) token[n++] = '1', ++digits;
    scale += exponent;
    if (scale > 512) scale = 512;
    if (scale < -512) scale = -512;
    int power = (int)scale - (int)digits + 1;
    token[n++] = 'e';
    if (power < 0) token[n++] = '-', power = -power;
    char reversed[4];
    unsigned count = 0;
    do { reversed[count++] = (char)('0' + power % 10); power /= 10; } while (power);
    while (count) token[n++] = reversed[--count];
  }
  token[n] = 0;
  *value = strtof(token, NULL);
  return true;

invalid:
  while (c != -1) c = next(reader);
  return false;
}
