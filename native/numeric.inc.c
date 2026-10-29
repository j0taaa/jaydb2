/* f32_text/show from official Bend 2.0.39 comp.ts (NATIVE.IO).
 * String construction uses the module arena; no malloc or stdio effects. */
static int f32_text(char* buf, f32 v) {
  int n = 0;
  int p = 0;
  if (v != v) {
    return sprintf(buf, "nan");
  }
  for (; p < 9; p += 1) {
    n = snprintf(buf, 40, "%.*e", p, (double)v);
    if (strtof(buf, NULL) == v) {
      break;
    }
  }
  char* ep = strchr(buf, 'e');
  if (ep == NULL) {
    return n;
  }
  int ex = atoi(ep + 1);
  if (ex >= 21 || ex <= -7) {
    return (int)(ep - buf) + sprintf(ep, "e%+d", ex);
  }
  // The scientific form has the rounded digits d, d[i] at the place ex - i:
  // write each place from the highest down, with a point before place -1.
  int  s = *buf == '-';
  char d[9];
  d[0] = buf[s];
  memcpy(d + 1, buf + s + 2, p);
  n = s;
  for (int q = ex > 0 ? ex : 0; q >= 0 || q >= ex - p; q -= 1) {
    if (q == -1) {
      buf[n++] = '.';
    }
    buf[n++] = q <= ex && q >= ex - p ? d[ex - q] : '0';
  }
  buf[n] = 0;
  return n;
}

static Term f32_show(Env e, Term x) {
  char buf[40];
  return io_str(e, buf, f32_text(buf, f32_unbox(x)));
}

#include "f32_parse.inc.c"

struct jaydb_f32_string {
  Env env;
  Term tail;
  unsigned char bytes[4];
  unsigned at, count;
};

static int jaydb_f32_next(void *context) {
  struct jaydb_f32_string *s = context;
  if (s->at < s->count) return s->bytes[s->at++];
  if (term_aux(s->tail) != CID_SCon) return -1;
  Term fields[2];
  spare_free(s->env, 1, ctr_take(s->env, s->tail, 2, fields));
  s->tail = fields[1];
  /* Identical to official io_utf8, including invalid Char replacement. */
  u64 c = fields[0];
  c = c > 0x10FFFF || (c >= 0xD800 && c <= 0xDFFF) ? 0xFFFD : c;
  unsigned k = c < 0x80 ? 1 : c < 0x800 ? 2 : c < 0x10000 ? 3 : 4;
  s->count = k;
  for (unsigned i = k; i > 1; --i) {
    s->bytes[i - 1] = (unsigned char)(0x80 | (c & 0x3F));
    c >>= 6;
  }
  s->bytes[0] = (unsigned char)(k == 1 ? c : (0xF00 >> k) | c);
  s->at = 1;
  return s->bytes[0];
}

static Term f32_read(Env e, Term string) {
  struct jaydb_f32_string reader = { .env = e, .tail = string };
  f32 value;
  bool valid = jaydb_f32_parse(jaydb_f32_next, &reader, &value);
  if (!valid) return term_pak(CID_None, 0);
  u64 at = heap_alloc(e, 0);
  Term word = f32_rewrap(value);
  e.mem[at] = cid_hot(CID_Some) ? rfc_seal(e, word) : word;
  return term_ctr(CID_Some, at);
}


