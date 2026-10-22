// The runtime of Flyscript compiled to C (see runtime.h).

#include "runtime.h"

#include <stdarg.h>
#ifndef FLY_FREESTANDING
#include <math.h>
#include <time.h>
#ifndef __wasm__
#include <sys/mman.h>
#endif
#endif

FLY_LOCAL void* fly_err = NULL;

typedef struct { uint32_t tag; size_t size; uint8_t data[]; } fly_failure;

void fly_err_box(uint32_t tag, const void* value, size_t size) {
  fly_failure* f = fly_alloc(sizeof(fly_failure) + size);
  f->tag = tag;
  f->size = size;
  memcpy(f->data, value, size);
  fly_err = f;
}

uint32_t fly_err_tag(void) { return ((fly_failure*)fly_err)->tag; }

void fly_err_take(void* out, size_t size) {
  fly_failure* f = fly_err;
  memcpy(out, f->data, f->size < size ? f->size : size);
  free(f);
  fly_err = NULL;
}

static _Noreturn void fiber_panic(const char* message);

// A panic unwinds the fiber it happens on; one on the main stack ends the program (§5.7).
_Noreturn void fly_panic(const char* message) { fiber_panic(message); }

#ifdef FLY_FREESTANDING
static _Noreturn void panic_exit(const char* message) { fly_os_panic(message, strlen(message)); }

// What a panic's message needs: `%d`, `%u`, `%llu`, `%lld`, `%zu`, `%s`, `%.*s` and `%%`.
static void format(char* out, size_t cap, const char* fmt, va_list ap) {
  size_t n = 0;
#define PUT(c) do { if (n + 1 < cap) out[n++] = (c); } while (0)
  for (const char* f = fmt; *f; f++) {
    if (*f != '%') { PUT(*f); continue; }
    f++;
    int prec = -1;
    if (f[0] == '.' && f[1] == '*') { prec = va_arg(ap, int); f += 2; }
    int longs = 0;
    while (*f == 'l') { longs++; f++; }
    bool size = *f == 'z';
    if (size) f++;
    if (*f == 's') {
      const char* s = va_arg(ap, const char*);
      for (int i = 0; s[i] && (prec < 0 || i < prec); i++) PUT(s[i]);
    } else if (*f == 'd' || *f == 'u') {
      unsigned long long u;
      bool neg = false;
      if (*f == 'd') {
        long long v = longs ? va_arg(ap, long long) : va_arg(ap, int);
        neg = v < 0;
        u = neg ? (unsigned long long)(-(v + 1)) + 1 : (unsigned long long)v;
      } else {
        u = size ? va_arg(ap, size_t) : longs ? va_arg(ap, unsigned long long) : va_arg(ap, unsigned);
      }
      char digits[24];
      int k = 0;
      do { digits[k++] = (char)('0' + u % 10); u /= 10; } while (u > 0);
      if (neg) PUT('-');
      while (k > 0) PUT(digits[--k]);
    } else if (*f == '%') {
      PUT('%');
    }
  }
#undef PUT
  out[n] = 0;
}
#else
static _Noreturn void panic_exit(const char* message) {
  fflush(stdout);
  printf("<panic: %s>\n", message);
  fflush(stdout);
  exit(101);
}

static void format(char* out, size_t cap, const char* fmt, va_list ap) { vsnprintf(out, cap, fmt, ap); }
#endif

_Noreturn void fly_panicf(const char* fmt, ...) {
  char buf[512];
  va_list ap;
  va_start(ap, fmt);
  format(buf, sizeof buf, fmt, ap);
  va_end(ap);
  fly_panic(buf);
}

// ---- integers ----

static void show128(fly_i128 v, char* out) {
  char tmp[64];
  int n = 0;
  unsigned __int128 u = v < 0 ? (unsigned __int128)(-(v + 1)) + 1 : (unsigned __int128)v;
  do { tmp[n++] = (char)('0' + (int)(u % 10)); u /= 10; } while (u > 0);
  int k = 0;
  if (v < 0) out[k++] = '-';
  while (n > 0) out[k++] = tmp[--n];
  out[k] = 0;
}

_Noreturn void fly_overflow(fly_i128 value, const char* type) {
  char num[64];
  show128(value, num);
  fly_panicf("arithmetic overflow: %s does not fit in `%s`", num, type);
}

// Overflowing `i128`, the widest type, is overflowing whatever the static type is.
fly_i128 fly_add128(fly_i128 a, fly_i128 b) {
  fly_i128 r;
  if (__builtin_add_overflow(a, b, &r)) fly_panic("arithmetic overflow");
  return r;
}
fly_i128 fly_sub128(fly_i128 a, fly_i128 b) {
  fly_i128 r;
  if (__builtin_sub_overflow(a, b, &r)) fly_panic("arithmetic overflow");
  return r;
}
fly_i128 fly_mul128(fly_i128 a, fly_i128 b) {
  fly_i128 r;
  if (__builtin_mul_overflow(a, b, &r)) fly_panic("arithmetic overflow");
  return r;
}
_Noreturn void fly_div_zero(void) { fly_panic("division by zero"); }

// ---- memory ----

void* fly_alloc(size_t size) {
  void* p = calloc(1, size ? size : 1);
  if (!p) fly_panic("out of memory");
  return p;
}

void* fly_arc_new(size_t size) {
  long* p = fly_alloc(16 + size);
  p[0] = 1;
  return (uint8_t*)p + 16;
}
// The count is shared by the tasks that share the value, on whichever cores they run.
void* fly_arc_retain(void* p) { __atomic_fetch_add((long*)((uint8_t*)p - 16), 1, __ATOMIC_RELAXED); return p; }
bool fly_arc_release(void* p) { return __atomic_sub_fetch((long*)((uint8_t*)p - 16), 1, __ATOMIC_ACQ_REL) == 0; }
void fly_arc_free(void* p) { free((uint8_t*)p - 16); }

void* fly_box(const void* value, size_t size) {
  void* p = fly_alloc(size);
  memcpy(p, value, size);
  return p;
}

// ---- strings ----

fly_str fly_str_lit(const char* bytes, size_t len) { return (fly_str){ (const uint8_t*)bytes, len }; }

fly_str fly_String_as_str(const fly_String* s) { return (fly_str){ s->ptr, s->len }; }

fly_String fly_String_new(void) { return (fly_String){ NULL, 0, 0 }; }

static void reserve(fly_String* s, size_t extra) {
  if (s->len + extra <= s->cap) return;
  size_t cap = s->cap ? s->cap * 2 : 16;
  while (cap < s->len + extra) cap *= 2;
  s->ptr = realloc(s->ptr, cap);
  if (!s->ptr) fly_panic("out of memory");
  s->cap = cap;
}

bool fly_String_try_reserve(fly_String* s, size_t extra) {
  if (s->len + extra <= s->cap) return true;
  if (extra > SIZE_MAX / 2 - s->len) return false;
  size_t cap = s->cap ? s->cap : 16;
  while (cap < s->len + extra) cap *= 2;
  uint8_t* p = realloc(s->ptr, cap);
  if (!p) return false;
  s->ptr = p;
  s->cap = cap;
  return true;
}

fly_String fly_String_from(fly_str t) {
  fly_String s = fly_String_new();
  fly_String_push(&s, t);
  return s;
}

void fly_String_push(fly_String* s, fly_str t) {
  if (t.len == 0) return;
  reserve(s, t.len);
  memcpy(s->ptr + s->len, t.ptr, t.len);
  s->len += t.len;
}

void fly_String_push_byte(fly_String* s, uint8_t b) {
  reserve(s, 1);
  s->ptr[s->len++] = b;
}

void fly_String_drop(fly_String* s) {
  free(s->ptr);
  *s = (fly_String){ 0 };
}

fly_String fly_String_clone(const fly_String* s) { return fly_String_from(fly_String_as_str(s)); }

bool fly_str_eq(fly_str a, fly_str b) { return a.len == b.len && (a.len == 0 || memcmp(a.ptr, b.ptr, a.len) == 0); }

int fly_str_cmp(fly_str a, fly_str b) {
  size_t n = a.len < b.len ? a.len : b.len;
  int c = n ? memcmp(a.ptr, b.ptr, n) : 0;
  if (c != 0) return c < 0 ? -1 : 1;
  return a.len < b.len ? -1 : a.len > b.len ? 1 : 0;
}

static bool continuation(fly_str s, size_t i) { return i < s.len && (s.ptr[i] & 0xc0) == 0x80; }

fly_str fly_str_slice(fly_str s, size_t lo, size_t hi) {
  if (lo > hi || hi > s.len) fly_panicf("range %zu..%zu out of bounds (length %zu)", lo, hi, s.len);
  // A string's bounds fall between characters: not on a UTF-8 continuation byte (§3.1).
  if (continuation(s, lo) || continuation(s, hi)) fly_panicf("range %zu..%zu splits a character", lo, hi);
  return (fly_str){ s.ptr + lo, hi - lo };
}

fly_String fly_show_i128(fly_i128 v) {
  char buf[64];
  show128(v, buf);
  return fly_String_from((fly_str){ (const uint8_t*)buf, strlen(buf) });
}

fly_String fly_show_u128(unsigned __int128 v) {
  char tmp[64];
  int n = 0;
  do { tmp[n++] = (char)('0' + (int)(v % 10)); v /= 10; } while (v > 0);
  char buf[64];
  for (int k = 0; k < n; k++) buf[k] = tmp[n - 1 - k];
  return fly_String_from((fly_str){ (const uint8_t*)buf, (size_t)n });
}

// As the reference prints a float: one decimal place when it is integral, else the shortest digits
// that read back as it.
#ifdef FLY_FREESTANDING
// Without the C library: the integer part and up to six decimals.
fly_String fly_show_f64(double v) {
  fly_String s = fly_String_new();
  if (v != v) { fly_String_push(&s, fly_str_lit("NaN", 3)); return s; }
  if (v < 0) { fly_String_push_byte(&s, '-'); v = -v; }
  if (v > 1e18) { fly_String_push(&s, fly_str_lit("inf", 3)); return s; }
  uint64_t whole = (uint64_t)v;
  fly_String w = fly_show_u128(whole);
  fly_String_push(&s, fly_String_as_str(&w));
  fly_String_drop(&w);
  uint64_t frac = (uint64_t)((v - (double)whole) * 1e6 + 0.5);
  fly_String_push_byte(&s, '.');
  char d[6];
  for (int k = 5; k >= 0; k--) { d[k] = (char)('0' + frac % 10); frac /= 10; }
  int last = 5;
  while (last > 0 && d[last] == '0') last--;
  for (int k = 0; k <= last; k++) fly_String_push_byte(&s, (uint8_t)d[k]);
  return s;
}
#else
fly_String fly_show_f64(double v) {
  char buf[64];
  if (isnan(v)) snprintf(buf, sizeof buf, "NaN");
  else if (isinf(v)) snprintf(buf, sizeof buf, v > 0 ? "inf" : "-inf");
  else if (v == floor(v) && fabs(v) < 1e15) snprintf(buf, sizeof buf, "%.1f", v);
  else {
    for (int p = 1; p <= 17; p++) {
      snprintf(buf, sizeof buf, "%.*g", p, v);
      if (strtod(buf, NULL) == v) break;
    }
  }
  return fly_String_from((fly_str){ (const uint8_t*)buf, strlen(buf) });
}
#endif

fly_String fly_show_bool(bool v) { return fly_String_from(v ? fly_str_lit("true", 4) : fly_str_lit("false", 5)); }

#ifndef FLY_FREESTANDING
void fly_println(fly_str s) {
  fwrite(s.ptr, 1, s.len, stdout);
  fputc('\n', stdout);
}
#endif

static bool space(uint8_t c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }

// As the reference's `lines()`: split at `\n`, a last empty line dropped, a `\r` before `\n` too.
bool fly_str_next_line(fly_str* rest, fly_str* line) {
  if (rest->len == 0) return false;
  size_t i = 0;
  while (i < rest->len && rest->ptr[i] != '\n') i++;
  *line = (fly_str){ rest->ptr, i };
  if (line->len > 0 && line->ptr[line->len - 1] == '\r') line->len--;
  size_t skip = i < rest->len ? i + 1 : i;
  rest->ptr += skip;
  rest->len -= skip;
  return true;
}

bool fly_str_next_word(fly_str* rest, fly_str* word) {
  while (rest->len > 0 && space(rest->ptr[0])) { rest->ptr++; rest->len--; }
  if (rest->len == 0) return false;
  size_t i = 0;
  while (i < rest->len && !space(rest->ptr[i])) i++;
  *word = (fly_str){ rest->ptr, i };
  rest->ptr += i;
  rest->len -= i;
  return true;
}

bool fly_str_find(fly_str s, fly_str needle, uint64_t* at) {
  if (needle.len == 0) { *at = 0; return true; }
  for (size_t i = 0; i + needle.len <= s.len; i++) {
    if (memcmp(s.ptr + i, needle.ptr, needle.len) == 0) { *at = i; return true; }
  }
  return false;
}

bool fly_str_starts(fly_str s, fly_str p) { return p.len <= s.len && (p.len == 0 || memcmp(s.ptr, p.ptr, p.len) == 0); }
bool fly_str_ends(fly_str s, fly_str p) { return p.len <= s.len && (p.len == 0 || memcmp(s.ptr + s.len - p.len, p.ptr, p.len) == 0); }

fly_str fly_str_trim(fly_str s) {
  while (s.len > 0 && space(s.ptr[0])) { s.ptr++; s.len--; }
  while (s.len > 0 && space(s.ptr[s.len - 1])) s.len--;
  return s;
}

// Strings hold UTF-8: only ASCII letters change case.
fly_String fly_str_case(fly_str s, bool upper) {
  fly_String out = fly_String_from(s);
  for (size_t i = 0; i < out.len; i++) {
    uint8_t c = out.ptr[i];
    if (upper && c >= 'a' && c <= 'z') out.ptr[i] = c - 32;
    if (!upper && c >= 'A' && c <= 'Z') out.ptr[i] = c + 32;
  }
  return out;
}

// As JavaScript's `s.split(from).join(to)`.
fly_String fly_str_replace_all(fly_str s, fly_str from, fly_str to) {
  fly_String out = fly_String_new();
  if (from.len == 0) {
    for (size_t i = 0; i < s.len; i++) {
      if (i > 0) fly_String_push(&out, to);
      fly_String_push_byte(&out, s.ptr[i]);
    }
    return out;
  }
  size_t i = 0;
  while (i < s.len) {
    if (i + from.len <= s.len && memcmp(s.ptr + i, from.ptr, from.len) == 0) {
      fly_String_push(&out, to);
      i += from.len;
    } else {
      fly_String_push_byte(&out, s.ptr[i++]);
    }
  }
  return out;
}

// As JavaScript's `s.split(sep)`: an empty separator splits between bytes.
fly_vec fly_str_split(fly_str s, fly_str sep) {
  fly_vec v = { 0 };
  if (sep.len == 0) {
    for (size_t i = 0; i < s.len; i++) {
      fly_String part = fly_String_from((fly_str){ s.ptr + i, 1 });
      fly_vec_push(&v, &part, sizeof part);
    }
    return v;
  }
  size_t start = 0, i = 0;
  while (i + sep.len <= s.len) {
    if (memcmp(s.ptr + i, sep.ptr, sep.len) == 0) {
      fly_String part = fly_String_from((fly_str){ s.ptr + start, i - start });
      fly_vec_push(&v, &part, sizeof part);
      i += sep.len;
      start = i;
    } else i++;
  }
  fly_String part = fly_String_from((fly_str){ s.ptr + start, s.len - start });
  fly_vec_push(&v, &part, sizeof part);
  return v;
}

// Decimal digits with an optional sign, which fit in an `i64`.
bool fly_parse_int(fly_str s, int64_t* out) {
  size_t i = 0;
  bool neg = false;
  if (i < s.len && (s.ptr[i] == '+' || s.ptr[i] == '-')) neg = s.ptr[i++] == '-';
  if (i == s.len) return false;
  fly_i128 v = 0;
  for (; i < s.len; i++) {
    if (s.ptr[i] < '0' || s.ptr[i] > '9') return false;
    v = v * 10 + (s.ptr[i] - '0');
    if (v > (fly_i128)INT64_MAX + 1) fly_panic("integer literal out of range");
  }
  if (neg) v = -v;
  if (v > INT64_MAX) fly_panic("integer literal out of range");
  *out = (int64_t)v;
  return true;
}

#ifdef FLY_FREESTANDING
// Without the C library: digits, a point and digits, an exponent.
bool fly_parse_float(fly_str s, double* out) {
  fly_str t = fly_str_trim(s);
  size_t i = 0;
  if (t.len == 0) return false;
  bool neg = t.ptr[0] == '-';
  if (neg || t.ptr[0] == '+') i++;
  double v = 0;
  bool digits = false;
  while (i < t.len && t.ptr[i] >= '0' && t.ptr[i] <= '9') { v = v * 10 + (t.ptr[i++] - '0'); digits = true; }
  if (i < t.len && t.ptr[i] == '.') {
    i++;
    double scale = 0.1;
    while (i < t.len && t.ptr[i] >= '0' && t.ptr[i] <= '9') { v += (t.ptr[i++] - '0') * scale; scale /= 10; digits = true; }
  }
  if (!digits) return false;
  if (i < t.len && (t.ptr[i] == 'e' || t.ptr[i] == 'E')) {
    i++;
    bool eneg = i < t.len && t.ptr[i] == '-';
    if (i < t.len && (t.ptr[i] == '-' || t.ptr[i] == '+')) i++;
    int e = 0;
    while (i < t.len && t.ptr[i] >= '0' && t.ptr[i] <= '9') e = e * 10 + (t.ptr[i++] - '0');
    while (e-- > 0) v = eneg ? v / 10 : v * 10;
  }
  if (i != t.len) return false;
  *out = neg ? -v : v;
  return true;
}
#else
// As JavaScript's `Number(s)` on text that is not blank.
bool fly_parse_float(fly_str s, double* out) {
  fly_str t = fly_str_trim(s);
  if (t.len == 0 || t.len > 255) return false;
  char buf[256];
  memcpy(buf, t.ptr, t.len);
  buf[t.len] = 0;
  char* end;
  double v = strtod(buf, &end);
  if (*end != 0 || isnan(v)) return false;
  *out = v;
  return true;
}
#endif

// ---- lists ----

_Noreturn void fly_out_of_bounds(uint64_t i, uint64_t len) {
  fly_panicf("index %llu out of bounds (length %llu)", (unsigned long long)i, (unsigned long long)len);
}

void* fly_vec_at(const fly_vec* v, size_t i, size_t size) {
  if (i >= v->len) fly_panicf("index %zu out of bounds (length %zu)", i, v->len);
  return (char*)v->ptr + i * size;
}

static void vreserve(fly_vec* v, size_t extra, size_t size) {
  if (v->len + extra <= v->cap) return;
  size_t cap = v->cap ? v->cap * 2 : 4;
  while (cap < v->len + extra) cap *= 2;
  v->ptr = realloc(v->ptr, cap * size);
  if (!v->ptr) fly_panic("out of memory");
  v->cap = cap;
}

bool fly_vec_try_reserve(fly_vec* v, size_t extra, size_t size) {
  if (v->len + extra <= v->cap) return true;
  size_t unit = size ? size : 1;
  if (extra > SIZE_MAX / 2 / unit - v->len) return false;
  size_t cap = v->cap ? v->cap : 4;
  while (cap < v->len + extra) cap *= 2;
  void* p = realloc(v->ptr, cap * unit);
  if (!p) return false;
  v->ptr = p;
  v->cap = cap;
  return true;
}

void fly_vec_push(fly_vec* v, const void* elem, size_t size) {
  vreserve(v, 1, size);
  memcpy((char*)v->ptr + v->len * size, elem, size);
  v->len++;
}

bool fly_vec_pop(fly_vec* v, void* out, size_t size) {
  if (v->len == 0) return false;
  v->len--;
  memcpy(out, (char*)v->ptr + v->len * size, size);
  return true;
}

void fly_vec_insert(fly_vec* v, size_t i, const void* elem, size_t size) {
  if (i > v->len) fly_panicf("index %zu out of bounds (length %zu)", i, v->len);
  vreserve(v, 1, size);
  char* p = (char*)v->ptr;
  memmove(p + (i + 1) * size, p + i * size, (v->len - i) * size);
  memcpy(p + i * size, elem, size);
  v->len++;
}

void fly_vec_remove(fly_vec* v, size_t i, void* out, size_t size) {
  if (i >= v->len) fly_panicf("index %zu out of bounds (length %zu)", i, v->len);
  char* p = (char*)v->ptr;
  memcpy(out, p + i * size, size);
  memmove(p + i * size, p + (i + 1) * size, (v->len - i - 1) * size);
  v->len--;
}

void fly_vec_truncate_raw(fly_vec* v, size_t n) { if (n < v->len) v->len = n; }

void fly_vec_free(fly_vec* v) {
  free(v->ptr);
  *v = (fly_vec){ 0 };
}

fly_slice fly_vec_slice(const fly_vec* v) { return (fly_slice){ v->ptr, v->len }; }

void* fly_slice_at(fly_slice s, size_t i, size_t size) {
  if (i >= s.len) fly_panicf("index %zu out of bounds (length %zu)", i, s.len);
  return (char*)s.ptr + i * size;
}

fly_slice fly_slice_range(fly_slice s, size_t lo, size_t hi, size_t size) {
  if (lo > hi || hi > s.len) fly_panicf("range %zu..%zu out of bounds (length %zu)", lo, hi, s.len);
  return (fly_slice){ (char*)s.ptr + lo * size, hi - lo };
}

fly_vec fly_vec_from(const void* elems, size_t n, size_t size) {
  fly_vec v = { 0 };
  if (n == 0) return v;
  vreserve(&v, n, size);
  memcpy(v.ptr, elems, n * size);
  v.len = n;
  return v;
}

void fly_slice_reverse(fly_slice s, size_t size) {
  uint8_t tmp[256];
  uint8_t* p = s.ptr;
  if (size > sizeof tmp) fly_panic("element too large to reverse");
  for (size_t i = 0, j = s.len ? s.len - 1 : 0; i < j; i++, j--) {
    memcpy(tmp, p + i * size, size);
    memcpy(p + i * size, p + j * size, size);
    memcpy(p + j * size, tmp, size);
  }
}

// A merge sort, which keeps equal elements in order.
void fly_sort(fly_slice s, size_t size, int (*cmp)(void*, const void*, const void*), void* ctx) {
  if (s.len < 2) return;
  uint8_t* a = s.ptr;
  uint8_t* buf = fly_alloc(s.len * size);
  for (size_t width = 1; width < s.len; width *= 2) {
    for (size_t lo = 0; lo < s.len; lo += 2 * width) {
      size_t mid = lo + width < s.len ? lo + width : s.len;
      size_t hi = lo + 2 * width < s.len ? lo + 2 * width : s.len;
      size_t i = lo, j = mid, k = lo;
      while (i < mid && j < hi) {
        if (cmp(ctx, a + j * size, a + i * size) < 0) memcpy(buf + k++ * size, a + j++ * size, size);
        else memcpy(buf + k++ * size, a + i++ * size, size);
      }
      while (i < mid) memcpy(buf + k++ * size, a + i++ * size, size);
      while (j < hi) memcpy(buf + k++ * size, a + j++ * size, size);
    }
    memcpy(a, buf, s.len * size);
  }
  free(buf);
}

// ---- maps ----

static void reindex(fly_map* m) {
  free(m->slots);
  m->nslots = 8;
  while (m->nslots < m->len * 2) m->nslots *= 2;
  m->slots = fly_alloc(m->nslots * sizeof(uint32_t));
  for (size_t i = 0; i < m->len; i++) {
    size_t s = m->hashes[i] & (m->nslots - 1);
    while (m->slots[s]) s = (s + 1) & (m->nslots - 1);
    m->slots[s] = (uint32_t)(i + 1);
  }
}

size_t fly_map_find(const fly_map* m, uint64_t h, const void* probe, bool (*eq)(const void*, const void*), size_t esize) {
  if (m->len == 0) return SIZE_MAX;
  for (size_t s = h & (m->nslots - 1); m->slots[s]; s = (s + 1) & (m->nslots - 1)) {
    size_t i = m->slots[s] - 1;
    if (m->hashes[i] == h && eq(m->entries + i * esize, probe)) return i;
  }
  return SIZE_MAX;
}

bool fly_map_try_reserve(fly_map* m, size_t extra, size_t esize) {
  size_t want = m->len + extra;
  if (extra > SIZE_MAX / 4 / (esize + sizeof(uint64_t) + 2 * sizeof(uint32_t)) - m->len) return false;
  if (want > m->cap) {
    size_t cap = m->cap ? m->cap : 8;
    while (cap < want) cap *= 2;
    uint8_t* e = realloc(m->entries, cap * esize);
    if (!e) return false;
    m->entries = e;
    uint64_t* h = realloc(m->hashes, cap * sizeof(uint64_t));
    if (!h) return false;
    m->hashes = h;
    m->cap = cap;
  }
  // The index is made big enough now, so inserting `extra` more never rebuilds it.
  size_t n = 8;
  while (n < want * 2) n *= 2;
  if (n > m->nslots) {
    uint32_t* slots = calloc(n, sizeof(uint32_t));
    if (!slots) return false;
    free(m->slots);
    m->slots = slots;
    m->nslots = n;
    for (size_t i = 0; i < m->len; i++) {
      size_t k = m->hashes[i] & (m->nslots - 1);
      while (m->slots[k]) k = (k + 1) & (m->nslots - 1);
      m->slots[k] = (uint32_t)(i + 1);
    }
  }
  return true;
}

void* fly_map_append(fly_map* m, uint64_t h, size_t esize) {
  if (m->len == m->cap) {
    m->cap = m->cap ? m->cap * 2 : 8;
    m->entries = realloc(m->entries, m->cap * esize);
    m->hashes = realloc(m->hashes, m->cap * sizeof(uint64_t));
    if (!m->entries || !m->hashes) fly_panic("out of memory");
  }
  size_t i = m->len++;
  m->hashes[i] = h;
  memset(m->entries + i * esize, 0, esize);
  if (m->len * 2 > m->nslots) reindex(m);
  else {
    size_t s = h & (m->nslots - 1);
    while (m->slots[s]) s = (s + 1) & (m->nslots - 1);
    m->slots[s] = (uint32_t)(i + 1);
  }
  return m->entries + i * esize;
}

// Removes entry `i` into `out`; those after it move down, as the reference's do.
void fly_map_remove_at(fly_map* m, size_t i, void* out, size_t esize) {
  memcpy(out, m->entries + i * esize, esize);
  memmove(m->entries + i * esize, m->entries + (i + 1) * esize, (m->len - i - 1) * esize);
  memmove(m->hashes + i, m->hashes + i + 1, (m->len - i - 1) * sizeof(uint64_t));
  m->len--;
  reindex(m);
}

void fly_map_free(fly_map* m) {
  free(m->entries);
  free(m->hashes);
  free(m->slots);
  *m = (fly_map){ 0 };
}

fly_Hasher fly_Hasher_new(void) { return (fly_Hasher){ 0xcbf29ce484222325ull }; }
static void hash_bytes(fly_Hasher* h, const uint8_t* p, size_t n) {
  for (size_t i = 0; i < n; i++) h->h = (h->h ^ p[i]) * 0x100000001b3ull;
}
void fly_Hasher_writeInt(fly_Hasher* h, int64_t v) {
  uint8_t b[8];
  for (int k = 0; k < 8; k++) b[k] = (uint8_t)((uint64_t)v >> (8 * k));
  hash_bytes(h, b, 8);
}
#ifdef FLY_FREESTANDING
// Without the C library: by its bits, `-0.0` as `0.0`.
void fly_Hasher_writeFloat(fly_Hasher* h, double v) {
  if (v == 0) v = 0;
  uint8_t b[8];
  memcpy(b, &v, 8);
  hash_bytes(h, b, 8);
}
#else
// A float hashes as the reference shows it, so `-0.0` hashes as `0.0`.
void fly_Hasher_writeFloat(fly_Hasher* h, double v) {
  char buf[64];
  if (v == 0) v = 0;
  if (isnan(v)) snprintf(buf, sizeof buf, "NaN");
  else if (v == floor(v) && fabs(v) < 1e21) snprintf(buf, sizeof buf, "%.0f", v);
  else {
    for (int p = 1; p <= 17; p++) {
      snprintf(buf, sizeof buf, "%.*g", p, v);
      if (strtod(buf, NULL) == v) break;
    }
  }
  hash_bytes(h, (const uint8_t*)buf, strlen(buf));
}
#endif
void fly_Hasher_writeBool(fly_Hasher* h, bool v) { uint8_t b = v; hash_bytes(h, &b, 1); }
void fly_Hasher_writeStr(fly_Hasher* h, fly_str s) { hash_bytes(h, s.ptr, s.len); }
uint64_t fly_Hasher_finish(const fly_Hasher* h) { return h->h; }

// ---- generators ----

FLY_LOCAL bool fly_stopping = false;

void* fly_iter_new(void* base, size_t len, size_t stride) {
  fly_iter* it = fly_alloc(sizeof(fly_iter));
  *it = (fly_iter){ base, len, 0, stride };
  return it;
}

void fly_gen_drop(fly_gen* g) {
  if (g->drop) g->drop(g->st);
  *g = (fly_gen){ 0 };
}

void* fly_gmap_new(fly_gen in, fly_fn f) {
  fly_gmap* s = fly_alloc(sizeof(fly_gmap));
  *s = (fly_gmap){ in, f };
  return s;
}
void* fly_gcount_new(fly_gen in, uint64_t n) {
  fly_gcount* s = fly_alloc(sizeof(fly_gcount));
  *s = (fly_gcount){ in, n };
  return s;
}
void* fly_gzip_new(fly_gen a, fly_gen b) {
  fly_gzip* s = fly_alloc(sizeof(fly_gzip));
  *s = (fly_gzip){ a, b };
  return s;
}
// An adapter is lent its function: whoever made the function drops it.
void fly_gmap_drop(void* s) { fly_gen_drop(&((fly_gmap*)s)->in); free(s); }
void fly_gcount_drop(void* s) { fly_gen_drop(&((fly_gcount*)s)->in); free(s); }
void fly_gzip_drop(void* s) { fly_gen_drop(&((fly_gzip*)s)->a); fly_gen_drop(&((fly_gzip*)s)->b); free(s); }

// ---- fibers ----

// Switching saves the callee-saved registers on the stack being left, and its stack pointer in
// the fiber being left, then restores the other's. A new fiber's stack holds a frame that returns
// into fly_fiber_trampoline, with the fiber where the restore puts it.

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#define FLY_ASAN 1
#endif
#endif
#if defined(__SANITIZE_ADDRESS__)
#define FLY_ASAN 1
#endif
#ifdef FLY_ASAN
void __sanitizer_start_switch_fiber(void** fake_stack_save, const void* bottom, size_t size);
void __sanitizer_finish_switch_fiber(void* fake_stack_save, const void** bottom_old, size_t* size_old);
#endif
// The thread sanitizer follows fibers as threads of its own.
#if defined(__has_feature)
#if __has_feature(thread_sanitizer)
#define FLY_TSAN 1
#endif
#endif
#if defined(__SANITIZE_THREAD__)
#define FLY_TSAN 1
#endif
#ifdef FLY_TSAN
void* __tsan_get_current_fiber(void);
void* __tsan_create_fiber(unsigned flags);
void __tsan_destroy_fiber(void* fiber);
void __tsan_switch_to_fiber(void* fiber, unsigned flags);
#endif

struct fly_fiber {
  // Whether the fiber ended in a panic: it stops where it panicked, never to run again.
  bool panicked;
  // Whether it is a thread's own stack, which a panic cannot leave.
  bool base;
  void* sp;
  void* stack;
  size_t size;
  void (*entry)(void* arg);
  void* arg;
  fly_fiber* back;
  fly_handler* handlers;
  bool done;
#ifdef FLY_TSAN
  void* tsan;
#endif
};

static fly_fiber main_fiber = { .base = true };
static FLY_LOCAL fly_fiber* current = &main_fiber;
FLY_LOCAL fly_handler* fly_handlers = NULL;
FLY_LOCAL bool fly_unwinding = false;

void fly_switch(void** save, void* to);
void fly_fiber_trampoline(void);
void fly_fiber_start(fly_fiber* f);

#ifdef __APPLE__
#define FLY_SYM(x) "_" #x
#else
#define FLY_SYM(x) #x
#endif

#if defined(__aarch64__) || defined(__arm64__)
__asm__(
  ".text\n.p2align 2\n.globl " FLY_SYM(fly_switch) "\n" FLY_SYM(fly_switch) ":\n"
  "  sub sp, sp, #160\n"
  "  stp x19, x20, [sp, #0]\n  stp x21, x22, [sp, #16]\n  stp x23, x24, [sp, #32]\n"
  "  stp x25, x26, [sp, #48]\n  stp x27, x28, [sp, #64]\n  stp x29, x30, [sp, #80]\n"
  "  stp d8, d9, [sp, #96]\n  stp d10, d11, [sp, #112]\n  stp d12, d13, [sp, #128]\n  stp d14, d15, [sp, #144]\n"
  "  mov x9, sp\n  str x9, [x0]\n  mov sp, x1\n"
  "  ldp x19, x20, [sp, #0]\n  ldp x21, x22, [sp, #16]\n  ldp x23, x24, [sp, #32]\n"
  "  ldp x25, x26, [sp, #48]\n  ldp x27, x28, [sp, #64]\n  ldp x29, x30, [sp, #80]\n"
  "  ldp d8, d9, [sp, #96]\n  ldp d10, d11, [sp, #112]\n  ldp d12, d13, [sp, #128]\n  ldp d14, d15, [sp, #144]\n"
  "  add sp, sp, #160\n  ret\n"
  ".globl " FLY_SYM(fly_fiber_trampoline) "\n" FLY_SYM(fly_fiber_trampoline) ":\n"
  "  mov x0, x19\n  bl " FLY_SYM(fly_fiber_start) "\n  brk #0\n");
enum { FRAME_WORDS = 20, FRAME_FIBER = 0, FRAME_RETURN = 11 };
#elif defined(__x86_64__)
__asm__(
  ".text\n.globl " FLY_SYM(fly_switch) "\n" FLY_SYM(fly_switch) ":\n"
  "  pushq %rbp\n  pushq %rbx\n  pushq %r12\n  pushq %r13\n  pushq %r14\n  pushq %r15\n"
  "  movq %rsp, (%rdi)\n  movq %rsi, %rsp\n"
  "  popq %r15\n  popq %r14\n  popq %r13\n  popq %r12\n  popq %rbx\n  popq %rbp\n  ret\n"
  ".globl " FLY_SYM(fly_fiber_trampoline) "\n" FLY_SYM(fly_fiber_trampoline) ":\n"
  "  movq %rbx, %rdi\n  call " FLY_SYM(fly_fiber_start) "\n  ud2\n");
enum { FRAME_WORDS = 8, FRAME_FIBER = 4, FRAME_RETURN = 6 };
#elif defined(__wasm__)
// WebAssembly cannot switch stacks itself: the host does, with JavaScript promise integration.
// Each fiber runs as a call of `fly_fiber_run` of its own, on a shadow stack of its own in linear
// memory, so what a suspended fiber lent stays where it is. Switching suspends the fiber leaving
// and resumes, or starts, the other; the host keeps each fiber's stack pointer meanwhile.
__attribute__((import_module("fly"), import_name("switch"))) void fly_host_switch(fly_fiber* from, fly_fiber* to);
__attribute__((import_module("fly"), import_name("free"))) void fly_host_free(fly_fiber* f);
__attribute__((export_name("fly_fiber_run"))) void fly_fiber_run(fly_fiber* f) { fly_fiber_start(f); }
__attribute__((export_name("fly_fiber_top"))) uintptr_t fly_fiber_top(fly_fiber* f);
#else
#error "fibers need arm64, x86-64 or WebAssembly"
#endif

static void switch_to(fly_fiber* to) {
  fly_fiber* from = current;
  from->handlers = fly_handlers;
  fly_handlers = to->handlers;
  current = to;
#if defined(FLY_ASAN)
  void* fake = NULL;
  __sanitizer_start_switch_fiber(from->done ? NULL : &fake, to->stack, to->size);
  fly_switch(&from->sp, to->sp);
  __sanitizer_finish_switch_fiber(fake, NULL, NULL);
#elif defined(FLY_TSAN)
  if (!from->tsan) from->tsan = __tsan_get_current_fiber();
  __tsan_switch_to_fiber(to->tsan, 0);
  fly_switch(&from->sp, to->sp);
#elif defined(__wasm__)
  fly_host_switch(from, to);
#else
  fly_switch(&from->sp, to->sp);
#endif
}

// The panic unwinding, until whoever started the fiber it began on takes it up.
static FLY_LOCAL char* panicking = NULL;
// The `Mutex` lock this thread holds, if any: a panic in its body gives it back.
static void unlock_held(void);

void fly_fiber_start(fly_fiber* f) {
#ifdef FLY_ASAN
  // The first fiber a thread starts is switched to from the thread's own stack, whose bounds the
  // sanitizer reports here: what switching back to it says.
  const void* bottom;
  size_t size;
  __sanitizer_finish_switch_fiber(NULL, &bottom, &size);
  if (f->back->base && !f->back->stack) {
    f->back->stack = (void*)bottom;
    f->back->size = size;
  }
#endif
  f->entry(f->arg);
  f->done = true;
  switch_to(f->back);
}

static _Noreturn void fiber_panic(const char* message) {
  unlock_held();
  if (current->base) panic_exit(message);
  if (!panicking) {
    size_t n = strlen(message);
    panicking = malloc(n + 1);
    memcpy(panicking, message, n + 1);
  }
  // The fiber ends here, as a finished one does, and whoever resumed it takes the panic up.
  current->panicked = true;
  current->done = true;
  switch_to(current->back);
  __builtin_trap();
}

// After a fiber this code resumed has run: a panic it ended with goes on here.
static void panic_goes_on(void) {
  if (panicking) fiber_panic(panicking);
}

#if defined(FLY_FREESTANDING) || defined(__wasm__)
// Stacks come from the program's memory, whole.
#define FLY_STACK (256u << 10)
static void* stack_new(size_t size) {
  void* p = malloc(size);
  if (!p) fly_panic("out of memory");
  return p;
}
static void stack_free(void* p, size_t size) { (void)size; free(p); }
#else
// Stacks are reserved large and committed as they are touched. A thread keeps a few it is done
// with, for the fibers it starts next.
#define FLY_STACK (64u << 20)
// The sanitizers keep what they knew of a stack's last frames, so under them none is kept.
#if defined(FLY_ASAN) || defined(FLY_TSAN)
enum { STACK_POOL = 0 };
#else
enum { STACK_POOL = 16 };
#endif
static FLY_LOCAL struct { void* stacks[STACK_POOL + 1]; int n; } stack_pool;
static void* stack_new(size_t size) {
  if (stack_pool.n > 0) return stack_pool.stacks[--stack_pool.n];
  void* p = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
  if (p == MAP_FAILED) fly_panic("out of memory");
  return p;
}
static void stack_free(void* p, size_t size) {
  if (stack_pool.n < STACK_POOL) stack_pool.stacks[stack_pool.n++] = p;
  else munmap(p, size);
}
#endif

static fly_fiber* fiber_new(void (*entry)(void*), void* arg, fly_handler* handlers) {
  fly_fiber* f = fly_alloc(sizeof(fly_fiber));
  f->size = FLY_STACK;
  f->stack = stack_new(f->size);
  f->entry = entry;
  f->arg = arg;
  f->handlers = handlers;
#ifdef FLY_TSAN
  f->tsan = __tsan_create_fiber(0);
#endif
#ifndef __wasm__
  // Otherwise the host starts it at the top of its stack.
  uintptr_t top = ((uintptr_t)f->stack + f->size) & ~(uintptr_t)15;
  void** frame = (void**)(top - FRAME_WORDS * sizeof(void*));
  memset(frame, 0, FRAME_WORDS * sizeof(void*));
  frame[FRAME_FIBER] = f;
  frame[FRAME_RETURN] = (void*)fly_fiber_trampoline;
  f->sp = frame;
#endif
  return f;
}

static void fiber_free(fly_fiber* f) {
#ifdef __wasm__
  fly_host_free(f);
#endif
#ifdef FLY_TSAN
  __tsan_destroy_fiber(f->tsan);
#endif
  stack_free(f->stack, f->size);
  free(f);
}

#ifdef __wasm__
uintptr_t fly_fiber_top(fly_fiber* f) { return ((uintptr_t)f->stack + f->size) & ~(uintptr_t)15; }
#endif

// ---- handlers ----

void fly_perform(uint32_t effect, int op, void* args, void* result) {
  fly_handler* h = fly_handlers;
  while (h && h->effect != effect) h = h->outer;
  if (!h) fly_panic("an effect is performed that nothing handles");
  h->op = op;
  h->args = args;
  h->result = result;
  h->suspended = current;
  switch_to(h->fiber->back);
}

void fly_handle_start(fly_handler* h, void (*entry)(void*), void* arg) {
  h->outer = fly_handlers;
  h->op = -1;
  h->fiber = fiber_new(entry, arg, h);
  h->fiber->back = current;
  switch_to(h->fiber);
  panic_goes_on();
}

// The handler is deep: what else the body performs goes to the handlers around the resumption.
void fly_handle_resume(fly_handler* h) {
  h->fiber->back = current;
  h->outer = fly_handlers;
  h->op = -1;
  switch_to(h->suspended);
  panic_goes_on();
}

bool fly_handle_done(const fly_handler* h) { return h->fiber->done; }

void fly_handle_unwind(fly_handler* h) {
  if (!h->fiber || h->fiber->done) return;
  bool was = fly_unwinding;
  fly_unwinding = true;
  fly_handle_resume(h);
  fly_unwinding = was;
}

void fly_handle_free(fly_handler* h) {
  if (h->fiber) fiber_free(h->fiber);
  h->fiber = NULL;
}

fly_unwind_state fly_cleanup_begin(void) {
  fly_unwind_state s = { fly_err, fly_unwinding, fly_stopping };
  fly_err = NULL;
  fly_unwinding = false;
  fly_stopping = false;
  return s;
}

void fly_cleanup_end(fly_unwind_state s) {
  fly_err = s.err;
  fly_unwinding = s.unwinding;
  fly_stopping = s.stopping;
}

void fly_cont_drop(fly_cont* k) {
  if (k->drop) k->drop(k->frame);
  *k = (fly_cont){ 0 };
}

// ---- `generate` ----

// The producer runs under a handler of nothing, whose outer handlers are those around each
// `next()`, so what else it performs goes to them.
typedef struct {
  fly_handler h;
  fly_fn producer;
  size_t size;
  void* out;
  bool started;
  uint8_t item[];
} fly_generated;

static bool generated_yield(void* env, void* item) {
  fly_generated* g = env;
  memcpy(g->out, item, g->size);
  g->h.suspended = current;
  g->h.op = 0;
  switch_to(g->h.fiber->back);
  return !fly_unwinding;
}

static void generated_run(void* arg) {
  fly_generated* g = arg;
  ((fly_unit (*)(void*, fly_yield))g->producer.fn)(g->producer.env, (fly_yield){ g, generated_yield });
}

static bool generated_next(void* st, void* out) {
  fly_generated* g = st;
  if (g->started && g->h.fiber->done) return false;
  g->out = out;
  g->h.op = -1;
  if (!g->started) {
    g->started = true;
    g->h.effect = UINT32_MAX;
    fly_handle_start(&g->h, generated_run, g);
  } else {
    fly_handle_resume(&g->h);
  }
  return !g->h.fiber->done;
}

static void generated_drop(void* st) {
  fly_generated* g = st;
  if (g->started) {
    fly_handle_unwind(&g->h);
    fly_handle_free(&g->h);
  }
  fly_fn* f = &g->producer;
  if (f->drop) f->drop(f->env);
  free(g);
}

fly_gen fly_generate(fly_fn producer, size_t size) {
  fly_generated* g = fly_alloc(sizeof(fly_generated) + size);
  g->producer = producer;
  g->size = size;
  return (fly_gen){ g, generated_next, generated_drop };
}

#ifndef FLY_FREESTANDING
// ---- the simulated world ----

typedef struct { fly_str key, val; } world_pair;
static struct {
  bool loaded;
  fly_str* incoming;
  size_t nincoming, accepted;
  world_pair* profiles;
  size_t nprofiles;
  world_pair* quotas;
  size_t nquotas;
  uint64_t faults, seed;
  // Whether there is a world to simulate: otherwise time is the machine's, and tasks its cores'.
  bool simulated;
} world;
uint64_t fly_clock = 0;
static uint64_t fault_rng;

// A small reader of the world's JSON: strings, numbers, booleans, arrays and objects.
static const char* json_at;
static void json_space(void) { while (*json_at == ' ' || *json_at == '\n' || *json_at == '\r' || *json_at == '\t') json_at++; }
static fly_str json_string(void) {
  json_space();
  if (*json_at != '"') fly_panic("FLY_WORLD: a string was expected");
  json_at++;
  fly_String out = fly_String_new();
  while (*json_at && *json_at != '"') {
    char c = *json_at++;
    if (c == '\\') {
      char e = *json_at++;
      switch (e) {
        case 'n': c = '\n'; break;
        case 'r': c = '\r'; break;
        case 't': c = '\t'; break;
        case 'b': c = '\b'; break;
        case 'f': c = '\f'; break;
        case 'u': { unsigned v = 0; for (int i = 0; i < 4; i++) { char h = *json_at++; v = v * 16 + (unsigned)(h <= '9' ? h - '0' : (h | 32) - 'a' + 10); } c = (char)v; break; }
        default: c = e;
      }
    }
    fly_String_push_byte(&out, (uint8_t)c);
  }
  json_at++;
  return (fly_str){ out.ptr, out.len };
}
static void json_skip(void);
static void json_skip(void) {
  json_space();
  if (*json_at == '"') { free((void*)json_string().ptr); return; }
  if (*json_at == '[' || *json_at == '{') {
    char close = *json_at == '[' ? ']' : '}';
    json_at++;
    json_space();
    while (*json_at && *json_at != close) {
      if (close == '}') { free((void*)json_string().ptr); json_space(); json_at++; }
      json_skip();
      json_space();
      if (*json_at == ',') json_at++;
      json_space();
    }
    json_at++;
    return;
  }
  while (*json_at && *json_at != ',' && *json_at != '}' && *json_at != ']') json_at++;
}
static void json_pairs(world_pair** out, size_t* n, bool booleans) {
  json_space();
  json_at++;
  size_t cap = 0;
  json_space();
  while (*json_at && *json_at != '}') {
    fly_str k = json_string();
    json_space();
    json_at++;
    json_space();
    fly_str v = { 0 };
    if (booleans) { v = (fly_str){ (const uint8_t*)(strncmp(json_at, "true", 4) == 0 ? "t" : "f"), 1 }; json_skip(); }
    else if (*json_at == '"') v = json_string();
    else json_skip();
    if (*n == cap) { cap = cap ? cap * 2 : 8; *out = realloc(*out, cap * sizeof(world_pair)); }
    (*out)[(*n)++] = (world_pair){ k, v };
    json_space();
    if (*json_at == ',') json_at++;
    json_space();
  }
  json_at++;
}
static void world_load(void) {
  if (world.loaded) return;
  world.loaded = true;
  world.seed = 0x5eed;
  const char* w = getenv("FLY_WORLD");
  world.simulated = w != NULL;
  if (w && *w) {
    json_at = w;
    json_space();
    json_at++;
    json_space();
    while (*json_at && *json_at != '}') {
      fly_str k = json_string();
      json_space();
      json_at++;
      json_space();
      if (fly_str_eq(k, fly_str_lit("incoming", 8))) {
        json_at++;
        size_t cap = 0;
        json_space();
        while (*json_at && *json_at != ']') {
          if (world.nincoming == cap) { cap = cap ? cap * 2 : 8; world.incoming = realloc(world.incoming, cap * sizeof(fly_str)); }
          world.incoming[world.nincoming++] = json_string();
          json_space();
          if (*json_at == ',') json_at++;
          json_space();
        }
        json_at++;
      } else if (fly_str_eq(k, fly_str_lit("profiles", 8))) {
        json_pairs(&world.profiles, &world.nprofiles, false);
      } else if (fly_str_eq(k, fly_str_lit("quotas", 6))) {
        json_pairs(&world.quotas, &world.nquotas, true);
      } else if (fly_str_eq(k, fly_str_lit("faults", 6)) || fly_str_eq(k, fly_str_lit("seed", 4))) {
        uint64_t v = strtoull(json_at, (char**)&json_at, 10);
        if (k.len == 6) world.faults = v; else world.seed = v;
      } else {
        json_skip();
      }
      free((void*)k.ptr);
      json_space();
      if (*json_at == ',') json_at++;
      json_space();
    }
  }
  fault_rng = world.seed > 1 ? world.seed : 1;
}

static uint64_t xorshift(uint64_t* r) {
  uint64_t x = *r;
  x ^= x << 13;
  x ^= x >> 7;
  x ^= x << 17;
  return *r = x;
}

bool fly_fault(void) {
  world_load();
  return world.faults > 0 && xorshift(&fault_rng) % 100 < world.faults;
}

bool fly_world_accept(fly_str* input) {
  world_load();
  size_t i = __atomic_fetch_add(&world.accepted, 1, __ATOMIC_RELAXED);
  if (i >= world.nincoming) return false;
  *input = world.incoming[i];
  return true;
}

uint64_t fly_now(void) {
  world_load();
  if (world.simulated) return fly_clock;
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec;
}

bool fly_world_profile(fly_str user, fly_str* name) {
  world_load();
  for (size_t i = 0; i < world.nprofiles; i++) {
    if (fly_str_eq(world.profiles[i].key, user)) { *name = world.profiles[i].val; return true; }
  }
  return false;
}

bool fly_world_quota(fly_str token) {
  world_load();
  for (size_t i = 0; i < world.nquotas; i++) {
    if (fly_str_eq(world.quotas[i].key, token)) return world.quotas[i].val.ptr[0] == 't';
  }
  return false;
}

// ---- tasks ----

#ifdef FLY_THREADS
// The scheduler on every core, below: what the functions compiled code calls turn to without a
// simulated world.
static bool threads;
static void mt_run(void (*main)(void), void (*entry)(void* task, void* closure));
static void mt_point(void);
static void mt_sleep(uint64_t nanos);
static int mt_spawn(int scope, void (*entry)(void* task, void* closure), void* closure, size_t size);
static void mt_join(int task, void* out);
static int mt_scope_open(void);
static void mt_scope_close(int scope);
static fly_chan mt_channel(void);
static void mt_send(fly_chan ch, const void* v, size_t size);
static bool mt_recv(fly_chan ch, void* out, size_t size);
static void mt_sender_gone(fly_chan ch);
static void mt_sender_clone(fly_chan ch);
typedef struct mt_task mt_task;
static void* mt_task_result(mt_task* t);
static void* mt_task_closure(mt_task* t);
#endif

enum { WAIT_NONE, WAIT_TASK, WAIT_CHANNEL, WAIT_UNTIL };

typedef struct {
  int id, scope;
  fly_fiber* fiber;
  fly_fiber* suspended;
  void (*entry)(void* task, void* closure);
  void* closure;
  void* result;
  size_t size;
  fly_failure* error;
  // The panic the task ended with, if it did.
  char* panic;
  bool started, finished, cancelled, deliver_cancel, deliver_deadlock;
  int wait_kind, wait_id;
  uint64_t until;
} task_t;

typedef struct { uint8_t* items; size_t len, head, size; long senders; bool closed; } chan_t;
typedef struct { int owner; int* tasks; size_t ntasks; fly_failure* failure; char* panic; } scope_t;

bool fly_tasks_on = false;
static struct {
  int current, next, scope_ids;
  int* ready;
  size_t nready, capready;
  int* blocked;
  size_t nblocked, capblocked;
  uint64_t rng;
  task_t** tasks;
  chan_t** chans;
  size_t cap;
  scope_t** scopes;
  size_t capscopes;
} sched = { .next = 1, .scope_ids = 1 };

static void grow_ids(int id) {
  if ((size_t)id < sched.cap) return;
  size_t cap = sched.cap ? sched.cap : 16;
  while (cap <= (size_t)id) cap *= 2;
  sched.tasks = realloc(sched.tasks, cap * sizeof(task_t*));
  sched.chans = realloc(sched.chans, cap * sizeof(chan_t*));
  memset(sched.tasks + sched.cap, 0, (cap - sched.cap) * sizeof(task_t*));
  memset(sched.chans + sched.cap, 0, (cap - sched.cap) * sizeof(chan_t*));
  sched.cap = cap;
}

static void push_ready(int t) {
  if (sched.nready == sched.capready) { sched.capready = sched.capready ? sched.capready * 2 : 16; sched.ready = realloc(sched.ready, sched.capready * sizeof(int)); }
  sched.ready[sched.nready++] = t;
}

static void push_blocked(int t) {
  if (sched.nblocked == sched.capblocked) { sched.capblocked = sched.capblocked ? sched.capblocked * 2 : 16; sched.blocked = realloc(sched.blocked, sched.capblocked * sizeof(int)); }
  sched.blocked[sched.nblocked++] = t;
}

static bool remove_blocked(int t) {
  for (size_t i = 0; i < sched.nblocked; i++) {
    if (sched.blocked[i] == t) {
      memmove(sched.blocked + i, sched.blocked + i + 1, (sched.nblocked - i - 1) * sizeof(int));
      sched.nblocked--;
      return true;
    }
  }
  return false;
}

static void wake(int kind, int id);
static void wake_until(uint64_t t);

// Hands the baton to a ready task, chosen by the seed; false if none can run. With none ready,
// time passes to the earliest sleeper's wake time, waking every task due then.
static bool pass(void) {
  if (sched.nready == 0) {
    bool any = false;
    uint64_t due = 0;
    for (size_t i = 0; i < sched.nblocked; i++) {
      task_t* t = sched.tasks[sched.blocked[i]];
      if (t->wait_kind == WAIT_UNTIL && (!any || t->until < due)) { due = t->until; any = true; }
    }
    if (any) {
      if (due > fly_clock) fly_clock = due;
      wake_until(due);
    }
  }
  if (sched.nready == 0) return false;
  uint64_t r = xorshift(&sched.rng);
  size_t i = (size_t)(r % sched.nready);
  sched.current = sched.ready[i];
  memmove(sched.ready + i, sched.ready + i + 1, (sched.nready - i - 1) * sizeof(int));
  sched.nready--;
  return true;
}

static void wake(int kind, int id) {
  for (size_t i = 0; i < sched.nblocked;) {
    task_t* t = sched.tasks[sched.blocked[i]];
    if (t->wait_kind == kind && t->wait_id == id) {
      int me = sched.blocked[i];
      memmove(sched.blocked + i, sched.blocked + i + 1, (sched.nblocked - i - 1) * sizeof(int));
      sched.nblocked--;
      push_ready(me);
    } else i++;
  }
}

static void wake_until(uint64_t due) {
  for (size_t i = 0; i < sched.nblocked;) {
    task_t* t = sched.tasks[sched.blocked[i]];
    if (t->wait_kind == WAIT_UNTIL && t->until == due) {
      int me = sched.blocked[i];
      memmove(sched.blocked + i, sched.blocked + i + 1, (sched.nblocked - i - 1) * sizeof(int));
      sched.nblocked--;
      push_ready(me);
    } else i++;
  }
}

static void cancel(int t) {
  sched.tasks[t]->cancelled = true;
  if (remove_blocked(t)) push_ready(t);
}

void fly_panic_deadlock(void) { fly_panic("deadlock: every task is waiting"); }

// Suspends the running task back to the scheduler, waiting for `kind`/`id` or not at all; when it
// is resumed, a cancellation or a deadlock is delivered to it.
static void suspend_task(int kind, int id) {
  task_t* t = sched.tasks[sched.current];
  t->wait_kind = kind;
  t->wait_id = id;
  t->suspended = current;
  switch_to(&main_fiber);
  task_t* me = sched.tasks[sched.current];
  if (me->deliver_deadlock) fly_panic_deadlock();
  if (me->deliver_cancel) {
    me->deliver_cancel = false;
    fly_unwinding = true;
  }
}

void fly_point(void) {
#ifdef FLY_THREADS
  if (threads) { mt_point(); return; }
#endif
  if (fly_tasks_on) suspend_task(WAIT_NONE, 0);
}

// Sleeping waits for the virtual clock, which passes only when no task can run; without a
// simulated world, for the machine's.
void fly_sleep(uint64_t nanos) {
#ifdef FLY_THREADS
  if (threads) { mt_sleep(nanos); return; }
#endif
  world_load();
  if (!world.simulated) {
    struct timespec ts = { (time_t)(nanos / 1000000000u), (long)(nanos % 1000000000u) };
    while (nanosleep(&ts, &ts) != 0) {}
    return;
  }
  if (!fly_tasks_on) { fly_clock += nanos; return; }
  if (nanos == 0) { fly_point(); return; }
  sched.tasks[sched.current]->until = fly_clock + nanos;
  suspend_task(WAIT_UNTIL, 0);
}

static void block(int kind, int id) {
  if (!fly_tasks_on) fly_panic_deadlock();
  suspend_task(kind, id);
}

// Task `me` has finished: its outcome goes to its scope, and its joiners wake.
static void end_task(int me) {
  task_t* t = sched.tasks[me];
  scope_t* st = sched.scopes[t->scope];
  // The first failure or panic cancels the scope: its body and its other tasks (§6.1).
  if ((t->panic || t->error) && !st->panic && !st->failure) {
    cancel(st->owner);
    for (size_t i = 0; i < st->ntasks; i++) if (st->tasks[i] != me) cancel(st->tasks[i]);
  }
  if (t->panic && !st->panic) st->panic = t->panic;
  // A failure is the scope's to raise, unless a join raises it first: it is raised once.
  if (t->error && !st->failure) st->failure = t->error;
  t->finished = true;
  wake(WAIT_TASK, me);
  if (!pass()) fly_panic_deadlock();
}

static void task_main(void* arg) {
  task_t* t = arg;
  t->entry(t, t->closure);
  if (FLY_FAILED) { t->error = fly_err; fly_err = NULL; }
  fly_unwinding = false;
}

static void main_entry(void* task, void* closure) { (void)task; ((void (*)(void))closure)(); }

void fly_tasks_run(void (*main)(void)) {
  fly_tasks_on = true;
  world_load();
#ifdef FLY_THREADS
  if (!world.simulated) { mt_run(main, main_entry); return; }
#endif
  sched.rng = world.seed > 1 ? world.seed : 1;
  grow_ids(0);
  task_t* t0 = fly_alloc(sizeof(task_t));
  t0->entry = main_entry;
  t0->closure = (void*)main;
  sched.tasks[0] = t0;
  sched.current = 0;
  for (;;) {
    int me = sched.current;
    task_t* t = sched.tasks[me];
    // A cancelled task unwinds at its next scheduling point; one not started never runs.
    if (!t->deliver_deadlock && t->cancelled) t->deliver_cancel = true;
    if (!t->started) {
      t->started = true;
      if (t->deliver_cancel) {
        t->deliver_cancel = false;
        end_task(me);
        continue;
      }
      t->fiber = fiber_new(task_main, t, NULL);
      t->suspended = t->fiber;
    }
    t->fiber->back = &main_fiber;
    switch_to(t->suspended);
    if (t->fiber->done) {
      if (panicking) {
        t->panic = panicking;
        panicking = NULL;
        fly_unwinding = false;
        fly_err = NULL;
      }
      if (me == 0) {
        if (t->panic) panic_exit(t->panic);
        if (t->error) fly_err = t->error;
        return;
      }
      end_task(me);
      continue;
    }
    if (t->wait_kind == WAIT_NONE) {
      push_ready(me);
      pass();
    } else {
      push_blocked(me);
      if (!pass()) {
        // Nothing else can run, so nothing can ever wake this task: reported, not waited on.
        remove_blocked(me);
        sched.current = me;
        t->deliver_deadlock = true;
      }
    }
  }
}

int fly_spawn(int scope, void (*entry)(void* task, void* closure), void* closure, size_t size) {
#ifdef FLY_THREADS
  if (threads) return mt_spawn(scope, entry, closure, size);
#endif
  int id = sched.next++;
  grow_ids(id);
  task_t* t = fly_alloc(sizeof(task_t));
  t->id = id;
  t->scope = scope;
  t->entry = entry;
  t->closure = closure;
  t->size = size;
  t->result = fly_alloc(size ? size : 1);
  sched.tasks[id] = t;
  push_ready(id);
  scope_t* st = sched.scopes[scope];
  st->tasks = realloc(st->tasks, (st->ntasks + 1) * sizeof(int));
  st->tasks[st->ntasks++] = id;
  fly_point();
  return id;
}

void fly_task_void(void* task, void* closure) {
  (void)task;
  fly_fn* f = closure;
  ((fly_unit (*)(void*))f->fn)(f->env);
  if (f->drop) f->drop(f->env);
  free(f);
}

void* fly_task_result(void* task) {
#ifdef FLY_THREADS
  if (threads) return mt_task_result(task);
#endif
  return ((task_t*)task)->result;
}
void* fly_task_closure(void* task) {
#ifdef FLY_THREADS
  if (threads) return mt_task_closure(task);
#endif
  return ((task_t*)task)->closure;
}

static void join_task(int task) {
  if (!sched.tasks[task]->finished) block(WAIT_TASK, task);
}

// A forked task's value, or its failure, raised.
void fly_join(int task, void* out) {
#ifdef FLY_THREADS
  if (threads) { mt_join(task, out); return; }
#endif
  join_task(task);
  if (fly_unwinding) return;
  task_t* t = sched.tasks[task];
  if (t->panic) fly_panic("a joined task did not finish");
  if (t->error) {
    scope_t* st = sched.scopes[t->scope];
    if (st && st->failure == t->error) st->failure = NULL;
    fly_err = t->error;
    t->error = NULL;
    return;
  }
  memcpy(out, t->result, t->size);
}

int fly_scope_open(void) {
#ifdef FLY_THREADS
  if (threads) return mt_scope_open();
#endif
  int sid = sched.scope_ids++;
  if ((size_t)sid >= sched.capscopes) {
    size_t cap = sched.capscopes ? sched.capscopes * 2 : 16;
    while (cap <= (size_t)sid) cap *= 2;
    sched.scopes = realloc(sched.scopes, cap * sizeof(scope_t*));
    sched.capscopes = cap;
  }
  scope_t* st = fly_alloc(sizeof(scope_t));
  st->owner = sched.current;
  sched.scopes[sid] = st;
  return sid;
}

// The end of a scope's body, however it ended: every task started in it is waited for, then
// the scope fails as its body or its first failed task did (§6.1).
void fly_scope_close(int sid, bool body_failed) {
  (void)body_failed;
#ifdef FLY_THREADS
  if (threads) { mt_scope_close(sid); return; }
#endif
  scope_t* st = sched.scopes[sid];
  task_t* me = sched.tasks[sched.current];
  // The body unwound because a task failed or panicked: the scope raises that instead.
  bool unwound = fly_unwinding && !st->failure && !st->panic;
  fly_unwinding = false;
  void* err = fly_err;
  fly_err = NULL;
  me->cancelled = false;
  for (size_t i = 0; i < st->ntasks; i++) {
    for (;;) {
      join_task(st->tasks[i]);
      if (!fly_unwinding) break;
      fly_unwinding = false;
      me->cancelled = false;
    }
  }
  me->cancelled = false;
  if (st->panic) fly_panic(st->panic);
  if (unwound) { fly_unwinding = true; if (err) free(err); return; }
  if (err) { fly_err = err; return; }
  if (st->failure) { fly_err = st->failure; st->failure = NULL; }
}

// ---- channels ----

fly_chan fly_channel(void) {
#ifdef FLY_THREADS
  if (threads) return mt_channel();
#endif
  int id = sched.next++;
  grow_ids(id);
  chan_t* c = fly_alloc(sizeof(chan_t));
  c->senders = 1;
  sched.chans[id] = c;
  return (fly_chan){ id };
}

void fly_send(fly_chan ch, const void* v, size_t size) {
#ifdef FLY_THREADS
  if (threads) { mt_send(ch, v, size); return; }
#endif
  chan_t* c = sched.chans[ch.ch];
  c->size = size;
  c->items = realloc(c->items, (c->len + 1) * (size ? size : 1));
  memcpy(c->items + c->len * size, v, size);
  c->len++;
  wake(WAIT_CHANNEL, ch.ch);
  fly_point();
}

// The next message, or false once the channel is closed and drained (or the task unwinds).
bool fly_recv(fly_chan ch, void* out, size_t size) {
#ifdef FLY_THREADS
  if (threads) return mt_recv(ch, out, size);
#endif
  for (;;) {
    chan_t* c = sched.chans[ch.ch];
    if (c->head < c->len) {
      memcpy(out, c->items + c->head * size, size);
      c->head++;
      return true;
    }
    if (c->closed) return false;
    block(WAIT_CHANNEL, ch.ch);
    if (fly_unwinding) return false;
  }
}

static void sender_gone(chan_t* c, int id) {
  c->senders = c->senders > 0 ? c->senders - 1 : 0;
  if (c->senders == 0) { c->closed = true; wake(WAIT_CHANNEL, id); }
}

void fly_close(fly_chan ch) {
#ifdef FLY_THREADS
  if (threads) { mt_sender_gone(ch); mt_point(); return; }
#endif
  sender_gone(sched.chans[ch.ch], ch.ch);
  fly_point();
}

// A destructor does not suspend: a sender dropped closes its channel then and there.
void fly_sender_drop(fly_chan* ch) {
#ifdef FLY_THREADS
  if (threads) { if (ch->ch) mt_sender_gone(*ch); ch->ch = 0; return; }
#endif
  if (ch->ch) sender_gone(sched.chans[ch->ch], ch->ch);
  ch->ch = 0;
}

fly_chan fly_sender_clone(const fly_chan* ch) {
#ifdef FLY_THREADS
  if (threads) { mt_sender_clone(*ch); return *ch; }
#endif
  sched.chans[ch->ch]->senders++;
  return *ch;
}

// ---- tasks on every core ----
//
// Without a simulated world, tasks run on a worker thread for each core. A task not yet started is
// any worker's: each keeps the tasks started on it in a deque the others steal from when they have
// nothing to do. Once started, a task stays on its worker: compiled code may keep the address of a
// thread's variable — the failure being raised, whether it unwinds — across a call that suspends,
// so a task resumed on another thread would read that thread's. A task waits by parking: it puts
// itself in the queue of what it waits for, under that queue's lock, and its worker runs others;
// whatever ends the wait moves it to its worker's inbox.

#ifdef FLY_THREADS
#include <pthread.h>
#include <sched.h>
#include <unistd.h>

static bool threads = false;

// A lock held for a few instructions at a time.
typedef struct { int v; } spin_t;

static inline void relax(void) {
#if defined(__aarch64__) || defined(__arm64__)
  __asm__ volatile("yield");
#elif defined(__x86_64__)
  __asm__ volatile("pause");
#endif
}

static void spin_lock(spin_t* l) {
  unsigned n = 0;
  while (__atomic_exchange_n(&l->v, 1, __ATOMIC_ACQUIRE)) {
    while (__atomic_load_n(&l->v, __ATOMIC_RELAXED)) {
      if (++n < 128) relax(); else sched_yield();
    }
  }
}

static void spin_unlock(spin_t* l) { __atomic_store_n(&l->v, 0, __ATOMIC_RELEASE); }

static uint64_t now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec;
}

// ---- what compiled code names by number ----

// Tasks, scopes and channels are numbers in compiled code. The table they are found in grows in
// chunks that never move, so a thread may read it while another adds to it.
enum { OBJ_BITS = 12, OBJ_CHUNK = 1 << OBJ_BITS, OBJ_CHUNKS = 1 << 18 };
static void** objs[OBJ_CHUNKS];
static int obj_count = 1;

static int obj_new(void* p) {
  int id = __atomic_fetch_add(&obj_count, 1, __ATOMIC_RELAXED);
  if (id >> OBJ_BITS >= OBJ_CHUNKS) fly_panic("too many tasks, scopes and channels");
  void*** slot = &objs[id >> OBJ_BITS];
  void** chunk = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
  if (!chunk) {
    void** made = fly_alloc(OBJ_CHUNK * sizeof(void*));
    void** seen = NULL;
    if (__atomic_compare_exchange_n(slot, &seen, made, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) chunk = made;
    else { free(made); chunk = seen; }
  }
  __atomic_store_n(&chunk[id & (OBJ_CHUNK - 1)], p, __ATOMIC_RELEASE);
  return id;
}

static void* obj_get(int id) { return __atomic_load_n(&objs[id >> OBJ_BITS][id & (OBJ_CHUNK - 1)], __ATOMIC_ACQUIRE); }
static void obj_clear(int id) { __atomic_store_n(&objs[id >> OBJ_BITS][id & (OBJ_CHUNK - 1)], NULL, __ATOMIC_RELEASE); }

// ---- deques ----

// A work-stealing deque (Chase and Lev, in Lê et al.'s form for weak memory): its owner pushes and
// pops at the bottom, others steal from the top. A buffer outgrown stays allocated, as a thief may
// still be reading it.
typedef struct dq_buf { long cap; struct dq_buf* old; void* items[]; } dq_buf;
typedef struct { long top, bottom; dq_buf* buf; } deque_t;

static dq_buf* dq_buf_new(long cap, dq_buf* old) {
  dq_buf* b = fly_alloc(sizeof(dq_buf) + (size_t)cap * sizeof(void*));
  b->cap = cap;
  b->old = old;
  return b;
}

static void dq_push(deque_t* d, void* x) {
  long b = __atomic_load_n(&d->bottom, __ATOMIC_RELAXED);
  long t = __atomic_load_n(&d->top, __ATOMIC_ACQUIRE);
  dq_buf* a = __atomic_load_n(&d->buf, __ATOMIC_RELAXED);
  if (b - t > a->cap - 1) {
    dq_buf* g = dq_buf_new(a->cap * 2, a);
    for (long i = t; i < b; i++) __atomic_store_n(&g->items[i & (g->cap - 1)], __atomic_load_n(&a->items[i & (a->cap - 1)], __ATOMIC_RELAXED), __ATOMIC_RELAXED);
    __atomic_store_n(&d->buf, g, __ATOMIC_RELEASE);
    a = g;
  }
  __atomic_store_n(&a->items[b & (a->cap - 1)], x, __ATOMIC_RELAXED);
  // Released with the item, for a thief that reads `bottom` to see what it takes.
  __atomic_store_n(&d->bottom, b + 1, __ATOMIC_RELEASE);
}

static void* dq_pop(deque_t* d) {
  long b = __atomic_load_n(&d->bottom, __ATOMIC_RELAXED) - 1;
  dq_buf* a = __atomic_load_n(&d->buf, __ATOMIC_RELAXED);
  __atomic_store_n(&d->bottom, b, __ATOMIC_RELAXED);
  __atomic_thread_fence(__ATOMIC_SEQ_CST);
  long t = __atomic_load_n(&d->top, __ATOMIC_RELAXED);
  void* x = NULL;
  if (t <= b) {
    x = __atomic_load_n(&a->items[b & (a->cap - 1)], __ATOMIC_RELAXED);
    if (t == b) {
      if (!__atomic_compare_exchange_n(&d->top, &t, t + 1, false, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) x = NULL;
      __atomic_store_n(&d->bottom, b + 1, __ATOMIC_RELAXED);
    }
  } else {
    __atomic_store_n(&d->bottom, b + 1, __ATOMIC_RELAXED);
  }
  return x;
}

static void* dq_steal(deque_t* d) {
  long t = __atomic_load_n(&d->top, __ATOMIC_ACQUIRE);
  __atomic_thread_fence(__ATOMIC_SEQ_CST);
  long b = __atomic_load_n(&d->bottom, __ATOMIC_ACQUIRE);
  if (t >= b) return NULL;
  dq_buf* a = __atomic_load_n(&d->buf, __ATOMIC_ACQUIRE);
  void* x = __atomic_load_n(&a->items[t & (a->cap - 1)], __ATOMIC_RELAXED);
  if (!__atomic_compare_exchange_n(&d->top, &t, t + 1, false, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) return NULL;
  return x;
}

static long dq_size(deque_t* d) {
  long b = __atomic_load_n(&d->bottom, __ATOMIC_ACQUIRE);
  long t = __atomic_load_n(&d->top, __ATOMIC_ACQUIRE);
  return b > t ? b - t : 0;
}

// ---- tasks, scopes, channels ----

typedef struct mt_task mt_task;
typedef struct mt_scope mt_scope;
typedef struct worker worker;

// The tasks waiting for something, in the order they began to, under the queue's lock.
typedef struct { spin_t lock; mt_task *head, *tail; } waitq;

struct mt_task {
  void (*entry)(void* task, void* closure);
  void* closure;
  void* result;
  size_t size;
  mt_scope* scope;
  worker* home;
  fly_fiber* fiber;
  fly_fiber* suspended;
  // How it ended: its failure, or the panic it ended with.
  fly_failure* error;
  char* panic;
  // Who still refers to it: itself while it lives, its scope while it does, and a forked task's
  // `Fiber` until it is joined.
  int refs;
  bool started, cancelled, yielded;
  // Its joiners, and whether it has finished, under their queue's lock.
  waitq joiners;
  bool finished;
  // The queue it waits in, if it waits, and its neighbours there.
  waitq* waiting;
  mt_task *wnext, *wprev;
  // Its neighbours among its scope's tasks still alive.
  mt_task *snext, *sprev;
  // The next task in its worker's inbox.
  mt_task* rnext;
  // What compiled code reads of the task, kept while another runs.
  void* err;
  bool unwinding, stopping;
  uint64_t sleep_gen;
};

// A scope: its tasks still alive, and how it fails. Its queue holds its owner while the owner waits
// for them at the scope's end; the queue's lock guards it all.
struct mt_scope {
  waitq q;
  mt_task* owner;
  mt_task* live;
  size_t nlive;
  bool closing;
  // The task whose failure the scope raises, unless a join raises it first; the first panic.
  mt_task* failer;
  char* panic;
};

// A channel: what was sent and not yet received, in a ring, and the receivers waiting, under its
// queue's lock.
typedef struct { waitq q; uint8_t* items; size_t head, len, cap, size; long senders; bool closed; } mt_chan;

struct worker {
  int index;
  fly_fiber own;
  fly_fiber* base;
  // Tasks to resume here, from any thread.
  spin_t inlock;
  mt_task *inhead, *intail;
  // Tasks started here that have not begun, and `par` work: either is any worker's to take.
  deque_t fresh, jobs;
  uint64_t rng;
};

static worker* workers;
static int nworkers;
static FLY_LOCAL worker* this_worker;
static FLY_LOCAL mt_task* running;
static mt_task* main_task;
static bool main_done;
// Tasks queued or running, and tasks begun and not ended: when none can run, and none sleeps, those
// alive wait for each other forever.
static long runnable, alive;

// Idle workers sleep here until there is work.
static pthread_mutex_t idle_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t idle_cv = PTHREAD_COND_INITIALIZER;
static int idlers;

static void notify(void) {
  __atomic_thread_fence(__ATOMIC_SEQ_CST);
  if (__atomic_load_n(&idlers, __ATOMIC_SEQ_CST) == 0) return;
  pthread_mutex_lock(&idle_mu);
  pthread_cond_broadcast(&idle_cv);
  pthread_mutex_unlock(&idle_mu);
}

static void task_unref(mt_task* t) {
  if (__atomic_sub_fetch(&t->refs, 1, __ATOMIC_ACQ_REL) > 0) return;
  free(t->result);
  free(t->panic);
  free(t);
}

static void inbox_push(worker* w, mt_task* t) {
  t->rnext = NULL;
  spin_lock(&w->inlock);
  if (w->intail) w->intail->rnext = t;
  else __atomic_store_n(&w->inhead, t, __ATOMIC_RELAXED);
  w->intail = t;
  spin_unlock(&w->inlock);
}

static mt_task* inbox_pop(worker* w) {
  if (!__atomic_load_n(&w->inhead, __ATOMIC_RELAXED)) return NULL;
  spin_lock(&w->inlock);
  mt_task* t = w->inhead;
  if (t) {
    __atomic_store_n(&w->inhead, t->rnext, __ATOMIC_RELAXED);
    if (!t->rnext) w->intail = NULL;
  }
  spin_unlock(&w->inlock);
  return t;
}

// A task that waited may run again, on its own worker.
static void unpark(mt_task* t) {
  __atomic_fetch_add(&runnable, 1, __ATOMIC_SEQ_CST);
  inbox_push(t->home, t);
  notify();
}

static void q_append(waitq* q, mt_task* t) {
  t->wnext = NULL;
  t->wprev = q->tail;
  if (q->tail) q->tail->wnext = t; else q->head = t;
  q->tail = t;
}

static void q_remove(waitq* q, mt_task* t) {
  if (t->wprev) t->wprev->wnext = t->wnext; else q->head = t->wnext;
  if (t->wnext) t->wnext->wprev = t->wprev; else q->tail = t->wprev;
  t->wnext = t->wprev = NULL;
}

// Wakes the first task waiting in `q`, whose lock is held.
static void wake_one(waitq* q) {
  mt_task* t = q->head;
  if (!t) return;
  q_remove(q, t);
  __atomic_store_n(&t->waiting, NULL, __ATOMIC_SEQ_CST);
  unpark(t);
}

static void wake_all(waitq* q) { while (q->head) wake_one(q); }

// The running task gives its worker up, until it is resumed: what compiled code reads of it is kept.
static void to_worker(mt_task* t) {
  t->err = fly_err;
  t->unwinding = fly_unwinding;
  t->stopping = fly_stopping;
  t->suspended = current;
  switch_to(this_worker->base);
}

// The running task waits in `q`, whose lock is held, until something wakes it; a cancellation
// wakes it too, unless it waits for its scope's tasks, which it must. The lock is released.
static void wait_in(waitq* q, bool cancellable) {
  mt_task* t = running;
  q_append(q, t);
  __atomic_store_n(&t->waiting, q, __ATOMIC_SEQ_CST);
  if (cancellable && __atomic_load_n(&t->cancelled, __ATOMIC_SEQ_CST)) {
    q_remove(q, t);
    __atomic_store_n(&t->waiting, NULL, __ATOMIC_SEQ_CST);
    spin_unlock(&q->lock);
    return;
  }
  t->yielded = false;
  __atomic_fetch_sub(&runnable, 1, __ATOMIC_SEQ_CST);
  spin_unlock(&q->lock);
  to_worker(t);
}

// Whether the running task has been cancelled: it unwinds from here (§6.1).
static bool cancelled_here(void) {
  mt_task* t = running;
  if (t && __atomic_load_n(&t->cancelled, __ATOMIC_ACQUIRE)) {
    fly_unwinding = true;
    return true;
  }
  return false;
}

// Cancels a task: one running or queued sees it at its next scheduling point; one waiting is woken.
static void cancel_task(mt_task* t) {
  __atomic_store_n(&t->cancelled, true, __ATOMIC_SEQ_CST);
  for (;;) {
    waitq* q = __atomic_load_n(&t->waiting, __ATOMIC_SEQ_CST);
    if (!q) return;
    spin_lock(&q->lock);
    if (__atomic_load_n(&t->waiting, __ATOMIC_SEQ_CST) == q) {
      q_remove(q, t);
      __atomic_store_n(&t->waiting, NULL, __ATOMIC_SEQ_CST);
      spin_unlock(&q->lock);
      unpark(t);
      return;
    }
    spin_unlock(&q->lock);
  }
}

// A scheduling point: a cancellation is delivered, and the worker's other tasks get a turn.
static void mt_point(void) {
  mt_task* t = running;
  if (!t || cancelled_here()) return;
  if (__atomic_load_n(&this_worker->inhead, __ATOMIC_RELAXED)) {
    t->yielded = true;
    to_worker(t);
    cancelled_here();
  }
}

// ---- sleeping ----

// Sleeping tasks wait in one queue; when each wakes is kept in a heap, under the queue's lock. A
// task woken early — cancelled — leaves its alarm behind, which then wakes nothing.
typedef struct { uint64_t due, gen; mt_task* task; } alarm_t;
static waitq sleepers;
static alarm_t* alarms;
static size_t nalarms, capalarms;
static uint64_t next_due;

static void alarm_push(alarm_t a) {
  if (nalarms == capalarms) {
    capalarms = capalarms ? capalarms * 2 : 16;
    alarms = realloc(alarms, capalarms * sizeof(alarm_t));
  }
  size_t i = nalarms++;
  while (i > 0 && alarms[(i - 1) / 2].due > a.due) { alarms[i] = alarms[(i - 1) / 2]; i = (i - 1) / 2; }
  alarms[i] = a;
}

static alarm_t alarm_pop(void) {
  alarm_t top = alarms[0], last = alarms[--nalarms];
  size_t i = 0;
  for (;;) {
    size_t c = 2 * i + 1;
    if (c >= nalarms) break;
    if (c + 1 < nalarms && alarms[c + 1].due < alarms[c].due) c++;
    if (alarms[c].due >= last.due) break;
    alarms[i] = alarms[c];
    i = c;
  }
  if (nalarms > 0) alarms[i] = last;
  return top;
}

static void mt_sleep(uint64_t nanos) {
  mt_task* t = running;
  if (nanos == 0) { mt_point(); return; }
  spin_lock(&sleepers.lock);
  __atomic_fetch_add(&t->refs, 1, __ATOMIC_RELAXED);
  alarm_push((alarm_t){ now_ns() + nanos, ++t->sleep_gen, t });
  __atomic_store_n(&next_due, alarms[0].due, __ATOMIC_RELEASE);
  wait_in(&sleepers, true);
  cancelled_here();
}

// Wakes the tasks whose alarms are due.
static void fire_alarms(void) {
  uint64_t due = __atomic_load_n(&next_due, __ATOMIC_ACQUIRE);
  if (!due || due > now_ns()) return;
  spin_lock(&sleepers.lock);
  uint64_t now = now_ns();
  while (nalarms > 0 && alarms[0].due <= now) {
    alarm_t a = alarm_pop();
    mt_task* t = a.task;
    if (__atomic_load_n(&t->waiting, __ATOMIC_SEQ_CST) == &sleepers && t->sleep_gen == a.gen) {
      q_remove(&sleepers, t);
      __atomic_store_n(&t->waiting, NULL, __ATOMIC_SEQ_CST);
      unpark(t);
    }
    task_unref(t);
  }
  __atomic_store_n(&next_due, nalarms ? alarms[0].due : 0, __ATOMIC_RELEASE);
  spin_unlock(&sleepers.lock);
}

// ---- running tasks ----

static void mt_task_main(void* arg) {
  mt_task* t = arg;
  t->entry(t, t->closure);
  if (FLY_FAILED) { t->error = fly_err; fly_err = NULL; }
  fly_unwinding = false;
}

// Task `t` has ended: its outcome goes to its scope, its joiners wake, and the first failure or
// panic cancels the scope's body and its other tasks (§6.1).
static void mt_end(mt_task* t) {
  if (t->fiber) { fiber_free(t->fiber); t->fiber = NULL; }
  // A task stops being alive before it stops being runnable: the other way round, an idle worker
  // could see one task alive and none able to run, and take that for a deadlock.
  if (t == main_task) {
    main_done = true;
    __atomic_fetch_sub(&alive, 1, __ATOMIC_SEQ_CST);
    __atomic_fetch_sub(&runnable, 1, __ATOMIC_SEQ_CST);
    return;
  }
  mt_scope* sc = t->scope;
  mt_task** cancels = NULL;
  size_t ncancels = 0;
  spin_lock(&sc->q.lock);
  if ((t->panic || t->error) && !sc->panic && !sc->failer) {
    cancels = fly_alloc((sc->nlive + 1) * sizeof(mt_task*));
    if (!sc->closing && sc->owner) {
      __atomic_fetch_add(&sc->owner->refs, 1, __ATOMIC_RELAXED);
      cancels[ncancels++] = sc->owner;
    }
    for (mt_task* o = sc->live; o; o = o->snext) {
      if (o == t) continue;
      __atomic_fetch_add(&o->refs, 1, __ATOMIC_RELAXED);
      cancels[ncancels++] = o;
    }
  }
  if (t->panic && !sc->panic) { sc->panic = t->panic; t->panic = NULL; }
  if (t->error && !sc->failer) {
    __atomic_fetch_add(&t->refs, 1, __ATOMIC_RELAXED);
    sc->failer = t;
  }
  if (t->sprev) t->sprev->snext = t->snext; else sc->live = t->snext;
  if (t->snext) t->snext->sprev = t->sprev;
  sc->nlive--;
  if (sc->nlive == 0) wake_all(&sc->q);
  spin_unlock(&sc->q.lock);
  for (size_t i = 0; i < ncancels; i++) {
    cancel_task(cancels[i]);
    task_unref(cancels[i]);
  }
  free(cancels);
  spin_lock(&t->joiners.lock);
  t->finished = true;
  wake_all(&t->joiners);
  spin_unlock(&t->joiners.lock);
  __atomic_fetch_sub(&alive, 1, __ATOMIC_SEQ_CST);
  __atomic_fetch_sub(&runnable, 1, __ATOMIC_SEQ_CST);
  // Its scope no longer refers to it, nor does it to itself.
  task_unref(t);
  task_unref(t);
}

static void run_task(worker* w, mt_task* t) {
  running = t;
  if (!t->started) {
    t->started = true;
    t->home = w;
    // A task cancelled before it began never runs.
    if (__atomic_load_n(&t->cancelled, __ATOMIC_ACQUIRE)) {
      running = NULL;
      mt_end(t);
      return;
    }
    t->fiber = fiber_new(mt_task_main, t, NULL);
    t->suspended = t->fiber;
  }
  fly_err = t->err;
  fly_unwinding = t->unwinding;
  fly_stopping = t->stopping;
  t->fiber->back = w->base;
  switch_to(t->suspended);
  running = NULL;
  if (t->fiber->done) {
    if (panicking) {
      t->panic = panicking;
      panicking = NULL;
    }
    fly_unwinding = false;
    fly_stopping = false;
    fly_err = NULL;
    mt_end(t);
  } else if (t->yielded) {
    inbox_push(w, t);
  }
}

// ---- `par` ----

// Work `join` lets another worker take: the second of the two, run where it is taken.
typedef struct { void (*run)(void* f, void* out); void* f; void* out; int done; } job_t;

static void run_job(job_t* j) {
  j->run(j->f, j->out);
  __atomic_store_n(&j->done, 1, __ATOMIC_RELEASE);
}

static uint64_t worker_rand(worker* w) {
  uint64_t x = w->rng;
  x ^= x << 13;
  x ^= x >> 7;
  x ^= x << 17;
  return w->rng = x;
}

// Another worker's: `par` work first, which a running task waits for, then a task not yet begun.
static job_t* steal_job(worker* w) {
  int start = (int)(worker_rand(w) % (uint64_t)nworkers);
  for (int k = 0; k < nworkers; k++) {
    worker* v = &workers[(start + k) % nworkers];
    if (v == w) continue;
    job_t* j = dq_steal(&v->jobs);
    if (j) return j;
  }
  return NULL;
}

static mt_task* steal_task(worker* w) {
  int start = (int)(worker_rand(w) % (uint64_t)nworkers);
  for (int k = 0; k < nworkers; k++) {
    worker* v = &workers[(start + k) % nworkers];
    if (v == w) continue;
    mt_task* t = dq_steal(&v->fresh);
    if (t) return t;
  }
  return NULL;
}

static void par_join(void (*a)(void*, void*), void* fa, void* oa, void (*b)(void*, void*), void* fb, void* ob) {
  worker* w = this_worker;
  // With work enough waiting to be taken here already, this pair runs here, in order.
  if (dq_size(&w->jobs) >= 4) {
    a(fa, oa);
    b(fb, ob);
    return;
  }
  job_t jb = { b, fb, ob, 0 };
  dq_push(&w->jobs, &jb);
  notify();
  a(fa, oa);
  // Only what `a` pushed was above `b`, and `a` took it back: `b` is next, unless it was taken.
  if (dq_pop(&w->jobs) == &jb) {
    b(fb, ob);
    return;
  }
  // Taken: help with other work until it is done.
  for (unsigned n = 0; !__atomic_load_n(&jb.done, __ATOMIC_ACQUIRE); n++) {
    job_t* j = steal_job(w);
    if (j) { run_job(j); n = 0; }
    else if (n < 128) relax();
    else sched_yield();
  }
}

// ---- workers ----

static bool work_anywhere(worker* w) {
  if (__atomic_load_n(&w->inhead, __ATOMIC_SEQ_CST)) return true;
  for (int k = 0; k < nworkers; k++) {
    if (dq_size(&workers[k].fresh) > 0 || dq_size(&workers[k].jobs) > 0) return true;
  }
  uint64_t due = __atomic_load_n(&next_due, __ATOMIC_ACQUIRE);
  return due && due <= now_ns();
}

static _Noreturn void mt_deadlock(void) { panic_exit("deadlock: every task is waiting"); }

static void idle(worker* w) {
  pthread_mutex_lock(&idle_mu);
  __atomic_fetch_add(&idlers, 1, __ATOMIC_SEQ_CST);
  if (!work_anywhere(w) && !(w == &workers[0] && main_done)) {
    uint64_t due = __atomic_load_n(&next_due, __ATOMIC_ACQUIRE);
    if (!due && __atomic_load_n(&runnable, __ATOMIC_SEQ_CST) == 0 && __atomic_load_n(&alive, __ATOMIC_SEQ_CST) > 0) mt_deadlock();
    if (due) {
      // The monotonic clock and the condition's clock differ: wait as long as is left.
      uint64_t left = due > now_ns() ? due - now_ns() : 0;
      struct timespec ts;
      clock_gettime(CLOCK_REALTIME, &ts);
      uint64_t at = (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec + left;
      ts.tv_sec = (time_t)(at / 1000000000u);
      ts.tv_nsec = (long)(at % 1000000000u);
      pthread_cond_timedwait(&idle_cv, &idle_mu, &ts);
    } else {
      pthread_cond_wait(&idle_cv, &idle_mu);
    }
  }
  __atomic_fetch_sub(&idlers, 1, __ATOMIC_SEQ_CST);
  pthread_mutex_unlock(&idle_mu);
}

static void work(worker* w) {
  for (;;) {
    if (w == &workers[0] && main_done) return;
    fire_alarms();
    mt_task* t = inbox_pop(w);
    if (!t) t = dq_pop(&w->fresh);
    if (!t) {
      job_t* j = steal_job(w);
      if (j) { run_job(j); continue; }
      t = steal_task(w);
    }
    if (t) { run_task(w, t); continue; }
    idle(w);
  }
}

static void* worker_thread(void* arg) {
  worker* w = arg;
  this_worker = w;
  current = w->base;
  work(w);
  return NULL;
}

static void mt_run(void (*main)(void), void (*entry)(void* task, void* closure)) {
  threads = true;
  const char* n = getenv("FLY_THREADS");
  long cores = n && *n ? strtol(n, NULL, 10) : sysconf(_SC_NPROCESSORS_ONLN);
  nworkers = cores > 0 ? (int)cores : 1;
  workers = fly_alloc((size_t)nworkers * sizeof(worker));
  for (int k = 0; k < nworkers; k++) {
    worker* w = &workers[k];
    w->index = k;
    w->own.base = true;
    w->base = k == 0 ? &main_fiber : &w->own;
    w->rng = 0x9e3779b97f4a7c15u * (uint64_t)(k + 1);
    w->fresh.buf = dq_buf_new(256, NULL);
    w->jobs.buf = dq_buf_new(256, NULL);
  }
  this_worker = &workers[0];
  mt_task* t = fly_alloc(sizeof(mt_task));
  t->entry = entry;
  t->closure = (void*)main;
  t->refs = 1;
  main_task = t;
  runnable = alive = 1;
  inbox_push(&workers[0], t);
  // Each worker's stack is as large as a fiber's: `par` work runs on it.
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, FLY_STACK);
  for (int k = 1; k < nworkers; k++) {
    pthread_t th;
    if (pthread_create(&th, &attr, worker_thread, &workers[k]) != 0) fly_panic("cannot start a worker thread");
    pthread_detach(th);
  }
  pthread_attr_destroy(&attr);
  work(&workers[0]);
  if (t->panic) panic_exit(t->panic);
  if (t->error) fly_err = t->error;
}

// ---- what compiled code calls, without a simulated world ----

static int mt_spawn(int scope, void (*entry)(void* task, void* closure), void* closure, size_t size) {
  mt_scope* sc = obj_get(scope);
  mt_task* t = fly_alloc(sizeof(mt_task));
  t->entry = entry;
  t->closure = closure;
  t->size = size;
  t->result = fly_alloc(size ? size : 1);
  t->scope = sc;
  // A forked task's `Fiber` refers to it too.
  t->refs = entry == fly_task_void ? 2 : 3;
  int id = obj_new(t);
  spin_lock(&sc->q.lock);
  t->snext = sc->live;
  if (sc->live) sc->live->sprev = t;
  sc->live = t;
  sc->nlive++;
  spin_unlock(&sc->q.lock);
  __atomic_fetch_add(&runnable, 1, __ATOMIC_SEQ_CST);
  __atomic_fetch_add(&alive, 1, __ATOMIC_SEQ_CST);
  dq_push(&this_worker->fresh, t);
  notify();
  mt_point();
  return id;
}

static void mt_join(int task, void* out) {
  mt_task* t = obj_get(task);
  spin_lock(&t->joiners.lock);
  while (!t->finished) {
    wait_in(&t->joiners, true);
    if (cancelled_here()) return;
    spin_lock(&t->joiners.lock);
  }
  spin_unlock(&t->joiners.lock);
  if (t->panic) fly_panic("a joined task did not finish");
  if (t->error) {
    // Raised here, so not again by the scope.
    fly_err = t->error;
    t->error = NULL;
  } else {
    memcpy(out, t->result, t->size);
  }
  obj_clear(task);
  task_unref(t);
}

static int mt_scope_open(void) {
  mt_scope* sc = fly_alloc(sizeof(mt_scope));
  sc->owner = running;
  return obj_new(sc);
}

static void mt_scope_close(int id) {
  mt_scope* sc = obj_get(id);
  mt_task* me = running;
  spin_lock(&sc->q.lock);
  // The body unwound because a task failed or panicked: the scope raises that instead.
  bool unwound = fly_unwinding && !sc->failer && !sc->panic;
  sc->closing = true;
  spin_unlock(&sc->q.lock);
  fly_unwinding = false;
  void* err = fly_err;
  fly_err = NULL;
  spin_lock(&sc->q.lock);
  while (sc->nlive > 0) {
    wait_in(&sc->q, false);
    spin_lock(&sc->q.lock);
  }
  spin_unlock(&sc->q.lock);
  __atomic_store_n(&me->cancelled, false, __ATOMIC_SEQ_CST);
  char* panic = sc->panic;
  mt_task* failer = sc->failer;
  obj_clear(id);
  free(sc);
  if (panic) {
    if (failer) task_unref(failer);
    fly_panic(panic);
  }
  if (unwound) {
    fly_unwinding = true;
    if (err) free(err);
  } else if (err) {
    fly_err = err;
  } else if (failer && failer->error) {
    fly_err = failer->error;
    failer->error = NULL;
  }
  if (failer) task_unref(failer);
}

static fly_chan mt_channel(void) {
  mt_chan* c = fly_alloc(sizeof(mt_chan));
  c->senders = 1;
  return (fly_chan){ obj_new(c) };
}

static void mt_send(fly_chan ch, const void* v, size_t size) {
  mt_chan* c = obj_get(ch.ch);
  spin_lock(&c->q.lock);
  if (c->len == c->cap) {
    size_t cap = c->cap ? c->cap * 2 : 8;
    uint8_t* items = fly_alloc(cap * (size ? size : 1));
    for (size_t i = 0; i < c->len; i++) memcpy(items + i * size, c->items + ((c->head + i) % c->cap) * size, size);
    free(c->items);
    c->items = items;
    c->head = 0;
    c->cap = cap;
  }
  c->size = size;
  memcpy(c->items + ((c->head + c->len) % c->cap) * size, v, size);
  c->len++;
  wake_one(&c->q);
  spin_unlock(&c->q.lock);
  mt_point();
}

static bool mt_recv(fly_chan ch, void* out, size_t size) {
  mt_chan* c = obj_get(ch.ch);
  spin_lock(&c->q.lock);
  for (;;) {
    if (c->len > 0) {
      memcpy(out, c->items + c->head * size, size);
      c->head = (c->head + 1) % c->cap;
      c->len--;
      spin_unlock(&c->q.lock);
      return true;
    }
    if (c->closed) {
      spin_unlock(&c->q.lock);
      return false;
    }
    wait_in(&c->q, true);
    if (cancelled_here()) return false;
    spin_lock(&c->q.lock);
  }
}

static void mt_sender_gone(fly_chan ch) {
  mt_chan* c = obj_get(ch.ch);
  spin_lock(&c->q.lock);
  if (c->senders > 0 && --c->senders == 0) {
    c->closed = true;
    wake_all(&c->q);
  }
  spin_unlock(&c->q.lock);
}

static void mt_sender_clone(fly_chan ch) {
  mt_chan* c = obj_get(ch.ch);
  spin_lock(&c->q.lock);
  c->senders++;
  spin_unlock(&c->q.lock);
}

// A `Mutex`'s lock is one of a few, chosen by its state's address: a body performs nothing, so it
// takes no other lock, and two locks sharing one only take turns.
static spin_t stripes[64];
static FLY_LOCAL spin_t* held;

void fly_lock(const void* state) {
  if (!threads) return;
  held = &stripes[((uintptr_t)state >> 4) & 63];
  spin_lock(held);
}

void fly_unlock(const void* state) {
  (void)state;
  if (!held) return;
  spin_unlock(held);
  held = NULL;
}

static void unlock_held(void) { fly_unlock(NULL); }

static void* mt_task_result(mt_task* t) { return t->result; }
static void* mt_task_closure(mt_task* t) { return t->closure; }

void fly_par_join(void (*a)(void* f, void* out), void* fa, void* oa, void (*b)(void* f, void* out), void* fb, void* ob) {
  if (threads && nworkers > 1 && this_worker) { par_join(a, fa, oa, b, fb, ob); return; }
  a(fa, oa);
  b(fb, ob);
}
#endif

#endif

// Without threads, a `Mutex` is never contended, and `join` runs its two in order.
#ifndef FLY_THREADS
void fly_lock(const void* state) { (void)state; }
void fly_unlock(const void* state) { (void)state; }
static void unlock_held(void) {}
void fly_par_join(void (*a)(void* f, void* out), void* fa, void* oa, void (*b)(void* f, void* out), void* fb, void* ob) {
  a(fa, oa);
  b(fb, ob);
}
#endif

// ---- regions ----

// Its header is 32 bytes, so what follows it is aligned for anything.
struct fly_chunk { fly_chunk* next; size_t used, cap, pad; };
#define CHUNK_DATA(c) ((uint8_t*)((c) + 1))

void* fly_arena_alloc(fly_arena* a, size_t size) {
  size = (size + 15) & ~(size_t)15;
  fly_chunk* c = a->head;
  if (!c || c->used + size > c->cap) {
    size_t cap = c ? c->cap * 2 : 4096;
    while (cap < size) cap *= 2;
    fly_chunk* n = fly_alloc(sizeof(fly_chunk) + cap);
    n->next = c;
    n->cap = cap;
    a->head = c = n;
  }
  void* p = CHUNK_DATA(c) + c->used;
  c->used += size;
  return p;
}

void fly_arena_free(fly_arena* a) {
  for (fly_chunk* c = a->head; c;) {
    fly_chunk* next = c->next;
    free(c);
    c = next;
  }
  a->head = NULL;
}

fly_str* fly_arena_str(fly_arena* a, fly_str s) {
  uint8_t* bytes = fly_arena_alloc(a, s.len);
  if (s.len) memcpy(bytes, s.ptr, s.len);
  fly_str* r = fly_arena_alloc(a, sizeof(fly_str));
  *r = (fly_str){ bytes, s.len };
  return r;
}

fly_slice* fly_arena_slice(fly_arena* a, fly_slice s, size_t size) {
  void* items = fly_arena_alloc(a, s.len * size);
  if (s.len) memcpy(items, s.ptr, s.len * size);
  fly_slice* r = fly_arena_alloc(a, sizeof(fly_slice));
  *r = (fly_slice){ items, s.len };
  return r;
}

fly_rlist* fly_rlist_new(fly_arena* a, size_t size) {
  fly_rlist* l = fly_arena_alloc(a, sizeof(fly_rlist));
  *l = (fly_rlist){ a, 0, size, NULL, NULL };
  return l;
}

void fly_rlist_push(fly_rlist* l, const void* v) {
  fly_rchunk* c = l->last;
  if (!c || c->len == c->cap) {
    size_t cap = c ? c->cap * 2 : 8;
    fly_rchunk* n = fly_arena_alloc(l->arena, sizeof(fly_rchunk) + cap * l->size);
    *n = (fly_rchunk){ NULL, 0, cap, 0 };
    if (c) c->next = n; else l->first = n;
    l->last = c = n;
  }
  memcpy(FLY_RCHUNK_DATA(c) + c->len * l->size, v, l->size);
  c->len++;
  l->len++;
}

void* fly_rlist_at(const fly_rlist* l, size_t i) {
  for (fly_rchunk* c = l->first; c; c = c->next) {
    if (i < c->len) return FLY_RCHUNK_DATA(c) + i * l->size;
    i -= c->len;
  }
  fly_panic("a region list's element out of bounds");
}

// Well-formed UTF-8: no overlong forms, surrogates, or code points past U+10FFFF.
bool fly_utf8_valid(fly_slice b) {
  const uint8_t* p = b.ptr;
  size_t i = 0, n = b.len;
  while (i < n) {
    uint8_t c = p[i];
    size_t k;
    uint32_t cp;
    if (c < 0x80) { i++; continue; }
    else if ((c & 0xe0) == 0xc0) { k = 1; cp = c & 0x1f; }
    else if ((c & 0xf0) == 0xe0) { k = 2; cp = c & 0x0f; }
    else if ((c & 0xf8) == 0xf0) { k = 3; cp = c & 0x07; }
    else return false;
    if (i + k >= n) return false;
    for (size_t j = 1; j <= k; j++) {
      if ((p[i + j] & 0xc0) != 0x80) return false;
      cp = (cp << 6) | (p[i + j] & 0x3f);
    }
    if ((k == 1 && cp < 0x80) || (k == 2 && cp < 0x800) || (k == 3 && cp < 0x10000)) return false;
    if (cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff)) return false;
    i += k + 1;
  }
  return true;
}

#ifndef FLY_FREESTANDING
// ---- files ----

static char* cpath(fly_str path) {
  char* p = fly_alloc(path.len + 1);
  memcpy(p, path.ptr, path.len);
  return p;
}

bool fly_read_file(fly_str path, fly_String* out) {
  char* p = cpath(path);
  FILE* f = fopen(p, "rb");
  free(p);
  if (!f) return false;
  *out = fly_String_new();
  uint8_t buf[65536];
  size_t n;
  while ((n = fread(buf, 1, sizeof buf, f)) > 0) fly_String_push(out, (fly_str){ buf, n });
  fclose(f);
  return true;
}

bool fly_write_file(fly_str path, fly_str content) {
  char* p = cpath(path);
  FILE* f = fopen(p, "wb");
  free(p);
  if (!f) return false;
  bool ok = fwrite(content.ptr, 1, content.len, f) == content.len;
  return fclose(f) == 0 && ok;
}

void fly_File_drop(fly_File* f) { fly_String_drop(&f->text); }

// ---- the program ----

int fly_argc;
char** fly_argv;

fly_str fly_arg_str(int i) {
  if (i + 1 >= fly_argc) fly_panicf("argument %d is missing", i + 1);
  return (fly_str){ (const uint8_t*)fly_argv[i + 1], strlen(fly_argv[i + 1]) };
}

int64_t fly_arg_int(int i) {
  fly_str s = fly_arg_str(i);
  char* end;
  long long v = strtoll((const char*)s.ptr, &end, 10);
  if (*end != 0) fly_panicf("argument %d is not an integer", i + 1);
  return v;
}

double fly_arg_float(int i) {
  fly_str s = fly_arg_str(i);
  char* end;
  double v = strtod((const char*)s.ptr, &end);
  if (*end != 0) fly_panicf("argument %d is not a number", i + 1);
  return v;
}

fly_slice fly_arg_strs(int i) {
  int n = fly_argc - 1 - i > 0 ? fly_argc - 1 - i : 0;
  fly_str* a = fly_alloc((size_t)n * sizeof(fly_str) + 1);
  for (int k = 0; k < n; k++) a[k] = fly_arg_str(i + k);
  return (fly_slice){ a, (size_t)n };
}

fly_slice fly_arg_strings(int i) {
  int n = fly_argc - 1 - i > 0 ? fly_argc - 1 - i : 0;
  fly_String* a = fly_alloc((size_t)n * sizeof(fly_String) + 1);
  for (int k = 0; k < n; k++) a[k] = fly_String_from(fly_arg_str(i + k));
  return (fly_slice){ a, (size_t)n };
}

void fly_args_free(fly_slice s, bool strings) {
  if (strings) for (size_t k = 0; k < s.len; k++) fly_String_drop(&((fly_String*)s.ptr)[k]);
  free(s.ptr);
}
#endif

#ifdef FLY_FREESTANDING
// ---- without the C library ----

typedef struct { size_t size; size_t pad; } fly_block;

void* fly_mem_alloc(size_t n) {
  fly_block* b = fly_os_alloc(sizeof(fly_block) + n, 16);
  if (!b) return NULL;
  b->size = n;
  return b + 1;
}
void* fly_mem_calloc(size_t n, size_t size) {
  void* p = fly_mem_alloc(n * size);
  if (p) memset(p, 0, n * size);
  return p;
}
void* fly_mem_realloc(void* p, size_t n) {
  if (!p) return fly_mem_alloc(n);
  fly_block* b = (fly_block*)p - 1;
  if (n <= b->size) return p;
  void* q = fly_mem_alloc(n);
  if (!q) return NULL;
  memcpy(q, p, b->size);
  fly_mem_free(p);
  return q;
}
void fly_mem_free(void* p) { if (p) fly_os_free((fly_block*)p - 1); }

// What compiled code calls of the C library's: weak, so a program may give its own.
__attribute__((weak)) void* memcpy(void* dst, const void* src, size_t n) {
  uint8_t* d = dst;
  const uint8_t* s = src;
  while (n--) *d++ = *s++;
  return dst;
}
__attribute__((weak)) void* memmove(void* dst, const void* src, size_t n) {
  uint8_t* d = dst;
  const uint8_t* s = src;
  if (d < s) while (n--) *d++ = *s++;
  else { d += n; s += n; while (n--) *--d = *--s; }
  return dst;
}
__attribute__((weak)) void* memset(void* dst, int c, size_t n) {
  uint8_t* d = dst;
  while (n--) *d++ = (uint8_t)c;
  return dst;
}
__attribute__((weak)) int memcmp(const void* a, const void* b, size_t n) {
  const uint8_t* x = a;
  const uint8_t* y = b;
  for (; n; n--, x++, y++) if (*x != *y) return *x < *y ? -1 : 1;
  return 0;
}
__attribute__((weak)) size_t strlen(const char* s) {
  size_t n = 0;
  while (s[n]) n++;
  return n;
}
#endif
