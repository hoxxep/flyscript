// The runtime of Flyscript compiled to C (see runtime.h).

#include "runtime.h"

#include <math.h>
#include <stdarg.h>

void* fly_err = NULL;

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

_Noreturn void fly_panic(const char* message) {
  fflush(stdout);
  printf("<panic: %s>\n", message);
  fflush(stdout);
  exit(101);
}

_Noreturn void fly_panicf(const char* fmt, ...) {
  char buf[512];
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(buf, sizeof buf, fmt, ap);
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

fly_String fly_show_bool(bool v) { return fly_String_from(v ? fly_str_lit("true", 4) : fly_str_lit("false", 5)); }

void fly_println(fly_str s) {
  fwrite(s.ptr, 1, s.len, stdout);
  fputc('\n', stdout);
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

static bool space(uint8_t c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }

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

// ---- lists ----

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
void fly_Hasher_writeBool(fly_Hasher* h, bool v) { uint8_t b = v; hash_bytes(h, &b, 1); }
void fly_Hasher_writeStr(fly_Hasher* h, fly_str s) { hash_bytes(h, s.ptr, s.len); }
uint64_t fly_Hasher_finish(const fly_Hasher* h) { return h->h; }

// ---- generators ----

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
