// The runtime of Flyscript compiled to C (see runtime.h).

#include "runtime.h"

#include <math.h>
#include <stdarg.h>
#include <sys/mman.h>

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

void* fly_arc_new(size_t size) {
  long* p = fly_alloc(16 + size);
  p[0] = 1;
  return (uint8_t*)p + 16;
}
void* fly_arc_retain(void* p) { ((long*)((uint8_t*)p - 16))[0]++; return p; }
bool fly_arc_release(void* p) { return --((long*)((uint8_t*)p - 16))[0] == 0; }
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

bool fly_stopping = false;

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

struct fly_fiber {
  void* sp;
  void* stack;
  size_t size;
  void (*entry)(void* arg);
  void* arg;
  fly_fiber* back;
  fly_handler* handlers;
  bool done;
};

static fly_fiber main_fiber;
static fly_fiber* current = &main_fiber;
fly_handler* fly_handlers = NULL;
bool fly_unwinding = false;

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
#else
#error "fibers need arm64 or x86-64"
#endif

static void switch_to(fly_fiber* to) {
  fly_fiber* from = current;
  from->handlers = fly_handlers;
  fly_handlers = to->handlers;
  current = to;
#ifdef FLY_ASAN
  void* fake = NULL;
  __sanitizer_start_switch_fiber(from->done ? NULL : &fake, to->stack, to->size);
  fly_switch(&from->sp, to->sp);
  __sanitizer_finish_switch_fiber(fake, NULL, NULL);
#else
  fly_switch(&from->sp, to->sp);
#endif
}

void fly_fiber_start(fly_fiber* f) {
#ifdef FLY_ASAN
  __sanitizer_finish_switch_fiber(NULL, NULL, NULL);
#endif
  f->entry(f->arg);
  f->done = true;
  switch_to(f->back);
}

// Stacks are reserved large and committed as they are touched.
#define FLY_STACK (64u << 20)

static fly_fiber* fiber_new(void (*entry)(void*), void* arg, fly_handler* handlers) {
  fly_fiber* f = fly_alloc(sizeof(fly_fiber));
  f->size = FLY_STACK;
  f->stack = mmap(NULL, f->size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
  if (f->stack == MAP_FAILED) fly_panic("out of memory");
  f->entry = entry;
  f->arg = arg;
  f->handlers = handlers;
  uintptr_t top = ((uintptr_t)f->stack + f->size) & ~(uintptr_t)15;
  void** frame = (void**)(top - FRAME_WORDS * sizeof(void*));
  memset(frame, 0, FRAME_WORDS * sizeof(void*));
  frame[FRAME_FIBER] = f;
  frame[FRAME_RETURN] = (void*)fly_fiber_trampoline;
  f->sp = frame;
  return f;
}

static void fiber_free(fly_fiber* f) {
  munmap(f->stack, f->size);
  free(f);
}

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
}

// The handler is deep: what else the body performs goes to the handlers around the resumption.
void fly_handle_resume(fly_handler* h) {
  h->fiber->back = current;
  h->outer = fly_handlers;
  h->op = -1;
  switch_to(h->suspended);
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
  if (*json_at == '"') { json_string(); return; }
  if (*json_at == '[' || *json_at == '{') {
    char close = *json_at == '[' ? ']' : '}';
    json_at++;
    json_space();
    while (*json_at && *json_at != close) {
      if (close == '}') { json_string(); json_space(); json_at++; }
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
  return xorshift(&fault_rng) % 100 < world.faults;
}

bool fly_world_accept(fly_str* input) {
  world_load();
  if (world.accepted >= world.nincoming) return false;
  *input = world.incoming[world.accepted++];
  return true;
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

enum { WAIT_NONE, WAIT_TASK, WAIT_CHANNEL };

typedef struct {
  int id, scope;
  fly_fiber* fiber;
  fly_fiber* suspended;
  void (*entry)(void* task, void* closure);
  void* closure;
  void* result;
  size_t size;
  fly_failure* error;
  bool started, finished, cancelled, deliver_cancel, deliver_deadlock;
  int wait_kind, wait_id;
} task_t;

typedef struct { uint8_t* items; size_t len, head, size; long senders; bool closed; } chan_t;
typedef struct { int owner; int* tasks; size_t ntasks; fly_failure* failure; } scope_t;

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

// Hands the baton to a ready task, chosen by the seed; false if none can run.
static bool pass(void) {
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
  if (fly_tasks_on) suspend_task(WAIT_NONE, 0);
}

static void block(int kind, int id) {
  if (!fly_tasks_on) fly_panic_deadlock();
  suspend_task(kind, id);
}

// Task `me` has finished: its outcome goes to its scope, and its joiners wake.
static void end_task(int me) {
  task_t* t = sched.tasks[me];
  scope_t* st = sched.scopes[t->scope];
  if (t->error && !st->failure) {
    // The first failure cancels the scope: its body and its other tasks. It is the scope's to
    // raise, unless a join raises it first: a failure is raised once.
    st->failure = t->error;
    cancel(st->owner);
    for (size_t i = 0; i < st->ntasks; i++) if (st->tasks[i] != me) cancel(st->tasks[i]);
  }
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
      if (me == 0) {
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

void* fly_task_result(void* task) { return ((task_t*)task)->result; }
void* fly_task_closure(void* task) { return ((task_t*)task)->closure; }

static void join_task(int task) {
  if (!sched.tasks[task]->finished) block(WAIT_TASK, task);
}

// A forked task's value, or its failure, raised.
void fly_join(int task, void* out) {
  join_task(task);
  if (fly_unwinding) return;
  task_t* t = sched.tasks[task];
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
  scope_t* st = sched.scopes[sid];
  task_t* me = sched.tasks[sched.current];
  // The body unwound because a task failed: the scope raises that failure instead.
  bool unwound = fly_unwinding && !(st->failure);
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
  if (unwound) { fly_unwinding = true; if (err) free(err); return; }
  if (err) { fly_err = err; return; }
  if (st->failure) { fly_err = st->failure; st->failure = NULL; }
}

// ---- channels ----

fly_chan fly_channel(void) {
  int id = sched.next++;
  grow_ids(id);
  chan_t* c = fly_alloc(sizeof(chan_t));
  c->senders = 1;
  sched.chans[id] = c;
  return (fly_chan){ id };
}

void fly_send(fly_chan ch, const void* v, size_t size) {
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
  sender_gone(sched.chans[ch.ch], ch.ch);
  fly_point();
}

// A destructor does not suspend: a sender dropped closes its channel then and there.
void fly_sender_drop(fly_chan* ch) {
  if (ch->ch) sender_gone(sched.chans[ch->ch], ch->ch);
  ch->ch = 0;
}

fly_chan fly_sender_clone(const fly_chan* ch) {
  sched.chans[ch->ch]->senders++;
  return *ch;
}

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
