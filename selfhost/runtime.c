// The runtime of Flyscript compiled to C (see runtime.h).

#include "runtime.h"

#include <stdarg.h>
#ifndef FLY_FREESTANDING
#include <math.h>
#include <time.h>
#ifndef __wasm__
#include <errno.h>
#include <fcntl.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <unistd.h>
#else
#include <sys/uio.h>
#include <unistd.h>
#endif
#endif

// A variable of the thread's. On threads it is reached through a call the compiler may neither
// inline nor reuse: a task may go on on another thread after a call that switched away, and an
// address computed before the switch would be the old thread's.
#ifdef FLY_THREADS
#define FLY_THREAD_VAR(T, name, init) \
  static FLY_LOCAL T name##_tls = init; \
  static __attribute__((noinline)) T* name##_ref(void) { T* p = &name##_tls; __asm__ volatile("" : "+r"(p)); return p; }
#else
#define FLY_THREAD_VAR(T, name, init) \
  static T name##_tls = init; \
  static inline T* name##_ref(void) { return &name##_tls; }
#endif

// The task running's context (runtime.h): with one thread, the one there is; on threads, the
// task's own, which the thread's pointer reaches. A worker running no task has one of its own.
#ifdef FLY_THREADS
static fly_ctx fly_ctx0;
FLY_THREAD_VAR(fly_ctx*, fly_cur, &fly_ctx0)
#define fly_cur (*fly_cur_ref())
__attribute__((noinline)) fly_ctx* fly_cx(void) { return fly_cur; }
// The context as the thread's pointer has it now, for the scheduler, which changes that pointer
// between tasks: unlike `fly_cx`, never one computed before.
#define fly_cx_now() (fly_cur)
#else
fly_ctx fly_ctx0;
fly_ctx* (fly_cx)(void) { return &fly_ctx0; }
#define fly_cx_now() (&fly_ctx0)
#endif
// As LLVM IR reaches its fields (llvm.fly's `cxField`).
_Static_assert(offsetof(fly_ctx, unwinding) == sizeof(void*) && offsetof(fly_ctx, stopping) == sizeof(void*) + 1 && offsetof(fly_ctx, handlers) == 2 * sizeof(void*), "fly_ctx as LLVM IR reaches it");

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

static _Noreturn void panic_exit(const char* message);

// A panic ends the program where it is, every task with it, running no one's cleanup (§5.7).
_Noreturn void fly_panic(const char* message) { panic_exit(message); }

#ifdef FLY_FREESTANDING
static _Noreturn void panic_exit(const char* message) { fly_os_panic(message, strlen(message)); }
#else
// Bytes to a stream of the program's, whole. In WebAssembly the C library's streams are left out:
// each line goes to the host as it is written.
static void write_out(int fd, const struct iovec* parts, int n) {
#ifdef __wasm__
  struct iovec left[4];
  for (int i = 0; i < n; i++) left[i] = parts[i];
  int k = 0;
  while (k < n) {
    ssize_t w = writev(fd, left + k, n - k);
    if (w < 0) return;
    while (k < n && (size_t)w >= left[k].iov_len) { w -= (ssize_t)left[k].iov_len; k++; }
    if (k < n) { left[k].iov_base = (char*)left[k].iov_base + w; left[k].iov_len -= (size_t)w; }
  }
#else
  FILE* f = fd == 2 ? stderr : stdout;
  for (int i = 0; i < n; i++) fwrite(parts[i].iov_base, 1, parts[i].iov_len, f);
#endif
}

void fly_out(fly_str s) {
  struct iovec part = { (void*)s.ptr, s.len };
  write_out(1, &part, 1);
}

static _Noreturn void panic_exit(const char* message) {
  // On worker threads, the first to panic reports it; the others wait for the end.
  static int reporting;
  if (__atomic_exchange_n(&reporting, 1, __ATOMIC_ACQ_REL)) for (;;) {}
  struct iovec parts[3] = { { "<panic: ", 8 }, { (void*)message, strlen(message) }, { ">\n", 2 } };
  write_out(1, parts, 3);
#ifndef __wasm__
  fflush(stdout);
#endif
  _Exit(101);
}
#endif

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
      for (int i = 0; (prec < 0 || i < prec) && s[i]; i++) PUT(s[i]);
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

// As `snprintf`, with the formats `format` knows: the length written.
static int fmt_text(char* out, size_t cap, const char* fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  format(out, cap, fmt, ap);
  va_end(ap);
  return (int)strlen(out);
}

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

#ifdef FLY_MALLOC
// Blocks of up to 16 KiB come in 36 classes of sizes, each a multiple of 16, four to a doubling
// past 128 bytes. A class's blocks are carved from spans of 64 KiB, each of one class, which say
// which in their first 16 bytes; spans are carved from one reservation of address space, which the
// system commits as it is touched. Each thread keeps a list per class of the blocks it freed, and
// allocates from it first; a list grown past a bound gives half back to its class's, which every
// thread shares, and an empty one takes a batch from there, or from a span. Larger blocks, and
// every block once the reservation is used up, are the C library's, which a block's address tells
// apart. Memory freed stays the program's, to allocate again.
//
// In WebAssembly, where the allocator is the C library's too, spans are the pages memory grows by,
// and a larger block is a run of whole pages, which says how many in its first 16 bytes; a run
// freed is kept, and the first kept that is long enough is used again, its rest kept apart.
#define FLY_SPAN ((size_t)64 << 10)
#define FLY_CLASSES 36
#define FLY_SMALL_MAX ((size_t)16 << 10)
#define FLY_BATCH 32

static inline size_t fly_class_size(unsigned c) {
  if (c < 8) return (size_t)(c + 1) * 16;
  unsigned k = c - 8;
  return (size_t)(5 + k % 4) << (5 + k / 4);
}

static inline unsigned fly_class_of(size_t n) {
  if (n <= 128) return n ? (unsigned)((n - 1) >> 4) : 0;
  unsigned b = 63 - (unsigned)__builtin_clzll((unsigned long long)(n - 1));
  return 8 + (b - 7) * 4 + (unsigned)(((n - 1) >> (b - 2)) & 3);
}

typedef struct { int lock; void* free; uint8_t* bump; uint8_t* end; } fly_central;
static fly_central fly_centrals[FLY_CLASSES];
static uint8_t* fly_heap_lo;
static uint8_t* fly_heap_hi;
static uint8_t* fly_heap_next;
static int fly_heap_state;

typedef struct { void* head[FLY_CLASSES]; uint32_t n[FLY_CLASSES]; } fly_cache;
FLY_THREAD_VAR(fly_cache, fly_cache, { { 0 } })

static void fly_spin_lock(int* l) {
  while (__atomic_exchange_n(l, 1, __ATOMIC_ACQUIRE)) {
    while (__atomic_load_n(l, __ATOMIC_RELAXED)) {
#if defined(__aarch64__)
      __asm__ volatile("yield");
#elif defined(__x86_64__)
      __asm__ volatile("pause");
#endif
    }
  }
}
static void fly_spin_unlock(int* l) { __atomic_store_n(l, 0, __ATOMIC_RELEASE); }

#ifdef __wasm__
// `n` spans more, from memory grown by as many pages.
static uint8_t* fly_spans(size_t n) {
  size_t at = __builtin_wasm_memory_grow(0, n);
  if (at == (size_t)-1) return NULL;
  uint8_t* p = (uint8_t*)(at * FLY_SPAN);
  if (!fly_heap_lo) fly_heap_lo = p;
  fly_heap_hi = p + n * FLY_SPAN;
  return p;
}
#else
// The reservation, made once, by whichever thread allocates first: 64 GiB, or 4 if the system will
// not give that, or none, and every block the C library's.
static void fly_heap_init(void) {
  int expected = 0;
  if (__atomic_compare_exchange_n(&fly_heap_state, &expected, 1, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
    size_t sizes[2] = { (size_t)64 << 30, (size_t)4 << 30 };
    for (int i = 0; i < 2; i++) {
      void* p = mmap(NULL, sizes[i] + FLY_SPAN, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
      if (p == MAP_FAILED) continue;
      uint8_t* lo = (uint8_t*)(((uintptr_t)p + FLY_SPAN - 1) & ~(uintptr_t)(FLY_SPAN - 1));
      fly_heap_next = lo;
      fly_heap_hi = lo + sizes[i];
      fly_heap_lo = lo;
      break;
    }
    __atomic_store_n(&fly_heap_state, 2, __ATOMIC_RELEASE);
  } else {
    while (__atomic_load_n(&fly_heap_state, __ATOMIC_ACQUIRE) != 2) {}
  }
}

// A span of the reservation, if any is left.
static uint8_t* fly_spans(size_t n) {
  if (__atomic_load_n(&fly_heap_state, __ATOMIC_ACQUIRE) != 2) fly_heap_init();
  if (!fly_heap_lo) return NULL;
  uint8_t* span = __atomic_fetch_add(&fly_heap_next, n * FLY_SPAN, __ATOMIC_RELAXED);
  return span + n * FLY_SPAN <= fly_heap_hi ? span : NULL;
}
#endif

#ifdef __wasm__
#define FLY_RUN 0xffffffffu
// A run of pages: `FLY_RUN`, how many, and the next run kept, in its first 16 bytes.
typedef struct fly_run { uint32_t mark; uint32_t spans; struct fly_run* next; } fly_run;
static fly_run* fly_runs;

static void* fly_large(size_t n) {
  size_t k = (n + 16 + FLY_SPAN - 1) / FLY_SPAN;
  fly_run** at = &fly_runs;
  while (*at && (*at)->spans < k) at = &(*at)->next;
  fly_run* r = *at;
  if (r) {
    *at = r->next;
    if (r->spans > k) {
      fly_run* rest = (fly_run*)((uint8_t*)r + k * FLY_SPAN);
      rest->mark = FLY_RUN;
      rest->spans = r->spans - (uint32_t)k;
      rest->next = fly_runs;
      fly_runs = rest;
      r->spans = (uint32_t)k;
    }
  } else {
    r = (fly_run*)fly_spans(k);
    if (!r) return NULL;
    r->mark = FLY_RUN;
    r->spans = (uint32_t)k;
  }
  return (uint8_t*)r + 16;
}
#else
static void* fly_large(size_t n) { return fly_sys_malloc(n); }
#endif

// A thread's list of class `c` is empty: a batch from the class's, or carved from its span, or
// from a new span. Holds the class's lock while it does.
static void* fly_refill(fly_cache* t, unsigned c, size_t n) {
  fly_central* k = &fly_centrals[c];
  size_t size = fly_class_size(c);
  fly_spin_lock(&k->lock);
  uint32_t got = 0;
  while (k->free && got < FLY_BATCH) {
    void* b = k->free;
    k->free = *(void**)b;
    *(void**)b = t->head[c];
    t->head[c] = b;
    got++;
  }
  while (got < FLY_BATCH) {
    if (k->bump + size > k->end) {
      uint8_t* span = fly_spans(1);
      if (!span) break;
      *(uint32_t*)span = c;
      k->bump = span + 16;
      k->end = span + FLY_SPAN;
    }
    void* b = k->bump;
    k->bump += size;
    *(void**)b = t->head[c];
    t->head[c] = b;
    got++;
  }
  fly_spin_unlock(&k->lock);
  if (!got) return fly_large(n);
  t->n[c] += got;
  void* p = t->head[c];
  t->head[c] = *(void**)p;
  t->n[c]--;
  return p;
}

// A thread's list of class `c` has grown past its bound: a batch of it goes back to the class's.
static void fly_flush(fly_cache* t, unsigned c) {
  void* first = t->head[c];
  void* last = first;
  for (uint32_t i = 1; i < FLY_BATCH; i++) last = *(void**)last;
  t->head[c] = *(void**)last;
  t->n[c] -= FLY_BATCH;
  fly_central* k = &fly_centrals[c];
  fly_spin_lock(&k->lock);
  *(void**)last = k->free;
  k->free = first;
  fly_spin_unlock(&k->lock);
}

static inline bool fly_small(const void* p) { return (const uint8_t*)p >= fly_heap_lo && (const uint8_t*)p < fly_heap_hi; }
static inline unsigned fly_class_at(const void* p) { return *(const uint32_t*)((uintptr_t)p & ~(uintptr_t)(FLY_SPAN - 1)); }

void* fly_mem_alloc(size_t n) {
  if (n > FLY_SMALL_MAX) return fly_large(n);
  unsigned c = fly_class_of(n);
  fly_cache* t = fly_cache_ref();
  void* p = t->head[c];
  if (!p) return fly_refill(t, c, n);
  t->head[c] = *(void**)p;
  t->n[c]--;
  return p;
}

void fly_mem_free(void* p) {
  if (!p) return;
  unsigned c;
#ifdef __wasm__
  c = fly_class_at(p);
  if (c == FLY_RUN) {
    fly_run* r = (fly_run*)((uint8_t*)p - 16);
    r->next = fly_runs;
    fly_runs = r;
    return;
  }
#else
  if (!fly_small(p)) { fly_sys_free(p); return; }
  c = fly_class_at(p);
#endif
  fly_cache* t = fly_cache_ref();
  *(void**)p = t->head[c];
  t->head[c] = p;
  if (++t->n[c] > 2 * FLY_BATCH) fly_flush(t, c);
}

void* fly_mem_calloc(size_t n, size_t size) {
  size_t total;
  if (__builtin_mul_overflow(n, size, &total)) return NULL;
  void* p = fly_mem_alloc(total);
  if (p) memset(p, 0, total);
  return p;
}

void* fly_mem_realloc(void* p, size_t n) {
  if (!p) return fly_mem_alloc(n);
#ifdef __wasm__
  if (fly_class_at(p) == FLY_RUN) {
    fly_run* r = (fly_run*)((uint8_t*)p - 16);
    size_t room = (size_t)r->spans * FLY_SPAN - 16;
    if (n <= room) return p;
    void* q = fly_mem_alloc(n);
    if (!q) return NULL;
    memcpy(q, p, room);
    fly_mem_free(p);
    return q;
  }
#else
  if (!fly_small(p)) {
    if (n > FLY_SMALL_MAX) return fly_sys_realloc(p, n);
    // Shrunk to a small block: what it keeps is all of `n`, as the old block is larger.
    void* q = fly_mem_alloc(n);
    if (!q) return NULL;
    memcpy(q, p, n);
    fly_sys_free(p);
    return q;
  }
#endif
  size_t have = fly_class_size(fly_class_at(p));
  if (n <= have) return p;
  void* q = fly_mem_alloc(n);
  if (!q) return NULL;
  memcpy(q, p, have);
  fly_mem_free(p);
  return q;
}

#ifdef __wasm__
// The program's allocator, the C library's code's too.
void* malloc(size_t n) { return fly_mem_alloc(n); }
void* calloc(size_t n, size_t size) { return fly_mem_calloc(n, size); }
void* realloc(void* p, size_t n) { return fly_mem_realloc(p, n); }
void free(void* p) { fly_mem_free(p); }
#endif
#endif

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

// A `Mutex`'s state follows a header of its own: its lock, and the tasks waiting for it.
#define MUTEX_HEADER 32

void* fly_mutex_new(const void* value, size_t size) {
  uint8_t* p = fly_alloc(MUTEX_HEADER + size);
  memset(p, 0, MUTEX_HEADER);
  memcpy(p + MUTEX_HEADER, value, size);
  return p + MUTEX_HEADER;
}

void fly_mutex_free(void* state) {
  if (state) free((uint8_t*)state - MUTEX_HEADER);
}

int64_t fly_atomic_add(int64_t* a, int64_t v) {
  int64_t old = __atomic_load_n(a, __ATOMIC_SEQ_CST), sum;
  do {
    if (__builtin_add_overflow(old, v, &sum)) fly_panic("arithmetic overflow");
  } while (!__atomic_compare_exchange_n(a, &old, sum, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST));
  return old;
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

// ---- floats as text ----
//
// Exactly, and without the C library: a float is m·2^e, and the decimal digits are found with
// integers as large as they need to be. Shown, a float is the fewest digits that read back as it,
// the nearest of them to it, written out in full without an exponent; `toFixed` rounds to the
// nearest, a value exactly halfway to the even; text is read as the nearest float, halfway to the
// even.

// An unsigned integer of up to 5,120 bits, its 32-bit digits least significant first.
typedef struct { uint32_t n; uint32_t d[160]; } fly_bignum;

static void big_set(fly_bignum* a, uint64_t v) {
  a->n = 0;
  while (v) { a->d[a->n++] = (uint32_t)v; v >>= 32; }
}

static void big_mul(fly_bignum* a, uint32_t m) {
  uint64_t c = 0;
  for (uint32_t i = 0; i < a->n; i++) {
    uint64_t t = (uint64_t)a->d[i] * m + c;
    a->d[i] = (uint32_t)t;
    c = t >> 32;
  }
  if (c) a->d[a->n++] = (uint32_t)c;
}

static void big_add_small(fly_bignum* a, uint32_t m) {
  uint64_t c = m;
  for (uint32_t i = 0; i < a->n && c; i++) {
    uint64_t t = (uint64_t)a->d[i] + c;
    a->d[i] = (uint32_t)t;
    c = t >> 32;
  }
  if (c) a->d[a->n++] = (uint32_t)c;
}

static void big_pow10(fly_bignum* a, int k) {
  static const uint32_t p[] = { 1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000 };
  for (; k >= 9; k -= 9) big_mul(a, 1000000000);
  if (k > 0) big_mul(a, p[k]);
}

static void big_shl(fly_bignum* a, int bits) {
  if (a->n == 0 || bits <= 0) return;
  int w = bits / 32, b = bits % 32;
  if (b) {
    uint32_t c = 0;
    for (uint32_t i = 0; i < a->n; i++) {
      uint32_t t = a->d[i];
      a->d[i] = (t << b) | c;
      c = t >> (32 - b);
    }
    if (c) a->d[a->n++] = c;
  }
  if (w) {
    for (int i = (int)a->n - 1; i >= 0; i--) a->d[i + w] = a->d[i];
    for (int i = 0; i < w; i++) a->d[i] = 0;
    a->n += (uint32_t)w;
  }
}

static int big_cmp(const fly_bignum* a, const fly_bignum* b) {
  if (a->n != b->n) return a->n < b->n ? -1 : 1;
  for (int i = (int)a->n - 1; i >= 0; i--) if (a->d[i] != b->d[i]) return a->d[i] < b->d[i] ? -1 : 1;
  return 0;
}

// a + b compared with c.
static int big_cmp_sum(const fly_bignum* a, const fly_bignum* b, const fly_bignum* c) {
  fly_bignum s = *a;
  uint64_t carry = 0;
  uint32_t n = a->n > b->n ? a->n : b->n;
  for (uint32_t i = 0; i < n; i++) {
    uint64_t t = (uint64_t)(i < a->n ? a->d[i] : 0) + (i < b->n ? b->d[i] : 0) + carry;
    s.d[i] = (uint32_t)t;
    carry = t >> 32;
  }
  s.n = n;
  if (carry) s.d[s.n++] = (uint32_t)carry;
  return big_cmp(&s, c);
}

// a -= b, where a >= b.
static void big_sub(fly_bignum* a, const fly_bignum* b) {
  int64_t borrow = 0;
  for (uint32_t i = 0; i < a->n; i++) {
    int64_t t = (int64_t)a->d[i] - (i < b->n ? b->d[i] : 0) - borrow;
    borrow = t < 0;
    a->d[i] = (uint32_t)(t + (borrow << 32));
  }
  while (a->n && a->d[a->n - 1] == 0) a->n--;
}

static bool big_bit(const fly_bignum* a, int i) {
  return i >= 0 && (uint32_t)(i / 32) < a->n && ((a->d[i / 32] >> (i % 32)) & 1);
}

// Whether any of the bits below bit `i` is set.
static bool big_any_below(const fly_bignum* a, int i) {
  for (int w = 0; w < i / 32 && (uint32_t)w < a->n; w++) if (a->d[w]) return true;
  int b = i % 32;
  return b && (uint32_t)(i / 32) < a->n && (a->d[i / 32] & ((1u << b) - 1));
}

static void big_shr(fly_bignum* a, int bits) {
  int w = bits / 32, b = bits % 32;
  if ((uint32_t)w >= a->n) { a->n = 0; return; }
  for (uint32_t i = 0; i + (uint32_t)w < a->n; i++) a->d[i] = a->d[i + w];
  a->n -= (uint32_t)w;
  if (b) for (uint32_t i = 0; i < a->n; i++) a->d[i] = (a->d[i] >> b) | (i + 1 < a->n ? a->d[i + 1] << (32 - b) : 0);
  while (a->n && a->d[a->n - 1] == 0) a->n--;
}

static int big_bits(const fly_bignum* a) {
  return a->n ? (int)(a->n - 1) * 32 + 32 - __builtin_clz(a->d[a->n - 1]) : 0;
}

// a /= m, giving the remainder.
static uint32_t big_div(fly_bignum* a, uint32_t m) {
  uint64_t r = 0;
  for (int i = (int)a->n - 1; i >= 0; i--) {
    uint64_t t = (r << 32) | a->d[i];
    a->d[i] = (uint32_t)(t / m);
    r = t % m;
  }
  while (a->n && a->d[a->n - 1] == 0) a->n--;
  return (uint32_t)r;
}

// The quotient num / den, which is below 2^64; num becomes the remainder.
static uint64_t big_quot(fly_bignum* num, const fly_bignum* den) {
  uint64_t q = 0;
  int s = big_bits(num) - big_bits(den);
  for (; s >= 0; s--) {
    fly_bignum t = *den;
    big_shl(&t, s);
    if (big_cmp(&t, num) <= 0) {
      big_sub(num, &t);
      q |= (uint64_t)1 << s;
    }
  }
  return q;
}

// The mantissa and exponent of a finite float that is not negative: v = m·2^e.
static void float_parts(double v, uint64_t* m, int* e) {
  uint64_t bits;
  memcpy(&bits, &v, 8);
  int be = (int)((bits >> 52) & 0x7ff);
  uint64_t frac = bits & (((uint64_t)1 << 52) - 1);
  if (be == 0) { *m = frac; *e = -1074; }
  else { *m = frac | ((uint64_t)1 << 52); *e = be - 1075; }
}

// The fewest decimal digits that read back as `v`, finite and positive, the nearest of them to it:
// v ≈ 0.d₁d₂…dₙ × 10^k. Steele and White's method: r/s is what is left to write, and m⁻/s and m⁺/s
// how far below and above it a float still reads as `v`.
static int shortest(double v, char* digits, int* k) {
  uint64_t f;
  int e;
  float_parts(v, &f, &e);
  bool even = (f & 1) == 0;
  // At a power of two the floats below are closer together than those above.
  bool tight = f == ((uint64_t)1 << 52) && e > -1074;
  fly_bignum r, s, mp, mm;
  big_set(&r, f);
  big_set(&s, 1);
  big_set(&mp, 1);
  big_set(&mm, 1);
  if (e >= 0) {
    big_shl(&r, e + (tight ? 2 : 1));
    big_set(&s, tight ? 4 : 2);
    big_shl(&mp, e + (tight ? 1 : 0));
    big_shl(&mm, e);
  } else {
    big_shl(&r, tight ? 2 : 1);
    big_shl(&s, (tight ? 2 : 1) - e);
    if (tight) big_set(&mp, 2);
  }
  // k from the number of bits, then exactly.
  int kk = (int)(((int64_t)(e + 63 - __builtin_clzll(f)) * 78913) >> 18);
  if (kk >= 0) big_pow10(&s, kk);
  else { big_pow10(&r, -kk); big_pow10(&mp, -kk); big_pow10(&mm, -kk); }
  for (;;) {
    int c = big_cmp_sum(&r, &mp, &s);
    if (even ? c >= 0 : c > 0) { big_mul(&s, 10); kk++; continue; }
    fly_bignum t = r;
    big_mul(&t, 10);
    fly_bignum u = mp;
    big_mul(&u, 10);
    c = big_cmp_sum(&t, &u, &s);
    if (even ? c < 0 : c <= 0) { r = t; mp = u; big_mul(&mm, 10); kk--; continue; }
    break;
  }
  int n = 0;
  for (;;) {
    big_mul(&r, 10);
    big_mul(&mp, 10);
    big_mul(&mm, 10);
    int d = 0;
    while (big_cmp(&r, &s) >= 0) { big_sub(&r, &s); d++; }
    int lo = big_cmp(&r, &mm);
    bool low = even ? lo <= 0 : lo < 0;
    int hi = big_cmp_sum(&r, &mp, &s);
    bool high = even ? hi >= 0 : hi > 0;
    if (!low && !high) { digits[n++] = (char)('0' + d); continue; }
    if (low && high) {
      fly_bignum twice = r;
      big_mul(&twice, 2);
      int c = big_cmp(&twice, &s);
      if (c > 0 || (c == 0 && (d & 1))) d++;
    } else if (high) {
      d++;
    }
    digits[n++] = (char)('0' + d);
    break;
  }
  // A last digit rounded up to ten carries into those before it.
  for (int i = n - 1; i > 0 && digits[i] > '9'; i--) { digits[i] = '0'; digits[i - 1]++; }
  if (digits[0] > '9') {
    digits[0] = '1';
    for (int i = 1; i < n; i++) digits[i] = '0';
    kk++;
  }
  while (n > 1 && digits[n - 1] == '0') n--;
  *k = kk;
  return n;
}

fly_String fly_show_f64(double v) {
  fly_String s = fly_String_new();
  if (v != v) { fly_String_push(&s, fly_str_lit("NaN", 3)); return s; }
  uint64_t bits;
  memcpy(&bits, &v, 8);
  if (bits >> 63) { fly_String_push_byte(&s, '-'); v = -v; }
  if (v > 1.7976931348623157e308) { fly_String_push(&s, fly_str_lit("inf", 3)); return s; }
  uint64_t f;
  int e;
  float_parts(v, &f, &e);
  // An integral value below 10^15 shows one decimal place.
  if (v < 1e15 && (e >= 0 || (e > -64 && (f & ((((uint64_t)1) << -e) - 1)) == 0))) {
    uint64_t w = e >= 0 ? f << e : f >> -e;
    fly_String n = fly_show_u128(w);
    fly_String_push(&s, fly_String_as_str(&n));
    fly_String_drop(&n);
    fly_String_push(&s, fly_str_lit(".0", 2));
    return s;
  }
  if (v == 0) { fly_String_push(&s, fly_str_lit("0.0", 3)); return s; }
  char d[20];
  int k;
  int n = shortest(v, d, &k);
  if (k <= 0) {
    fly_String_push(&s, fly_str_lit("0.", 2));
    for (int i = 0; i < -k; i++) fly_String_push_byte(&s, '0');
    fly_String_push(&s, (fly_str){ (const uint8_t*)d, (size_t)n });
  } else if (k >= n) {
    fly_String_push(&s, (fly_str){ (const uint8_t*)d, (size_t)n });
    for (int i = n; i < k; i++) fly_String_push_byte(&s, '0');
  } else {
    fly_String_push(&s, (fly_str){ (const uint8_t*)d, (size_t)k });
    fly_String_push_byte(&s, '.');
    fly_String_push(&s, (fly_str){ (const uint8_t*)d + k, (size_t)(n - k) });
  }
  return s;
}

// The digits of `a`, which is emptied.
static void big_decimal(fly_bignum* a, fly_String* out) {
  char buf[1600];
  int n = 0;
  do {
    uint32_t chunk = big_div(a, 1000000000);
    for (int i = 0; i < 9; i++) { buf[n++] = (char)('0' + chunk % 10); chunk /= 10; }
  } while (a->n);
  while (n > 1 && buf[n - 1] == '0') n--;
  for (int i = n - 1; i >= 0; i--) fly_String_push_byte(out, (uint8_t)buf[i]);
}

fly_String fly_float_fixed(double v, uint32_t digits) {
  fly_String s = fly_String_new();
  if (v != v) { fly_String_push(&s, fly_str_lit("NaN", 3)); return s; }
  uint64_t bits;
  memcpy(&bits, &v, 8);
  if (bits >> 63) { fly_String_push_byte(&s, '-'); v = -v; }
  if (v > 1.7976931348623157e308) { fly_String_push(&s, fly_str_lit("inf", 3)); return s; }
  if (digits > 100) digits = 100;
  uint64_t f;
  int e;
  float_parts(v, &f, &e);
  // v·10^digits, rounded to the nearest integer, halfway to the even.
  fly_bignum q;
  big_set(&q, f);
  big_pow10(&q, (int)digits);
  if (e >= 0) {
    big_shl(&q, e);
  } else {
    // q >>= -e, the bits shifted out deciding the rounding: the first of them is a half.
    int drop = -e;
    bool half = big_bit(&q, drop - 1), rest = big_any_below(&q, drop - 1);
    big_shr(&q, drop);
    if (half && (rest || (q.n && (q.d[0] & 1)))) big_add_small(&q, 1);
  }
  fly_String num = fly_String_new();
  big_decimal(&q, &num);
  // At least one digit before the point.
  size_t len = num.len;
  if (len <= digits) {
    fly_String_push_byte(&s, '0');
    if (digits) {
      fly_String_push_byte(&s, '.');
      for (size_t i = len; i < digits; i++) fly_String_push_byte(&s, '0');
      fly_String_push(&s, fly_String_as_str(&num));
    }
  } else {
    fly_String_push(&s, (fly_str){ num.ptr, len - digits });
    if (digits) {
      fly_String_push_byte(&s, '.');
      fly_String_push(&s, (fly_str){ num.ptr + len - digits, digits });
    }
  }
  fly_String_drop(&num);
  return s;
}

// Decimal text as the nearest float, halfway to the even: an optional sign, digits with a point
// among or before or after them, and an exponent, nothing else.
bool fly_parse_float(fly_str t, double* out) {
  size_t i = 0;
  bool neg = false;
  if (i < t.len && (t.ptr[i] == '+' || t.ptr[i] == '-')) { neg = t.ptr[i] == '-'; i++; }
  // The significant digits, up to 800, and whether any beyond them is not zero.
  char sig[801];
  int n = 0, exp10 = 0;
  bool any = false, more = false, point = false;
  for (; i < t.len; i++) {
    uint8_t c = t.ptr[i];
    if (c == '.' && !point) { point = true; continue; }
    if (c < '0' || c > '9') break;
    any = true;
    if (n == 0 && c == '0') { if (point) exp10--; continue; }
    if (n < 800) { sig[n++] = (char)c; if (point) exp10--; }
    else { if (c != '0') more = true; if (!point) exp10++; }
  }
  if (!any) return false;
  if (i < t.len && (t.ptr[i] == 'e' || t.ptr[i] == 'E')) {
    i++;
    bool eneg = false;
    if (i < t.len && (t.ptr[i] == '+' || t.ptr[i] == '-')) { eneg = t.ptr[i] == '-'; i++; }
    if (i == t.len || t.ptr[i] < '0' || t.ptr[i] > '9') return false;
    long x = 0;
    for (; i < t.len && t.ptr[i] >= '0' && t.ptr[i] <= '9'; i++) if (x < 100000) x = x * 10 + (t.ptr[i] - '0');
    exp10 += (int)(eneg ? -x : x);
  }
  if (i != t.len) return false;
  double v;
  if (n == 0) v = 0;
  else if (n + exp10 > 310) v = 1.0 / 0.0;
  else if (n + exp10 < -326) v = 0;
  else {
    // A digit 1 past the 800th stands for the rest, which only breaks a tie.
    if (more) { sig[n++] = '1'; exp10--; }
    fly_bignum num, den;
    big_set(&num, 0);
    for (int k = 0; k < n; k++) {
      big_mul(&num, 10);
      big_add_small(&num, (uint32_t)(sig[k] - '0'));
    }
    big_set(&den, 1);
    if (exp10 >= 0) big_pow10(&num, exp10);
    else big_pow10(&den, -exp10);
    // num / den = q·2^b, with 2^52 <= q < 2^53, or b = -1074 for a subnormal.
    int b = big_bits(&num) - big_bits(&den) - 53;
    uint64_t q;
    fly_bignum rem, d;
    for (;;) {
      if (b < -1074) b = -1074;
      rem = num;
      d = den;
      if (b >= 0) big_shl(&d, b);
      else big_shl(&rem, -b);
      q = big_quot(&rem, &d);
      if (q >= ((uint64_t)1 << 53)) { b++; continue; }
      if (q < ((uint64_t)1 << 52) && b > -1074) { b--; continue; }
      break;
    }
    fly_bignum twice = rem;
    big_mul(&twice, 2);
    int c = big_cmp(&twice, &d);
    if (c > 0 || (c == 0 && (q & 1))) q++;
    if (q == ((uint64_t)1 << 53)) { q >>= 1; b++; }
    if (b > 971) v = 1.0 / 0.0;
    else {
      uint64_t bits = q < ((uint64_t)1 << 52) ? q : ((uint64_t)(b + 1075) << 52) | (q & (((uint64_t)1 << 52) - 1));
      memcpy(&v, &bits, 8);
    }
  }
  *out = neg ? -v : v;
  return true;
}

fly_String fly_show_bool(bool v) { return fly_String_from(v ? fly_str_lit("true", 4) : fly_str_lit("false", 5)); }

#ifndef FLY_FREESTANDING
// A line written whole, under the stream's lock, so lines from tasks on other cores never mix.
static void write_line(int fd, fly_str s) {
  struct iovec parts[2] = { { (void*)s.ptr, s.len }, { "\n", 1 } };
#ifdef __wasm__
  write_out(fd, parts, 2);
#else
  FILE* f = fd == 2 ? stderr : stdout;
  flockfile(f);
  write_out(fd, parts, 2);
  funlockfile(f);
#endif
}

void fly_println(fly_str s) { write_line(1, s); }
void fly_eprintln(fly_str s) { write_line(2, s); }

// The program ends here, with the status asked for: no cleanup runs, as for a panic (§5.7).
_Noreturn void fly_exit(int32_t code) {
#ifndef __wasm__
  fflush(stdout);
#endif
  _Exit(code);
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
// A float hashes by its bits, as `Eq` sees it: `-0.0` as `0.0`, every `NaN` as one.
void fly_Hasher_writeFloat(fly_Hasher* h, double v) {
  if (v == 0) v = 0;
  if (v != v) v = __builtin_nan("");
  uint8_t b[8];
  memcpy(b, &v, 8);
  hash_bytes(h, b, 8);
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
// The fiber running on this thread.
FLY_THREAD_VAR(fly_fiber*, cur_fiber, &main_fiber)
#define cur_fiber (*cur_fiber_ref())

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
  fly_fiber* from = cur_fiber;
  fly_ctx* cx = fly_cx_now();
  from->handlers = cx->handlers;
  cx->handlers = to->handlers;
  cur_fiber = to;
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
typedef struct { void* stacks[STACK_POOL + 1]; int n; } stack_pool_t;
FLY_THREAD_VAR(stack_pool_t, stack_pool, { 0 })
#define stack_pool (*stack_pool_ref())
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
  fly_ctx* cx = fly_cx();
  fly_handler* inner = cx->handlers;
  fly_handler* h = inner;
  while (h && h->effect != effect && !h->dying) h = h->outer;
  // Code being dropped is cut off from every handler, its own and those around: the operation is
  // cancelled, and the code unwinds from it (§5.3).
  if (h && h->dying) {
    cx->unwinding = true;
    return;
  }
  if (!h) fly_panic("an effect is performed that nothing handles");
  // A direct handler's arm runs here, in the context of its `handle`: what it performs goes to
  // the handlers around that. The arm runs on this task, so its context is this one.
  if (h->direct) {
    cx->handlers = h->outer;
    h->direct(h->frame, op, args, result);
    cx->handlers = inner;
    return;
  }
  h->op = op;
  h->args = args;
  h->result = result;
  h->from = inner;
  h->suspended = cur_fiber;
  switch_to(h->fiber->back);
}

bool fly_handled(uint32_t effect) {
  for (fly_handler* h = fly_handlers; h; h = h->outer) {
    if (h->effect == effect) return true;
  }
  return false;
}

void fly_handle_keep(fly_handler* h) { h->kept = true; }

void fly_handle_start(fly_handler* h, void (*entry)(void*), void* arg) {
  h->outer = fly_handlers;
  h->dying = false;
  h->op = -1;
  h->fiber = fiber_new(entry, arg, h);
  h->fiber->back = cur_fiber;
  switch_to(h->fiber);
}

// The handler is deep: what else the body performs goes to the handlers around the resumption.
void fly_handle_resume(fly_handler* h) {
  h->fiber->back = cur_fiber;
  h->outer = fly_handlers;
  h->op = -1;
  switch_to(h->suspended);
}

bool fly_handle_done(const fly_handler* h) { return h->fiber->done; }

// Unwinds a suspended body: what the code dropping it is in the middle of — a failure it raises,
// an unwinding of its own — is set aside meanwhile, so the body's cleanup cannot take it for its
// own, and then goes on.
void fly_handle_unwind(fly_handler* h) {
  if (!h->fiber || h->fiber->done) return;
  fly_ctx* cx = fly_cx_now();
  fly_unwind_state saved = { cx->err, cx->unwinding, cx->stopping };
  cx->err = NULL;
  cx->unwinding = true;
  cx->stopping = false;
  // A body whose continuation could leave its arm, dropped, is cut off from every handler; so is
  // such a body suspended in this one, taken through an operation of it (§5.3).
  if (h->kept) h->dying = true;
  for (fly_handler* x = h->from; x && x != h; x = x->outer) {
    if (x->kept && x->fiber) x->dying = true;
  }
  fly_handle_resume(h);
  cx = fly_cx_now();
  cx->err = saved.err;
  cx->unwinding = saved.unwinding;
  cx->stopping = saved.stopping;
}

void fly_handle_free(fly_handler* h) {
  if (h->fiber) fiber_free(h->fiber);
  h->fiber = NULL;
}

#ifdef FLY_FREESTANDING
static void cleaning(int d) { (void)d; }
#else
static void cleaning(int d);
#endif

// Cleanup — a `defer`'s body — runs to its end: a cancellation that comes meanwhile is delivered at
// the task's first scheduling point after it (§5.6).
fly_unwind_state fly_cleanup_begin(void) {
  cleaning(1);
  fly_unwind_state s = { fly_err, fly_unwinding, fly_stopping };
  fly_err = NULL;
  fly_unwinding = false;
  fly_stopping = false;
  return s;
}

void fly_cleanup_end(fly_unwind_state s) {
  cleaning(-1);
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
  g->h.suspended = cur_fiber;
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
  // The hosts a program may connect to, `host:port`, each with what it sends back.
  world_pair* peers;
  size_t npeers;
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
      } else if (fly_str_eq(k, fly_str_lit("peers", 5))) {
        json_pairs(&world.peers, &world.npeers, false);
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

// ---- sockets ----

#if defined(FLY_THREADS)
// On worker threads a socket does not block: a task waits for it to be ready (below).
static bool io_wait(int fd, bool write);
static void io_register(int fd);
static bool threads;
#endif

static int io_error(int e) {
#ifdef __wasm__
  (void)e;
  return FLY_IO_PERMISSION_DENIED;
#else
  switch (e) {
    case EPIPE: return FLY_IO_BROKEN_PIPE;
    case ETIMEDOUT: return FLY_IO_TIMED_OUT;
    case ENOENT: return FLY_IO_NOT_FOUND;
    case EACCES: case EPERM: return FLY_IO_PERMISSION_DENIED;
    case EADDRINUSE: return FLY_IO_ADDR_IN_USE;
    case ECONNREFUSED: return FLY_IO_REFUSED;
    default: return FLY_IO_RESET;
  }
#endif
}

// Whether to wait for a descriptor that would block, rather than let it block the thread.
static bool nonblocking(void) {
#ifdef FLY_THREADS
  return threads;
#else
  return false;
#endif
}

int fly_listen(uint16_t port) {
  world_load();
  if (world.simulated) return port;
#ifdef __wasm__
  return -FLY_IO_PERMISSION_DENIED;
#else
  // A peer gone is an error a write reports, not a signal that ends the program.
  signal(SIGPIPE, SIG_IGN);
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) return -io_error(errno);
  int one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in a = { 0 };
  a.sin_family = AF_INET;
  a.sin_port = htons(port);
  a.sin_addr.s_addr = htonl(INADDR_ANY);
  if (bind(fd, (struct sockaddr*)&a, sizeof a) != 0 || listen(fd, SOMAXCONN) != 0) {
    int e = errno;
    close(fd);
    return -io_error(e);
  }
  if (nonblocking()) {
    fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK);
#ifdef FLY_THREADS
    io_register(fd);
#endif
  }
  return fd + 1;
#endif
}

uint16_t fly_listener_port(int listener) {
  if (world.simulated) return (uint16_t)listener;
#ifdef __wasm__
  return 0;
#else
  struct sockaddr_in a = { 0 };
  socklen_t n = sizeof a;
  if (getsockname(listener - 1, (struct sockaddr*)&a, &n) != 0) return 0;
  return ntohs(a.sin_port);
#endif
}

bool fly_accept(int listener, fly_socket* out) {
  world_load();
  if (world.simulated) {
    fly_str input;
    if (!fly_world_accept(&input)) return false;
    *out = (fly_socket){ .input = input };
    return true;
  }
#ifdef __wasm__
  (void)listener;
  (void)out;
  return false;
#else
  for (;;) {
    int fd = accept(listener - 1, NULL, NULL);
    if (fd >= 0) {
      int one = 1;
      setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
      if (nonblocking()) {
        fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK);
#ifdef FLY_THREADS
        io_register(fd);
#endif
      }
      *out = (fly_socket){ .fd = fd + 1 };
      return true;
    }
    if (errno == EINTR || errno == ECONNABORTED) continue;
#ifdef FLY_THREADS
    if ((errno == EAGAIN || errno == EWOULDBLOCK) && nonblocking()) {
      if (!io_wait(listener - 1, false)) return false;
      continue;
    }
#endif
    return false;
  }
#endif
}

int fly_connect(fly_str host, uint16_t port, fly_socket* out) {
  world_load();
  *out = (fly_socket){ 0 };
  if (world.simulated) {
    if (fly_fault()) return FLY_IO_TIMED_OUT;
    char key[300];
    int k = fmt_text(key, sizeof key, "%.*s:%u", (int)host.len, (const char*)host.ptr, (unsigned)port);
    for (size_t i = 0; i < world.npeers; i++) {
      if (fly_str_eq(world.peers[i].key, (fly_str){ (const uint8_t*)key, (size_t)k })) {
        out->input = world.peers[i].val;
        out->peer = world.peers[i].key;
        return FLY_IO_OK;
      }
    }
    return FLY_IO_REFUSED;
  }
#ifdef __wasm__
  return FLY_IO_PERMISSION_DENIED;
#else
  signal(SIGPIPE, SIG_IGN);
  char name[256], service[8];
  if (host.len >= sizeof name) return FLY_IO_NOT_FOUND;
  memcpy(name, host.ptr, host.len);
  name[host.len] = 0;
  fmt_text(service, sizeof service, "%u", (unsigned)port);
  struct addrinfo hints = { 0 }, *found = NULL;
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  if (getaddrinfo(name, service, &hints, &found) != 0) return FLY_IO_NOT_FOUND;
  int failure = FLY_IO_REFUSED;
  // Each address the name has, in the order the resolver gives them, until one answers.
  for (struct addrinfo* a = found; a; a = a->ai_next) {
    int fd = socket(a->ai_family, a->ai_socktype, a->ai_protocol);
    if (fd < 0) { failure = io_error(errno); continue; }
    bool waits = nonblocking();
    if (waits) {
      fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK);
#ifdef FLY_THREADS
      io_register(fd);
#endif
    }
    int r;
    do { r = connect(fd, a->ai_addr, a->ai_addrlen); } while (r != 0 && errno == EINTR);
#ifdef FLY_THREADS
    if (r != 0 && errno == EINPROGRESS && waits) {
      // Connected, or refused, once the descriptor may be written. A task cancelled meanwhile
      // unwinds, with a socket of nothing.
      if (!io_wait(fd, true)) { close(fd); freeaddrinfo(found); return FLY_IO_OK; }
      int e = 0;
      socklen_t n = sizeof e;
      getsockopt(fd, SOL_SOCKET, SO_ERROR, &e, &n);
      r = e ? -1 : 0;
      errno = e;
    }
#endif
    if (r == 0) {
      int one = 1;
      setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
      freeaddrinfo(found);
      out->fd = fd + 1;
      return FLY_IO_OK;
    }
    failure = io_error(errno);
    close(fd);
  }
  freeaddrinfo(found);
  return failure;
#endif
}

int fly_sock_read(fly_socket* s, fly_slice buf, uint64_t* n) {
  *n = 0;
  if (!s->fd) {
    if (fly_fault()) return FLY_IO_TIMED_OUT;
    size_t k = s->input.len - s->pos;
    if (buf.len < k) k = buf.len;
    memcpy(buf.ptr, s->input.ptr + s->pos, k);
    s->pos += k;
    *n = k;
    return FLY_IO_OK;
  }
#ifdef __wasm__
  return FLY_IO_PERMISSION_DENIED;
#else
  for (;;) {
    ssize_t k = read(s->fd - 1, buf.ptr, buf.len);
    if (k >= 0) { *n = (uint64_t)k; return FLY_IO_OK; }
    if (errno == EINTR) continue;
#ifdef FLY_THREADS
    if ((errno == EAGAIN || errno == EWOULDBLOCK) && nonblocking()) {
      if (!io_wait(s->fd - 1, false)) return FLY_IO_OK;
      continue;
    }
#endif
    return io_error(errno);
  }
#endif
}

int fly_sock_write(fly_socket* s, fly_slice bytes) {
  if (!s->fd) {
    if (fly_fault()) return FLY_IO_BROKEN_PIPE;
    if (!s->out.ptr) s->out = fly_String_new();
    fly_String_push(&s->out, (fly_str){ bytes.ptr, bytes.len });
    return FLY_IO_OK;
  }
#ifdef __wasm__
  return FLY_IO_PERMISSION_DENIED;
#else
  size_t done = 0;
  while (done < bytes.len) {
    ssize_t k = write(s->fd - 1, (const uint8_t*)bytes.ptr + done, bytes.len - done);
    if (k >= 0) { done += (size_t)k; continue; }
    if (errno == EINTR) continue;
#ifdef FLY_THREADS
    if ((errno == EAGAIN || errno == EWOULDBLOCK) && nonblocking()) {
      if (!io_wait(s->fd - 1, true)) return FLY_IO_OK;
      continue;
    }
#endif
    return io_error(errno);
  }
  return FLY_IO_OK;
#endif
}

// What the simulated world shows of what a program sends: `-> status body`, `-> peer: text`, or
// `-> text`, on standard output with the program's own lines.
static void sim_line(fly_str peer, long code, fly_str text) {
  fly_String line = fly_String_from(fly_str_lit("-> ", 3));
  if (code >= 0) {
    fly_String n = fly_show_u128((unsigned __int128)code);
    fly_String_push(&line, fly_String_as_str(&n));
    fly_String_drop(&n);
    fly_String_push(&line, fly_str_lit(" ", 1));
  } else if (peer.len) {
    fly_String_push(&line, peer);
    fly_String_push(&line, fly_str_lit(": ", 2));
  }
  fly_String_push(&line, text);
  fly_String_push(&line, fly_str_lit("\n", 1));
  fly_out(fly_String_as_str(&line));
  fly_String_drop(&line);
}

int fly_sock_status(fly_socket* s, unsigned code, fly_str body) {
  if (!s->fd) {
    if (fly_fault()) return FLY_IO_BROKEN_PIPE;
    sim_line(fly_str_lit("", 0), code, body);
    return FLY_IO_OK;
  }
  char head[96];
  int n = fmt_text(head, sizeof head, "HTTP/1.1 %u %s\r\nContent-Length: %zu\r\nConnection: close\r\n\r\n", code, code < 400 ? "OK" : "Error", body.len);
  int e = fly_sock_write(s, (fly_slice){ head, (size_t)n });
  return e ? e : fly_sock_write(s, (fly_slice){ (void*)body.ptr, body.len });
}

// Closing a simulated connection shows what was written to it, `\r\n` as a line break.
void fly_sock_close(fly_socket* s) {
  if (!s->fd) {
    if (s->out.len > 0) {
      fly_String text = fly_String_new();
      for (size_t i = 0; i < s->out.len; i++) {
        if (s->out.ptr[i] == '\r' && i + 1 < s->out.len && s->out.ptr[i + 1] == '\n') continue;
        fly_String_push(&text, (fly_str){ s->out.ptr + i, 1 });
      }
      size_t n = text.len;
      while (n > 0 && text.ptr[n - 1] == '\n') n--;
      sim_line(s->peer, -1, (fly_str){ text.ptr, n });
      fly_String_drop(&text);
    }
    fly_String_drop(&s->out);
    return;
  }
#ifndef __wasm__
  close(s->fd - 1);
#endif
  s->fd = 0;
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
static void mt_cleaning(int d);
static void mt_sleep(uint64_t nanos);
static int mt_spawn(int scope, void (*entry)(void* task, void* closure), void* closure, size_t size);
static void mt_join(int task, void* out);
static int mt_scope_open(void);
static void mt_scope_close(int scope);
static fly_chan mt_channel(void (*drop)(void*));
static void mt_receiver_gone(fly_chan ch);
static bool mt_send(fly_chan ch, const void* v, size_t size);
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
  bool started, finished, cancelled, deliver_cancel, deliver_deadlock;
  // How deep it is in cleanup, which a cancellation waits for.
  int cleaning;
  int wait_kind, wait_id;
  uint64_t until;
} task_t;

// A channel: what was sent and not yet received, its senders, whether its receiver is gone, and
// what drops a message, which it does to those no one will receive.
typedef struct { uint8_t* items; size_t len, head, size; long senders; bool closed, deaf; void (*drop)(void*); } chan_t;
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
  if (!sched.tasks[t]->cleaning && remove_blocked(t)) push_ready(t);
}

void fly_panic_deadlock(void) { fly_panic("deadlock: every task is waiting"); }

// Suspends the running task back to the scheduler, waiting for `kind`/`id` or not at all; when it
// is resumed, a cancellation or a deadlock is delivered to it.
static void suspend_task(int kind, int id) {
  task_t* t = sched.tasks[sched.current];
  t->wait_kind = kind;
  t->wait_id = id;
  t->suspended = cur_fiber;
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

static void cleaning(int d) {
#ifdef FLY_THREADS
  if (threads) { mt_cleaning(d); return; }
#endif
  if (fly_tasks_on) sched.tasks[sched.current]->cleaning += d;
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
  // The first failure cancels the scope: its body and its other tasks (§6.1).
  if (t->error && !st->failure) {
    cancel(st->owner);
    for (size_t i = 0; i < st->ntasks; i++) if (st->tasks[i] != me) cancel(st->tasks[i]);
  }
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
    if (!t->deliver_deadlock && t->cancelled && !t->cleaning) t->deliver_cancel = true;
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
  // The body unwound because a task failed: the scope raises that instead.
  bool unwound = fly_unwinding && !st->failure;
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

fly_chan fly_channel(void (*drop)(void*)) {
#ifdef FLY_THREADS
  if (threads) return mt_channel(drop);
#endif
  int id = sched.next++;
  grow_ids(id);
  chan_t* c = fly_alloc(sizeof(chan_t));
  c->senders = 1;
  c->drop = drop;
  sched.chans[id] = c;
  return (fly_chan){ id };
}

// A channel both of whose ends are gone is freed.
static void chan_maybe_free(int id) {
  chan_t* c = sched.chans[id];
  if (c->senders > 0 || !c->deaf) return;
  free(c->items);
  free(c);
  sched.chans[id] = NULL;
}

// Whether the message went to the channel: once its receiver is gone, it is dropped instead.
bool fly_send(fly_chan ch, const void* v, size_t size) {
#ifdef FLY_THREADS
  if (threads) return mt_send(ch, v, size);
#endif
  chan_t* c = sched.chans[ch.ch];
  bool ok = !c->deaf;
  if (ok) {
    c->size = size;
    c->items = realloc(c->items, (c->len + 1) * (size ? size : 1));
    memcpy(c->items + c->len * size, v, size);
    c->len++;
    wake(WAIT_CHANNEL, ch.ch);
  } else if (c->drop) {
    c->drop((void*)v);
  }
  fly_point();
  return ok;
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
  chan_maybe_free(id);
}

// The receiving end dropped: what is sent from now on is dropped, and the channel freed once its
// senders are gone too.
void fly_receiver_drop(fly_chan* ch) {
#ifdef FLY_THREADS
  if (threads) { if (ch->ch) mt_receiver_gone(*ch); ch->ch = 0; return; }
#endif
  if (!ch->ch) return;
  chan_t* c = sched.chans[ch->ch];
  c->deaf = true;
  // What is in it is dropped now: a message may hold a reply someone waits for. It is taken out
  // first, as dropping one may reach this channel.
  uint8_t* items = c->items;
  size_t head = c->head, len = c->len, size = c->size;
  c->items = NULL;
  c->head = c->len = 0;
  if (c->drop) for (size_t i = head; i < len; i++) c->drop(items + i * size);
  free(items);
  chan_maybe_free(ch->ch);
  ch->ch = 0;
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
// nothing to do. A task waits by parking: it puts itself in the queue of what it waits for, under
// that queue's lock, and its worker runs others; whatever ends the wait moves it to the inbox of
// the worker that ended it, or of the last it ran on, and an idle worker takes from any inbox. So a
// task goes on wherever a core is free: what compiled code reads of it is its own context, and
// every variable of a thread's is reached afresh after a switch (`FLY_THREAD_VAR`).

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
  // How it ended: its failure, if it failed.
  fly_failure* error;
  // Who still refers to it: itself while it lives, its scope while it does, and a forked task's
  // `Fiber` until it is joined.
  int refs;
  bool started, cancelled, yielded;
  // How deep it is in cleanup, which a cancellation waits for.
  int cleaning;
  // Its joiners, and whether it has finished, under their queue's lock.
  waitq joiners;
  bool finished;
  // The queue it waits in, if it waits, and its neighbours there.
  waitq* waiting;
  mt_task *wnext, *wprev;
  // Its neighbours among its scope's tasks still alive.
  mt_task *snext, *sprev;
  // The next task in an inbox.
  mt_task* rnext;
  // The lock its worker gives back once it has switched away to wait.
  spin_t* release;
  // What compiled code reads and sets of it, wherever it runs.
  fly_ctx ctx;
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
  // The task whose failure the scope raises, unless a join raises it first.
  mt_task* failer;
};

// A channel: what was sent and not yet received, in a ring, and the receivers waiting, under its
// queue's lock.
typedef struct { waitq q; uint8_t* items; size_t head, len, cap, size; long senders; bool closed, deaf; void (*drop)(void*); } mt_chan;

struct worker {
  int index;
  fly_fiber own;
  fly_fiber* base;
  // The context of whatever runs here outside a task: `par` work stolen while idle.
  fly_ctx own_ctx;
  fly_ctx* idle_ctx;
  // Tasks to resume here, from any thread.
  spin_t inlock;
  mt_task *inhead, *intail;
  // Tasks started here that have not begun, and `par` work: either is any worker's to take.
  deque_t fresh, jobs;
  uint64_t rng;
  // Tasks the kernel's events woke while this worker took them: the first is its own to run.
  int harvested;
  bool harvesting;
};

static worker* workers;
static int nworkers;
FLY_THREAD_VAR(worker*, this_worker, NULL)
#define this_worker (*this_worker_ref())
FLY_THREAD_VAR(mt_task*, running, NULL)
#define running (*running_ref())
static mt_task* main_task;
static bool main_done;
// Tasks queued or running, and tasks begun and not ended: when none can run, and none sleeps, those
// alive wait for each other forever.
static long runnable, alive;

// Idle workers sleep here until there is work.
static pthread_mutex_t idle_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t idle_cv = PTHREAD_COND_INITIALIZER;
static int idlers;

// Whether an idle worker waits for the kernel's events about sockets, which `poll_wake`
// interrupts. One at a time: the kernel wakes every thread waiting on a queue for each event.
static int pollers;
// Workers looking for work before they sleep: a few at a time, as each looks at every worker's
// queues, and a crowd looking would slow the workers whose queues they are. While one looks,
// work queued wakes no one: it finds it.
static int spinners;
static void poll_wake(void);

// There is work: one idle worker wakes to take it, from wherever it is, for each piece of work
// there is one call. Waking them all for each would have every idle worker contend for one task.
// One asleep wakes before the one waiting for events, which events need.
static void notify(void) {
  __atomic_thread_fence(__ATOMIC_SEQ_CST);
  // A worker looking for work finds it: none needs waking.
  if (__atomic_load_n(&spinners, __ATOMIC_SEQ_CST) > 0) return;
  if (__atomic_load_n(&idlers, __ATOMIC_SEQ_CST) > 0) {
    pthread_mutex_lock(&idle_mu);
    if (idlers > 0) {
      pthread_cond_signal(&idle_cv);
      pthread_mutex_unlock(&idle_mu);
      return;
    }
    pthread_mutex_unlock(&idle_mu);
  }
  if (__atomic_load_n(&pollers, __ATOMIC_SEQ_CST) > 0) poll_wake();
}

// Every idle worker wakes: the program's thread among them, which the end of `main` is for.
static void notify_all(void) {
  __atomic_thread_fence(__ATOMIC_SEQ_CST);
  for (long k = __atomic_load_n(&pollers, __ATOMIC_SEQ_CST); k > 0; k--) poll_wake();
  if (__atomic_load_n(&idlers, __ATOMIC_SEQ_CST) == 0) return;
  pthread_mutex_lock(&idle_mu);
  pthread_cond_broadcast(&idle_cv);
  pthread_mutex_unlock(&idle_mu);
}

static void task_unref(mt_task* t) {
  if (__atomic_sub_fetch(&t->refs, 1, __ATOMIC_ACQ_REL) > 0) return;
  free(t->result);
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

// A task that waited may run again: on the worker that woke it, if one did, which the data it
// waited for is warm on; otherwise on the last it ran on. Any idle worker may take it from there.
static void unpark(mt_task* t) {
  __atomic_fetch_add(&runnable, 1, __ATOMIC_SEQ_CST);
  worker* w = this_worker;
  inbox_push(w ? w : t->home, t);
  // A worker that took the kernel's events runs the first task they woke itself: another is woken
  // only for those after it.
  if (w && w->harvesting && w->harvested++ == 0) return;
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

// The running task gives its worker up, until it is resumed. A task that waits holds the lock of
// what it waits for until then: its worker gives the lock back once the task has switched away,
// for until then nothing may wake it, which would let another worker resume it half switched.
static void to_worker(mt_task* t, spin_t* release) {
  t->release = release;
  t->suspended = cur_fiber;
  switch_to(this_worker->base);
}

// The running task waits in `q`, whose lock is held, until something wakes it; a cancellation
// wakes it too, unless it waits for its scope's tasks, which it must. The lock is released.
static void wait_in(waitq* q, bool cancellable) {
  mt_task* t = running;
  q_append(q, t);
  __atomic_store_n(&t->waiting, q, __ATOMIC_SEQ_CST);
  if (cancellable && __atomic_load_n(&t->cancelled, __ATOMIC_SEQ_CST) && !__atomic_load_n(&t->cleaning, __ATOMIC_SEQ_CST)) {
    q_remove(q, t);
    __atomic_store_n(&t->waiting, NULL, __ATOMIC_SEQ_CST);
    spin_unlock(&q->lock);
    return;
  }
  t->yielded = false;
  __atomic_fetch_sub(&runnable, 1, __ATOMIC_SEQ_CST);
  to_worker(t, &q->lock);
}

// Whether the running task has been cancelled: it unwinds from here (§6.1).
static bool cancelled_here(void) {
  mt_task* t = running;
  if (t && __atomic_load_n(&t->cancelled, __ATOMIC_ACQUIRE) && !__atomic_load_n(&t->cleaning, __ATOMIC_SEQ_CST)) {
    fly_unwinding = true;
    return true;
  }
  return false;
}

// Cancels a task: one running or queued sees it at its next scheduling point; one waiting is woken.
static void cancel_task(mt_task* t) {
  __atomic_store_n(&t->cancelled, true, __ATOMIC_SEQ_CST);
  // One in cleanup is left to finish it; it sees the cancellation at its next scheduling point.
  if (__atomic_load_n(&t->cleaning, __ATOMIC_SEQ_CST)) return;
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

static void mt_cleaning(int d) {
  mt_task* t = running;
  if (t) __atomic_fetch_add(&t->cleaning, d, __ATOMIC_SEQ_CST);
}

// A scheduling point: a cancellation is delivered, and the worker's other tasks get a turn.
static void mt_point(void) {
  mt_task* t = running;
  if (!t || cancelled_here()) return;
  if (__atomic_load_n(&this_worker->inhead, __ATOMIC_RELAXED)) {
    t->yielded = true;
    to_worker(t, NULL);
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
    __atomic_store_n(&main_done, true, __ATOMIC_SEQ_CST);
    __atomic_fetch_sub(&alive, 1, __ATOMIC_SEQ_CST);
    __atomic_fetch_sub(&runnable, 1, __ATOMIC_SEQ_CST);
    // It may have ended on another worker than the program's thread, which may be asleep.
    notify_all();
    return;
  }
  mt_scope* sc = t->scope;
  mt_task** cancels = NULL;
  size_t ncancels = 0;
  spin_lock(&sc->q.lock);
  if (t->error && !sc->failer) {
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

// Runs `t` here until it waits, yields or ends; it may have run elsewhere before, and may run
// elsewhere after: what it reads of itself is its own context, which this thread now points to.
static void run_task(worker* w, mt_task* t) {
  running = t;
  t->home = w;
  if (!t->started) {
    t->started = true;
    // A task cancelled before it began never runs.
    if (__atomic_load_n(&t->cancelled, __ATOMIC_ACQUIRE)) {
      running = NULL;
      mt_end(t);
      return;
    }
    t->fiber = fiber_new(mt_task_main, t, NULL);
    t->suspended = t->fiber;
  }
  fly_cur = &t->ctx;
  t->fiber->back = w->base;
  switch_to(t->suspended);
  fly_cur = w->idle_ctx;
  running = NULL;
  // Once the lock of what it waits for is given back, the task may be woken and run elsewhere: what
  // is needed of it is read first.
  bool done = t->fiber->done, yielded = t->yielded;
  spin_t* release = t->release;
  t->release = NULL;
  if (release) spin_unlock(release);
  if (done) {
    mt_end(t);
  } else if (yielded) {
    inbox_push(w, t);
  }
}

// ---- waiting for sockets ----

// Each descriptor, by its number, has a record of who waits to read it and who to write it, made
// when it is first used and never freed: an event about a descriptor closed meanwhile only wakes
// whoever uses its number next, who tries again and waits again. Idle workers wait for the
// kernel's events themselves, edge-triggered, and wake the waiters, the woken tasks queued on the
// worker that saw the event; an edge that came while no one waited is remembered, for the next to
// try again at once. A thread between the kernel and the workers would make every event a handoff
// between threads, which caps a server at what one thread can hand off.
#if defined(__APPLE__) || defined(__FreeBSD__)
#include <sys/event.h>
#define FLY_KQUEUE 1
#elif defined(__linux__)
#include <sys/epoll.h>
#include <sys/eventfd.h>
#define FLY_EPOLL 1
#endif

typedef struct { waitq q[2]; bool ready[2]; } io_obj;

static io_obj** io_chunks[OBJ_CHUNKS];
static int poll_fd = -1;
#if defined(FLY_EPOLL)
// What wakes a worker waiting in `epoll_wait`: written to, it is readable.
static int poll_wake_fd = -1;
#endif
// Set once sockets are in use: from then on idle workers wait for the kernel's events.
static bool polling;
static pthread_once_t poll_once = PTHREAD_ONCE_INIT;
// Tasks waiting for a descriptor: while any do, none waiting is a deadlock, as an event may come.
static long io_waiting;

static io_obj* io_of(int fd) {
  io_obj*** slot = &io_chunks[fd >> OBJ_BITS];
  io_obj** chunk = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
  if (!chunk) {
    io_obj** made = fly_alloc(OBJ_CHUNK * sizeof(io_obj*));
    io_obj** seen = NULL;
    if (__atomic_compare_exchange_n(slot, &seen, made, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) chunk = made;
    else { free(made); chunk = seen; }
  }
  io_obj** at = &chunk[fd & (OBJ_CHUNK - 1)];
  io_obj* o = __atomic_load_n(at, __ATOMIC_ACQUIRE);
  if (!o) {
    io_obj* made = fly_alloc(sizeof(io_obj));
    io_obj* seen = NULL;
    if (__atomic_compare_exchange_n(at, &seen, made, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) o = made;
    else { free(made); o = seen; }
  }
  return o;
}

// The kernel says `fd` may be read, or written: its waiters try again.
static void io_ready(int fd, int dir) {
  io_obj* o = io_of(fd);
  spin_lock(&o->q[dir].lock);
  o->ready[dir] = true;
  wake_all(&o->q[dir]);
  spin_unlock(&o->q[dir].lock);
}

static void io_harvest(int64_t wait_ns);

// Takes the events the kernel has, waiting for one up to `wait_ns` (forever if negative), and
// wakes the tasks waiting for them, queued on this worker.
static void io_poll(int64_t wait_ns) {
  worker* w = this_worker;
  w->harvesting = true;
  w->harvested = 0;
  io_harvest(wait_ns);
  w->harvesting = false;
}

static void io_harvest(int64_t wait_ns) {
  struct timespec ts = { (time_t)(wait_ns / 1000000000), (long)(wait_ns % 1000000000) };
#if defined(FLY_KQUEUE)
  struct kevent evs[64];
  int n = kevent(poll_fd, NULL, 0, evs, 64, wait_ns < 0 ? NULL : &ts);
  for (int i = 0; i < n; i++) {
    if (evs[i].filter == EVFILT_USER) continue;
    io_ready((int)evs[i].ident, evs[i].filter == EVFILT_WRITE ? 1 : 0);
  }
#elif defined(FLY_EPOLL)
  struct epoll_event evs[64];
  int n = epoll_wait(poll_fd, evs, 64, wait_ns < 0 ? -1 : (int)((wait_ns + 999999) / 1000000));
  for (int i = 0; i < n; i++) {
    uint32_t e = evs[i].events;
    if (evs[i].data.fd == poll_wake_fd) {
      uint64_t count;
      while (read(poll_wake_fd, &count, sizeof count) > 0) {}
      continue;
    }
    if (e & (EPOLLIN | EPOLLRDHUP | EPOLLHUP | EPOLLERR)) io_ready(evs[i].data.fd, 0);
    if (e & (EPOLLOUT | EPOLLHUP | EPOLLERR)) io_ready(evs[i].data.fd, 1);
  }
#else
  (void)ts;
#endif
}

// Takes the events the kernel has, without waiting, unless another worker is taking them.
static void io_take(void) {
  int none = 0;
  if (__atomic_load_n(&pollers, __ATOMIC_RELAXED) != 0) return;
  if (!__atomic_compare_exchange_n(&pollers, &none, 1, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)) return;
  io_poll(0);
  __atomic_store_n(&pollers, 0, __ATOMIC_SEQ_CST);
}

// Wakes a worker waiting for the kernel's events: one, as the event is taken by one wait.
static void poll_wake(void) {
#if defined(FLY_KQUEUE)
  struct kevent ev;
  EV_SET(&ev, 0, EVFILT_USER, 0, NOTE_TRIGGER, 0, NULL);
  kevent(poll_fd, &ev, 1, NULL, 0, NULL);
#elif defined(FLY_EPOLL)
  uint64_t one = 1;
  if (write(poll_wake_fd, &one, sizeof one) < 0) {}
#endif
}

static void poll_start(void) {
#if defined(FLY_KQUEUE)
  poll_fd = kqueue();
  struct kevent ev;
  EV_SET(&ev, 0, EVFILT_USER, EV_ADD | EV_CLEAR, 0, 0, NULL);
  if (poll_fd < 0 || kevent(poll_fd, &ev, 1, NULL, 0, NULL) < 0) fly_panic("cannot wait for sockets");
#elif defined(FLY_EPOLL)
  poll_fd = epoll_create1(0);
  poll_wake_fd = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
  struct epoll_event ev = { .events = EPOLLIN | EPOLLET, .data.fd = poll_wake_fd };
  if (poll_fd < 0 || poll_wake_fd < 0 || epoll_ctl(poll_fd, EPOLL_CTL_ADD, poll_wake_fd, &ev) < 0) fly_panic("cannot wait for sockets");
#else
  fly_panic("cannot wait for sockets");
#endif
  __atomic_store_n(&polling, true, __ATOMIC_SEQ_CST);
  // Workers asleep until now wait for the kernel's events from here on.
  notify_all();
}

// A descriptor made: its events, from now until it is closed, go to the workers.
static void io_register(int fd) {
  pthread_once(&poll_once, poll_start);
  io_obj* o = io_of(fd);
  for (int d = 0; d < 2; d++) {
    spin_lock(&o->q[d].lock);
    o->ready[d] = false;
    spin_unlock(&o->q[d].lock);
  }
#if defined(FLY_KQUEUE)
  struct kevent ev[2];
  EV_SET(&ev[0], fd, EVFILT_READ, EV_ADD | EV_CLEAR, 0, 0, NULL);
  EV_SET(&ev[1], fd, EVFILT_WRITE, EV_ADD | EV_CLEAR, 0, 0, NULL);
  kevent(poll_fd, ev, 2, NULL, 0, NULL);
#elif defined(FLY_EPOLL)
  struct epoll_event ev = { .events = EPOLLIN | EPOLLOUT | EPOLLRDHUP | EPOLLET, .data.fd = fd };
  epoll_ctl(poll_fd, EPOLL_CTL_ADD, fd, &ev);
#endif
}

// The running task waits until `fd` may be read, or written: false if it was cancelled.
static bool io_wait(int fd, bool write) {
  io_obj* o = io_of(fd);
  int d = write ? 1 : 0;
  spin_lock(&o->q[d].lock);
  if (o->ready[d]) {
    o->ready[d] = false;
    spin_unlock(&o->q[d].lock);
    return !cancelled_here();
  }
  __atomic_fetch_add(&io_waiting, 1, __ATOMIC_SEQ_CST);
  wait_in(&o->q[d], true);
  __atomic_fetch_sub(&io_waiting, 1, __ATOMIC_SEQ_CST);
  return !cancelled_here();
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

// Another worker's: a task not yet begun, then one woken there that waits for its worker.
static mt_task* steal_task(worker* w) {
  int start = (int)(worker_rand(w) % (uint64_t)nworkers);
  for (int k = 0; k < nworkers; k++) {
    worker* v = &workers[(start + k) % nworkers];
    if (v == w) continue;
    mt_task* t = dq_steal(&v->fresh);
    if (t) return t;
  }
  for (int k = 0; k < nworkers; k++) {
    worker* v = &workers[(start + k) % nworkers];
    if (v == w) continue;
    mt_task* t = inbox_pop(v);
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
  (void)w;
  for (int k = 0; k < nworkers; k++) {
    if (__atomic_load_n(&workers[k].inhead, __ATOMIC_SEQ_CST)) return true;
    if (dq_size(&workers[k].fresh) > 0 || dq_size(&workers[k].jobs) > 0) return true;
  }
  uint64_t due = __atomic_load_n(&next_due, __ATOMIC_ACQUIRE);
  return due && due <= now_ns();
}

static _Noreturn void mt_deadlock(void) { panic_exit("deadlock: every task is waiting"); }

static void idle(worker* w) {
  bool io = __atomic_load_n(&polling, __ATOMIC_ACQUIRE);
  // Under load the next piece of work is microseconds away: looking for it a while costs less than
  // sleeping and being woken, which takes the kernel tens of microseconds each way.
  uint64_t until = now_ns() + 50000;
  bool spin = __atomic_add_fetch(&spinners, 1, __ATOMIC_SEQ_CST) <= 4;
  if (!spin) __atomic_sub_fetch(&spinners, 1, __ATOMIC_SEQ_CST);
  for (unsigned n = 1; spin; n++) {
    if (n % 64 == 0) {
      // Events no one waits for are this worker's to take, between looks.
      if (io) io_take();
      if (work_anywhere(w)) { __atomic_sub_fetch(&spinners, 1, __ATOMIC_SEQ_CST); return; }
      if (now_ns() > until) break;
    }
    relax();
  }
  if (spin) __atomic_sub_fetch(&spinners, 1, __ATOMIC_SEQ_CST);
  int none = 0;
  if (io && __atomic_compare_exchange_n(&pollers, &none, 1, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)) {
    // Asleep in the kernel's wait for events, which work from elsewhere interrupts: counted first,
    // so that work queued after the look below wakes it.
    if (!work_anywhere(w) && !(w == &workers[0] && __atomic_load_n(&main_done, __ATOMIC_SEQ_CST))) {
      uint64_t due = __atomic_load_n(&next_due, __ATOMIC_ACQUIRE);
      if (!due && __atomic_load_n(&runnable, __ATOMIC_SEQ_CST) == 0 && __atomic_load_n(&alive, __ATOMIC_SEQ_CST) > 0 && __atomic_load_n(&io_waiting, __ATOMIC_SEQ_CST) == 0) mt_deadlock();
      uint64_t now = now_ns();
      io_poll(due ? (int64_t)(due > now ? due - now : 0) : -1);
    }
    __atomic_store_n(&pollers, 0, __ATOMIC_SEQ_CST);
    return;
  }
  pthread_mutex_lock(&idle_mu);
  __atomic_fetch_add(&idlers, 1, __ATOMIC_SEQ_CST);
  if (!work_anywhere(w) && !(w == &workers[0] && __atomic_load_n(&main_done, __ATOMIC_SEQ_CST))) {
    uint64_t due = __atomic_load_n(&next_due, __ATOMIC_ACQUIRE);
    if (!due && __atomic_load_n(&runnable, __ATOMIC_SEQ_CST) == 0 && __atomic_load_n(&alive, __ATOMIC_SEQ_CST) > 0 && __atomic_load_n(&io_waiting, __ATOMIC_SEQ_CST) == 0) mt_deadlock();
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
  for (unsigned turn = 1;; turn++) {
    if (w == &workers[0] && __atomic_load_n(&main_done, __ATOMIC_SEQ_CST)) return;
    fire_alarms();
    // A worker that always has work still takes the kernel's events now and then, for the tasks
    // waiting for sockets while every worker is busy.
    if (turn % 32 == 0 && __atomic_load_n(&polling, __ATOMIC_ACQUIRE)) io_take();
    // Tasks woken here and tasks begun here take turns: either kind always first would leave the
    // other waiting for as long as the first kind keeps coming, as a busy server's connections do.
    mt_task* t;
    if (turn % 2) { t = inbox_pop(w); if (!t) t = dq_pop(&w->fresh); }
    else { t = dq_pop(&w->fresh); if (!t) t = inbox_pop(w); }
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
  fly_cur = w->idle_ctx;
  cur_fiber = w->base;
  work(w);
  return NULL;
}

static void mt_run(void (*main)(void), void (*entry)(void* task, void* closure)) {
  threads = true;
  // A program whose tasks run on threads may run for long, a server: what it prints goes out a
  // line at a time.
  setvbuf(stdout, NULL, _IOLBF, 0);
  const char* n = getenv("FLY_THREADS");
  long cores = n && *n ? strtol(n, NULL, 10) : sysconf(_SC_NPROCESSORS_ONLN);
  nworkers = cores > 0 ? (int)cores : 1;
  workers = fly_alloc((size_t)nworkers * sizeof(worker));
  for (int k = 0; k < nworkers; k++) {
    worker* w = &workers[k];
    w->index = k;
    w->own.base = true;
    w->base = k == 0 ? &main_fiber : &w->own;
    // The first worker is the program's thread, whose context is the program's outside its tasks.
    w->idle_ctx = k == 0 ? &fly_ctx0 : &w->own_ctx;
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
  // The body unwound because a task failed: the scope raises that instead.
  bool unwound = fly_unwinding && !sc->failer;
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
  mt_task* failer = sc->failer;
  obj_clear(id);
  free(sc);
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

static fly_chan mt_channel(void (*drop)(void*)) {
  mt_chan* c = fly_alloc(sizeof(mt_chan));
  c->senders = 1;
  c->drop = drop;
  return (fly_chan){ obj_new(c) };
}

// Frees a channel both of whose ends are gone, which nothing else can reach.
static void mt_chan_free(int id, mt_chan* c) {
  free(c->items);
  obj_clear(id);
  free(c);
}

// The receiving end is gone: what is in the channel is taken out and dropped, outside its lock, as
// dropping a message may reach the channel again. Whichever end goes last frees the channel,
// decided under the lock: with senders left, the last of them will.
static void mt_receiver_gone(fly_chan ch) {
  mt_chan* c = obj_get(ch.ch);
  spin_lock(&c->q.lock);
  c->deaf = true;
  uint8_t* items = c->items;
  size_t head = c->head, len = c->len, cap = c->cap, size = c->size;
  c->items = NULL;
  c->head = c->len = c->cap = 0;
  void (*drop)(void*) = c->drop;
  bool gone = c->senders == 0;
  spin_unlock(&c->q.lock);
  if (gone) mt_chan_free(ch.ch, c);
  if (drop) for (size_t i = 0; i < len; i++) drop(items + ((head + i) % cap) * size);
  free(items);
}

static bool mt_send(fly_chan ch, const void* v, size_t size) {
  mt_chan* c = obj_get(ch.ch);
  spin_lock(&c->q.lock);
  if (c->deaf) {
    spin_unlock(&c->q.lock);
    if (c->drop) c->drop((void*)v);
    mt_point();
    return false;
  }
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
  return true;
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
  bool gone = c->senders == 0 && c->deaf;
  spin_unlock(&c->q.lock);
  if (gone) mt_chan_free(ch.ch, c);
}

static void mt_sender_clone(fly_chan ch) {
  mt_chan* c = obj_get(ch.ch);
  spin_lock(&c->q.lock);
  c->senders++;
  spin_unlock(&c->q.lock);
}

// A `Mutex`'s lock, in the header before its state. Its body performs nothing, so it is held
// briefly and never across a scheduling point: a task that finds it held spins a little, then
// waits in its queue, giving its core to others, and is woken in turn.
typedef struct { waitq q; bool held; } mt_mutex;
_Static_assert(sizeof(mt_mutex) <= MUTEX_HEADER, "a mutex's header holds its lock");

static mt_mutex* mutex_of(const void* state) { return (mt_mutex*)((uint8_t*)state - MUTEX_HEADER); }

static bool mutex_try(mt_mutex* m) {
  spin_lock(&m->q.lock);
  bool free_ = !__atomic_load_n(&m->held, __ATOMIC_RELAXED);
  if (free_) __atomic_store_n(&m->held, true, __ATOMIC_RELAXED);
  spin_unlock(&m->q.lock);
  return free_;
}

void fly_lock(const void* state) {
  if (!threads) return;
  mt_mutex* m = mutex_of(state);
  for (int i = 0; i < 64; i++) {
    if (!__atomic_load_n(&m->held, __ATOMIC_RELAXED) && mutex_try(m)) return;
    relax();
  }
  spin_lock(&m->q.lock);
  while (__atomic_load_n(&m->held, __ATOMIC_RELAXED)) {
    wait_in(&m->q, false);
    spin_lock(&m->q.lock);
  }
  __atomic_store_n(&m->held, true, __ATOMIC_RELAXED);
  spin_unlock(&m->q.lock);
}

void fly_unlock(const void* state) {
  if (!threads || !state) return;
  mt_mutex* m = mutex_of(state);
  spin_lock(&m->q.lock);
  __atomic_store_n(&m->held, false, __ATOMIC_RELAXED);
  wake_one(&m->q);
  spin_unlock(&m->q.lock);
}

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
  double v;
  if (!fly_parse_float(s, &v)) fly_panicf("argument %d is not a number", i + 1);
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
