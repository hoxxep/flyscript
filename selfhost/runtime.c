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
#include <pthread.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <unistd.h>
#else
#include <fcntl.h>
#include <sys/uio.h>
#include <unistd.h>
#endif
#endif

// A variable of the thread's. A call of a function runs on one thread to its end, a task that stops
// returning from every function it is in and calling them again as it goes on (§11.3), so the
// variable's address may be computed once in a function and kept.
#ifdef FLY_THREADS
#define FLY_THREAD_VAR(T, name, init) \
  static FLY_LOCAL T name##_tls = init; \
  static inline T* name##_ref(void) { return &name##_tls; }
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
fly_ctx* fly_cx(void) { return fly_cur; }
// The context as the thread's pointer has it now, for the scheduler, which changes that pointer
// between tasks: unlike `fly_cx`, never one computed before.
#define fly_cx_now() (fly_cur)
#else
fly_ctx fly_ctx0;
fly_ctx* (fly_cx)(void) { return &fly_ctx0; }
#define fly_cx_now() (&fly_ctx0)
#endif
// As LLVM IR reaches its fields (llvm.fly's `cxField`).
_Static_assert(offsetof(fly_ctx, unwinding) == sizeof(void*) && offsetof(fly_ctx, pend) == sizeof(void*) + 1 && offsetof(fly_ctx, handlers) == 2 * sizeof(void*), "fly_ctx as LLVM IR reaches it");

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
// Whether the program is ending, every task stopping where it is (§5.7).
static bool ending;

// What a panic's message is when there is no memory to copy it into.
static char out_of_memory[] = "out of memory";

// Running out of memory ends the program (§5.7): unwinding would itself need memory, and nearly
// every function allocates, which would make nearly every one a function a panic may leave.
_Noreturn void fly_out_of_memory(void) { panic_exit("out of memory"); }

// A program's C made by the C back end (FLY_C_UNWIND) unwinds by the tables too: it is compiled
// with -fexceptions, each function's cleanup a frame record's (c.fly's `withLanding`).
#if defined(FLY_LANDING_PADS) && defined(FLY_C_UNWIND)
#undef FLY_C_UNWIND
#endif
#if defined(FLY_LANDING_PADS) && defined(__wasm__) && !defined(FLY_FREESTANDING)
// WebAssembly's exceptions are its own: a landing pad is a funclet that runs whatever is thrown
// through it, and `fly_try` catches what is thrown with the C++ tag, here the program's own, there
// being no C++ library to define it. A panic is thrown with nothing in it: what it says is the
// task's (`fly_ctx.panic`).
__asm__(".globl __cpp_exception\n.tagtype __cpp_exception i32\n__cpp_exception:\n");
static _Noreturn void raise_panic(void) {
  static char token;
  __builtin_wasm_throw(0, &token);
}
// What a landing pad asks first: whether what passes is a panic, and not the host's exception by
// which the program ends (`proc_exit`), which runs no cleanup.
bool fly_panicking(void) { return !ending && fly_cx_now()->panic; }
#define FLY_GO_ON(c) raise_panic()
#define FLY_UNCAUGHT(c) false
#elif (defined(FLY_LANDING_PADS) || defined(FLY_C_UNWIND)) && !defined(FLY_FREESTANDING)
#include <unwind.h>
#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#define FLY_UNWIND_ASAN 1
#endif
#endif
#if defined(__SANITIZE_ADDRESS__)
#define FLY_UNWIND_ASAN 1
#endif
#ifdef FLY_UNWIND_ASAN
void __asan_handle_no_return(void);
#endif
#endif

#if defined(FLY_LANDING_PADS) && defined(__wasm__)
#elif defined(FLY_LANDING_PADS) && !defined(FLY_FREESTANDING)
// A panic is an exception of its own class, raised in two phases as C++'s are: the first finds the
// innermost catch point (`fly_try`, whose landing pad catches `fly_panic_type`), the second runs
// the landing pad of each frame on the way, which goes on with `resume`, or, in a machine whose
// cleanup may wait, catches it, the machine unwinding on by its flag (`fly_panic_flag`). Foreign
// exceptions run the cleanups and are caught by no catch point.
#define FLY_PANIC_CLASS 0x464c590050414e43ull
const char fly_panic_type = 0;

static uintptr_t read_uleb(const uint8_t** p) {
  uintptr_t v = 0;
  unsigned shift = 0;
  uint8_t b;
  do { b = *(*p)++; v |= (uintptr_t)(b & 0x7f) << shift; shift += 7; } while (b & 0x80);
  return v;
}

static intptr_t read_sleb(const uint8_t** p) {
  uintptr_t v = 0;
  unsigned shift = 0;
  uint8_t b;
  do { b = *(*p)++; v |= (uintptr_t)(b & 0x7f) << shift; shift += 7; } while (b & 0x80);
  if ((b & 0x40) && shift < 8 * sizeof v) v |= ~(uintptr_t)0 << shift;
  return (intptr_t)v;
}

// A value of the exception tables, in DWARF's encoding `enc`.
static uintptr_t read_encoded(const uint8_t** pp, uint8_t enc) {
  const uint8_t* p = *pp;
  uintptr_t v;
  switch (enc & 0x0f) {
    case 0x00: memcpy(&v, p, sizeof v); p += sizeof v; break;
    case 0x01: v = read_uleb(&p); break;
    case 0x02: { uint16_t x; memcpy(&x, p, 2); p += 2; v = x; break; }
    case 0x03: { uint32_t x; memcpy(&x, p, 4); p += 4; v = x; break; }
    case 0x04: { uint64_t x; memcpy(&x, p, 8); p += 8; v = (uintptr_t)x; break; }
    case 0x09: v = (uintptr_t)read_sleb(&p); break;
    case 0x0a: { int16_t x; memcpy(&x, p, 2); p += 2; v = (uintptr_t)(intptr_t)x; break; }
    case 0x0b: { int32_t x; memcpy(&x, p, 4); p += 4; v = (uintptr_t)(intptr_t)x; break; }
    case 0x0c: { int64_t x; memcpy(&x, p, 8); p += 8; v = (uintptr_t)x; break; }
    default: abort();
  }
  if (v && (enc & 0x70) == 0x10) v += (uintptr_t)*pp;
  else if ((enc & 0x70) != 0) abort();
  if (v && (enc & 0x80)) v = *(const uintptr_t*)v;
  *pp = p;
  return v;
}

static size_t encoded_size(uint8_t enc) {
  switch (enc & 0x0f) {
    case 0x02: case 0x0a: return 2;
    case 0x03: case 0x0b: return 4;
    case 0x04: case 0x0c: return 8;
    default: return sizeof(uintptr_t);
  }
}

// The personality of Flyscript's functions and its catch points: Itanium's exception tables, read
// for the landing pad of the call the frame is in, which is a cleanup, a catch of a panic, or both.
_Unwind_Reason_Code fly_personality(int version, _Unwind_Action actions, uint64_t cls, struct _Unwind_Exception* e,
                                    struct _Unwind_Context* ctx) {
  if (version != 1) return _URC_FATAL_PHASE1_ERROR;
  const uint8_t* p = (const uint8_t*)_Unwind_GetLanguageSpecificData(ctx);
  if (!p) return _URC_CONTINUE_UNWIND;
  int before = 0;
  uintptr_t ip = _Unwind_GetIPInfo(ctx, &before);
  if (!before) ip--;
  uintptr_t start = _Unwind_GetRegionStart(ctx);
  uint8_t enc = *p++;
  uintptr_t lpstart = enc == 0xff ? start : read_encoded(&p, enc);
  uint8_t tenc = *p++;
  const uint8_t* types = NULL;
  if (tenc != 0xff) {
    uintptr_t off = read_uleb(&p);
    types = p + off;
  }
  uint8_t csenc = *p++;
  uintptr_t cslen = read_uleb(&p);
  const uint8_t* table = p + cslen;
  uintptr_t pad = 0, action = 0;
  while (p < table) {
    uintptr_t s = read_encoded(&p, csenc), l = read_encoded(&p, csenc), lp = read_encoded(&p, csenc), a = read_uleb(&p);
    if (ip < start + s) break;
    if (ip < start + s + l) {
      if (lp) { pad = lpstart + lp; action = a; }
      break;
    }
  }
  if (!pad) return _URC_CONTINUE_UNWIND;
  bool ours = cls == FLY_PANIC_CLASS && !(actions & _UA_FORCE_UNWIND);
  bool cleanup = action == 0;
  intptr_t handler = 0;
  if (action) {
    const uint8_t* ap = table + action - 1;
    for (;;) {
      intptr_t filter = read_sleb(&ap);
      const uint8_t* at = ap;
      intptr_t next = read_sleb(&ap);
      if (filter == 0) cleanup = true;
      else if (filter > 0 && ours && types) {
        const uint8_t* tp = types - (size_t)filter * encoded_size(tenc);
        if ((const void*)read_encoded(&tp, tenc) == &fly_panic_type) { handler = filter; break; }
      }
      if (!next) break;
      ap = at + next;
    }
  }
  if (actions & _UA_SEARCH_PHASE) return handler ? _URC_HANDLER_FOUND : _URC_CONTINUE_UNWIND;
  // Below the frame the search found, a catch is passed by, and only cleanups run.
  if (!(actions & _UA_HANDLER_FRAME)) handler = 0;
  if (!handler && !cleanup) return _URC_CONTINUE_UNWIND;
  _Unwind_SetGR(ctx, __builtin_eh_return_data_regno(0), (uintptr_t)e);
  _Unwind_SetGR(ctx, __builtin_eh_return_data_regno(1), (uintptr_t)handler);
  _Unwind_SetIP(ctx, pad);
  return _URC_INSTALL_CONTEXT;
}

static void panic_exception_free(_Unwind_Reason_Code r, struct _Unwind_Exception* e) { (void)r; free(e); }

static _Noreturn void raise_panic(void) {
#ifdef FLY_UNWIND_ASAN
  // The frames given up without running their epilogues leave nothing poisoned behind.
  __asan_handle_no_return();
#endif
  struct _Unwind_Exception* e = calloc(1, sizeof *e);
  if (e) {
    e->exception_class = FLY_PANIC_CLASS;
    e->exception_cleanup = panic_exception_free;
    _Unwind_RaiseException(e);
    free(e);
  }
  // Nothing catches it: frames the tables do not cover, or no memory for the exception.
  fly_ctx* c = fly_cx_now();
  panic_exit(c->panic ? c->panic : "a panic");
}

// A catch point's landing pad is done with the exception it caught.
void fly_caught(void* e) { _Unwind_DeleteException(e); }
#define FLY_GO_ON(c) raise_panic()
// Whether nothing would catch a panic, which then ends the program at once.
#define FLY_UNCAUGHT(c) false
#elif defined(FLY_C_UNWIND) && !defined(FLY_FREESTANDING)
#ifndef __EXCEPTIONS
#error "a program's C is compiled with -fexceptions (selfhost/ccflags.sh), so that a panic runs its cleanups"
#endif
// C cannot catch: a panic is a forced unwind, as a thread's cancellation is, which runs each
// frame's cleanup and stops at the frame of the innermost catch point, whose record it jumps to.
static _Unwind_Reason_Code unwind_stop(int version, _Unwind_Action actions, _Unwind_Exception_Class cls,
                                       struct _Unwind_Exception* e, struct _Unwind_Context* ctx, void* arg) {
  (void)version; (void)cls; (void)arg;
  fly_unw* u = fly_cx_now()->unw;
  if ((actions & _UA_END_OF_STACK) || _Unwind_GetCFA(ctx) > u->frame) {
    free(e);
    _longjmp(u->buf, 1);
  }
  return _URC_NO_REASON;
}
static _Noreturn void unwind_to_catch(void) {
#ifdef FLY_UNWIND_ASAN
  __asan_handle_no_return();
#endif
  struct _Unwind_Exception* e = calloc(1, sizeof *e);
  if (!e) _longjmp(fly_cx_now()->unw->buf, 1);
  e->exception_class = 0x464c590050414e43ull;
  _Unwind_ForcedUnwind(e, unwind_stop, NULL);
  free(e);
  _longjmp(fly_cx_now()->unw->buf, 1);
}
#define FLY_GO_ON(c) unwind_to_catch()
#define FLY_UNCAUGHT(c) (!(c)->unw)
#elif !defined(FLY_FREESTANDING)
#error "a panic unwinds by landing pads (FLY_LANDING_PADS) or by C's cleanups (FLY_C_UNWIND)"
#endif

// A panic unwinds the task it happens in (§5.7), the frames up to the innermost catch point running
// their cleanups. A panic while one unwinds the same task ends the program, as does one with
// nowhere to go.
_Noreturn void fly_panic(const char* message) {
#ifdef FLY_FREESTANDING
  panic_exit(message);
#else
  fly_ctx* c = fly_cx_now();
  if (c->panic) {
    size_t n = strlen(message) + strlen(c->panic) + 40;
    char* both = malloc(n);
    if (!both) panic_exit(message);
    snprintf(both, n, "%s, while unwinding from a panic: %s", message, c->panic);
    panic_exit(both);
  }
  if (c->destroying) {
    size_t n = strlen(message) + 20;
    char* in = malloc(n);
    if (!in) panic_exit(message);
    snprintf(in, n, "%s, in a destructor", message);
    panic_exit(in);
  }
  c->panic = strdup(message);
  if (!c->panic) c->panic = out_of_memory;
  if (FLY_UNCAUGHT(c)) panic_exit(c->panic);
  FLY_GO_ON(c);
#endif
}


_Noreturn void fly_unwind_on(void) {
#ifdef FLY_FREESTANDING
  panic_exit("a panic");
#else
  fly_ctx* c = fly_cx_now();
  if (FLY_UNCAUGHT(c)) panic_exit(c->panic ? c->panic : "a panic");
  FLY_GO_ON(c);
#endif
}

#if defined(FLY_FREESTANDING)
bool fly_try(void (*f)(void* a), void* a) { f(a); return false; }
#elif defined(FLY_C_UNWIND)
bool fly_try(void (*f)(void* a), void* a) {
  fly_unw u;
  fly_frames_mark m;
  fly_frames_keep(&m);
  fly_unw_push(&u);
  if (FLY_UNW_CATCH(&u)) {
    fly_cx_now()->unw = u.prev;
    fly_frames_back(&m);
    return true;
  }
  f(a);
  fly_unw_pop(&u);
  return fly_try_flagged(&m);
}
#endif

// The panic a catch point has taken up, which no longer unwinds its task; and its message let go.
static void stack_restore(void);
static char* panic_take(void) {
  stack_restore();
  fly_ctx* c = fly_cx_now();
  char* m = c->panic;
  c->panic = NULL;
  // A failure or a cancellation it overtook is over too.
  if (c->err) { free(c->err); c->err = NULL; }
  c->unwinding = false;
  return m;
}
static void panic_free(char* m) { if (m && m != out_of_memory) free(m); }
// A panic taken up raised again, in the task running now.
static _Noreturn void panic_again(char* m) {
#ifdef FLY_FREESTANDING
  panic_exit(m ? m : "a panic");
#else
  char buf[512];
  snprintf(buf, sizeof buf, "%s", m ? m : "a panic");
  panic_free(m);
  fly_panic(buf);
#endif
}

// ---- `join`'s halves (§6.5) ----
// Each half of a `join` is a closure, `f` a `fly_fn`, its result written at `out`. A panic in one
// ends the other first, so nothing they borrow goes while either may use it: the other half, not
// yet begun, is dropped without running; once done, what it gave is dropped; and then the first
// panic goes on.

// Runs half `h`, taking up a panic that unwinds it, whose closure is then dropped: the panic's
// message, or NULL.
typedef struct { void (*h)(void* f, void* out); void* f; void* out; } half_t;
static void half_body(void* a) { half_t* x = a; x->h(x->f, x->out); }
static char* run_half(void (*h)(void* f, void* out), void* f, void* out) {
  half_t x = { h, f, out };
  if (!fly_try(half_body, &x)) return NULL;
  char* m = panic_take();
  fly_fn* fn = f;
  if (fn->drop) fn->drop(fn->env);
  return m;
}

static void drop_half(void* f) {
  fly_fn* fn = f;
  if (fn->drop) fn->drop(fn->env);
}

static void join_in_order(void (*a)(void* f, void* out), void* fa, void* oa, void (*da)(void* out),
                          void (*b)(void* f, void* out), void* fb, void* ob, void (*db)(void* out)) {
  char* m = run_half(a, fa, oa);
  if (m) { drop_half(fb); panic_again(m); }
  m = run_half(b, fb, ob);
  if (m) { if (da) da(oa); panic_again(m); }
}

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
  ending = true;
  struct iovec parts[3] = { { "<panic: ", 8 }, { (void*)message, strlen(message) }, { ">\n", 2 } };
  write_out(1, parts, 3);
#ifndef __wasm__
  fflush(stdout);
#endif
  _Exit(101);
}

// A spawned task's panic, which ends that task alone, reported as one line written whole.
static void report_spawned_panic(const char* message) {
  const char* head = "<panic in a spawned task: ";
  size_t h = strlen(head), m = strlen(message);
  char* line = malloc(h + m + 3);
  if (!line) return;
  memcpy(line, head, h);
  memcpy(line + h, message, m);
  memcpy(line + h + m, ">\n", 3);
  struct iovec part = { line, h + m + 2 };
  write_out(1, &part, 1);
  free(line);
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
  unsigned __int128 m = v < 0 ? (unsigned __int128)0 - (unsigned __int128)v : (unsigned __int128)v;
  size_t n = (size_t)fly_rt_show_int(v < 0, (uint64_t)(m >> 64), (uint64_t)m, (uint8_t*)out);
  out[n] = 0;
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

#ifdef FLY_THREADS
// A thread that ends gives every block it keeps back to the classes'.
static void fly_cache_release(void) {
  fly_cache* t = fly_cache_ref();
  for (unsigned c = 0; c < FLY_CLASSES; c++) {
    void* first = t->head[c];
    if (!first) continue;
    void* last = first;
    while (*(void**)last) last = *(void**)last;
    fly_central* k = &fly_centrals[c];
    fly_spin_lock(&k->lock);
    *(void**)last = k->free;
    k->free = first;
    fly_spin_unlock(&k->lock);
    t->head[c] = NULL;
    t->n[c] = 0;
  }
}
#endif

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
  if (!p) fly_out_of_memory();
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
#define MUTEX_HEADER 48

void* fly_mutex_new(const void* value, size_t size) {
  uint8_t* p = fly_alloc(MUTEX_HEADER + size);
  memset(p, 0, MUTEX_HEADER);
  memcpy(p + MUTEX_HEADER, value, size);
  return p + MUTEX_HEADER;
}

void fly_mutex_free(void* state) {
  if (state) free((uint8_t*)state - MUTEX_HEADER);
}

// Whether a panic left a `Mutex`'s state while lending it (§6.2): the last byte of its header,
// read and written under its lock. Locking a poisoned mutex gives the lock back and panics.
static uint8_t* poison_of(const void* state) { return (uint8_t*)state - 1; }
void fly_mutex_check(const void* state) {
  if (*poison_of(state)) {
    fly_unlock(state);
    fly_panic("locked a `Mutex` that a panic left poisoned");
  }
}
void fly_mutex_poison(const void* state, bool poisoned) { *poison_of(state) = poisoned; }

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
  if (!s->ptr) fly_out_of_memory();
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

// ---- numbers as text: the runtime's Flyscript (rt/format.fly) ----

fly_String fly_show_i128(fly_i128 v) {
  uint8_t buf[48];
  unsigned __int128 m = v < 0 ? (unsigned __int128)0 - (unsigned __int128)v : (unsigned __int128)v;
  size_t n = (size_t)fly_rt_show_int(v < 0, (uint64_t)(m >> 64), (uint64_t)m, buf);
  return fly_String_from((fly_str){ buf, n });
}

fly_String fly_show_u128(unsigned __int128 v) {
  uint8_t buf[48];
  size_t n = (size_t)fly_rt_show_int(false, (uint64_t)(v >> 64), (uint64_t)v, buf);
  return fly_String_from((fly_str){ buf, n });
}

fly_String fly_show_f64(double v) {
  uint8_t buf[400];
  size_t n = (size_t)fly_rt_show_f64(v, buf);
  return fly_String_from((fly_str){ buf, n });
}

fly_String fly_float_fixed(double v, uint32_t digits) {
  uint8_t buf[512];
  size_t n = (size_t)fly_rt_float_fixed(v, digits, buf);
  return fly_String_from((fly_str){ buf, n });
}

bool fly_parse_float(fly_str t, double* out) { return fly_rt_parse_float(t.ptr, t.len, out); }

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
  ending = true;
#ifndef __wasm__
  fflush(stdout);
#endif
  _Exit(code);
}
#endif

#ifndef FLY_FREESTANDING
// ---- the file system and the process, for `Io` ----

#include <dirent.h>
#include <errno.h>
#include <sys/stat.h>
#ifndef __wasm__
#include <poll.h>
#include <spawn.h>
#include <sys/wait.h>
extern char** environ;
#endif

static int io_errno(void) {
  switch (errno) {
    case ENOENT: case ENOTDIR: return 1;
    case EEXIST: return 3;
    case ENOTEMPTY: return 4;
#ifdef ENOSYS
    case ENOSYS: return 5;
#endif
#ifdef ENOTSUP
    case ENOTSUP: return 5;
#endif
    default: return 2;
  }
}

// A path as C has it, the working directory for an empty one; freed by the caller.
static char* io_path(fly_str s) {
  if (s.len == 0) s = (fly_str){ (const uint8_t*)".", 1 };
  char* p = malloc(s.len + 1);
  if (!p) fly_out_of_memory();
  memcpy(p, s.ptr, s.len);
  p[s.len] = 0;
  return p;
}

int fly_io_stat(fly_str path, uint64_t* size, bool* dir, int64_t* modified) {
  char* p = io_path(path);
  struct stat st;
  int r = stat(p, &st);
  free(p);
  if (r != 0) return io_errno();
  *size = (uint64_t)st.st_size;
  *dir = S_ISDIR(st.st_mode);
#ifdef __APPLE__
  *modified = (int64_t)st.st_mtimespec.tv_sec * 1000000000 + st.st_mtimespec.tv_nsec;
#else
  *modified = (int64_t)st.st_mtim.tv_sec * 1000000000 + st.st_mtim.tv_nsec;
#endif
  return 0;
}

static int io_name_cmp(const void* a, const void* b) {
  const fly_String* x = a;
  const fly_String* y = b;
  size_t n = x->len < y->len ? x->len : y->len;
  int c = memcmp(x->ptr, y->ptr, n);
  return c ? c : (x->len < y->len ? -1 : x->len > y->len);
}

int fly_io_list(fly_str path, fly_vec* names) {
  char* p = io_path(path);
  DIR* d = opendir(p);
  free(p);
  if (!d) return io_errno();
  fly_vec v = { 0 };
  struct dirent* e;
  while ((e = readdir(d))) {
    if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
    fly_String n = fly_String_from((fly_str){ (const uint8_t*)e->d_name, strlen(e->d_name) });
    fly_vec_push(&v, &n, sizeof(fly_String));
  }
  closedir(d);
  if (v.len) qsort(v.ptr, v.len, sizeof(fly_String), io_name_cmp);
  *names = v;
  return 0;
}

int fly_io_mkdir(fly_str path) {
  char* p = io_path(path);
  int r = mkdir(p, 0777);
  free(p);
  return r == 0 ? 0 : io_errno();
}

int fly_io_remove(fly_str path) {
  char* p = io_path(path);
  struct stat st;
  int r = lstat(p, &st);
  if (r == 0) r = S_ISDIR(st.st_mode) ? rmdir(p) : unlink(p);
  int k = r == 0 ? 0 : io_errno();
  free(p);
  return k;
}

int fly_io_rename(fly_str from, fly_str to) {
  char* a = io_path(from);
  char* b = io_path(to);
  int r = rename(a, b);
  int k = r == 0 ? 0 : io_errno();
  free(a);
  free(b);
  return k;
}

// Files by descriptor (std/io), the standard streams among them: written, standard output and
// error go where `println` and `eprintln` write, in order with them.
int fly_io_open(fly_str path, uint8_t mode, uint32_t* fd) {
  char* p = io_path(path);
  int flags = mode == 0 ? O_RDONLY : mode == 1 ? (O_WRONLY | O_CREAT | O_TRUNC) : (O_WRONLY | O_CREAT | O_APPEND);
#ifdef O_CLOEXEC
  flags |= O_CLOEXEC;
#endif
  int f;
  do { f = open(p, flags, 0666); } while (f < 0 && errno == EINTR);
  int k = f < 0 ? io_errno() : 0;
  free(p);
  if (f >= 0) *fd = (uint32_t)f;
  return k;
}

int fly_io_read(uint32_t fd, fly_slice buf, uint64_t* n) {
  for (;;) {
    ssize_t k = read((int)fd, buf.ptr, buf.len);
    if (k >= 0) { *n = (uint64_t)k; return 0; }
    if (errno != EINTR) return io_errno();
  }
}

int fly_io_write(uint32_t fd, fly_slice buf, uint64_t* n) {
  if (fd == 1 || fd == 2) {
    struct iovec part = { buf.ptr, buf.len };
    write_out((int)fd, &part, 1);
    *n = buf.len;
    return 0;
  }
  for (;;) {
    ssize_t k = write((int)fd, buf.ptr, buf.len);
    if (k >= 0) { *n = (uint64_t)k; return 0; }
    if (errno != EINTR) return io_errno();
  }
}

void fly_io_close(uint32_t fd) {
  if (fd > 2) close((int)fd);
}

// What a dropped file does: no scheduling point, as a destructor performs nothing.
void fly_fd_release(uint32_t fd) { if (fd > 2) close((int)fd); }

bool fly_io_env(fly_str name, fly_String* value) {
  char* n = io_path(name);
  const char* v = getenv(n);
  free(n);
  if (!v) return false;
  *value = fly_String_from((fly_str){ (const uint8_t*)v, strlen(v) });
  return true;
}

fly_String fly_io_cwd(void) {
  char buf[4096];
  if (!getcwd(buf, sizeof buf)) return fly_String_from(fly_str_lit("/", 1));
  return fly_String_from((fly_str){ (const uint8_t*)buf, strlen(buf) });
}

int64_t fly_io_wall(void) {
  struct timespec t;
  clock_gettime(CLOCK_REALTIME, &t);
  return (int64_t)t.tv_sec * 1000000000 + t.tv_nsec;
}

int fly_io_run(fly_str program, fly_slice args, fly_str input, int32_t* status, fly_String* out, fly_String* err) {
#ifdef __wasm__
  (void)program; (void)args; (void)input; (void)status; (void)out; (void)err;
  return 5;
#else
  int in[2], o[2], e[2];
  if (pipe(in) || pipe(o) || pipe(e)) return io_errno();
  char** argv = malloc((args.len + 2) * sizeof(char*));
  argv[0] = io_path(program);
  for (size_t i = 0; i < args.len; i++) argv[i + 1] = io_path(fly_String_as_str(&((fly_String*)args.ptr)[i]));
  argv[args.len + 1] = NULL;
  posix_spawn_file_actions_t fa;
  posix_spawn_file_actions_init(&fa);
  posix_spawn_file_actions_adddup2(&fa, in[0], 0);
  posix_spawn_file_actions_adddup2(&fa, o[1], 1);
  posix_spawn_file_actions_adddup2(&fa, e[1], 2);
  int fds[6] = { in[0], in[1], o[0], o[1], e[0], e[1] };
  for (int i = 0; i < 6; i++) posix_spawn_file_actions_addclose(&fa, fds[i]);
  pid_t pid;
  int r = posix_spawnp(&pid, argv[0], &fa, NULL, argv, environ);
  posix_spawn_file_actions_destroy(&fa);
  for (size_t i = 0; i < args.len + 1; i++) free(argv[i]);
  free(argv);
  close(in[0]);
  close(o[1]);
  close(e[1]);
  if (r != 0) {
    close(in[1]);
    close(o[0]);
    close(e[0]);
    errno = r;
    return io_errno();
  }
  // What it reads, given while what it writes is taken, so that neither side waits on the other.
  fly_String so = fly_String_new(), se = fly_String_new();
  size_t given = 0;
  if (input.len == 0) { close(in[1]); in[1] = -1; }
  int open = 2;
  while (open > 0) {
    struct pollfd ps[3] = { { o[0], POLLIN, 0 }, { e[0], POLLIN, 0 }, { in[1], POLLOUT, 0 } };
    int n = in[1] >= 0 ? 3 : 2;
    if (poll(ps, (nfds_t)n, -1) < 0) { if (errno == EINTR) continue; break; }
    for (int i = 0; i < 2; i++) {
      if (ps[i].fd < 0 || !(ps[i].revents & (POLLIN | POLLHUP | POLLERR))) continue;
      uint8_t buf[4096];
      ssize_t k = read(ps[i].fd, buf, sizeof buf);
      if (k > 0) fly_String_push(i == 0 ? &so : &se, (fly_str){ buf, (size_t)k });
      else { close(ps[i].fd); if (i == 0) o[0] = -1; else e[0] = -1; open--; }
    }
    if (n == 3 && (ps[2].revents & (POLLOUT | POLLHUP | POLLERR))) {
      ssize_t k = (ps[2].revents & POLLOUT) ? write(in[1], input.ptr + given, input.len - given) : -1;
      if (k > 0) given += (size_t)k;
      if (k <= 0 || given == input.len) { close(in[1]); in[1] = -1; }
    }
  }
  if (in[1] >= 0) close(in[1]);
  int ws = 0;
  while (waitpid(pid, &ws, 0) < 0 && errno == EINTR) {}
  *status = WIFEXITED(ws) ? WEXITSTATUS(ws) : 128 + (WIFSIGNALED(ws) ? WTERMSIG(ws) : 0);
  *out = so;
  *err = se;
  return 0;
#endif
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
  if (!v->ptr) fly_out_of_memory();
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

void fly_vec_extend(fly_vec* v, const void* elems, size_t n, size_t size) {
  if (n == 0) return;
  vreserve(v, n, size);
  memcpy((char*)v->ptr + v->len * size, elems, n * size);
  v->len += n;
}

void fly_slice_copy(fly_slice to, fly_slice from, size_t size) {
  if (to.len != from.len) fly_panicf("copyFrom: %zu elements in place of %zu", from.len, to.len);
  memmove(to.ptr, from.ptr, to.len * size);
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

// A drop never stops its task, so what is left for later is the thread's. A destructor does not
// unwind (§5.7), so nothing leaves the loop but its end.
typedef struct { void (*f)(void*, size_t); void* p; size_t n; } fly_later;
typedef struct { fly_later* at; size_t len, cap; bool on; } fly_laters;
FLY_THREAD_VAR(fly_laters, laters, { 0 })

#ifdef __wasm__
unsigned fly_drop_depth;
#endif

// The drops left for later are run one at a time, low on the stack, each leaving what it holds for
// later in turn: in WebAssembly, nesting its own drops afresh.
void fly_drop_later(void (*f)(void*, size_t), void* p, size_t n) {
  fly_laters* l = laters_ref();
  if (l->on) {
    if (l->len == l->cap) {
      size_t cap = l->cap ? l->cap * 2 : 16;
      fly_later* at = realloc(l->at, cap * sizeof(fly_later));
      if (!at) fly_out_of_memory();
      l->at = at;
      l->cap = cap;
    }
    l->at[l->len++] = (fly_later){ f, p, n };
    return;
  }
  l->on = true;
#ifdef __wasm__
  unsigned depth = fly_drop_depth;
  fly_drop_depth = 0;
#endif
  f(p, n);
  while (l->len > 0) {
    fly_later x = l->at[--l->len];
#ifdef __wasm__
    fly_drop_depth = 0;
#endif
    x.f(x.p, x.n);
  }
#ifdef __wasm__
  fly_drop_depth = depth;
#endif
  free(l->at);
  *l = (fly_laters){ 0 };
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
    if (!m->entries || !m->hashes) fly_out_of_memory();
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
  if (g->drop) { fly_destroy_begin(); g->drop(g->st); fly_destroy_end(); }
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

// ---- the stack ----

// A thread's stack: every task runs on the stack of the thread running it, as far as it may until
// it stops, and code that suspends keeps what it needs in frames of its own, not on the stack.

// The limit of the stack of the thread running (runtime.h): none if its bounds are not to be had.
FLY_THREAD_VAR(uintptr_t, stack_limit0, 0)
#define stack_limit0 (*stack_limit0_ref())

static void thread_stack_limit(void) {
  uintptr_t low = 0;
#if defined(FLY_FREESTANDING)
#elif defined(__wasm__)
  extern char __stack_low;
  low = (uintptr_t)&__stack_low;
#elif defined(__APPLE__)
  pthread_t self = pthread_self();
  low = (uintptr_t)pthread_get_stackaddr_np(self) - pthread_get_stacksize_np(self);
#elif defined(__linux__)
  pthread_attr_t a;
  void* addr;
  size_t size;
  if (pthread_getattr_np(pthread_self(), &a) == 0) {
    if (pthread_attr_getstack(&a, &addr, &size) == 0) low = (uintptr_t)addr;
    pthread_attr_destroy(&a);
  }
#endif
  stack_limit0 = low ? low + FLY_HEADROOM : 0;
}

__attribute__((constructor)) static void main_stack_limit(void) {
  thread_stack_limit();
  fly_ctx0.limit = stack_limit0;
}

// Half the headroom is the cleanups' as the panic unwinds the task, until a catch point takes it
// up (`stack_restore`).
_Noreturn void fly_stack_overflow(void) {
  fly_ctx* cx = fly_cx_now();
  if (cx->limit == stack_limit0) cx->limit = stack_limit0 - FLY_HEADROOM / 2;
  fly_panic("stack overflow");
}

// The check, for code made through LLVM, which inlines it.
void fly_stack_at(uintptr_t sp) { fly_stack_check(sp); }

static void stack_restore(void) { fly_cx_now()->limit = stack_limit0; }

#ifdef FLY_THREADS
// The stack tasks run on: as large as a thread is given, committed as it is touched, so that a
// task may go as deep on one thread as on another, the program's own included.
#define FLY_STACK (64u << 20)
typedef struct { void* (*run)(void*); void* arg; } big_stack_t;
static void* on_big_stack(void* a) {
  big_stack_t* b = a;
  thread_stack_limit();
  void* r = b->run(b->arg);
#ifdef FLY_MALLOC
  fly_cache_release();
#endif
  return r;
}
// Runs `run(arg)` on a thread of its own, of FLY_STACK, the program's thread waiting for it.
static void run_on_big_stack(void* (*run)(void*), void* arg) {
  big_stack_t b = { run, arg };
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, FLY_STACK);
  pthread_t th;
  if (pthread_create(&th, &attr, on_big_stack, &b) != 0) fly_panic("cannot start the scheduler's thread");
  pthread_attr_destroy(&attr);
  pthread_join(th, NULL);
}
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
  // The body returns, each of its frames saying where it stopped, to the `handle`'s own code.
  h->op = op;
  h->args = args;
  h->result = result;
  h->from = inner;
  h->waiting = true;
  cx->pend = FLY_PEND_PERFORM;
  cx->pend_h = h;
}

bool fly_handled(uint32_t effect) {
  for (fly_handler* h = fly_handlers; h; h = h->outer) {
    if (h->effect == effect) return true;
  }
  return false;
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
  fly_ctx* cx = fly_cx_now();
  fly_unwind_state s = { cx->err, cx->unwinding, cx->panicking };
  cx->err = NULL;
  cx->unwinding = false;
  cx->panicking = false;
  return s;
}

void fly_cleanup_end(fly_unwind_state s) {
  cleaning(-1);
  fly_ctx* cx = fly_cx_now();
  cx->err = s.err;
  cx->unwinding = s.unwinding;
  cx->panicking = s.panicking;
}

void fly_panic_flag(void) {
  fly_ctx* cx = fly_cx_now();
  cx->unwinding = true;
  cx->panicking = true;
}

_Noreturn void fly_panic_again(void) {
  fly_ctx* cx = fly_cx_now();
  cx->panicking = false;
  cx->unwinding = false;
  fly_unwind_on();
}

bool fly_try_flagged(const fly_frames_mark* m) {
  fly_ctx* cx = fly_cx_now();
  if (!cx->panicking) return false;
  cx->panicking = false;
  fly_frames_back(m);
  return true;
}

void fly_cont_drop(fly_cont* k) {
  if (k->drop) { fly_destroy_begin(); k->drop(k->frame); fly_destroy_end(); }
  *k = (fly_cont){ 0 };
}

// ---- code that may suspend, as state machines ----

// A chunk of a frame arena: frames are taken from its end, and a chunk too small for the next is
// followed by another, twice as large, up to FRAME_CHUNK, or as large as the frame. The first is
// as large as the first frame, so a task whose frames nest in its root's takes no more than it
// needs. A chunk emptied is kept, the largest one, by the context the code runs in, for the next
// that would be made, so a call that goes past a chunk's end and returns again and again takes
// nothing from the allocator; it is freed as the task stops (`fly_spare_free`), so a task parked
// holds only the frames it is in, and no task is given another's.
struct fly_frame_chunk { fly_frame_chunk* prev; char* end; _Alignas(16) char data[]; };
enum { FRAME_CHUNK = 16384 };

static size_t chunk_room(const fly_frame_chunk* c) { return (size_t)(c->end - c->data); }

// Chunk `c`, emptied, kept by the running context if it is the largest it has emptied yet.
static void chunk_spare(fly_frame_chunk* c) {
  fly_ctx* cx = fly_cx_now();
  if (cx->spare && chunk_room(cx->spare) >= chunk_room(c)) { free(c); return; }
  if (cx->spare) free(cx->spare);
  cx->spare = c;
}

void* fly_frame_push(size_t size) {
  fly_ctx* cx = fly_cx_now();
  if (!cx->frames) cx->frames = calloc(1, sizeof(fly_frames));
  fly_frames* a = cx->frames;
  size = (size + 15) & ~(size_t)15;
  if (!a->chunk || (size_t)(a->end - a->top) < size) {
    size_t n = a->chunk ? 2 * chunk_room(a->chunk) : size;
    if (n > FRAME_CHUNK) n = FRAME_CHUNK;
    if (n < size) n = size;
    fly_frame_chunk* c = cx->spare;
    if (c && chunk_room(c) >= size) {
      cx->spare = NULL;
    } else {
      c = fly_alloc(sizeof(fly_frame_chunk) + n);
      c->end = c->data + n;
    }
    c->prev = a->chunk;
    a->chunk = c;
    a->top = c->data;
    a->end = c->end;
  }
  void* p = a->top;
  a->top += size;
  *(uint32_t*)p = 0;
  return p;
}

// A slot whose frame is marked, its low bit set, holds a frame nested in the caller's own, which
// the machine neither takes from the arena nor gives back to it.
void* fly_frame_take(void** slot, size_t size) {
  if (!*slot) *slot = fly_frame_push(size);
  return (void*)((uintptr_t)*slot & ~(uintptr_t)1);
}

void fly_frame_end(void** slot, void* frame) {
  if (!((uintptr_t)*slot & 1)) fly_frame_pop(frame);
  *slot = NULL;
}

// The chunks above the one `p` is in, or ends, emptied; `p` the arena's top.
static void frames_cut(fly_frames* a, char* p) {
  while (a->chunk && !(p >= a->chunk->data && p <= a->chunk->end)) {
    fly_frame_chunk* c = a->chunk;
    a->chunk = c->prev;
    chunk_spare(c);
    if (a->chunk) a->end = a->chunk->end;
  }
  a->top = a->chunk ? p : NULL;
}

void fly_frame_pop(void* frame) { frames_cut(fly_cx_now()->frames, frame); }

void fly_spare_free(fly_ctx* cx) {
  if (cx->spare) free(cx->spare);
  cx->spare = NULL;
}

void fly_frames_free(fly_frames* a) {
  fly_ctx* cx = fly_cx_now();
  if (cx->frames == a) cx->frames = a->outer;
  while (a->chunk) {
    fly_frame_chunk* c = a->chunk;
    a->chunk = c->prev;
    free(c);
  }
  a->top = a->end = NULL;
}

// Arena `a` in use. Still in use, as a panic left it, it keeps the one it was entered from.
static void frames_enter(fly_ctx* cx, fly_frames* a) {
  if (cx->frames != a) a->outer = cx->frames;
  cx->frames = a;
}

void fly_frames_keep(fly_frames_mark* m) {
  fly_frames* a = fly_cx_now()->frames;
  *m = (fly_frames_mark){ a, a ? a->top : NULL };
}

void fly_frames_back(const fly_frames_mark* m) {
  fly_cx_now()->frames = m->frames;
  if (m->frames) frames_cut(m->frames, m->top);
}

void fly_machine_unwind(void (*call)(void* env, void* frame), void* env, void* frame) {
  fly_ctx* cx = fly_cx_now();
  fly_unwind_state saved = { cx->err, cx->unwinding, cx->panicking };
  cx->err = NULL;
  cx->unwinding = true;
  cx->panicking = false;
  call(env, frame);
  fly_panic_again_if();
  cx = fly_cx_now();
  cx->err = saved.err;
  cx->unwinding = saved.unwinding;
  cx->panicking = saved.panicking;
}

void fly_handle_enter(fly_handler* h, fly_frames* arena, fly_frames** saved) {
  fly_ctx* cx = fly_cx_now();
  h->outer = cx->handlers;
  h->op = -1;
  h->waiting = false;
  cx->handlers = h;
  *saved = cx->frames;
  frames_enter(cx, arena);
}

void fly_handle_leave(fly_handler* h, fly_frames* saved) {
  fly_ctx* cx = fly_cx_now();
  cx->handlers = h->outer;
  cx->frames = saved;
}

bool fly_handle_took(fly_handler* h) {
  fly_ctx* cx = fly_cx_now();
  if (cx->pend != FLY_PEND_PERFORM || cx->pend_h != h) return false;
  cx->pend = 0;
  cx->pend_h = NULL;
  return true;
}

fly_unwind_state fly_handle_drop_begin(fly_handler* h) {
  fly_ctx* cx = fly_cx_now();
  fly_unwind_state saved = { cx->err, cx->unwinding, cx->panicking };
  cx->err = NULL;
  cx->unwinding = true;
  cx->panicking = false;
  if (h->kept) h->dying = true;
  for (fly_handler* x = h->from; x && x != h; x = x->outer) {
    if (x->kept && x->waiting) x->dying = true;
  }
  return saved;
}

void fly_handle_drop_end(fly_unwind_state s) {
  fly_panic_again_if();
  fly_ctx* cx = fly_cx_now();
  cx->err = s.err;
  cx->unwinding = s.unwinding;
  cx->panicking = s.panicking;
}

void fly_handle_drop_m(fly_handler* h, fly_frames* arena, void** bslot, void (*run)(void* h)) {
  if (!*bslot) return;
  fly_unwind_state u = fly_handle_drop_begin(h);
  fly_frames* saved;
  fly_handle_enter(h, arena, &saved);
  run(h);
  fly_handle_leave(h, saved);
  fly_handle_drop_end(u);
}

// `generate(f)`, its producer a state machine: its frame, and the frames of what it calls
// indirectly, are the generator's own, in an arena of its own, for the generator outlives the
// code pulling it at any one time.
typedef struct {
  fly_fn producer;
  void* frame;
  fly_frames arena;
  bool done;
} fly_generated_m;

typedef fly_unit (*producer_m)(void* env, void** slot, void* out);

static bool generated_m_next(void* st, void* out) {
  fly_generated_m* g = st;
  if (g->done) return false;
  fly_ctx* cx = fly_cx_now();
  fly_frames* saved = cx->frames;
  frames_enter(cx, &g->arena);
  ((producer_m)g->producer.fn)(g->producer.env, &g->frame, out);
  cx = fly_cx_now();
  cx->frames = saved;
  fly_panic_again_if();
  if (cx->pend == FLY_PEND_YIELD) {
    cx->pend = 0;
    return true;
  }
  // Suspended for something else, which goes on to the code pulling it; or ended.
  if (cx->pend) return false;
  g->done = true;
  return false;
}

static void generated_m_unwind(void* env, void* frame) {
  fly_generated_m* g = env;
  (void)frame;
  ((producer_m)g->producer.fn)(g->producer.env, &g->frame, NULL);
}

static void generated_m_drop(void* st) {
  fly_generated_m* g = st;
  if (g->frame) {
    // A generator dropped is cut off from every handler: what its cleanup performs is cancelled,
    // the cleanup unwinding from it (§5.3).
    fly_ctx* cx = fly_cx_now();
    fly_handler barrier = { .effect = UINT32_MAX, .dying = true, .outer = cx->handlers };
    fly_handler* outer = cx->handlers;
    cx->handlers = &barrier;
    fly_frames* saved = cx->frames;
    frames_enter(cx, &g->arena);
    fly_machine_unwind(generated_m_unwind, g, g->frame);
    cx = fly_cx_now();
    cx->frames = saved;
    cx->handlers = outer;
  }
  fly_frames_free(&g->arena);
  fly_fn* f = &g->producer;
  if (f->drop) f->drop(f->env);
  free(g);
}

fly_gen fly_generate_m(fly_fn producer) {
  fly_generated_m* g = fly_alloc(sizeof(fly_generated_m));
  *g = (fly_generated_m){ .producer = producer };
  return (fly_gen){ g, generated_m_next, generated_m_drop };
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

// A runtime routine that waits is a leaf of the machine that calls it: called first, with its
// wait record zeroed, it makes its request and, unless it is answered at once, stops, the task's
// context pending; called again with the same record, it goes on from where it stopped, its
// locals whatever it kept in the record. `W_SUSPEND` stops it, returning what follows, and is
// where it goes on.
#define W_BEGIN(w) switch ((w)->step) { case 0:;
#define W_END }
#define W_SUSPEND(w, ...) do { (w)->step = __LINE__; return __VA_ARGS__; case __LINE__:; } while (0)

// ---- sockets ----

#if defined(FLY_THREADS)
// On worker threads a socket does not block: a task waits for it to be ready (below), by
// `IO_WAIT`, after which it sees whether it was cancelled meanwhile.
static bool io_wait_begin(int fd, bool write);
static void io_wait_end(void);
static bool cancelled_here(void);
static void io_register(int fd);
static bool threads;
#define IO_WAIT(w, fd, write, ...) do { if (io_wait_begin((fd), (write))) { W_SUSPEND(w, __VA_ARGS__); io_wait_end(); } } while (0)
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

bool fly_accept(fly_wait* w, int listener, fly_socket* out) {
  world_load();
  if (world.simulated) {
    fly_str input;
    if (!fly_world_accept(&input)) return false;
    *out = (fly_socket){ .input = input };
    return true;
  }
#ifdef __wasm__
  (void)w;
  (void)listener;
  (void)out;
  return false;
#else
  W_BEGIN(w)
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
      IO_WAIT(w, listener - 1, false, false);
      if (cancelled_here()) return false;
      continue;
    }
#endif
    return false;
  }
  W_END
  return false;
#endif
}

// ---- secure random bytes, for `Io.random` ----

static uint64_t random_rng;

#ifndef __wasm__
#include <sys/random.h>
#endif

// Against a simulated world, bytes of its seed, so that a run replays (§6.4); else the system's
// generator, which never fails once the system has seeded it.
void fly_io_random(fly_slice buf) {
  world_load();
  uint8_t* p = buf.ptr;
  if (world.simulated) {
    if (!random_rng) random_rng = (world.seed ^ 0x9E3779B97F4A7C15ull) | 1;
    for (size_t i = 0; i < buf.len; i += 8) {
      uint64_t x = xorshift(&random_rng);
      for (size_t k = 0; k < 8 && i + k < buf.len; k++) p[i + k] = (uint8_t)(x >> (8 * k));
    }
    return;
  }
  // `getentropy` gives at most 256 bytes a call.
  for (size_t i = 0; i < buf.len; i += 256) {
    size_t n = buf.len - i < 256 ? buf.len - i : 256;
    if (getentropy(p + i, n) != 0) fly_panic("the system's secure random generator failed");
  }
}

// ---- cryptography (std/crypto) ----
// Each operation is one of a few, numbered as the host import under WebAssembly numbers them,
// given up to four byte strings and room for what it makes: how much it made, or -1 if what it
// opened was forged (or, for a signature, is not one), -2 if its input cannot be what it takes.

enum { CRYPTO_SHA256 = 1, CRYPTO_SHA384, CRYPTO_SHA512, CRYPTO_HMAC256, CRYPTO_HMAC512, CRYPTO_HKDF256, CRYPTO_SEAL, CRYPTO_OPEN, CRYPTO_ED_PUBLIC, CRYPTO_ED_SIGN, CRYPTO_ED_VERIFY };

#ifdef __wasm__
__attribute__((import_module("fly"), import_name("crypto"))) int32_t fly_host_crypto(int32_t op, const void* a, size_t na, const void* b, size_t nb, const void* c, size_t nc, const void* d, size_t nd, void* out, size_t cap);
static long crypto_op(int op, fly_slice a, fly_slice b, fly_slice c, fly_slice d, uint8_t* out, size_t cap) {
  return fly_host_crypto(op, a.ptr, a.len, b.ptr, b.len, c.ptr, c.len, d.ptr, d.len, out, cap);
}
#else
#include <dlfcn.h>

// libcrypto's functions, by name, found when cryptography is first used: a program that uses none
// needs no OpenSSL. `FLY_LIBCRYPTO` names the library if it is not where the system keeps it.
#define CRYPTO_FNS(X) \
  X(void*, EVP_sha256, (void)) X(void*, EVP_sha384, (void)) X(void*, EVP_sha512, (void)) \
  X(int, EVP_Digest, (const void*, size_t, unsigned char*, unsigned*, const void*, void*)) \
  X(unsigned char*, EVP_Q_mac, (void*, const char*, const char*, const char*, const void*, const void*, size_t, const unsigned char*, size_t, unsigned char*, size_t, size_t*)) \
  X(void*, EVP_KDF_fetch, (void*, const char*, const char*)) X(void, EVP_KDF_free, (void*)) \
  X(void*, EVP_KDF_CTX_new, (void*)) X(void, EVP_KDF_CTX_free, (void*)) \
  X(int, EVP_KDF_derive, (void*, unsigned char*, size_t, const void*)) \
  X(void*, EVP_aes_256_gcm, (void)) X(void*, EVP_CIPHER_CTX_new, (void)) X(void, EVP_CIPHER_CTX_free, (void*)) \
  X(int, EVP_CIPHER_CTX_ctrl, (void*, int, int, void*)) \
  X(int, EVP_EncryptInit_ex, (void*, const void*, void*, const unsigned char*, const unsigned char*)) \
  X(int, EVP_EncryptUpdate, (void*, unsigned char*, int*, const unsigned char*, int)) \
  X(int, EVP_EncryptFinal_ex, (void*, unsigned char*, int*)) \
  X(int, EVP_DecryptInit_ex, (void*, const void*, void*, const unsigned char*, const unsigned char*)) \
  X(int, EVP_DecryptUpdate, (void*, unsigned char*, int*, const unsigned char*, int)) \
  X(int, EVP_DecryptFinal_ex, (void*, unsigned char*, int*)) \
  X(void*, EVP_PKEY_new_raw_private_key, (int, void*, const unsigned char*, size_t)) \
  X(void*, EVP_PKEY_new_raw_public_key, (int, void*, const unsigned char*, size_t)) \
  X(int, EVP_PKEY_get_raw_public_key, (const void*, unsigned char*, size_t*)) X(void, EVP_PKEY_free, (void*)) \
  X(void*, EVP_MD_CTX_new, (void)) X(void, EVP_MD_CTX_free, (void*)) \
  X(int, EVP_DigestSignInit, (void*, void**, const void*, void*, void*)) \
  X(int, EVP_DigestSign, (void*, unsigned char*, size_t*, const unsigned char*, size_t)) \
  X(int, EVP_DigestVerifyInit, (void*, void**, const void*, void*, void*)) \
  X(int, EVP_DigestVerify, (void*, const unsigned char*, size_t, const unsigned char*, size_t))

static struct {
#define CRYPTO_FIELD(R, name, args) R(*name) args;
  CRYPTO_FNS(CRYPTO_FIELD)
} ossl;
static int ossl_state;

// A library of OpenSSL's: the one `env` names, else the first of `names` the loader finds.
void* fly_openssl_open(const char* env, const char* const* names) {
  const char* own = getenv(env);
  if (own && *own) return dlopen(own, RTLD_NOW | RTLD_LOCAL);
  for (const char* const* n = names; *n; n++) {
    void* h = dlopen(*n, RTLD_NOW | RTLD_LOCAL);
    if (h) return h;
  }
  return NULL;
}

static void crypto_load(void) {
  if (__atomic_load_n(&ossl_state, __ATOMIC_ACQUIRE) == 2) return;
  static const char* const names[] = {
#ifdef __APPLE__
    // Never the system's unversioned libcrypto, which ends any program that loads it.
    "libcrypto.3.dylib", "/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib", "/usr/local/opt/openssl@3/lib/libcrypto.3.dylib",
    "libcrypto.4.dylib", "/opt/homebrew/opt/openssl@4/lib/libcrypto.4.dylib", "/usr/local/opt/openssl@4/lib/libcrypto.4.dylib",
#else
    "libcrypto.so.3", "libcrypto.so.4",
#endif
    NULL };
  // One thread loads it; the others wait for it.
  int expected = 0;
  if (!__atomic_compare_exchange_n(&ossl_state, &expected, 1, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
    while (__atomic_load_n(&ossl_state, __ATOMIC_ACQUIRE) != 2) {}
    return;
  }
  void* h = fly_openssl_open("FLY_LIBCRYPTO", names);
  if (!h) fly_panic("cryptography needs OpenSSL 3 or later (libcrypto), which was not found: set FLY_LIBCRYPTO to it");
#define CRYPTO_LOAD(R, name, args) \
  if (!(ossl.name = (R(*) args)dlsym(h, #name))) fly_panicf("this libcrypto has no %s: cryptography needs OpenSSL 3 or later", #name);
#define CRYPTO_LOAD_SSL(R, name, args) \
  if (!(tls.name = (R(*) args)dlsym(h, #name))) fly_panicf("this libssl has no %s: TLS needs OpenSSL 3 or later", #name);
  CRYPTO_FNS(CRYPTO_LOAD)
  __atomic_store_n(&ossl_state, 2, __ATOMIC_RELEASE);
}

// OpenSSL's parameter of an operation, as `OSSL_PARAM` lays it out.
typedef struct { const char* key; unsigned type; void* data; size_t size, returned; } ossl_param;

static long crypto_cipher(bool seal, fly_slice key, fly_slice nonce, fly_slice text, fly_slice aad, uint8_t* out) {
  if (key.len != 32 || nonce.len != 12 || text.len > 0x7fffffff - 16 || aad.len > 0x7fffffff) return -2;
  if (!seal && text.len < 16) return -1;
  size_t n = seal ? text.len : text.len - 16;
  void* ctx = ossl.EVP_CIPHER_CTX_new();
  int k = 0, ok = 1;
  ok &= (seal ? ossl.EVP_EncryptInit_ex : ossl.EVP_DecryptInit_ex)(ctx, ossl.EVP_aes_256_gcm(), NULL, key.ptr, nonce.ptr);
  int (*update)(void*, unsigned char*, int*, const unsigned char*, int) = seal ? ossl.EVP_EncryptUpdate : ossl.EVP_DecryptUpdate;
  if (aad.len) ok &= update(ctx, NULL, &k, aad.ptr, (int)aad.len);
  if (n) ok &= update(ctx, out, &k, text.ptr, (int)n);
  // EVP_CTRL_GCM_SET_TAG and EVP_CTRL_GCM_GET_TAG: the tag is checked before the end, made after.
  if (!seal) ok &= ossl.EVP_CIPHER_CTX_ctrl(ctx, 0x11, 16, (uint8_t*)text.ptr + n);
  int done = (seal ? ossl.EVP_EncryptFinal_ex : ossl.EVP_DecryptFinal_ex)(ctx, out + n, &k);
  if (seal) ok &= done > 0 && ossl.EVP_CIPHER_CTX_ctrl(ctx, 0x10, 16, out + n);
  ossl.EVP_CIPHER_CTX_free(ctx);
  if (!seal && done <= 0) return -1;
  if (!ok) fly_panic("libcrypto failed to run AES-256-GCM");
  return (long)(seal ? n + 16 : n);
}

static long crypto_op(int op, fly_slice a, fly_slice b, fly_slice c, fly_slice d, uint8_t* out, size_t cap) {
  crypto_load();
  switch (op) {
    case CRYPTO_SHA256: case CRYPTO_SHA384: case CRYPTO_SHA512: {
      void* md = op == CRYPTO_SHA256 ? ossl.EVP_sha256() : op == CRYPTO_SHA384 ? ossl.EVP_sha384() : ossl.EVP_sha512();
      unsigned n = 0;
      if (!ossl.EVP_Digest(a.ptr, a.len, out, &n, md, NULL)) fly_panic("libcrypto failed to hash");
      return n;
    }
    case CRYPTO_HMAC256: case CRYPTO_HMAC512: {
      size_t n = 0;
      if (!ossl.EVP_Q_mac(NULL, "HMAC", NULL, op == CRYPTO_HMAC256 ? "SHA256" : "SHA512", NULL, a.ptr, a.len, b.ptr, b.len, out, cap, &n)) fly_panic("libcrypto failed to run HMAC");
      return (long)n;
    }
    case CRYPTO_HKDF256: {
      if (cap > 255 * 32) return -2;
      void* kdf = ossl.EVP_KDF_fetch(NULL, "HKDF", NULL);
      void* ctx = kdf ? ossl.EVP_KDF_CTX_new(kdf) : NULL;
      // OSSL_PARAM_UTF8_STRING 4, OSSL_PARAM_OCTET_STRING 5; a salt of none is one of zeros.
      uint8_t none = 0;
      ossl_param ps[] = {
        { "digest", 4, "SHA256", 6, (size_t)-1 }, { "key", 5, a.ptr ? a.ptr : &none, a.len, (size_t)-1 },
        { "salt", 5, b.ptr ? b.ptr : &none, b.len, (size_t)-1 }, { "info", 5, c.ptr ? c.ptr : &none, c.len, (size_t)-1 }, { NULL, 0, NULL, 0, 0 } };
      int ok = ctx && (cap == 0 || ossl.EVP_KDF_derive(ctx, out, cap, ps) > 0);
      if (ctx) ossl.EVP_KDF_CTX_free(ctx);
      if (kdf) ossl.EVP_KDF_free(kdf);
      if (!ok) fly_panic("libcrypto failed to run HKDF");
      return (long)cap;
    }
    case CRYPTO_SEAL: case CRYPTO_OPEN:
      return crypto_cipher(op == CRYPTO_SEAL, a, b, c, d, out);
    case CRYPTO_ED_PUBLIC: case CRYPTO_ED_SIGN: {
      // EVP_PKEY_ED25519, which is NID_ED25519.
      if (a.len != 32) return -2;
      void* key = ossl.EVP_PKEY_new_raw_private_key(1087, NULL, a.ptr, 32);
      if (!key) fly_panic("libcrypto failed to make an Ed25519 key");
      size_t n = cap;
      int ok;
      if (op == CRYPTO_ED_PUBLIC) {
        ok = ossl.EVP_PKEY_get_raw_public_key(key, out, &n);
      } else {
        void* m = ossl.EVP_MD_CTX_new();
        ok = ossl.EVP_DigestSignInit(m, NULL, NULL, NULL, key) > 0 && ossl.EVP_DigestSign(m, out, &n, b.ptr, b.len) > 0;
        ossl.EVP_MD_CTX_free(m);
      }
      ossl.EVP_PKEY_free(key);
      if (!ok) fly_panic("libcrypto failed to sign with Ed25519");
      return (long)n;
    }
    case CRYPTO_ED_VERIFY: {
      if (a.len != 32 || c.len != 64) return -1;
      void* key = ossl.EVP_PKEY_new_raw_public_key(1087, NULL, a.ptr, 32);
      if (!key) return -1;
      void* m = ossl.EVP_MD_CTX_new();
      int ok = ossl.EVP_DigestVerifyInit(m, NULL, NULL, NULL, key) > 0 && ossl.EVP_DigestVerify(m, c.ptr, 64, b.ptr, b.len) == 1;
      ossl.EVP_MD_CTX_free(m);
      ossl.EVP_PKEY_free(key);
      return ok ? 0 : -1;
    }
  }
  return -2;
}
#endif

static const fly_slice no_bytes = { NULL, 0 };

// The bytes an operation makes, at most `cap` of them; `what` says what its input must be.
static fly_vec crypto_bytes(int op, fly_slice a, fly_slice b, fly_slice c, fly_slice d, size_t cap, const char* what) {
  uint8_t* out = fly_alloc(cap ? cap : 1);
  long n = crypto_op(op, a, b, c, d, out, cap);
  if (n < 0) fly_panic(what);
  fly_vec v = fly_vec_from(out, (size_t)n, 1);
  free(out);
  return v;
}

fly_vec fly_crypto_sha256(fly_slice data) { return crypto_bytes(CRYPTO_SHA256, data, no_bytes, no_bytes, no_bytes, 32, ""); }
fly_vec fly_crypto_sha384(fly_slice data) { return crypto_bytes(CRYPTO_SHA384, data, no_bytes, no_bytes, no_bytes, 48, ""); }
fly_vec fly_crypto_sha512(fly_slice data) { return crypto_bytes(CRYPTO_SHA512, data, no_bytes, no_bytes, no_bytes, 64, ""); }
fly_vec fly_crypto_hmac_sha256(fly_slice key, fly_slice data) { return crypto_bytes(CRYPTO_HMAC256, key, data, no_bytes, no_bytes, 32, ""); }
fly_vec fly_crypto_hmac_sha512(fly_slice key, fly_slice data) { return crypto_bytes(CRYPTO_HMAC512, key, data, no_bytes, no_bytes, 64, ""); }
fly_vec fly_crypto_hkdf_sha256(fly_slice secret, fly_slice salt, fly_slice info, uint64_t length) {
  if (length > 255 * 32) fly_panic("HKDF-SHA-256 makes at most 8160 bytes");
  return crypto_bytes(CRYPTO_HKDF256, secret, salt, info, no_bytes, (size_t)length, "");
}
fly_vec fly_crypto_seal(fly_slice key, fly_slice nonce, fly_slice plaintext, fly_slice aad) {
  return crypto_bytes(CRYPTO_SEAL, key, nonce, plaintext, aad, plaintext.len + 16, "AES-256-GCM takes a 32-byte key and a 12-byte nonce");
}
bool fly_crypto_open(fly_slice key, fly_slice nonce, fly_slice sealed, fly_slice aad, fly_vec* plaintext) {
  uint8_t* out = fly_alloc(sealed.len ? sealed.len : 1);
  long n = crypto_op(CRYPTO_OPEN, key, nonce, sealed, aad, out, sealed.len);
  if (n == -2) fly_panic("AES-256-GCM takes a 32-byte key and a 12-byte nonce");
  if (n >= 0) *plaintext = fly_vec_from(out, (size_t)n, 1);
  free(out);
  return n >= 0;
}
fly_vec fly_crypto_ed25519_public(fly_slice secret) { return crypto_bytes(CRYPTO_ED_PUBLIC, secret, no_bytes, no_bytes, no_bytes, 32, "an Ed25519 secret key is 32 bytes"); }
fly_vec fly_crypto_ed25519_sign(fly_slice secret, fly_slice message) { return crypto_bytes(CRYPTO_ED_SIGN, secret, message, no_bytes, no_bytes, 64, "an Ed25519 secret key is 32 bytes"); }
bool fly_crypto_ed25519_verify(fly_slice key, fly_slice message, fly_slice signature) {
  uint8_t none;
  return crypto_op(CRYPTO_ED_VERIFY, key, message, signature, no_bytes, &none, 0) == 0;
}

bool fly_crypto_equal(fly_slice a, fly_slice b) {
  if (a.len != b.len) return false;
  volatile uint8_t d = 0;
  for (size_t i = 0; i < a.len; i++) d |= ((const uint8_t*)a.ptr)[i] ^ ((const uint8_t*)b.ptr)[i];
  return d == 0;
}

// ---- TLS (std/net's `connectTls`): OpenSSL's libssl, found when first used ----

#ifndef __wasm__
#define TLS_FNS(X) \
  X(const void*, TLS_client_method, (void)) X(void*, SSL_CTX_new, (const void*)) \
  X(int, SSL_CTX_set_default_verify_paths, (void*)) X(void, SSL_CTX_set_verify, (void*, int, void*)) \
  X(long, SSL_CTX_ctrl, (void*, int, long, void*)) X(uint64_t, SSL_CTX_set_options, (void*, uint64_t)) \
  X(void*, SSL_new, (void*)) X(void, SSL_free, (void*)) X(int, SSL_set_fd, (void*, int)) \
  X(long, SSL_ctrl, (void*, int, long, void*)) X(int, SSL_set1_host, (void*, const char*)) \
  X(void*, SSL_get0_param, (void*)) X(int, X509_VERIFY_PARAM_set1_ip_asc, (void*, const char*)) \
  X(int, SSL_connect, (void*)) X(int, SSL_get_error, (const void*, int)) X(long, SSL_get_verify_result, (const void*)) \
  X(int, SSL_read, (void*, void*, int)) X(int, SSL_write, (void*, const void*, int)) X(int, SSL_shutdown, (void*))

static struct {
  TLS_FNS(CRYPTO_FIELD)
} tls;
static void* tls_ctx;
static int tls_state;

static void tls_load(void) {
  if (__atomic_load_n(&tls_state, __ATOMIC_ACQUIRE) == 2) return;
  static const char* const names[] = {
#ifdef __APPLE__
    "libssl.3.dylib", "/opt/homebrew/opt/openssl@3/lib/libssl.3.dylib", "/usr/local/opt/openssl@3/lib/libssl.3.dylib",
    "libssl.4.dylib", "/opt/homebrew/opt/openssl@4/lib/libssl.4.dylib", "/usr/local/opt/openssl@4/lib/libssl.4.dylib",
#else
    "libssl.so.3", "libssl.so.4",
#endif
    NULL };
  int expected = 0;
  if (!__atomic_compare_exchange_n(&tls_state, &expected, 1, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
    while (__atomic_load_n(&tls_state, __ATOMIC_ACQUIRE) != 2) {}
    return;
  }
  void* h = fly_openssl_open("FLY_LIBSSL", names);
  if (!h) fly_panic("TLS needs OpenSSL 3 or later (libssl), which was not found: set FLY_LIBSSL to it");
  // libssl's own functions, and libcrypto's, which it brings: `dlsym` searches both.
  TLS_FNS(CRYPTO_LOAD_SSL)
  tls_ctx = tls.SSL_CTX_new(tls.TLS_client_method());
  if (!tls_ctx) fly_panic("libssl failed to start");
  // Verify the peer (SSL_VERIFY_PEER) against the system's roots, or those `SSL_CERT_FILE` and
  // `SSL_CERT_DIR` name; TLS 1.2 at least (SSL_CTRL_SET_MIN_PROTO_VERSION); and a peer that closes
  // without saying so ends the stream (SSL_OP_IGNORE_UNEXPECTED_EOF), as HTTP's lengths guard it.
  tls.SSL_CTX_set_default_verify_paths(tls_ctx);
  tls.SSL_CTX_set_verify(tls_ctx, 1, NULL);
  tls.SSL_CTX_ctrl(tls_ctx, 123, 0x0303, NULL);
  tls.SSL_CTX_set_options(tls_ctx, 1ull << 7);
  __atomic_store_n(&tls_state, 2, __ATOMIC_RELEASE);
}

// libssl's error codes: SSL_ERROR_SSL, SSL_ERROR_WANT_READ, SSL_ERROR_WANT_WRITE,
// SSL_ERROR_SYSCALL, SSL_ERROR_ZERO_RETURN.
enum { TLS_FAILED = 1, TLS_WANT_READ = 2, TLS_WANT_WRITE = 3, TLS_SYSCALL = 5, TLS_CLOSED = 6 };

// Waits until the socket can go on as libssl asks, after which `tls_cancelled` says whether the
// task was cancelled meanwhile.
#ifdef FLY_THREADS
#define TLS_WAIT(w, fd, err, ...) do { if (nonblocking()) IO_WAIT(w, (fd), (err) == TLS_WANT_WRITE, __VA_ARGS__); } while (0)
static bool tls_cancelled(void) { return nonblocking() && cancelled_here(); }
#else
#define TLS_WAIT(w, fd, err, ...) ((void)0)
static bool tls_cancelled(void) { return false; }
#endif

static bool is_address(const char* name) {
  for (const char* p = name; *p; p++) if (*p == ':') return true;
  for (const char* p = name; *p; p++) if (!(*p == '.' || (*p >= '0' && *p <= '9'))) return false;
  return true;
}
#endif

// It connects first, by a wait record of its own, and keeps the socket in the record until the
// handshake is done: what it was given to write to is written only as it ends.
int fly_connect_tls(fly_wait* w, fly_str host, uint16_t port, fly_socket* out) {
  fly_wait* inner;
  fly_socket* sock;
  W_BEGIN(w)
  w->p[0] = fly_alloc(sizeof(fly_wait));
  w->p[1] = fly_alloc(sizeof(fly_socket));
  *(fly_wait*)w->p[0] = (fly_wait){ 0 };
  for (;;) {
    w->n = fly_connect(w->p[0], host, port, w->p[1]);
    if (!fly_cx_now()->pend) break;
    W_SUSPEND(w, 0);
  }
  inner = w->p[0];
  sock = w->p[1];
  free(inner);
  // A simulated world's peers answer in the clear, as if TLS were there.
  if (w->n || !sock->fd) {
    *out = *sock;
    free(sock);
    return w->n;
  }
#ifdef __wasm__
  free(sock);
  *out = (fly_socket){ 0 };
  return FLY_IO_PERMISSION_DENIED;
#else
  tls_load();
  int fd = sock->fd - 1;
  char name[256];
  memcpy(name, host.ptr, host.len);
  name[host.len] = 0;
  void* s = tls.SSL_new(tls_ctx);
  tls.SSL_set_fd(s, fd);
  // A name is sent as SNI (SSL_CTRL_SET_TLSEXT_HOSTNAME) and checked against the certificate's
  // names; an address against its addresses.
  if (is_address(name)) {
    tls.X509_VERIFY_PARAM_set1_ip_asc(tls.SSL_get0_param(s), name);
  } else {
    tls.SSL_ctrl(s, 55, 0, name);
    tls.SSL_set1_host(s, name);
  }
  sock->tls = s;
  for (;;) {
    sock = w->p[1];
    int r = tls.SSL_connect(sock->tls);
    if (r == 1) break;
    int err = tls.SSL_get_error(sock->tls, r);
    bool cancelled = false;
    if (err == TLS_WANT_READ || err == TLS_WANT_WRITE) {
      TLS_WAIT(w, sock->fd - 1, err, 0);
      sock = w->p[1];
      if (!tls_cancelled()) continue;
      cancelled = true;
    }
    // X509_V_OK is 0: anything else is a certificate the system does not trust for this host.
    int k = cancelled ? FLY_IO_OK : tls.SSL_get_verify_result(sock->tls) != 0 ? FLY_IO_UNTRUSTED : err == TLS_SYSCALL && errno ? io_error(errno) : FLY_IO_RESET;
    tls.SSL_free(sock->tls);
    close(sock->fd - 1);
    free(sock);
    *out = (fly_socket){ 0 };
    return k;
  }
  *out = *(fly_socket*)w->p[1];
  free(w->p[1]);
  return FLY_IO_OK;
#endif
  W_END
  return 0;
}

// What it has found of the name, the address it is trying and the failure so far are kept in the
// record while it waits for an address to answer.
int fly_connect(fly_wait* w, fly_str host, uint16_t port, fly_socket* out) {
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
  (void)w;
  return FLY_IO_PERMISSION_DENIED;
#else
  int fd, r;
  W_BEGIN(w)
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
  w->p[0] = found;
  w->a[0] = FLY_IO_REFUSED;
  // Each address the name has, in the order the resolver gives them, until one answers.
  for (w->p[1] = found; w->p[1]; w->p[1] = ((struct addrinfo*)w->p[1])->ai_next) {
    struct addrinfo* a = w->p[1];
    fd = socket(a->ai_family, a->ai_socktype, a->ai_protocol);
    if (fd < 0) { w->a[0] = io_error(errno); continue; }
    bool waits = nonblocking();
    if (waits) {
      fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK);
#ifdef FLY_THREADS
      io_register(fd);
#endif
    }
    do { r = connect(fd, a->ai_addr, a->ai_addrlen); } while (r != 0 && errno == EINTR);
#ifdef FLY_THREADS
    if (r != 0 && errno == EINPROGRESS && waits) {
      // Connected, or refused, once the descriptor may be written. A task cancelled meanwhile
      // unwinds, with a socket of nothing.
      w->n = fd;
      IO_WAIT(w, fd, true, 0);
      fd = w->n;
      if (cancelled_here()) { close(fd); freeaddrinfo(w->p[0]); return FLY_IO_OK; }
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
      freeaddrinfo(w->p[0]);
      out->fd = fd + 1;
      return FLY_IO_OK;
    }
    w->a[0] = io_error(errno);
    close(fd);
  }
  freeaddrinfo(w->p[0]);
  return (int)w->a[0];
  W_END
  return 0;
#endif
}

int fly_sock_read(fly_wait* w, fly_socket* s, fly_slice buf, uint64_t* n) {
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
  (void)w;
  return FLY_IO_PERMISSION_DENIED;
#else
  W_BEGIN(w)
  if (s->tls) {
    for (;;) {
      int len = buf.len > 0x40000000 ? 0x40000000 : (int)buf.len;
      int k = tls.SSL_read(s->tls, buf.ptr, len);
      if (k > 0) { *n = (uint64_t)k; return FLY_IO_OK; }
      int err = tls.SSL_get_error(s->tls, k);
      if (err == TLS_CLOSED) return FLY_IO_OK;
      if (err == TLS_WANT_READ || err == TLS_WANT_WRITE) {
        TLS_WAIT(w, s->fd - 1, err, 0);
        if (tls_cancelled()) return FLY_IO_OK;
        continue;
      }
      if (err == TLS_SYSCALL && errno == EINTR) continue;
      return err == TLS_SYSCALL && errno ? io_error(errno) : FLY_IO_RESET;
    }
  }
  for (;;) {
    ssize_t k = read(s->fd - 1, buf.ptr, buf.len);
    if (k >= 0) { *n = (uint64_t)k; return FLY_IO_OK; }
    if (errno == EINTR) continue;
#ifdef FLY_THREADS
    if ((errno == EAGAIN || errno == EWOULDBLOCK) && nonblocking()) {
      IO_WAIT(w, s->fd - 1, false, 0);
      if (cancelled_here()) return FLY_IO_OK;
      continue;
    }
#endif
    return io_error(errno);
  }
  W_END
  return 0;
#endif
}

// How much it has written is kept in the record.
int fly_sock_write(fly_wait* w, fly_socket* s, fly_slice bytes) {
  if (!s->fd) {
    if (fly_fault()) return FLY_IO_BROKEN_PIPE;
    if (!s->out.ptr) s->out = fly_String_new();
    fly_String_push(&s->out, (fly_str){ bytes.ptr, bytes.len });
    return FLY_IO_OK;
  }
#ifdef __wasm__
  (void)w;
  return FLY_IO_PERMISSION_DENIED;
#else
#define done (*(size_t*)&w->a[0])
  W_BEGIN(w)
  done = 0;
  // libssl writes all it is given, or nothing; after it asks to wait, it is given the same again.
  while (s->tls && done < bytes.len) {
    size_t left = bytes.len - done;
    int len = left > 0x40000000 ? 0x40000000 : (int)left;
    int k = tls.SSL_write(s->tls, (const uint8_t*)bytes.ptr + done, len);
    if (k > 0) { done += (size_t)k; continue; }
    int err = tls.SSL_get_error(s->tls, k);
    if (err == TLS_WANT_READ || err == TLS_WANT_WRITE) {
      TLS_WAIT(w, s->fd - 1, err, 0);
      if (tls_cancelled()) return FLY_IO_OK;
      continue;
    }
    if (err == TLS_SYSCALL && errno == EINTR) continue;
    return err == TLS_SYSCALL && errno == EPIPE ? FLY_IO_BROKEN_PIPE : err == TLS_SYSCALL && errno ? io_error(errno) : FLY_IO_RESET;
  }
  while (done < bytes.len) {
    ssize_t k = write(s->fd - 1, (const uint8_t*)bytes.ptr + done, bytes.len - done);
    if (k >= 0) { done += (size_t)k; continue; }
    if (errno == EINTR) continue;
#ifdef FLY_THREADS
    if ((errno == EAGAIN || errno == EWOULDBLOCK) && nonblocking()) {
      IO_WAIT(w, s->fd - 1, true, 0);
      if (cancelled_here()) return FLY_IO_OK;
      continue;
    }
#endif
    return io_error(errno);
  }
  W_END
#undef done
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

// The response is made once, into memory the record keeps, and written by the record's write.
int fly_sock_status(fly_wait* w, fly_socket* s, unsigned code, fly_str body) {
  if (!s->fd) {
    if (fly_fault()) return FLY_IO_BROKEN_PIPE;
    sim_line(fly_str_lit("", 0), code, body);
    return FLY_IO_OK;
  }
  if (w->step == 0) {
    char head[96];
    int n = fmt_text(head, sizeof head, "HTTP/1.1 %u %s\r\nContent-Length: %zu\r\nConnection: close\r\n\r\n", code, code < 400 ? "OK" : "Error", body.len);
    uint8_t* all = fly_alloc((size_t)n + body.len + 1);
    memcpy(all, head, (size_t)n);
    if (body.len) memcpy(all + n, body.ptr, body.len);
    w->p[1] = all;
    w->a[1] = (int64_t)((size_t)n + body.len);
  }
  int e = fly_sock_write(w, s, (fly_slice){ w->p[1], (size_t)w->a[1] });
  if (fly_cx_now()->pend) return 0;
  free(w->p[1]);
  return e;
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
  // A TLS session says it is ending, if it can at once, and is freed.
  if (s->tls) {
    tls.SSL_shutdown(s->tls);
    tls.SSL_free(s->tls);
    s->tls = NULL;
  }
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
static void mt_run(void (*main)(void**), void (*entry)(void* task, void* closure, void** slot));
static void mt_point(fly_wait* w);
static void mt_cleaning(int d);
static void mt_sleep(fly_wait* w, uint64_t nanos);
static int mt_spawn(fly_wait* w, int scope, void (*entry)(void* task, void* closure, void** slot), const fly_fn* f, size_t size);
static void* mt_task_spawn(fly_wait* w, int scope, const fly_fn* f);
static void mt_task_cancel(void* h);
static int32_t mt_task_wait(fly_wait* w, void* h, fly_String* message);
static size_t mt_task_any(fly_wait* w, void* const* ts, size_t n);
static void mt_task_clone(void* h);
static void mt_task_drop(void* h);
static void mt_join(fly_wait* w, int task, void* out);
static int mt_scope_open(void);
static void mt_scope_close(fly_wait* w, int scope);
static void mt_scope_cancel(int scope);
static fly_chan mt_channel(void (*drop)(void*));
static void mt_receiver_gone(fly_chan ch);
static bool mt_send(fly_wait* w, fly_chan ch, const void* v, size_t size);
static bool mt_recv(fly_wait* w, fly_chan ch, void* out, size_t size);
static void mt_sender_gone(fly_chan ch);
static void mt_sender_clone(fly_chan ch);
typedef struct mt_task mt_task;
static void* mt_task_result(mt_task* t);
static void* mt_task_closure(mt_task* t);
#endif

// The scheduler of a simulated world is the runtime's Flyscript (rt/sched.fly): what is here is
// what it runs on. Each task is a record of what compiled code gave it — its entry, closure and
// result — its root machine's frame, and how deep it is in cleanup; it asks the scheduler for
// anything that touches another task, a scope, a channel or the clock, by a request it leaves
// here (`ASK`): answered at once, or the task stops, its machines returning to the scheduler, and
// is run again, its answer here, to go on from where it stopped.

typedef struct {
  // Its root machine's frame, and the frame arena of what it runs.
  void* slot;
  fly_frames frames;
  bool started, done;
  void (*entry)(void* task, void* closure, void** slot);
  // What it runs: `main`'s runner, or a closure, kept here (`fn`).
  void* closure;
  fly_fn fn;
  void* result;
  size_t size;
  fly_failure* error;
  // The panic it ended with, if it was forked.
  char* panic;
  bool forked;
  // A spawned task, as its `Task`s see it: its number while it runs; how many refer to it; how it
  // ended (FLY_TASK_*), with its panic's message, and whether that has been told.
  int32_t id;
  int handles;
  int8_t how;
  bool told;
  char* message;
  // How deep it is in cleanup, which a cancellation waits for.
  int cleaning;
  // What the scheduler delivers as it resumes the task, and its answer to what the task asked:
  // the task's own, for others ask while it waits.
  bool deliver_cancel, deliver_deadlock;
  int64_t reply;
  // What of the context the tasks share is the task's own while it waits: the panic its cleanup
  // runs for, and how deep in destructors it is.
  char* unwinding_panic;
  int destroying;
} task_t;

bool fly_tasks_on = false;
// The records by the scheduler's numbering, which channels share; and the one running.
static task_t** core_tasks;
static size_t core_cap;
static task_t* core_cur;

// What `fly_rt_answer` gives for what only the scheduler, on its own stack, can answer.
#define FLY_LATER (-INT64_C(0x7fffffffffffffff))

// The request the running task left, and its answer (rt/sched.fly's numbering).
enum { REQ_POINT = 1, REQ_SLEEP, REQ_SPAWN, REQ_JOIN_WAIT, REQ_JOIN_TAKE, REQ_SCOPE_OPEN, REQ_SCOPE_FAILED, REQ_SCOPE_WAIT, REQ_SCOPE_TAKE,
       REQ_UNCANCEL, REQ_CHANNEL, REQ_SEND, REQ_RECV, REQ_CLOSE, REQ_SENDER_DROP, REQ_SENDER_CLONE, REQ_DEAFEN, REQ_TAKE_ITEMS,
       REQ_SCOPE_CANCEL, REQ_TASK_KILL, REQ_TASK_ANY, REQ_IS_CANCELLED };
static struct { int kind; int64_t a[2]; void* p; } req;

void fly_panic_deadlock(void) { fly_panic("deadlock: every task is waiting"); }

// The scheduler, while it runs a task: what the task may ask of it on its own stack.
static uint8_t* core_sched;
void fly_core_sched(uint8_t* state) { core_sched = state; }

// A request of the scheduler's. What needs no choice of who runs next is answered here, at once,
// at `out`; anything else the task waits for: it suspends, false, and is resumed with the answer.
static bool ask_begin(int kind, int64_t a, int64_t b, void* p, int64_t* out) {
  req.kind = kind;
  req.a[0] = a;
  req.a[1] = b;
  req.p = p;
  if (kind != REQ_POINT && kind != REQ_SLEEP && kind != REQ_SPAWN && kind != REQ_CLOSE) {
    int64_t r = fly_rt_answer(core_sched, kind);
    if (r != FLY_LATER) { *out = r; return false; }
  }
  core_cur->reply = 0;
  fly_cx_now()->pend = FLY_PEND_WAIT;
  return true;
}

// The answer a waiting task is resumed with, and what the scheduler delivers with it.
static int64_t ask_answer(void) {
  task_t* me = core_cur;
  if (me->deliver_deadlock) fly_panic_deadlock();
  if (me->deliver_cancel) {
    me->deliver_cancel = false;
    fly_unwinding = true;
  }
  return me->reply;
}


// Asks, at a step of routine `w`, which returns `...` meanwhile if it must wait; the answer at `r`.
#define ASK(w, r, kind, a, b, p, ...) do { if (ask_begin((kind), (a), (b), (p), &(r))) { W_SUSPEND(w, __VA_ARGS__); (r) = ask_answer(); } } while (0)

// What is always answered at once, asked by code that cannot wait: a destructor, the runtime.
static int64_t ask_now(int kind, int64_t a, int64_t b, void* p) {
  int64_t r = 0;
  if (ask_begin(kind, a, b, p, &r)) fly_panic("the runtime waited where it cannot");
  return r;
}

int32_t fly_core_kind(void) { return req.kind; }
int64_t fly_core_arg(int32_t i) { return req.a[i]; }
uint8_t* fly_core_ptr(int32_t i) { (void)i; return req.p; }
uint8_t* fly_core_alloc(uint64_t size) { return fly_alloc((size_t)size); }
void fly_core_free(uint8_t* p) { free(p); }
void fly_core_reply(int64_t v) { core_cur->reply = v; }
void fly_core_answer(int32_t id, int64_t v) { core_tasks[id]->reply = v; }
uint64_t fly_core_clock(void) { return fly_clock; }
void fly_core_set_clock(uint64_t t) { fly_clock = t; }
int32_t fly_core_cleaning(int32_t id) { return core_tasks[id] ? core_tasks[id]->cleaning : 0; }

void fly_core_adopt(int32_t id, uint8_t* record) {
  if ((size_t)id >= core_cap) {
    size_t cap = core_cap ? core_cap : 16;
    while (cap <= (size_t)id) cap *= 2;
    core_tasks = realloc(core_tasks, cap * sizeof(task_t*));
    memset(core_tasks + core_cap, 0, (cap - core_cap) * sizeof(task_t*));
    core_cap = cap;
  }
  core_tasks[id] = (task_t*)record;
}

static void main_entry(void* task, void* closure, void** slot);

// A task's closure, boxed, which its entry drops once it has run: dropped here if a panic ended it
// first.
static void drop_task_closure(void* c) {
  fly_fn* f = c;
  if (f->drop) f->drop(f->env);
}

// A task's panic ends it (§5.7): a spawned task's is reported, and its scope goes on; a forked
// task's ends it as a failure would, its scope cancelled, and goes on in the task that opened the
// scope once every task in it has finished.
static void task_body(void* a) { task_t* t = a; t->entry(t, t->closure, &t->slot); }

// Runs the task's root machine until it ends or waits: whether it ended.
static bool task_main(task_t* t) {
  if (fly_try(task_body, t)) {
    char* m = panic_take();
    if (t->entry != main_entry) drop_task_closure(t->closure);
    if (t->forked) t->panic = m;
    else { t->how = FLY_TASK_PANICKED; t->message = m; }
    fly_cx_now()->pend = 0;
    return true;
  }
  if (fly_cx_now()->pend) {
    fly_cx_now()->pend = 0;
    return false;
  }
  if (FLY_FAILED) { t->error = fly_err; fly_err = NULL; }
  if (!t->forked) t->how = fly_unwinding ? FLY_TASK_CANCELLED : FLY_TASK_DONE;
  fly_unwinding = false;
  return true;
}

// A spawned task's record is let go once it has ended and no `Task` refers to it, its panic, if no
// `wait` gave it, reported then (§5.7).
static void task_release(task_t* t) {
  if (t->how == FLY_TASK_PANICKED && !t->told) report_spawned_panic(t->message);
  panic_free(t->message);
  free(t->result);
  free(t);
}

// Task `id` has ended, having run or not (cancelled before it began): its frames are let go, and a
// spawned task's number, which the scheduler gives out again.
void fly_core_end(int32_t id, bool ran) {
  task_t* t = core_tasks[id];
  if (!ran) {
    drop_task_closure(t->closure);
    if (!t->forked) t->how = FLY_TASK_CANCELLED;
  }
  fly_frames_free(&t->frames);
  if (t->forked) return;
  core_tasks[id] = NULL;
  if (t->handles == 0) task_release(t);
}

// Runs task `id` until it asks again, 0, or ends, 1, or ends failing, 2.
// The task runs on the program's own stack, its frames in its own arena, until it ends or waits.
int32_t fly_core_run(int32_t id, bool deadlock, bool cancel) {
  task_t* t = core_tasks[id];
  t->deliver_deadlock = deadlock;
  t->deliver_cancel = cancel;
  core_cur = t;
  fly_ctx* cx = fly_cx_now();
  fly_frames* frames = cx->frames;
  cx->frames = &t->frames;
  cx->panic = t->unwinding_panic;
  cx->destroying = t->destroying;
  t->done = task_main(t);
  // Stopped, the task holds only the frames it is in.
  fly_spare_free(cx);
  cx = fly_cx_now();
  cx->frames = frames;
  t->unwinding_panic = cx->panic;
  t->destroying = cx->destroying;
  cx->panic = NULL;
  cx->destroying = 0;
  if (!t->done) return 0;
  return t->error || t->panic ? 2 : 1;
}

// A task of `entry`, given `main`'s runner or a copy of the closure at `f`, and a result of `size`
// bytes, if it gives one.
static task_t* new_task(void (*entry)(void* task, void* closure, void** slot), void* closure, const fly_fn* f, size_t size) {
  task_t* t = fly_alloc(sizeof(task_t));
  t->forked = entry != fly_task_void;
  t->entry = entry;
  if (f) t->fn = *f; else t->fn.fn = closure;
  t->closure = &t->fn;
  t->size = size;
  t->result = size ? fly_alloc(size) : NULL;
  return t;
}

void fly_point(fly_wait* w) {
#ifdef FLY_THREADS
  if (threads) { mt_point(w); return; }
#endif
  if (!fly_tasks_on) return;
  W_BEGIN(w)
  int64_t r;
  ASK(w, r, REQ_POINT, 0, 0, NULL);
  (void)r;
  W_END
}

static void cleaning(int d) {
#ifdef FLY_THREADS
  if (threads) { mt_cleaning(d); return; }
#endif
  if (fly_tasks_on) core_cur->cleaning += d;
}

// Sleeping waits for the virtual clock, which passes only when no task can run; without a
// simulated world, for the machine's.
void fly_sleep(fly_wait* w, uint64_t nanos) {
#ifdef FLY_THREADS
  if (threads) { mt_sleep(w, nanos); return; }
#endif
  world_load();
  if (!world.simulated) {
    struct timespec ts = { (time_t)(nanos / 1000000000u), (long)(nanos % 1000000000u) };
    while (nanosleep(&ts, &ts) != 0) {}
    return;
  }
  if (!fly_tasks_on) { fly_clock += nanos; return; }
  W_BEGIN(w)
  int64_t r;
  ASK(w, r, REQ_SLEEP, (int64_t)nanos, 0, NULL);
  (void)r;
  W_END
}

static void main_entry(void* task, void* closure, void** slot) { (void)task; ((void (*)(void**))((fly_fn*)closure)->fn)(slot); }

// The program's root (§5.7): a panic that unwinds `run` ends here, and with it the program. With
// no tasks nothing it does waits.
typedef struct { void (*run)(void**); } root_t;
static void root_body(void* a) {
  void* slot = NULL;
  ((root_t*)a)->run(&slot);
  if (fly_pending) fly_panic("the program waited with no tasks to wait for");
}
void fly_root(void (*run)(void**)) {
  root_t r = { run };
  if (fly_try(root_body, &r)) panic_exit(fly_cx_now()->panic);
}

#ifdef FLY_THREADS
// The simulated world's tasks, on the program's context, from the thread they run on.
static void* sim_tasks(void* t0) {
  uintptr_t limit = fly_ctx0.limit;
  fly_ctx0.limit = stack_limit0;
  fly_rt_tasks(world.seed, (uint8_t*)t0);
  fly_ctx0.limit = limit;
  return NULL;
}
#endif

void fly_tasks_run(void (*main)(void**)) {
  fly_tasks_on = true;
  world_load();
#ifdef FLY_THREADS
  if (!world.simulated) { mt_run(main, main_entry); return; }
#endif
  task_t* t0 = new_task(main_entry, (void*)main, NULL, 0);
#ifdef FLY_THREADS
  run_on_big_stack(sim_tasks, t0);
#else
  fly_rt_tasks(world.seed, (uint8_t*)t0);
#endif
  // The main task's root is the program's: its panic, its cleanup done, ends the program.
  if (t0->panic) panic_exit(t0->panic);
  if (t0->error) fly_err = t0->error;
}

// Starts a task of `entry`, given a copy of the closure at `f`, made as it is first called.
int fly_spawn(fly_wait* w, int scope, void (*entry)(void* task, void* closure, void** slot), const fly_fn* f, size_t size) {
#ifdef FLY_THREADS
  if (threads) return mt_spawn(w, scope, entry, f, size);
#endif
  int64_t r = 0;
  W_BEGIN(w)
  ASK(w, r, REQ_SPAWN, scope, 1, new_task(entry, NULL, f, size), 0);
  W_END
  return (int)r;
}

// ---- `Task` (§6.1): a spawned task's record, which its `Task`s refer to ----

void* fly_task_spawn(fly_wait* w, int scope, const fly_fn* f) {
#ifdef FLY_THREADS
  if (threads) return mt_task_spawn(w, scope, f);
#endif
  int64_t r = 0;
  W_BEGIN(w)
  w->p[0] = new_task(fly_task_void, NULL, f, 0);
  ((task_t*)w->p[0])->how = FLY_TASK_RUNNING;
  ((task_t*)w->p[0])->handles = 1;
  ASK(w, r, REQ_SPAWN, scope, 0, w->p[0], NULL);
  ((task_t*)w->p[0])->id = (int32_t)r;
  W_END
  return w->p[0];
}

void fly_task_cancel(void* h) {
#ifdef FLY_THREADS
  if (threads) { mt_task_cancel(h); return; }
#endif
  task_t* t = h;
  if (t->how == FLY_TASK_RUNNING) ask_now(REQ_TASK_KILL, t->id, 0, NULL);
}

// How the task ended, once it has: FLY_TASK_*, a panic's message written at `message`.
int32_t fly_task_wait(fly_wait* w, void* h, fly_String* message) {
#ifdef FLY_THREADS
  if (threads) return mt_task_wait(w, h, message);
#endif
  task_t* t = h;
  int64_t r;
  W_BEGIN(w)
  while (t->how == FLY_TASK_RUNNING) {
    ASK(w, r, REQ_JOIN_WAIT, t->id, 0, NULL, 0);
    if (fly_unwinding) return FLY_TASK_DONE;
  }
  W_END
  (void)r;
  if (t->how == FLY_TASK_PANICKED) {
    t->told = true;
    *message = fly_String_from(fly_str_lit(t->message, strlen(t->message)));
  }
  return t->how;
}

// The index of the first of `ts` to have ended, once one has.
size_t fly_task_any(fly_wait* w, void* const* ts, size_t n) {
  if (n == 0) fly_panic("waited for any of no tasks");
#ifdef FLY_THREADS
  if (threads) return mt_task_any(w, ts, n);
#endif
  int64_t r;
  W_BEGIN(w)
  w->p[0] = fly_alloc(n * sizeof(int32_t));
  for (;;) {
    for (size_t i = 0; i < n; i++) {
      task_t* t = ts[i];
      if (t->how != FLY_TASK_RUNNING) { free(w->p[0]); return i; }
      ((int32_t*)w->p[0])[i] = t->id;
    }
    ASK(w, r, REQ_TASK_ANY, (int64_t)n, 0, w->p[0], 0);
    if (fly_unwinding) { free(w->p[0]); return 0; }
  }
  W_END
  (void)r;
  return 0;
}

void* fly_task_clone(void* h) {
#ifdef FLY_THREADS
  if (threads) { mt_task_clone(h); return h; }
#endif
  ((task_t*)h)->handles++;
  return h;
}

void fly_task_drop(void* h) {
  if (!h) return;
#ifdef FLY_THREADS
  if (threads) { mt_task_drop(h); return; }
#endif
  task_t* t = h;
  if (--t->handles == 0 && t->how != FLY_TASK_RUNNING) task_release(t);
}

void fly_task_void(void* task, void* closure, void** slot) {
  (void)task;
  fly_fn* f = closure;
  ((fly_unit (*)(void*, void**, void*))f->fn)(f->env, slot, NULL);
  // Stopped, it goes on; ended by a panic, the task's end drops what it was given.
  if (fly_pending || fly_cx_now()->panicking) return;
  if (f->drop) f->drop(f->env);
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

// A forked task's value, or its failure, raised.
void fly_join(fly_wait* w, int task, void* out) {
#ifdef FLY_THREADS
  if (threads) { mt_join(w, task, out); return; }
#endif
  int64_t r;
  W_BEGIN(w)
  ASK(w, r, REQ_JOIN_WAIT, task, 0, NULL);
  W_END
  (void)r;
  if (fly_unwinding) return;
  task_t* t = core_tasks[task];
  // It panicked, which cancels the scope and the joiner with it.
  if (t->panic) { fly_unwinding = true; return; }
  if (t->error) {
    ask_now(REQ_JOIN_TAKE, task, 0, NULL);
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
  return (int)ask_now(REQ_SCOPE_OPEN, 0, 0, NULL);
}

// The end of a scope's body, however it ended: every task started in it is waited for, then
// the scope fails as its body or its first failed task did (§6.1). Cancelled while it waits, the
// task cancels them, and waits on. What it found as the body ended is kept in the record.
void fly_scope_close(fly_wait* w, int sid, bool body_failed) {
  (void)body_failed;
#ifdef FLY_THREADS
  if (threads) { mt_scope_close(w, sid); return; }
#endif
  int64_t more;
  W_BEGIN(w)
  // The body left by unwinding — a failure, a cancellation — cancels the scope's tasks (§6.1).
  w->n = fly_unwinding;
  fly_unwinding = false;
  w->p[0] = fly_err;
  fly_err = NULL;
  if (w->n || w->p[0]) ask_now(REQ_SCOPE_CANCEL, sid, 0, NULL);
  for (;;) {
    ASK(w, more, REQ_SCOPE_WAIT, sid, 0, NULL);
    if (fly_unwinding) {
      fly_unwinding = false;
      ask_now(REQ_SCOPE_CANCEL, sid, 0, NULL);
    } else if (!more) {
      break;
    }
  }
  W_END
  bool unwinding = w->n;
  void* err = w->p[0];
  // The body unwound because a task failed: the scope raises that instead, the cancellation its
  // failure made over. Otherwise one from outside — its own scope's, or its `Task`'s — goes on,
  // whether it came in the body or as the task waited.
  bool failed_scope = ask_now(REQ_SCOPE_FAILED, sid, 0, NULL);
  if (unwinding && !failed_scope) { fly_unwinding = true; if (err) free(err); return; }
  if (failed_scope) ask_now(REQ_UNCANCEL, 0, 0, NULL);
  if (err) { fly_err = err; return; }
  int64_t failed = ask_now(REQ_SCOPE_TAKE, sid, 0, NULL);
  if (failed >= 0 && core_tasks[failed]->panic) {
    char* m = core_tasks[failed]->panic;
    core_tasks[failed]->panic = NULL;
    panic_again(m);
  }
  if (failed >= 0) { fly_err = core_tasks[failed]->error; core_tasks[failed]->error = NULL; return; }
  if (ask_now(REQ_IS_CANCELLED, 0, 0, NULL)) fly_unwinding = true;
}

// A panic unwound the body of scope `sid` (§5.7), caught where the scope is: its tasks are
// cancelled, as a failure would cancel them, and once every one has finished the panic goes on.
void fly_scope_panicked(fly_wait* w, int sid) {
#ifdef FLY_THREADS
  if (threads) {
    if (w->step == 0) { w->p[0] = panic_take(); mt_scope_cancel(sid); }
    mt_scope_close(w, sid);
    if (fly_pending) return;
    panic_again(w->p[0]);
  }
#endif
  int64_t more;
  W_BEGIN(w)
  w->p[0] = panic_take();
  ask_now(REQ_SCOPE_CANCEL, sid, 0, NULL);
  for (;;) {
    ASK(w, more, REQ_SCOPE_WAIT, sid, 0, NULL);
    if (fly_unwinding) fly_unwinding = false;
    else if (!more) break;
  }
  W_END
  ask_now(REQ_UNCANCEL, 0, 0, NULL);
  int64_t failed = ask_now(REQ_SCOPE_TAKE, sid, 0, NULL);
  if (failed >= 0) { panic_free(core_tasks[failed]->panic); core_tasks[failed]->panic = NULL; free(core_tasks[failed]->error); core_tasks[failed]->error = NULL; }
  panic_again(w->p[0]);
}

// ---- channels ----
//
// The scheduler keeps what is sent; a channel's ends here are its number, and what drops a
// message it will not deliver, which a channel's receiving end keeps (`fly_receiver_drop`).

static void (**chan_drops)(void*);
static size_t chan_cap;

fly_chan fly_channel(void (*drop)(void*)) {
#ifdef FLY_THREADS
  if (threads) return mt_channel(drop);
#endif
  int id = (int)ask_now(REQ_CHANNEL, 0, 0, NULL);
  if ((size_t)id >= chan_cap) {
    size_t cap = chan_cap ? chan_cap : 16;
    while (cap <= (size_t)id) cap *= 2;
    chan_drops = realloc(chan_drops, cap * sizeof(*chan_drops));
    chan_cap = cap;
  }
  chan_drops[id] = drop;
  return (fly_chan){ id };
}

// Where a message waits while its task does: in the wait record itself, which is in the task's
// frame and does not move, if it fits in the record's two words, and otherwise on the heap.
static void* wait_buffer(fly_wait* w, size_t size) {
  if (size <= sizeof w->a) { w->n = 1; return w->a; }
  w->n = 0;
  return fly_alloc(size ? size : 1);
}

static void wait_buffer_free(fly_wait* w) {
  if (!w->n) free(w->p[0]);
}

// Whether the message went to the channel: once its receiver is gone, it is dropped instead.
// The message is the routine's own, copied as it is first called: the scheduler reads it once the
// task has given way, when the caller's copy may be gone.
bool fly_send(fly_wait* w, fly_chan ch, const void* v, size_t size) {
#ifdef FLY_THREADS
  if (threads) return mt_send(w, ch, v, size);
#endif
  int64_t r = 0;
  W_BEGIN(w)
  w->p[0] = wait_buffer(w, size);
  memcpy(w->p[0], v, size);
  ASK(w, r, REQ_SEND, ch.ch, (int64_t)size, w->p[0], false);
  if (r) { wait_buffer_free(w); return true; }
  if (chan_drops[ch.ch]) chan_drops[ch.ch](w->p[0]);
  wait_buffer_free(w);
  ASK(w, r, REQ_POINT, 0, 0, NULL, false);
  W_END
  return false;
}

// The next message, or false once the channel is closed and drained (or the task unwinds). The
// scheduler puts it where the routine keeps it, which the caller's copy is filled from.
bool fly_recv(fly_wait* w, fly_chan ch, void* out, size_t size) {
#ifdef FLY_THREADS
  if (threads) return mt_recv(w, ch, out, size);
#endif
  int64_t r = 0;
  W_BEGIN(w)
  w->p[0] = wait_buffer(w, size);
  for (;;) {
    ASK(w, r, REQ_RECV, ch.ch, 0, w->p[0], false);
    if (r != 2 || fly_unwinding) break;
  }
  W_END
  if (r == 1) memcpy(out, w->p[0], size);
  wait_buffer_free(w);
  return r == 1 && !fly_unwinding;
}

// The receiving end dropped: what is sent from now on is dropped, and the channel freed once its
// senders are gone too. What it holds is dropped now: a message may hold a reply someone waits
// for. It is taken out first, as dropping one may reach this channel.
void fly_receiver_drop(fly_chan* ch) {
#ifdef FLY_THREADS
  if (threads) { if (ch->ch) mt_receiver_gone(*ch); ch->ch = 0; return; }
#endif
  if (!ch->ch) return;
  int id = ch->ch;
  ch->ch = 0;
  int64_t held = ask_now(REQ_DEAFEN, id, 0, NULL);
  size_t n = (size_t)(held >> 32), size = (size_t)(held & 0xffffffff);
  uint8_t* items = fly_alloc(n * size + 1);
  ask_now(REQ_TAKE_ITEMS, id, 0, items);
  if (chan_drops[id]) for (size_t i = 0; i < n; i++) chan_drops[id](items + i * size);
  free(items);
}

void fly_close(fly_wait* w, fly_chan ch) {
#ifdef FLY_THREADS
  if (threads) { if (w->step == 0) mt_sender_gone(ch); mt_point(w); return; }
#endif
  int64_t r;
  W_BEGIN(w)
  ASK(w, r, REQ_CLOSE, ch.ch, 0, NULL);
  (void)r;
  W_END
}

// A destructor does not suspend: a sender dropped closes its channel then and there.
void fly_sender_drop(fly_chan* ch) {
#ifdef FLY_THREADS
  if (threads) { if (ch->ch) mt_sender_gone(*ch); ch->ch = 0; return; }
#endif
  if (ch->ch) ask_now(REQ_SENDER_DROP, ch->ch, 0, NULL);
  ch->ch = 0;
}

fly_chan fly_sender_clone(const fly_chan* ch) {
#ifdef FLY_THREADS
  if (threads) { mt_sender_clone(*ch); return *ch; }
#endif
  ask_now(REQ_SENDER_CLONE, ch->ch, 0, NULL);
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

static bool spin_trylock(spin_t* l) { return !__atomic_load_n(&l->v, __ATOMIC_RELAXED) && !__atomic_exchange_n(&l->v, 1, __ATOMIC_ACQUIRE); }

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

// A task's record holds what every task needs as it waits; what only some need is apart: a forked
// task's entry and result follow its record (`mt_fork`), and what waits for it is in a record made
// by the first to (`mt_join`).
struct mt_task {
  // What it runs: a closure, or, for `main`, its runner as the function.
  fly_fn fn;
  mt_scope* scope;
  worker* home;
  // Its root machine's frame, and the frame arena of what it runs.
  void* slot;
  fly_frames frames;
  // How it ended: its failure, if it failed; its panic, if it panicked (§5.7), which while it waits
  // in cleanup a panic runs is that panic, and the rest of the context is its worker's.
  fly_failure* error;
  char* panic;
  // What waits for it, once anything has: set once, and read once `finished` is (`mt_join_of`).
  struct mt_join* join;
  // The queue it waits in, if it waits, and its neighbours there.
  waitq* waiting;
  mt_task *wnext, *wprev;
  // Its neighbours among its scope's tasks still alive.
  mt_task *snext, *sprev;
  // The next task in an inbox.
  mt_task* rnext;
  // A spawned task, as its `Task`s see it, which share one reference: how many there are; how it
  // ended (FLY_TASK_*); whether its panic has been told, which whoever tells it first sets.
  int handles;
  // Who still refers to it: itself while it lives, its scope while it does, and a forked task's
  // `Fiber` until it is joined.
  int refs;
  // How deep it is in cleanup, which a cancellation waits for, and in destructors.
  int cleaning, destroying;
  int8_t how;
  bool forked, told, finished;
  // Cancelled by its scope, which may take that back, or by its `Task`, for good (`killed`).
  bool started, cancelled, killed, yielded;
};

// One waiting for any of several tasks, among one of them's: it is told by `fired` and woken in `q`.
struct mt_any { struct mt_any* next; waitq* q; bool fired; };

// What waits for a task: its joiners, and those waiting for any of several tasks it is among, under
// the queue's lock, which `finished` is read under too. It is made by the first to wait, and put
// in the task by an exchange; a task that ends sets `finished` before it looks for it, and one that
// waits looks at `finished` after it has put it in, both in one order, so that one sees the other.
struct mt_join { waitq q; struct mt_any* anys; };

static struct mt_join* mt_join_of(mt_task* t) {
  struct mt_join* j = __atomic_load_n(&t->join, __ATOMIC_SEQ_CST);
  if (j) return j;
  struct mt_join* made = fly_alloc(sizeof(struct mt_join));
  if (__atomic_compare_exchange_n(&t->join, &j, made, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)) return made;
  free(made);
  return j;
}

// A forked task's entry, and its result, of `size` bytes, after its record.
struct mt_fork { void (*entry)(void* task, void* closure, void** slot); uint32_t size; _Alignas(16) char result[]; };
#define MT_FORK_AT ((sizeof(mt_task) + 15) & ~(size_t)15)
static struct mt_fork* mt_fork_of(mt_task* t) { return (struct mt_fork*)((char*)t + MT_FORK_AT); }

// A forked task, or `main`, runs its entry; any other its closure, by `fly_task_void`.
static void (*mt_entry(mt_task* t))(void*, void*, void**) { return t->forked ? mt_fork_of(t)->entry : fly_task_void; }

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

// A channel: its monitor, the receivers waiting under it; what it holds, the runtime's Flyscript's
// (rt/mt.fly); and what drops a message it will not deliver.
typedef struct { waitq q; uint8_t* state; void (*drop)(void*); } mt_chan;

// Each worker's timer: a hierarchical timing wheel (Varghese and Lauck, as tokio's), of six levels
// of 64 slots, a slot of level `k` the 64^k milliseconds whose digits above `k` are the wheel's
// time's. What is in a slot is the wait records of the sleeps due then, linked through the records
// themselves, which are in the sleeping tasks' frames: a sleep takes nothing more, and is put in
// and taken out at once. A sleeping task waits in `q`, under whose lock the wheel is, so that a
// cancellation finds it as it finds any task that waits; tasks going to sleep on every core at
// once do not queue for one lock. `due` is when the wheel next has something to do, in the
// clock's nanoseconds, or 0; any worker does it once it is due, so a worker asleep holds up none.
enum { WHEEL_LEVELS = 6, WHEEL_SLOTS = 64 };
typedef struct {
  waitq q;
  fly_wait* slot[WHEEL_LEVELS][WHEEL_SLOTS];
  uint64_t occupied[WHEEL_LEVELS];
  // The time it has come to, in milliseconds, and how many sleeps are in it.
  uint64_t now;
  size_t n;
  uint64_t due;
} sleep_timer;

struct worker {
  int index;
  sleep_timer timer;
  // Asleep for want of work: `parked` set, waiting under its own lock for whoever has work to clear
  // it and wake it, so that workers going to sleep and waking do not queue for one lock.
  pthread_mutex_t park_mu;
  pthread_cond_t park_cv;
  int parked;
  // The context of the task running here.
  fly_ctx run_ctx;
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
  // The lock the task running here gives back once it has stopped to wait (`to_worker`).
  spin_t* release;
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

// How many workers are asleep for want of work, each on its own condition (`worker.parked`).
static int idlers;

// Wakes worker `w` if it is asleep: whether it was.
static bool unpark_worker(worker* w) {
  int one = 1;
  if (!__atomic_compare_exchange_n(&w->parked, &one, 0, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)) return false;
  pthread_mutex_lock(&w->park_mu);
  pthread_cond_signal(&w->park_cv);
  pthread_mutex_unlock(&w->park_mu);
  return true;
}

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
    // Starting from a worker of its own, so that those woken spread.
    worker* me = this_worker;
    int at = me ? me->index : 0;
    for (int k = 1; k <= nworkers; k++) {
      if (unpark_worker(&workers[(at + k) % nworkers])) return;
    }
  }
  if (__atomic_load_n(&pollers, __ATOMIC_SEQ_CST) > 0) poll_wake();
}

// Every idle worker wakes: the program's thread among them, which the end of `main` is for.
static void notify_all(void) {
  __atomic_thread_fence(__ATOMIC_SEQ_CST);
  for (long k = __atomic_load_n(&pollers, __ATOMIC_SEQ_CST); k > 0; k--) poll_wake();
  if (__atomic_load_n(&idlers, __ATOMIC_SEQ_CST) == 0) return;
  for (int k = 0; k < nworkers; k++) unpark_worker(&workers[k]);
}

static void task_unref(mt_task* t) {
  if (__atomic_sub_fetch(&t->refs, 1, __ATOMIC_ACQ_REL) > 0) return;
  panic_free(t->panic);
  free(t->join);
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

static bool is_cancelled(mt_task* t) {
  return __atomic_load_n(&t->cancelled, __ATOMIC_ACQUIRE) || __atomic_load_n(&t->killed, __ATOMIC_ACQUIRE);
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

// The running task gives its worker up, until it is resumed: it returns to the worker, suspended.
// A task that waits holds the lock of what it waits for until then: its worker gives the lock back
// once the task has stopped, for until then nothing may wake it, which would let another worker
// resume it while it is still running here.
static void to_worker(mt_task* t, spin_t* release) {
  (void)t;
  this_worker->release = release;
  fly_cx_now()->pend = FLY_PEND_WAIT;
}

// The running task waits in `q`, whose lock is held, until something wakes it: true, and it
// suspends, the lock released once it has; a cancellation wakes it too, unless it waits for its
// scope's tasks, which it must. Cancelled already, it does not wait: false, the lock released.
static bool wait_in(waitq* q, bool cancellable) {
  mt_task* t = running;
  q_append(q, t);
  __atomic_store_n(&t->waiting, q, __ATOMIC_SEQ_CST);
  if (cancellable && is_cancelled(t) && !__atomic_load_n(&t->cleaning, __ATOMIC_SEQ_CST)) {
    q_remove(q, t);
    __atomic_store_n(&t->waiting, NULL, __ATOMIC_SEQ_CST);
    spin_unlock(&q->lock);
    return false;
  }
  t->yielded = false;
  __atomic_fetch_sub(&runnable, 1, __ATOMIC_SEQ_CST);
  to_worker(t, &q->lock);
  return true;
}
#define WAIT_IN(w, q, cancellable, ...) do { if (wait_in((q), (cancellable))) W_SUSPEND(w, __VA_ARGS__); } while (0)

// Whether the running task has been cancelled: it unwinds from here (§6.1).
static bool cancelled_here(void) {
  mt_task* t = running;
  if (t && is_cancelled(t) && !__atomic_load_n(&t->cleaning, __ATOMIC_SEQ_CST)) {
    fly_unwinding = true;
    return true;
  }
  return false;
}

// A monitor, for the runtime's Flyscript (rt/mt.fly): a wait queue and its lock.
void fly_mon_lock(uint8_t* m) { spin_lock(&((waitq*)m)->lock); }
void fly_mon_unlock(uint8_t* m) { spin_unlock(&((waitq*)m)->lock); }
void fly_mon_wake_one(uint8_t* m) { wake_one((waitq*)m); }
void fly_mon_wake_all(uint8_t* m) { wake_all((waitq*)m); }
void fly_core_relax(void) { relax(); }
void fly_core_yield(void) { sched_yield(); }

// A task waiting is woken to see that it is cancelled; one in cleanup is left to finish it.
static void wake_cancelled(mt_task* t);

// Cancels a task: one running or queued sees it at its next scheduling point; one waiting is woken.
static void cancel_task(mt_task* t) {
  __atomic_store_n(&t->cancelled, true, __ATOMIC_SEQ_CST);
  wake_cancelled(t);
}

static void kill_task(mt_task* t) {
  __atomic_store_n(&t->killed, true, __ATOMIC_SEQ_CST);
  wake_cancelled(t);
}

static void wake_cancelled(mt_task* t) {
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
static void mt_point(fly_wait* w) {
  mt_task* t = running;
  W_BEGIN(w)
  if (!t || cancelled_here()) return;
  if (__atomic_load_n(&this_worker->inhead, __ATOMIC_RELAXED)) {
    t->yielded = true;
    to_worker(t, NULL);
    W_SUSPEND(w);
    cancelled_here();
  }
  W_END
}

// ---- sleeping: each worker's timer wheel (`sleep_timer`) ----

// A sleep's wait record, while the sleep is in a wheel: when it is due, in milliseconds (`a[0]`);
// whose it is (`a[1]`); the records before and after it in its slot (`p[1]`, `p[0]`); and which
// worker's wheel and slot it is in, or -1 once it is in none (`n`), which the waking worker sets
// before it wakes the task, and which the task, going on, reads to see whether to take it out.
#define SLEEP_DUE(w) ((uint64_t)(w)->a[0])
#define SLEEP_TASK(w) ((mt_task*)(intptr_t)(w)->a[1])
#define SLEEP_NEXT(w) (*(fly_wait**)&(w)->p[0])
#define SLEEP_PREV(w) (*(fly_wait**)&(w)->p[1])
enum { WHEEL_SPAN = WHEEL_LEVELS * 6, WHEEL_CELLS = WHEEL_LEVELS * WHEEL_SLOTS };

static uint64_t now_ms(void) { return now_ns() / 1000000u; }

// The level a time due falls in from the wheel's: that of the highest digit, of six bits, in which
// the two differ; one past the wheel's reach goes in its last level, and on again from there.
static int wheel_level(uint64_t now, uint64_t due) {
  uint64_t differ = (now ^ due) | (WHEEL_SLOTS - 1);
  if (differ >> WHEEL_SPAN) differ = ((uint64_t)1 << WHEEL_SPAN) - 1;
  return (63 - __builtin_clzll(differ)) / 6;
}

static void wheel_link(sleep_timer* tm, int worker, fly_wait* w) {
  uint64_t due = SLEEP_DUE(w) < tm->now ? tm->now : SLEEP_DUE(w);
  int k = wheel_level(tm->now, due);
  int i = (int)((due >> (6 * k)) & (WHEEL_SLOTS - 1));
  fly_wait** head = &tm->slot[k][i];
  SLEEP_PREV(w) = NULL;
  SLEEP_NEXT(w) = *head;
  if (*head) SLEEP_PREV(*head) = w;
  *head = w;
  tm->occupied[k] |= (uint64_t)1 << i;
  __atomic_store_n(&w->n, worker * WHEEL_CELLS + k * WHEEL_SLOTS + i, __ATOMIC_RELEASE);
}

static void wheel_unlink(sleep_timer* tm, fly_wait* w) {
  int cell = w->n % WHEEL_CELLS, k = cell / WHEEL_SLOTS, i = cell % WHEEL_SLOTS;
  if (SLEEP_PREV(w)) SLEEP_NEXT(SLEEP_PREV(w)) = SLEEP_NEXT(w); else tm->slot[k][i] = SLEEP_NEXT(w);
  if (SLEEP_NEXT(w)) SLEEP_PREV(SLEEP_NEXT(w)) = SLEEP_PREV(w);
  if (!tm->slot[k][i]) tm->occupied[k] &= ~((uint64_t)1 << i);
  __atomic_store_n(&w->n, -1, __ATOMIC_RELEASE);
}

// When the wheel next has a slot to take up, in milliseconds, and its level, or false: the first
// level with anything in it, whose slots come before all those of the levels above; in it, the
// first slot from the wheel's time on — at level 0 that time's own, above it one a whole turn on if
// its digit is the time's, which a sleep beyond the wheel's reach can be.
static bool wheel_next(const sleep_timer* tm, uint64_t* at, int* level) {
  for (int k = 0; k < WHEEL_LEVELS; k++) {
    uint64_t occ = tm->occupied[k];
    if (!occ) continue;
    int shift = 6 * k;
    unsigned digit = (unsigned)((tm->now >> shift) & (WHEEL_SLOTS - 1));
    uint64_t rot = (occ >> digit) | (digit ? occ << (64 - digit) : 0);
    // Above level 0 the time's own slot is a whole turn on, after every other.
    unsigned ahead = k == 0 ? (unsigned)__builtin_ctzll(rot) : (rot & ~(uint64_t)1) ? (unsigned)__builtin_ctzll(rot & ~(uint64_t)1) : 64;
    uint64_t span = (uint64_t)1 << shift;
    *at = (tm->now & ~(span - 1)) + (uint64_t)ahead * span;
    *level = k;
    return true;
  }
  return false;
}

// The wheel brought to time `until`: each slot due on the way taken up, its sleeps that are due
// woken, and the rest put in again, lower down. Under the wheel's lock.
static void wheel_advance(sleep_timer* tm, int worker, uint64_t until) {
  uint64_t at;
  int k;
  while (wheel_next(tm, &at, &k) && at <= until) {
    tm->now = at;
    int i = (int)((at >> (6 * k)) & (WHEEL_SLOTS - 1));
    fly_wait* w = tm->slot[k][i];
    tm->slot[k][i] = NULL;
    tm->occupied[k] &= ~((uint64_t)1 << i);
    while (w) {
      fly_wait* next = SLEEP_NEXT(w);
      // Due by the time the wheel is brought to, it wakes now, rather than going down a level first.
      if (SLEEP_DUE(w) <= until) {
        __atomic_store_n(&w->n, -1, __ATOMIC_RELEASE);
        tm->n--;
        // Its task cannot have gone on past its sleep, for which it takes this lock.
        mt_task* t = SLEEP_TASK(w);
        if (__atomic_load_n(&t->waiting, __ATOMIC_SEQ_CST) == &tm->q) {
          q_remove(&tm->q, t);
          __atomic_store_n(&t->waiting, NULL, __ATOMIC_SEQ_CST);
          unpark(t);
        }
      } else {
        wheel_link(tm, worker, w);
      }
      w = next;
    }
  }
  if (until > tm->now) tm->now = until;
}

static void wheel_set_due(sleep_timer* tm) {
  uint64_t at;
  int k;
  uint64_t due = tm->n && wheel_next(tm, &at, &k) ? (at ? at : 1) * 1000000u : 0;
  __atomic_store_n(&tm->due, due, __ATOMIC_RELEASE);
}

static void mt_sleep(fly_wait* w, uint64_t nanos) {
  mt_task* t = running;
  if (nanos == 0) { mt_point(w); return; }
  W_BEGIN(w)
  worker* me = this_worker;
  sleep_timer* tm = &me->timer;
  spin_lock(&tm->q.lock);
  // An empty wheel starts again from now, rather than walk from when it was last used.
  if (!tm->n) tm->now = now_ms();
  // Due at the first millisecond that is wholly past the sleep, so that it is never cut short.
  w->a[0] = (int64_t)((now_ns() + nanos + 999999u) / 1000000u);
  w->a[1] = (int64_t)(intptr_t)t;
  wheel_link(tm, me->index, w);
  tm->n++;
  wheel_set_due(tm);
  WAIT_IN(w, &tm->q, true);
  // Cancelled before or after it slept, its sleep is taken out of the wheel. Woken by the wheel, it
  // is out already, which the waking worker marked before waking it: no lock is taken again.
  {
    int32_t at = __atomic_load_n(&w->n, __ATOMIC_ACQUIRE);
    if (at >= 0) {
      sleep_timer* own = &workers[at / WHEEL_CELLS].timer;
      spin_lock(&own->q.lock);
      if (w->n >= 0) {
        wheel_unlink(own, w);
        own->n--;
        wheel_set_due(own);
      }
      spin_unlock(&own->q.lock);
    }
  }
  cancelled_here();
  W_END
}

// The first of every worker's wheels' next work, or 0.
static uint64_t earliest_due(void) {
  uint64_t first = 0;
  for (int k = 0; k < nworkers; k++) {
    uint64_t d = __atomic_load_n(&workers[k].timer.due, __ATOMIC_ACQUIRE);
    if (d && (!first || d < first)) first = d;
  }
  return first;
}

// Brings every worker's wheel that has work due to now. A wheel another worker is at is passed by:
// every worker asleep wakes as the first is due, and would otherwise wait for each other's turn.
static void fire_alarms(void) {
  uint64_t now = 0;
  for (int k = 0; k < nworkers; k++) {
    sleep_timer* tm = &workers[k].timer;
    uint64_t due = __atomic_load_n(&tm->due, __ATOMIC_ACQUIRE);
    if (!due) continue;
    if (!now) now = now_ns();
    if (due > now) continue;
    if (!spin_trylock(&tm->q.lock)) continue;
    wheel_advance(tm, k, now / 1000000u);
    wheel_set_due(tm);
    spin_unlock(&tm->q.lock);
  }
}

// ---- running tasks ----

static void mt_task_body(void* a) { mt_task* t = a; mt_entry(t)(t, &t->fn, &t->slot); }

// Runs the task's root machine until it ends or waits: whether it ended.
static bool mt_task_main(mt_task* t) {
  if (fly_try(mt_task_body, t)) {
    char* m = panic_take();
    if (mt_entry(t) != main_entry) drop_task_closure(&t->fn);
    t->panic = m;
    if (!t->forked) __atomic_store_n(&t->how, FLY_TASK_PANICKED, __ATOMIC_RELEASE);
    fly_cx_now()->pend = 0;
    return true;
  }
  if (fly_cx_now()->pend) {
    fly_cx_now()->pend = 0;
    return false;
  }
  if (FLY_FAILED) { t->error = fly_err; fly_err = NULL; }
  if (!t->forked) __atomic_store_n(&t->how, fly_unwinding ? FLY_TASK_CANCELLED : FLY_TASK_DONE, __ATOMIC_RELEASE);
  fly_unwinding = false;
  return true;
}

// A spawned task's panic no `wait` gave is told once nothing can ask for it: by whichever of its
// end and its last `Task`'s drop comes second, only once.
static void tell_panic(mt_task* t) {
  if (__atomic_load_n(&t->how, __ATOMIC_ACQUIRE) == FLY_TASK_PANICKED && !__atomic_exchange_n(&t->told, true, __ATOMIC_ACQ_REL)) report_spawned_panic(t->panic);
}

// Task `t` has ended: its outcome goes to its scope, its joiners wake, and the first failure or
// panic cancels the scope's body and its other tasks (§6.1).
static void mt_end(mt_task* t) {
  fly_frames_free(&t->frames);
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
  // A panic no `Task` can ask for is told as the task ends, before its scope sees it end: after, the
  // scope's body could go on and print before it.
  if (!t->forked && __atomic_load_n(&t->handles, __ATOMIC_ACQUIRE) == 0) tell_panic(t);
  mt_scope* sc = t->scope;
  mt_task** cancels = NULL;
  size_t ncancels = 0;
  spin_lock(&sc->q.lock);
  // A spawned task's panic ends it alone (§5.7).
  bool failed = t->error || (t->forked && t->panic);
  if (failed && !sc->failer) {
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
  if (failed && !sc->failer) {
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
  __atomic_store_n(&t->finished, true, __ATOMIC_SEQ_CST);
  struct mt_join* j = __atomic_load_n(&t->join, __ATOMIC_SEQ_CST);
  if (j) {
    spin_lock(&j->q.lock);
    wake_all(&j->q);
    for (struct mt_any* a = j->anys; a; a = a->next) {
      __atomic_store_n(&a->fired, true, __ATOMIC_SEQ_CST);
      spin_lock(&a->q->lock);
      wake_one(a->q);
      spin_unlock(&a->q->lock);
    }
    spin_unlock(&j->q.lock);
  }
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
    if (is_cancelled(t)) {
      running = NULL;
      drop_task_closure(&t->fn);
      if (!t->forked) __atomic_store_n(&t->how, FLY_TASK_CANCELLED, __ATOMIC_RELEASE);
      mt_end(t);
      return;
    }
  }
  // The task runs in its worker's context, on its worker's stack, with what is its own.
  fly_ctx* cx = &w->run_ctx;
  *cx = (fly_ctx){ .frames = &t->frames, .panic = t->panic, .destroying = t->destroying, .limit = stack_limit0 };
  fly_cur = cx;
  bool done = mt_task_main(t);
  if (!done) {
    t->panic = cx->panic;
    t->destroying = cx->destroying;
  }
  // Stopped, the task holds only the frames it is in.
  fly_spare_free(cx);
  fly_cur = w->idle_ctx;
  running = NULL;
  // Once the lock of what it waits for is given back, the task may be woken and run elsewhere: what
  // is needed of it is read first.
  bool yielded = t->yielded;
  spin_t* release = w->release;
  w->release = NULL;
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

// The running task waits until `fd` may be read, or written: true if it suspends, to go on with
// `io_wait_end` as it is woken; false if it is ready at once, or the task is cancelled.
static bool io_wait_begin(int fd, bool write) {
  io_obj* o = io_of(fd);
  int d = write ? 1 : 0;
  spin_lock(&o->q[d].lock);
  if (o->ready[d]) {
    o->ready[d] = false;
    spin_unlock(&o->q[d].lock);
    return false;
  }
  __atomic_fetch_add(&io_waiting, 1, __ATOMIC_SEQ_CST);
  if (wait_in(&o->q[d], true)) return true;
  __atomic_fetch_sub(&io_waiting, 1, __ATOMIC_SEQ_CST);
  return false;
}

static void io_wait_end(void) { __atomic_fetch_sub(&io_waiting, 1, __ATOMIC_SEQ_CST); }

// ---- `par` ----

// Work `join` lets another worker take: the second of the two, run where it is taken.
typedef struct { void (*run)(void* f, void* out); void* f; void* out; int done; char* panic; } job_t;

// A job's panic is taken up where it runs, and goes on in the `join` that made it.
static void run_job(job_t* j) {
  j->panic = run_half(j->run, j->f, j->out);
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

static void par_join(void (*a)(void*, void*), void* fa, void* oa, void (*da)(void*), void (*b)(void*, void*), void* fb, void* ob, void (*db)(void*)) {
  worker* w = this_worker;
  // With work enough waiting to be taken here already, this pair runs here, in order.
  if (dq_size(&w->jobs) >= 4) {
    join_in_order(a, fa, oa, da, b, fb, ob, db);
    return;
  }
  job_t jb = { b, fb, ob, 0, NULL };
  dq_push(&w->jobs, &jb);
  notify();
  char* ma = run_half(a, fa, oa);
  // Only what `a` pushed was above `b`, and `a` took it back: `b` is next, unless it was taken.
  if (dq_pop(&w->jobs) == &jb) {
    if (ma) { drop_half(fb); panic_again(ma); }
    char* mb = run_half(b, fb, ob);
    if (mb) { if (da) da(oa); panic_again(mb); }
    return;
  }
  // Taken: help with other work until it is done.
  for (unsigned n = 0; !__atomic_load_n(&jb.done, __ATOMIC_ACQUIRE); n++) {
    job_t* j = steal_job(w);
    if (j) { run_job(j); n = 0; }
    else if (n < 128) relax();
    else sched_yield();
  }
  if (ma || jb.panic) {
    if (!ma && da) da(oa);
    if (!jb.panic && db) db(ob);
    if (ma && jb.panic) panic_free(jb.panic);
    panic_again(ma ? ma : jb.panic);
  }
}

// ---- workers ----

static bool work_anywhere(worker* w) {
  (void)w;
  for (int k = 0; k < nworkers; k++) {
    if (__atomic_load_n(&workers[k].inhead, __ATOMIC_SEQ_CST)) return true;
    if (dq_size(&workers[k].fresh) > 0 || dq_size(&workers[k].jobs) > 0) return true;
  }
  uint64_t due = earliest_due();
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
      uint64_t due = earliest_due();
      if (!due && __atomic_load_n(&runnable, __ATOMIC_SEQ_CST) == 0 && __atomic_load_n(&alive, __ATOMIC_SEQ_CST) > 0 && __atomic_load_n(&io_waiting, __ATOMIC_SEQ_CST) == 0) mt_deadlock();
      uint64_t now = now_ns();
      io_poll(due ? (int64_t)(due > now ? due - now : 0) : -1);
    }
    __atomic_store_n(&pollers, 0, __ATOMIC_SEQ_CST);
    return;
  }
  // Asleep from here: work queued after the look below finds it so, and wakes it.
  __atomic_fetch_add(&idlers, 1, __ATOMIC_SEQ_CST);
  __atomic_store_n(&w->parked, 1, __ATOMIC_SEQ_CST);
  pthread_mutex_lock(&w->park_mu);
  if (!work_anywhere(w) && !(w == &workers[0] && __atomic_load_n(&main_done, __ATOMIC_SEQ_CST))) {
    uint64_t due = earliest_due();
    if (!due && __atomic_load_n(&runnable, __ATOMIC_SEQ_CST) == 0 && __atomic_load_n(&alive, __ATOMIC_SEQ_CST) > 0 && __atomic_load_n(&io_waiting, __ATOMIC_SEQ_CST) == 0) mt_deadlock();
    if (due) {
      // The monotonic clock and the condition's clock differ: wait as long as is left.
      uint64_t left = due > now_ns() ? due - now_ns() : 0;
      struct timespec ts;
      clock_gettime(CLOCK_REALTIME, &ts);
      uint64_t at = (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec + left;
      ts.tv_sec = (time_t)(at / 1000000000u);
      ts.tv_nsec = (long)(at % 1000000000u);
      if (__atomic_load_n(&w->parked, __ATOMIC_SEQ_CST)) pthread_cond_timedwait(&w->park_cv, &w->park_mu, &ts);
    } else {
      while (__atomic_load_n(&w->parked, __ATOMIC_SEQ_CST)) pthread_cond_wait(&w->park_cv, &w->park_mu);
    }
  }
  __atomic_store_n(&w->parked, 0, __ATOMIC_SEQ_CST);
  pthread_mutex_unlock(&w->park_mu);
  __atomic_fetch_sub(&idlers, 1, __ATOMIC_SEQ_CST);
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
  thread_stack_limit();
  fly_cur->limit = stack_limit0;
  work(w);
  return NULL;
}

static void mt_run(void (*main)(void**), void (*entry)(void* task, void* closure, void** slot)) {
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
    // The first worker is the program's thread, whose context is the program's outside its tasks.
    w->idle_ctx = k == 0 ? &fly_ctx0 : &w->own_ctx;
    w->rng = 0x9e3779b97f4a7c15u * (uint64_t)(k + 1);
    pthread_mutex_init(&w->park_mu, NULL);
    pthread_cond_init(&w->park_cv, NULL);
    w->fresh.buf = dq_buf_new(256, NULL);
    w->jobs.buf = dq_buf_new(256, NULL);
  }
  this_worker = &workers[0];
  mt_task* t = fly_alloc(MT_FORK_AT + sizeof(struct mt_fork));
  mt_fork_of(t)->entry = entry;
  t->fn.fn = (void*)main;
  t->refs = 1;
  // Its panic, once the workers have stopped, ends the program.
  t->forked = true;
  main_task = t;
  runnable = alive = 1;
  inbox_push(&workers[0], t);
  // Each worker's stack is FLY_STACK, the first's too: tasks and `par` work run on it.
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, FLY_STACK);
  for (int k = 1; k < nworkers; k++) {
    pthread_t th;
    if (pthread_create(&th, &attr, worker_thread, &workers[k]) != 0) fly_panic("cannot start a worker thread");
    pthread_detach(th);
  }
  pthread_attr_destroy(&attr);
  run_on_big_stack(worker_thread, &workers[0]);
  if (t->panic) panic_exit(t->panic);
  if (t->error) fly_err = t->error;
}

// ---- what compiled code calls, without a simulated world ----

// A task started in scope `scope`, which itself and its scope refer to, and `refs` more; `handles`
// `Task`s, set before any other worker can see it.
static mt_task* mt_start(int scope, void (*entry)(void* task, void* closure, void** slot), const fly_fn* f, size_t size, int refs, int handles) {
  mt_scope* sc = obj_get(scope);
  bool forked = entry != fly_task_void;
  mt_task* t = fly_alloc(forked ? MT_FORK_AT + sizeof(struct mt_fork) + size : sizeof(mt_task));
  if (forked) {
    mt_fork_of(t)->entry = entry;
    mt_fork_of(t)->size = (uint32_t)size;
  }
  t->fn = *f;
  t->scope = sc;
  t->forked = forked;
  t->how = FLY_TASK_RUNNING;
  t->refs = 2 + refs;
  t->handles = handles;
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
  return t;
}

static int mt_spawn(fly_wait* w, int scope, void (*entry)(void* task, void* closure, void** slot), const fly_fn* f, size_t size) {
  // A forked task's `Fiber` refers to it too, by its number.
  if (w->step == 0) w->n = obj_new(mt_start(scope, entry, f, size, 1, 0));
  mt_point(w);
  return w->n;
}

// ---- `Task`, with threads ----

static void* mt_task_spawn(fly_wait* w, int scope, const fly_fn* f) {
  // Its `Task`s share one reference.
  if (w->step == 0) {
    w->p[1] = mt_start(scope, fly_task_void, f, 0, 1, 1);
  }
  mt_point(w);
  return w->p[1];
}

static void mt_task_cancel(void* h) {
  mt_task* t = h;
  if (__atomic_load_n(&t->how, __ATOMIC_ACQUIRE) == FLY_TASK_RUNNING) kill_task(t);
}

static int32_t mt_task_wait(fly_wait* w, void* h, fly_String* message) {
  mt_task* t = h;
  struct mt_join* j;
  W_BEGIN(w)
  j = mt_join_of(t);
  spin_lock(&j->q.lock);
  while (!__atomic_load_n(&t->finished, __ATOMIC_SEQ_CST)) {
    WAIT_IN(w, &j->q, true, 0);
    if (cancelled_here()) return FLY_TASK_DONE;
    j = t->join;
    spin_lock(&j->q.lock);
  }
  spin_unlock(&j->q.lock);
  W_END
  int32_t how = __atomic_load_n(&t->how, __ATOMIC_ACQUIRE);
  if (how == FLY_TASK_PANICKED) {
    __atomic_store_n(&t->told, true, __ATOMIC_RELEASE);
    *message = fly_String_from(fly_str_lit(t->panic, strlen(t->panic)));
  }
  return how;
}

// What it waits in, and the records each task tells it by, are the routine's own, in the heap.
static size_t mt_task_any(fly_wait* w, void* const* ts, size_t n) {
  struct mt_any* as;
  waitq* qp;
  size_t found, k;
  bool cancelled;
  W_BEGIN(w)
  w->p[0] = fly_alloc(n * sizeof(struct mt_any));
  w->p[1] = fly_alloc(sizeof(waitq));
  for (;;) {
    as = w->p[0];
    qp = w->p[1];
    *qp = (waitq){ 0 };
    found = n, k = 0;
    for (; k < n; k++) {
      mt_task* t = ts[k];
      struct mt_join* j = mt_join_of(t);
      spin_lock(&j->q.lock);
      if (__atomic_load_n(&t->finished, __ATOMIC_SEQ_CST)) { spin_unlock(&j->q.lock); found = k; break; }
      as[k] = (struct mt_any){ j->anys, qp, false };
      j->anys = &as[k];
      spin_unlock(&j->q.lock);
    }
    cancelled = false;
    if (found == n) {
      // A task that ends from here on sets `fired` before it takes the lock this one holds.
      spin_lock(&qp->lock);
      bool fired = false;
      for (size_t i = 0; i < n; i++) fired = fired || __atomic_load_n(&as[i].fired, __ATOMIC_SEQ_CST);
      if (fired) spin_unlock(&qp->lock);
      else {
        w->n = (int32_t)k;
        WAIT_IN(w, qp, true, 0);
        as = w->p[0];
        qp = w->p[1];
        k = (size_t)w->n;
      }
      cancelled = cancelled_here();
    }
    for (size_t i = 0; i < k; i++) {
      struct mt_join* j = ((mt_task*)ts[i])->join;
      spin_lock(&j->q.lock);
      for (struct mt_any** p = &j->anys; *p; p = &(*p)->next) {
        if (*p == &as[i]) { *p = as[i].next; break; }
      }
      spin_unlock(&j->q.lock);
    }
    if (cancelled) { free(as); free(qp); return 0; }
    for (size_t i = 0; i < n; i++) {
      mt_task* t = ts[i];
      if (__atomic_load_n(&t->finished, __ATOMIC_SEQ_CST)) { free(as); free(qp); return i; }
    }
  }
  W_END
  return 0;
}

static void mt_task_clone(void* h) { __atomic_fetch_add(&((mt_task*)h)->handles, 1, __ATOMIC_RELAXED); }

static void mt_task_drop(void* h) {
  mt_task* t = h;
  if (__atomic_sub_fetch(&t->handles, 1, __ATOMIC_ACQ_REL) > 0) return;
  if (__atomic_load_n(&t->finished, __ATOMIC_SEQ_CST)) tell_panic(t);
  task_unref(t);
}

static void mt_join(fly_wait* w, int task, void* out) {
  mt_task* t = obj_get(task);
  struct mt_join* j;
  W_BEGIN(w)
  j = mt_join_of(t);
  spin_lock(&j->q.lock);
  while (!__atomic_load_n(&t->finished, __ATOMIC_SEQ_CST)) {
    WAIT_IN(w, &j->q, true);
    if (cancelled_here()) return;
    j = t->join;
    spin_lock(&j->q.lock);
  }
  spin_unlock(&j->q.lock);
  W_END
  if (t->panic) {
    // It panicked, which cancels the scope and the joiner with it; the scope raises the panic.
    fly_unwinding = true;
  } else if (t->error) {
    // Raised here, so not again by the scope.
    fly_err = t->error;
    t->error = NULL;
  } else {
    memcpy(out, mt_fork_of(t)->result, mt_fork_of(t)->size);
  }
  obj_clear(task);
  task_unref(t);
}

static int mt_scope_open(void) {
  mt_scope* sc = fly_alloc(sizeof(mt_scope));
  sc->owner = running;
  return obj_new(sc);
}

// What it found as the body ended is kept in the record: whether it unwound, its failure, and
// whether it has spread a cancellation to the scope's tasks.
static void mt_scope_close(fly_wait* w, int id) {
  mt_scope* sc = obj_get(id);
  mt_task* me = running;
  W_BEGIN(w)
  w->a[0] = fly_unwinding;
  fly_unwinding = false;
  w->p[0] = fly_err;
  fly_err = NULL;
  // The body left by unwinding — a failure, a cancellation — cancels the scope's tasks (§6.1).
  if (w->a[0] || w->p[0]) mt_scope_cancel(id);
  spin_lock(&sc->q.lock);
  sc->closing = true;
  // Every task started in it is waited for. Cancelled while it waits, the task cancels them, once,
  // and waits on.
  w->a[1] = w->a[0] || w->p[0];
  while (sc->nlive > 0) {
    if (!w->a[1] && is_cancelled(me)) {
      w->a[1] = true;
      spin_unlock(&sc->q.lock);
      mt_scope_cancel(id);
      spin_lock(&sc->q.lock);
      continue;
    }
    WAIT_IN(w, &sc->q, !w->a[1]);
    spin_lock(&sc->q.lock);
  }
  spin_unlock(&sc->q.lock);
  W_END
  bool unwinding = w->a[0];
  void* err = w->p[0];
  // The body unwound because a task failed: the scope raises that instead, the cancellation its
  // failure made over. Otherwise one from outside goes on, whether it came in the body or as the
  // task waited.
  mt_task* failer = sc->failer;
  bool unwound = unwinding && !failer;
  if (failer) __atomic_store_n(&me->cancelled, false, __ATOMIC_SEQ_CST);
  obj_clear(id);
  free(sc);
  char* panic = NULL;
  if (unwound) {
    fly_unwinding = true;
    if (err) free(err);
  } else if (err) {
    fly_err = err;
  } else if (failer && failer->panic) {
    panic = failer->panic;
    failer->panic = NULL;
  } else if (failer && failer->error) {
    fly_err = failer->error;
    failer->error = NULL;
  }
  if (failer) task_unref(failer);
  if (panic) panic_again(panic);
  if (!unwound && !err && !failer && is_cancelled(me)) fly_unwinding = true;
}

// A panic unwound scope `id`'s body: its tasks still alive are cancelled.
static void mt_scope_cancel(int id) {
  mt_scope* sc = obj_get(id);
  spin_lock(&sc->q.lock);
  mt_task** cancels = fly_alloc((sc->nlive + 1) * sizeof(mt_task*));
  size_t n = 0;
  for (mt_task* o = sc->live; o; o = o->snext) {
    __atomic_fetch_add(&o->refs, 1, __ATOMIC_RELAXED);
    cancels[n++] = o;
  }
  spin_unlock(&sc->q.lock);
  for (size_t i = 0; i < n; i++) {
    cancel_task(cancels[i]);
    task_unref(cancels[i]);
  }
  free(cancels);
}

static fly_chan mt_channel(void (*drop)(void*)) {
  mt_chan* c = fly_alloc(sizeof(mt_chan));
  c->state = fly_rt_mt_channel();
  c->drop = drop;
  return (fly_chan){ obj_new(c) };
}

// Frees a channel both of whose ends are gone, which nothing else can reach.
static void mt_chan_free(int id, mt_chan* c) {
  fly_rt_mt_free(c->state);
  obj_clear(id);
  free(c);
}

// The receiving end is gone: what is in the channel is taken out and dropped, outside its lock, as
// dropping a message may reach the channel again. Whichever end goes last frees the channel.
static void mt_receiver_gone(fly_chan ch) {
  mt_chan* c = obj_get(ch.ch);
  uint8_t* items = NULL;
  uint64_t n = 0, size = 0;
  void (*drop)(void*) = c->drop;
  if (fly_rt_mt_deafen((uint8_t*)&c->q, c->state, &items, &n, &size)) mt_chan_free(ch.ch, c);
  if (drop) for (uint64_t i = 0; i < n; i++) drop(items + i * size);
  free(items);
}

static bool mt_send(fly_wait* w, fly_chan ch, const void* v, size_t size) {
  mt_chan* c = obj_get(ch.ch);
  if (w->step == 0) {
    w->n = fly_rt_mt_send((uint8_t*)&c->q, c->state, (uint8_t*)v, size);
    if (!w->n && c->drop) c->drop((void*)v);
  }
  mt_point(w);
  return w->n;
}

// The next message: it waits under the channel's monitor while there is none, and is put at `out`
// by the call that finds one.
static bool mt_recv(fly_wait* w, fly_chan ch, void* out, size_t size) {
  (void)size;
  mt_chan* c = obj_get(ch.ch);
  W_BEGIN(w)
  for (;;) {
    spin_lock(&c->q.lock);
    int32_t r = fly_rt_mt_take(c->state, out);
    if (r != 2) { spin_unlock(&c->q.lock); return r == 1; }
    WAIT_IN(w, &c->q, true, false);
    if (cancelled_here()) return false;
  }
  W_END
  return false;
}

static void mt_sender_gone(fly_chan ch) {
  mt_chan* c = obj_get(ch.ch);
  if (fly_rt_mt_sender_gone((uint8_t*)&c->q, c->state)) mt_chan_free(ch.ch, c);
}

static void mt_sender_clone(fly_chan ch) {
  mt_chan* c = obj_get(ch.ch);
  fly_rt_mt_sender_clone((uint8_t*)&c->q, c->state);
}

// A `Mutex`'s monitor and whether it is held, in the header before its state; how it is taken and
// given back is the runtime's Flyscript's (rt/mt.fly).
typedef struct { waitq q; int32_t held; } mt_mutex;
_Static_assert(sizeof(mt_mutex) < MUTEX_HEADER, "a mutex's header holds its lock, and its poison after");

static mt_mutex* mutex_of(const void* state) { return (mt_mutex*)((uint8_t*)state - MUTEX_HEADER); }

void fly_lock(const void* state) {
  if (!threads) return;
  mt_mutex* m = mutex_of(state);
  fly_rt_mt_lock((uint8_t*)&m->q, &m->held);
}

void fly_unlock(const void* state) {
  if (!threads || !state) return;
  mt_mutex* m = mutex_of(state);
  fly_rt_mt_unlock((uint8_t*)&m->q, &m->held);
}

static void* mt_task_result(mt_task* t) { return t->forked ? mt_fork_of(t)->result : NULL; }
static void* mt_task_closure(mt_task* t) { return &t->fn; }

void fly_par_join(void (*a)(void* f, void* out), void* fa, void* oa, void (*da)(void* out),
                  void (*b)(void* f, void* out), void* fb, void* ob, void (*db)(void* out)) {
  if (threads && nworkers > 1 && this_worker) { par_join(a, fa, oa, da, b, fb, ob, db); return; }
  join_in_order(a, fa, oa, da, b, fb, ob, db);
}
#endif

#endif

// Without threads, a `Mutex` is never contended, and `join` runs its two in order; the monitors
// the runtime's Flyscript has for threads are never reached.
#ifndef FLY_THREADS
#ifndef FLY_FREESTANDING
static _Noreturn void no_threads(void) { fly_panic("a monitor without threads"); }
void fly_mon_lock(uint8_t* m) { (void)m; no_threads(); }
void fly_mon_unlock(uint8_t* m) { (void)m; no_threads(); }
void fly_mon_wake_one(uint8_t* m) { (void)m; no_threads(); }
void fly_mon_wake_all(uint8_t* m) { (void)m; no_threads(); }
void fly_core_relax(void) {}
void fly_core_yield(void) {}
#endif
void fly_lock(const void* state) { (void)state; }
void fly_unlock(const void* state) { (void)state; }
void fly_par_join(void (*a)(void* f, void* out), void* fa, void* oa, void (*da)(void* out),
                  void (*b)(void* f, void* out), void* fb, void* ob, void (*db)(void* out)) {
  join_in_order(a, fa, oa, da, b, fb, ob, db);
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

// Bytes as text: each maximal part of them that begins no well-formed sequence is U+FFFD, as
// WHATWG's decoder and Rust's `from_utf8_lossy` have it. Bytes that are UTF-8 become the string's.
fly_String fly_utf8_lossy(fly_vec b) {
  if (fly_utf8_valid((fly_slice){ b.ptr, b.len })) return (fly_String){ (uint8_t*)b.ptr, b.len, b.cap };
  const uint8_t* p = b.ptr;
  fly_String out = fly_String_new();
  size_t i = 0;
  while (i < b.len) {
    uint8_t c = p[i];
    if (c < 0x80) { fly_String_push_byte(&out, c); i++; continue; }
    // How many bytes follow, and the range the first of them may take.
    size_t need = 0;
    uint8_t lo = 0x80, hi = 0xbf;
    if (c >= 0xc2 && c <= 0xdf) need = 1;
    else if (c == 0xe0) { need = 2; lo = 0xa0; }
    else if ((c >= 0xe1 && c <= 0xec) || c == 0xee || c == 0xef) need = 2;
    else if (c == 0xed) { need = 2; hi = 0x9f; }
    else if (c == 0xf0) { need = 3; lo = 0x90; }
    else if (c >= 0xf1 && c <= 0xf3) need = 3;
    else if (c == 0xf4) { need = 3; hi = 0x8f; }
    size_t j = i + 1;
    bool ok = need > 0;
    for (size_t k = 0; ok && k < need; k++, j++) {
      if (j >= b.len || p[j] < lo || p[j] > hi) { ok = false; break; }
      lo = 0x80;
      hi = 0xbf;
    }
    if (ok) {
      fly_String_push(&out, (fly_str){ p + i, j - i });
      i = j;
    } else {
      fly_String_push(&out, (fly_str){ (const uint8_t*)"\xef\xbf\xbd", 3 });
      // The byte that broke the sequence starts the next, unless it was the first.
      i = j > i + 1 ? j : i + 1;
    }
  }
  free(b.ptr);
  return out;
}

// Well-formed UTF-8: no overlong forms, surrogates, or code points past U+10FFFF.
// Each sequence by its first byte, as RFC 3629's table has it: the range its second byte may take,
// which rules out overlong forms, surrogates and what is past U+10FFFF, and continuation bytes for
// the rest. ASCII is taken eight bytes at a time.
// In clang's vector extensions, where the target has a byte lookup.
#if defined(__clang__) && (defined(__aarch64__) || defined(__SSSE3__) || defined(__wasm_simd128__))
#define FLY_UTF8_VECTORS 1
typedef uint8_t fly_v16 __attribute__((vector_size(16)));

static inline fly_v16 utf8_lookup(fly_v16 table, fly_v16 idx) {
  fly_v16 r;
  fly_lookup16((uint8_t*)&r, (const uint8_t*)&idx, (const uint8_t*)&table);
  return r;
}

// Sixteen bytes checked with the sixteen before them (Keiser and Lemire, "Validating UTF-8 in
// less than one instruction per byte", 2021): each pair of a byte and the one before it is looked
// up by the high nibble of each and the low nibble of the first, three tables whose entries are the
// errors that nibble allows, and a pair is wrong where the three agree on one; that the third and
// fourth bytes of a long sequence are continuations is checked apart. The errors, as bits.
enum { U8_TOO_SHORT = 1 << 0, U8_TOO_LONG = 1 << 1, U8_OVERLONG_3 = 1 << 2, U8_TOO_LARGE = 1 << 3,
  U8_SURROGATE = 1 << 4, U8_OVERLONG_2 = 1 << 5, U8_TOO_LARGE_1000 = 1 << 6, U8_OVERLONG_4 = 1 << 6,
  U8_TWO_CONTS = 1 << 7, U8_CARRY = U8_TOO_SHORT | U8_TOO_LONG | U8_TWO_CONTS };

static inline fly_v16 utf8_block_errors(fly_v16 input, fly_v16 prev) {
  const fly_v16 b1hi = { U8_TOO_LONG, U8_TOO_LONG, U8_TOO_LONG, U8_TOO_LONG, U8_TOO_LONG, U8_TOO_LONG, U8_TOO_LONG, U8_TOO_LONG,
    U8_TWO_CONTS, U8_TWO_CONTS, U8_TWO_CONTS, U8_TWO_CONTS, U8_TOO_SHORT | U8_OVERLONG_2, U8_TOO_SHORT,
    U8_TOO_SHORT | U8_OVERLONG_3 | U8_SURROGATE, U8_TOO_SHORT | U8_TOO_LARGE | U8_TOO_LARGE_1000 | U8_OVERLONG_4 };
  const uint8_t big = U8_CARRY | U8_TOO_LARGE | U8_TOO_LARGE_1000;
  const fly_v16 b1lo = { U8_CARRY | U8_OVERLONG_3 | U8_OVERLONG_2 | U8_OVERLONG_4, U8_CARRY | U8_OVERLONG_2, U8_CARRY, U8_CARRY,
    U8_CARRY | U8_TOO_LARGE, big, big, big, big, big, big, big, big, big | U8_SURROGATE, big, big };
  const uint8_t cont8 = U8_TOO_LONG | U8_OVERLONG_2 | U8_TWO_CONTS | U8_OVERLONG_3 | U8_TOO_LARGE_1000 | U8_OVERLONG_4;
  const uint8_t cont9 = U8_TOO_LONG | U8_OVERLONG_2 | U8_TWO_CONTS | U8_OVERLONG_3 | U8_TOO_LARGE;
  const uint8_t contA = U8_TOO_LONG | U8_OVERLONG_2 | U8_TWO_CONTS | U8_SURROGATE | U8_TOO_LARGE;
  const fly_v16 b2hi = { U8_TOO_SHORT, U8_TOO_SHORT, U8_TOO_SHORT, U8_TOO_SHORT, U8_TOO_SHORT, U8_TOO_SHORT, U8_TOO_SHORT, U8_TOO_SHORT,
    cont8, cont9, contA, contA, U8_TOO_SHORT, U8_TOO_SHORT, U8_TOO_SHORT, U8_TOO_SHORT };
  fly_v16 prev1 = __builtin_shufflevector(prev, input, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30);
  fly_v16 prev2 = __builtin_shufflevector(prev, input, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29);
  fly_v16 prev3 = __builtin_shufflevector(prev, input, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28);
  fly_v16 special = utf8_lookup(b1hi, prev1 >> 4) & utf8_lookup(b1lo, prev1 & 0x0F) & utf8_lookup(b2hi, input >> 4);
  // Where a byte must be a third or fourth: after a lead of three bytes two back, or of four three back.
  fly_v16 third = __builtin_elementwise_sub_sat(prev2, (fly_v16){ 0 } + (uint8_t)(0xE0 - 0x80));
  fly_v16 fourth = __builtin_elementwise_sub_sat(prev3, (fly_v16){ 0 } + (uint8_t)(0xF0 - 0x80));
  fly_v16 must = (third | fourth) & 0x80;
  return must ^ special;
}

// Whether the last bytes of a block begin a sequence the block does not end.
static inline fly_v16 utf8_incomplete(fly_v16 input) {
  const fly_v16 max = { 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0xF0 - 1, 0xE0 - 1, 0xC0 - 1 };
  return __builtin_elementwise_sub_sat(input, max);
}

static inline bool utf8_any(fly_v16 v) { return __builtin_reduce_or(v) != 0; }
#endif

bool fly_utf8_valid(fly_slice b) {
#ifdef FLY_UTF8_VECTORS
  // Sixteen bytes or more: the last block is the last sixteen, which may overlap the one before,
  // as checking a byte with the one before it again changes nothing. Fewer are checked below.
  if (b.len >= 16) {
    const uint8_t* p = b.ptr;
    size_t i = 0, n = b.len;
    fly_v16 prev = { 0 }, err = { 0 }, incomplete = { 0 };
    for (;;) {
      fly_v16 v;
      memcpy(&v, p + i, 16);
      // Sixteen ASCII bytes are well formed, if nothing before them was left unfinished.
      if (__builtin_reduce_max(v) < 0x80) err |= incomplete;
      else err |= utf8_block_errors(v, prev);
      incomplete = utf8_incomplete(v);
      if (i + 16 == n) break;
      i = i + 32 <= n ? i + 16 : n - 16;
      // The sixteen bytes before the block, nothing before the first byte counted as ASCII.
      if (i >= 16) {
        memcpy(&prev, p + i - 16, 16);
      } else {
        prev = (fly_v16){ 0 };
        memcpy((uint8_t*)&prev + (16 - i), p, i);
      }
    }
    return !utf8_any(err | incomplete);
  }
#endif
  const uint8_t* p = b.ptr;
  size_t i = 0, n = b.len;
  while (i < n) {
    while (i + 8 <= n) {
      uint64_t w;
      memcpy(&w, p + i, 8);
      if (w & 0x8080808080808080ull) break;
      i += 8;
    }
    if (i >= n) break;
    uint8_t c = p[i];
    if (c < 0x80) { i++; continue; }
    if (c >= 0xc2 && c <= 0xdf) {
      if (i + 1 >= n || (p[i + 1] & 0xc0) != 0x80) return false;
      i += 2;
      continue;
    }
    size_t k;
    uint8_t lo = 0x80, hi = 0xbf;
    if (c >= 0xe0 && c <= 0xef) {
      k = 2;
      if (c == 0xe0) lo = 0xa0;
      else if (c == 0xed) hi = 0x9f;
    } else if (c >= 0xf0 && c <= 0xf4) {
      k = 3;
      if (c == 0xf0) lo = 0x90;
      else if (c == 0xf4) hi = 0x8f;
    } else {
      return false;
    }
    if (n - i <= k) return false;
    if (p[i + 1] < lo || p[i + 1] > hi) return false;
    if ((p[i + 2] & 0xc0) != 0x80) return false;
    if (k == 3 && (p[i + 3] & 0xc0) != 0x80) return false;
    i += k + 1;
  }
  return true;
}

#ifndef FLY_FREESTANDING
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
