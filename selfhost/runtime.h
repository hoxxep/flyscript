// The runtime of Flyscript compiled to C: what compiled code calls that the standard library
// declares without a body, and the operations code generation leaves to it. Compiled code is
// GNU C (statement expressions), for clang or gcc.
//
// Values: integers and floats are C's; `void` is `fly_unit`. A string is bytes and a length: `str`
// borrows them (`fly_str`), `String` owns them (`fly_String`). Every list — `Vec`, slice — is the
// same untyped shape, its elements cast where they are read. A value that owns memory is dead when
// it is all zero bits: a move zeroes what it moves from, and a drop does nothing to a dead value,
// so every way out of a scope may drop all it owns.

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef FLY_FREESTANDING
// A freestanding program — a kernel, firmware — has no C library. It supplies memory and what a
// panic does; the runtime supplies the rest of what compiled code calls, each replaceable.
void* fly_os_alloc(size_t size, size_t align);
void fly_os_free(void* p);
_Noreturn void fly_os_panic(const char* message, size_t len);
void* memcpy(void* dst, const void* src, size_t n);
void* memmove(void* dst, const void* src, size_t n);
void* memset(void* dst, int c, size_t n);
int memcmp(const void* a, const void* b, size_t n);
size_t strlen(const char* s);
// The C library's allocation, over the program's: each block remembers its size.
void* fly_mem_alloc(size_t n);
void* fly_mem_calloc(size_t n, size_t size);
void* fly_mem_realloc(void* p, size_t n);
void fly_mem_free(void* p);
#define malloc fly_mem_alloc
#define calloc fly_mem_calloc
#define realloc fly_mem_realloc
#define free fly_mem_free
#else
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// Blocks come from the runtime's own allocator (runtime.c). Natively the C library's names are made
// to mean it here, its own code keeping the C library's; in WebAssembly it is the program's
// `malloc`, the C library's too. Under a sanitizer, and built with `FLY_SYSTEM_MALLOC`, blocks are
// the C library's, so that a sanitizer, or a checker of leaks, sees every one.
#if defined(__has_feature)
#if __has_feature(address_sanitizer) || __has_feature(thread_sanitizer)
#define FLY_SANITIZED 1
#endif
#endif
#if defined(__SANITIZE_ADDRESS__) || defined(__SANITIZE_THREAD__)
#define FLY_SANITIZED 1
#endif
#if defined(__wasm__) && !defined(FLY_SANITIZED) && !defined(FLY_SYSTEM_MALLOC)
#define FLY_MALLOC 1
#elif !defined(FLY_SANITIZED) && !defined(FLY_SYSTEM_MALLOC)
#define FLY_MALLOC 1
static inline void* fly_sys_malloc(size_t n) { return malloc(n); }
static inline void* fly_sys_realloc(void* p, size_t n) { return realloc(p, n); }
static inline void fly_sys_free(void* p) { free(p); }
void* fly_mem_alloc(size_t n);
void* fly_mem_calloc(size_t n, size_t size);
void* fly_mem_realloc(void* p, size_t n);
void fly_mem_free(void* p);
#define malloc fly_mem_alloc
#define calloc fly_mem_calloc
#define realloc fly_mem_realloc
#define free fly_mem_free
#endif
#endif

typedef uint8_t fly_unit;

// A program that starts tasks runs them on every core, unless it runs against a simulated world
// (§6.4). A task may then go on on another core after it waits, so the runtime's state of a
// thread is kept in variables of the thread's, and what compiled code reads of the task running is
// the task's own (`fly_ctx`, below).
#if defined(FLY_TASKS) && !defined(FLY_FREESTANDING) && !defined(__wasm__)
#define FLY_THREADS 1
#define FLY_LOCAL _Thread_local
#else
#define FLY_LOCAL
#endif

// A function of C's is declared under a name of the program's, bound to its own symbol.
#define FLY_XSTR(x) #x
#define FLY_STR(x) FLY_XSTR(x)
#define FLY_SYMBOL(name) __asm__(FLY_STR(__USER_LABEL_PREFIX__) #name)
typedef __int128 fly_i128;

typedef struct { const uint8_t* ptr; size_t len; } fly_str;
typedef struct { uint8_t* ptr; size_t len; size_t cap; } fly_String;
typedef struct { void* ptr; size_t len; size_t cap; } fly_vec;
typedef struct { void* ptr; size_t len; } fly_slice;
// A closure: its environment, what drops it, and its code, cast to its type where it is called.
typedef struct { void* env; void (*drop)(void*); void* fn; } fly_fn;

// ---- the task running ----

typedef struct fly_handler fly_handler;
typedef struct fly_unw fly_unw;
// What compiled code reads and sets of the task running: the failure being raised, if any — what
// was thrown, boxed, which a function that may fail returns with set, for its caller to check;
// whether the task unwinds, a computation whose continuation was dropped; whether a generator
// stops; the handlers in force, innermost first; and, for a panic (§5.7), the records of the
// functions it would unwind, innermost first, and the message of the panic unwinding them, if one
// is. The last two are each fiber's own.
// And the limit of the stack it runs on now (below), and how deep in destructors it is, from which
// a panic does not unwind (§5.7): each fiber's own, as the panic is.
// A frame arena (§11.3): the frames of calls of code that may suspend whose frame is not nested in
// their caller's, each taken as the call starts and given back as it ends, last first. A
// generator's or a `handle`'s own arena keeps the one in use as it was entered, `outer`, which is
// in use again should it be freed while in use, as a panic unwinds out of it.
typedef struct fly_frame_chunk fly_frame_chunk;
typedef struct fly_frames fly_frames;
struct fly_frames { char* top; char* end; fly_frame_chunk* chunk; fly_frames* outer; };
// `pend` says why code returned suspended (FLY_PEND_*), and for whom; `frames` is the arena calls
// take frames from.
typedef struct fly_ctx { void* err; bool unwinding; uint8_t pend; fly_handler* handlers; fly_unw* unw; char* panic; uintptr_t limit; int destroying; fly_handler* pend_h; fly_frames* frames; } fly_ctx;
#ifdef FLY_THREADS
// The context of the task running. Within one call of a function it is always the same, wherever
// the task goes on, so it is `const`: a compiler may compute it once a call. It is computed afresh
// from the thread's own pointer to it, which the scheduler sets as it runs each task.
fly_ctx* fly_cx(void) __attribute__((const));
#else
// With one thread there is one context. Code made through LLVM calls the function, which it
// inlines.
extern fly_ctx fly_ctx0;
fly_ctx* (fly_cx)(void);
#define fly_cx() (&fly_ctx0)
#endif
#define fly_err (fly_cx()->err)
#define fly_unwinding (fly_cx()->unwinding)
#define fly_handlers (fly_cx()->handlers)
#define fly_pending (fly_cx()->pend)
#define FLY_FAILED (fly_err != NULL)

// ---- failure ----

// What was thrown, boxed: its tag, for a value of a union, and the bytes of its payload, or of
// the whole value. A `catch` takes it out as the type its pattern takes apart.
void fly_err_box(uint32_t tag, const void* value, size_t size);
uint32_t fly_err_tag(void);
void fly_err_take(void* out, size_t size);

_Noreturn void fly_panic(const char* message);

// ---- the stack (§5.7) ----
// Overflowing a stack is a panic of its task. A function that calls others checks, as it starts,
// that its stack pointer is above the limit of the stack it runs on: that stack's lowest address
// and FLY_HEADROOM. As a panic for an overflow unwinds, half the headroom is the cleanups'; the
// catch point that takes the panic up gives it back. The limit is the task's context's, which the
// runtime sets as it switches stacks: a variable of the thread's could not be read by compiled
// code, which may go on on another thread after a call, the variable's address computed before.
// A freestanding program does not check.
#define FLY_HEADROOM (64u << 10)
_Noreturn void fly_stack_overflow(void);
void fly_stack_at(uintptr_t sp);
// A destructor does not unwind: a panic that escapes one ends the program (§5.7). What drops a
// value runs a `Drop` impl, or unwinds a continuation or a generator, between these.
#define fly_destroy_begin() (fly_cx()->destroying++)
#define fly_destroy_end() (fly_cx()->destroying--)
static inline __attribute__((always_inline)) void fly_stack_check(uintptr_t sp) {
  if (__builtin_expect(sp < fly_cx()->limit, 0)) fly_stack_overflow();
}
// The end of the program, out of memory (§5.7).
_Noreturn void fly_out_of_memory(void);

// ---- panics (§5.7) ----

// A panic unwinds its task as a failure nothing catches would, each function it leaves running
// its cleanups as the platform unwinds it: code made through LLVM by landing pads — natively by
// the tables, under `fly_personality`, in WebAssembly by its own exceptions (FLY_LANDING_PADS) —
// and a program's C by each function's frame record, whose cleanup is its own (c.fly's
// `withLanding`, compiled with -fexceptions: FLY_C_UNWIND). Only catch points take a panic up
// (`fly_try`). In C, which cannot catch, a catch point keeps a record on its fiber's chain while it
// runs — where its frame is, and a jump buffer — which a panic's unwinding stops at and jumps to.
// A freestanding program does not unwind: its panic goes to `fly_os_panic`.
#if !defined(FLY_FREESTANDING) && !defined(FLY_LANDING_PADS)
#include <setjmp.h>
struct fly_unw { fly_unw* prev; uintptr_t frame; jmp_buf buf; };
#define FLY_UNW_CATCH(u) ((u)->frame = (uintptr_t)__builtin_frame_address(0), _setjmp((u)->buf))
static inline void fly_unw_push(fly_unw* u) { fly_ctx* c = fly_cx(); u->prev = c->unw; c->unw = u; }
static inline void fly_unw_pop(fly_unw* u) { fly_cx()->unw = u->prev; }
#endif
// What a catch point that has taken a panic up does to go on with it.
_Noreturn void fly_unwind_on(void);
// A catch point — a task's root, a fiber's, `Io.scope`, `Mutex.lock`, `join`, `main`: runs `f(a)`,
// and gives whether a panic unwound out of it, which is then the fiber's (`fly_ctx.panic`), for
// the catch point to take up or to go on with (`fly_unwind_on`). In native code made through
// LLVM it is the module's own, with a landing pad that catches a panic (llvm.fly); elsewhere it
// takes up a record.
bool fly_try(void (*f)(void* a), void* a);
// A routine of the runtime's that may wait — for the scheduler, a socket, the clock, other tasks —
// is a state machine too, of a few steps: its caller keeps this record of where it stopped, zeroed
// before the first call, and calls it again with it to go on.
typedef struct { int32_t step; int32_t n; int64_t a[3]; void* p[3]; } fly_wait;
// A spawned task's `Task` (§6.1): the task's record, which lasts while it runs or a `Task` refers
// to it. How it ended is TaskEnd's tags, in their order.
enum { FLY_TASK_RUNNING = -1, FLY_TASK_DONE = 0, FLY_TASK_CANCELLED = 1, FLY_TASK_PANICKED = 2 };
void* fly_task_spawn(fly_wait* w, int scope, const fly_fn* f);
void fly_task_cancel(void* t);
int32_t fly_task_wait(fly_wait* w, void* t, fly_String* message);
size_t fly_task_any(fly_wait* w, void* const* ts, size_t n);
void* fly_task_clone(void* t);
void fly_task_drop(void* t);
// The program's root: a panic that unwinds `run` ends the program there. `run` is the root
// machine of the program's one task, given the slot it keeps its frame in.
void fly_root(void (*run)(void**));
// Bytes to standard output.
void fly_out(fly_str s);

// ---- the file system and the process, for `Io` (std/fs, std/process) ----
// Each gives 0, or what went wrong as one of `IoErr`'s tags: 1 `#NotFound`, 2 `#PermissionDenied`,
// 3 `#Exists`, 4 `#NotEmpty`, 5 `#Unsupported`.
int fly_io_stat(fly_str path, uint64_t* size, bool* dir, int64_t* modified);
int fly_io_list(fly_str path, fly_vec* names);
int fly_io_mkdir(fly_str path);
int fly_io_remove(fly_str path);
int fly_io_rename(fly_str from, fly_str to);
bool fly_io_env(fly_str name, fly_String* value);
fly_String fly_io_cwd(void);
int fly_io_run(fly_str program, fly_slice args, fly_str input, int32_t* status, fly_String* out, fly_String* err);
int64_t fly_io_wall(void);
int fly_io_open(fly_str path, uint8_t mode, uint32_t* fd);
int fly_io_read(uint32_t fd, fly_slice buf, uint64_t* n);
int fly_io_write(uint32_t fd, fly_slice buf, uint64_t* n);
void fly_io_close(uint32_t fd);
void fly_fd_release(uint32_t fd);
// Secure random bytes, of the world's seed against a simulated world.
void fly_io_random(fly_slice buf);

// ---- cryptography (std/crypto): OpenSSL's libcrypto natively, the host's under WebAssembly ----
fly_vec fly_crypto_sha256(fly_slice data);
fly_vec fly_crypto_sha384(fly_slice data);
fly_vec fly_crypto_sha512(fly_slice data);
fly_vec fly_crypto_hmac_sha256(fly_slice key, fly_slice data);
fly_vec fly_crypto_hmac_sha512(fly_slice key, fly_slice data);
fly_vec fly_crypto_hkdf_sha256(fly_slice secret, fly_slice salt, fly_slice info, uint64_t length);
fly_vec fly_crypto_seal(fly_slice key, fly_slice nonce, fly_slice plaintext, fly_slice aad);
bool fly_crypto_open(fly_slice key, fly_slice nonce, fly_slice sealed, fly_slice aad, fly_vec* plaintext);
fly_vec fly_crypto_ed25519_public(fly_slice secret);
fly_vec fly_crypto_ed25519_sign(fly_slice secret, fly_slice message);
bool fly_crypto_ed25519_verify(fly_slice key, fly_slice message, fly_slice signature);
bool fly_crypto_equal(fly_slice a, fly_slice b);
_Noreturn void fly_exit(int32_t code);
_Noreturn void fly_panicf(const char* fmt, ...);

// ---- the runtime's Flyscript (selfhost/rt), which every native and WebAssembly program has ----
// A `usize` is 64 bits wide on every target, WebAssembly's too: `uint64_t`, not `size_t`. Each
// is named by its symbol, as the program's C defines it, so that LLVM sees one function, not two
// that meet only once linked: a build split across cores would lose them.
// Numbers as text (rt/format.fly): each writes at `out`, which has room enough, and gives how much.
uint64_t fly_rt_show_f64(double v, uint8_t* out) FLY_SYMBOL(fly_rt_show_f64);
uint64_t fly_rt_float_fixed(double v, uint32_t places, uint8_t* out) FLY_SYMBOL(fly_rt_float_fixed);
bool fly_rt_parse_float(const uint8_t* text, uint64_t len, double* out) FLY_SYMBOL(fly_rt_parse_float);
uint64_t fly_rt_show_int(bool negative, uint64_t high, uint64_t low, uint8_t* out) FLY_SYMBOL(fly_rt_show_int);
// The scheduler of a simulated world (rt/sched.fly): runs the tasks until the main one, whose
// record is `main`, ends.
void fly_rt_tasks(uint64_t seed, uint8_t* main) FLY_SYMBOL(fly_rt_tasks);
int64_t fly_rt_answer(uint8_t* state, int32_t kind) FLY_SYMBOL(fly_rt_answer);
// What the runtime's Flyscript calls of it (rt/sched.fly), by symbol, as Flyscript's C imports it.
int32_t fly_core_run(int32_t id, bool deadlock, bool cancel) FLY_SYMBOL(fly_core_run);
void fly_core_adopt(int32_t id, uint8_t* record) FLY_SYMBOL(fly_core_adopt);
int32_t fly_core_cleaning(int32_t id) FLY_SYMBOL(fly_core_cleaning);
void fly_core_end(int32_t id, bool ran) FLY_SYMBOL(fly_core_end);
void fly_core_sched(uint8_t* state) FLY_SYMBOL(fly_core_sched);
uint64_t fly_core_clock(void) FLY_SYMBOL(fly_core_clock);
void fly_core_set_clock(uint64_t t) FLY_SYMBOL(fly_core_set_clock);
int32_t fly_core_kind(void) FLY_SYMBOL(fly_core_kind);
int64_t fly_core_arg(int32_t i) FLY_SYMBOL(fly_core_arg);
uint8_t* fly_core_ptr(int32_t i) FLY_SYMBOL(fly_core_ptr);
void fly_core_reply(int64_t v) FLY_SYMBOL(fly_core_reply);
void fly_core_answer(int32_t id, int64_t v) FLY_SYMBOL(fly_core_answer);
uint8_t* fly_core_alloc(uint64_t size) FLY_SYMBOL(fly_core_alloc);
void fly_core_free(uint8_t* p) FLY_SYMBOL(fly_core_free);
// Channels and `Mutex` on every core (rt/mt.fly), over the C core's monitors.
uint8_t* fly_rt_mt_channel(void) FLY_SYMBOL(fly_rt_mt_channel);
void fly_rt_mt_free(uint8_t* state) FLY_SYMBOL(fly_rt_mt_free);
bool fly_rt_mt_send(uint8_t* m, uint8_t* state, uint8_t* v, uint64_t size) FLY_SYMBOL(fly_rt_mt_send);
int32_t fly_rt_mt_take(uint8_t* state, uint8_t* out) FLY_SYMBOL(fly_rt_mt_take);
bool fly_rt_mt_deafen(uint8_t* m, uint8_t* state, uint8_t** items, uint64_t* n, uint64_t* size) FLY_SYMBOL(fly_rt_mt_deafen);
bool fly_rt_mt_sender_gone(uint8_t* m, uint8_t* state) FLY_SYMBOL(fly_rt_mt_sender_gone);
void fly_rt_mt_sender_clone(uint8_t* m, uint8_t* state) FLY_SYMBOL(fly_rt_mt_sender_clone);
void fly_rt_mt_lock(uint8_t* m, int32_t* held) FLY_SYMBOL(fly_rt_mt_lock);
void fly_rt_mt_unlock(uint8_t* m, int32_t* held) FLY_SYMBOL(fly_rt_mt_unlock);
void fly_mon_lock(uint8_t* m) FLY_SYMBOL(fly_mon_lock);
void fly_mon_unlock(uint8_t* m) FLY_SYMBOL(fly_mon_unlock);
void fly_mon_wake_one(uint8_t* m) FLY_SYMBOL(fly_mon_wake_one);
void fly_mon_wake_all(uint8_t* m) FLY_SYMBOL(fly_mon_wake_all);
void fly_core_relax(void) FLY_SYMBOL(fly_core_relax);
void fly_core_yield(void) FLY_SYMBOL(fly_core_yield);

// ---- integers ----

_Noreturn void fly_overflow(fly_i128 value, const char* type);
#define FLY_CHECK(T, NAME, LO, HI, X) ({ fly_i128 fly_v_ = (X); if (fly_v_ < (fly_i128)(LO) || fly_v_ > (fly_i128)(HI)) fly_overflow(fly_v_, NAME); (T)fly_v_; })
// Checked arithmetic at the type's own width: the builtins compute the exact result and say whether
// a `T` holds it. Only when it does not is the result made again, in 128 bits, for the message.
#define FLY_ADD(T, NAME, X, Y) ({ T fly_r_; if (__builtin_add_overflow((X), (Y), &fly_r_)) fly_overflow(fly_add128((fly_i128)(X), (fly_i128)(Y)), NAME); fly_r_; })
#define FLY_SUB(T, NAME, X, Y) ({ T fly_r_; if (__builtin_sub_overflow((X), (Y), &fly_r_)) fly_overflow(fly_sub128((fly_i128)(X), (fly_i128)(Y)), NAME); fly_r_; })
#define FLY_MUL(T, NAME, X, Y) ({ T fly_r_; if (__builtin_mul_overflow((X), (Y), &fly_r_)) fly_overflow(fly_mul128((fly_i128)(X), (fly_i128)(Y)), NAME); fly_r_; })
fly_i128 fly_add128(fly_i128 a, fly_i128 b);
fly_i128 fly_sub128(fly_i128 a, fly_i128 b);
fly_i128 fly_mul128(fly_i128 a, fly_i128 b);
_Noreturn void fly_div_zero(void);

// ---- strings ----

fly_str fly_str_lit(const char* bytes, size_t len);
fly_str fly_String_as_str(const fly_String* s);
fly_String fly_String_new(void);
fly_String fly_String_from(fly_str s);
void fly_String_push(fly_String* s, fly_str t);
void fly_String_push_byte(fly_String* s, uint8_t b);
void fly_String_drop(fly_String* s);
// Room for `extra` more bytes, or false if there is no memory for it.
bool fly_String_try_reserve(fly_String* s, size_t extra);
fly_String fly_String_clone(const fly_String* s);
bool fly_str_eq(fly_str a, fly_str b);
int fly_str_cmp(fly_str a, fly_str b);
fly_str fly_str_slice(fly_str s, size_t lo, size_t hi);
fly_String fly_show_i128(fly_i128 v);
fly_String fly_show_u128(unsigned __int128 v);
fly_String fly_show_f64(double v);
fly_String fly_float_fixed(double v, uint32_t digits);
fly_String fly_show_bool(bool v);
void fly_println(fly_str s);
void fly_eprintln(fly_str s);
bool fly_str_next_line(fly_str* rest, fly_str* line);
bool fly_str_next_word(fly_str* rest, fly_str* word);
bool fly_str_find(fly_str s, fly_str needle, uint64_t* at);
bool fly_str_starts(fly_str s, fly_str prefix);
bool fly_str_ends(fly_str s, fly_str suffix);
fly_str fly_str_trim(fly_str s);
fly_String fly_str_case(fly_str s, bool upper);
fly_String fly_str_replace_all(fly_str s, fly_str from, fly_str to);
fly_vec fly_str_split(fly_str s, fly_str sep);
bool fly_parse_int(fly_str s, int64_t* out);
bool fly_parse_float(fly_str s, double* out);

// ---- lists ----

void* fly_vec_at(const fly_vec* v, size_t i, size_t size);
_Noreturn void fly_out_of_bounds(uint64_t i, uint64_t len);
void fly_vec_push(fly_vec* v, const void* elem, size_t size);
void fly_vec_extend(fly_vec* v, const void* elems, size_t n, size_t size);
void fly_slice_copy(fly_slice to, fly_slice from, size_t size);
// Room for `extra` more elements, or false if there is no memory for it.
bool fly_vec_try_reserve(fly_vec* v, size_t extra, size_t size);
bool fly_vec_pop(fly_vec* v, void* out, size_t size);
void fly_vec_insert(fly_vec* v, size_t i, const void* elem, size_t size);
void fly_vec_remove(fly_vec* v, size_t i, void* out, size_t size);
void fly_vec_truncate_raw(fly_vec* v, size_t n);
void fly_vec_free(fly_vec* v);
fly_slice fly_vec_slice(const fly_vec* v);
void* fly_slice_at(fly_slice s, size_t i, size_t size);
fly_slice fly_slice_range(fly_slice s, size_t lo, size_t hi, size_t size);
fly_vec fly_vec_from(const void* elems, size_t n, size_t size);
void fly_slice_reverse(fly_slice s, size_t size);
// A stable sort, by `cmp` given `ctx`.
void fly_sort(fly_slice s, size_t size, int (*cmp)(void* ctx, const void* a, const void* b), void* ctx);

// ---- maps ----

// A hash map: its entries in the order they were inserted, each a key and a value laid out as the
// entry type the compiler makes, and an index from hashes to entries. Hashing and comparing keys is
// the compiler's: it hashes a key with the key type's `Hash` and gives the lookup its `Eq`.
typedef struct {
  uint8_t* entries;
  uint64_t* hashes;
  size_t len, cap;
  uint32_t* slots;
  size_t nslots;
} fly_map;
size_t fly_map_find(const fly_map* m, uint64_t h, const void* probe, bool (*eq)(const void* entry, const void* probe), size_t esize);
void* fly_map_append(fly_map* m, uint64_t h, size_t esize);
// Room for `extra` more entries, index included, or false if there is no memory for it.
bool fly_map_try_reserve(fly_map* m, size_t extra, size_t esize);
void fly_map_remove_at(fly_map* m, size_t i, void* out, size_t esize);
void fly_map_free(fly_map* m);

// As the reference hashes: FNV-1a over the bytes each write gives.
typedef struct { uint64_t h; } fly_Hasher;
fly_Hasher fly_Hasher_new(void);
void fly_Hasher_writeInt(fly_Hasher* h, int64_t v);
void fly_Hasher_writeFloat(fly_Hasher* h, double v);
void fly_Hasher_writeBool(fly_Hasher* h, bool v);
void fly_Hasher_writeStr(fly_Hasher* h, fly_str s);
uint64_t fly_Hasher_finish(const fly_Hasher* h);

// ---- generators ----

// A generator pulled for its items: its state, what makes its next item (false at the end), and
// what drops it. The compiler makes `next` for each kind of item.
typedef struct { void* st; bool (*next)(void* st, void* out); void (*drop)(void* st); } fly_gen;
// The state of a generator over the elements of a list, or of a map's entries: every `stride`
// bytes from `base`.
typedef struct { uint8_t* base; size_t len, i, stride; } fly_iter;
void* fly_iter_new(void* base, size_t len, size_t stride);
void fly_gen_drop(fly_gen* g);
// The states of the adapters: what they pull from, and what they add.
typedef struct { fly_gen in; fly_fn f; } fly_gmap;
typedef struct { fly_gen in; uint64_t n; } fly_gcount;
typedef struct { fly_gen a, b; } fly_gzip;
void* fly_gmap_new(fly_gen in, fly_fn f);
void* fly_gcount_new(fly_gen in, uint64_t n);
void* fly_gzip_new(fly_gen a, fly_gen b);
void fly_gmap_drop(void* s);
void fly_gcount_drop(void* s);
void fly_gzip_drop(void* s);

// ---- memory ----

void* fly_alloc(size_t size);
// An `Arc`'s contents, after a count of the handles to them.
void* fly_arc_new(size_t size);
void* fly_arc_retain(void* p);
// Whether that was the last handle: the contents are then the caller's to drop, then free.
bool fly_arc_release(void* p);
void fly_arc_free(void* p);
void* fly_box(const void* value, size_t size);

// ---- fibers and handlers ----

// A fiber: a stack of its own, which runs until it suspends and is resumed where it left off.
typedef struct fly_fiber fly_fiber;
// A `handle`: the effect it handles, the operation the body performed (-1 for none), where the body
// keeps that operation's arguments and wants its result, and the handlers around it.
struct fly_handler {
  uint32_t effect;
  int op;
  void* args;
  void* result;
  fly_handler* outer;
  // A direct handler's arms: its body runs where it is, and each operation calls them, given its
  // frame, and returns with the result they give.
  void (*direct)(void* frame, int op, void* args, void* result);
  void* frame;
  // The handlers in force where its body last performed one of its operations.
  fly_handler* from;
  // Its body is being dropped: cut off from every handler, what it performs is cancelled (§5.3).
  bool dying;
  // An arm lets its continuation leave it: the body, dropped, is cut off.
  bool kept;
  // Its body, a state machine, is suspended by an operation of its own.
  bool waiting;
};
void fly_perform(uint32_t effect, int op, void* args, void* result);
// Whether a `handle` of `effect` is around the running code.
bool fly_handled(uint32_t effect);
// Cleanup — a `defer`, a destructor — runs to its end however its block is left: what is
// unwinding past it is set aside while it runs, so its own failures, loops and handlers work,
// and then goes on.
typedef struct { void* err; bool unwinding; } fly_unwind_state;
fly_unwind_state fly_cleanup_begin(void);
void fly_cleanup_end(fly_unwind_state s);
// A continuation: the frame of the `handle` it resumes, how to resume it with the operation's
// result, and how to drop it, which unwinds the body.
typedef struct { void* frame; void* resume; void (*drop)(void* frame); } fly_cont;
void fly_cont_drop(fly_cont* k);


// ---- code that may suspend, as state machines (§11.3) ----
// A call that suspends returns with the task's context pending: `pend` says why — an item yielded
// to what pulls the generator, an operation performed for the handler `pend_h` — and every
// function between it and the code that takes the suspension returns too, its frame saying where
// it stopped. Called again with its frame, each goes on from there. A function's frame is nested
// in its caller's when the caller can say what it is; otherwise the callee takes it from the
// task's frame arena as it starts, keeping it in a slot its caller holds, and gives it back as it
// ends.
enum { FLY_PEND_YIELD = 1, FLY_PEND_PERFORM = 2, FLY_PEND_WAIT = 3 };
void* fly_frame_push(size_t size);
void fly_frame_pop(void* frame);
// A machine's frame, from the slot its caller holds: taken from the arena as the machine first starts.
void* fly_frame_take(void** slot, size_t size);
void fly_frames_free(fly_frames* a);
// Where the arena in use is, kept as a catch point is entered, and given back as it takes up a
// panic, the frames the panic left behind with it.
typedef struct { fly_frames* frames; char* top; } fly_frames_mark;
void fly_frames_keep(fly_frames_mark* m);
void fly_frames_back(const fly_frames_mark* m);
// A suspended machine whose frame is `frame`, dropped: called again unwinding, it runs its
// cleanup for where it stopped. `call` calls it.
void fly_machine_unwind(void (*call)(void* env, void* frame), void* env, void* frame);
// A handler's body runs under it, with the frames of what it calls indirectly in its own arena,
// for its continuation may outlive the code that started it (§5.3).
void fly_handle_enter(fly_handler* h, fly_frames* arena, fly_frames** saved);
void fly_handle_leave(fly_handler* h, fly_frames* saved);
// Whether the code that returned performed an operation of `h`'s: then it is `h`'s to run.
bool fly_handle_took(fly_handler* h);
// A suspended body, dropped, runs its cleanup: what the code dropping it is in the middle of is
// set aside meanwhile, and a body whose continuation could leave its arm is cut off from every
// handler (§5.3).
fly_unwind_state fly_handle_drop_begin(fly_handler* h);
void fly_handle_drop_end(fly_unwind_state s);
// The same, for code that passes only pointers: drops `h`'s body, its frame in the slot `bslot`, by
// calling `run(h)`, under `h` and with the arena of what the body calls, if the body is suspended.
void fly_handle_drop_m(fly_handler* h, fly_frames* arena, void** bslot, void (*run)(void* h));
// `generate(f)` over a producer made a state machine: it runs until it yields, and is pulled.
fly_gen fly_generate_m(fly_fn producer);

// ---- the simulated world and tasks (§6.4) ----

// The world a program runs against, from `FLY_WORLD`: connections waiting to be accepted, a
// database of profiles and quotas, the percent of I/O operations that fail, and the seed that
// decides which do and how tasks interleave. Time passes only as tasks sleep.
extern uint64_t fly_clock;
bool fly_fault(void);
bool fly_world_accept(fly_str* input);
bool fly_world_profile(fly_str user, fly_str* name);
bool fly_world_quota(fly_str token);

// Tasks. Against a simulated world one runs at a time, and at each scheduling point the next is
// chosen by a seeded generator, as the reference's scheduler does, so a seed reproduces an
// interleaving. Otherwise they run on a worker thread for each core. `fly_tasks_run` runs `main`
// as the first task, on the main stack's behalf.
extern bool fly_tasks_on;
void fly_tasks_run(void (*main)(void**));
void fly_point(fly_wait* w);
void fly_sleep(fly_wait* w, uint64_t nanos);
// The time: the simulated world's clock, or the machine's monotonic one, in nanoseconds.
uint64_t fly_now(void);
// A `Mutex`: its state on the heap after a header holding its lock, which `fly_lock` takes by the
// state's address. The body it guards performs nothing, so it holds no other lock and does not
// suspend while it holds this one.
void* fly_mutex_new(const void* value, size_t size);
void fly_mutex_free(void* state);
void fly_lock(const void* state);
// Whether a panic left the state while it was lent, which locking it again panics over (§6.2).
void fly_mutex_check(const void* state);
void fly_mutex_poison(const void* state, bool poisoned);
// A panic unwound a scope's body: its tasks are cancelled and waited for, and the panic goes on.
void fly_scope_panicked(fly_wait* w, int sid);
// `fetchAdd` of an `Atomic<i64>`: what was there; a sum that overflows panics and changes nothing.
int64_t fly_atomic_add(int64_t* a, int64_t v);
void fly_unlock(const void* state);
// `join(a, b)` of `std/par`: both run, maybe at once on two cores, each putting its result where
// its `out` points; each is pure, so the order cannot be seen.
void fly_par_join(void (*a)(void* f, void* out), void* fa, void* oa, void (*da)(void* out),
                  void (*b)(void* f, void* out), void* fb, void* ob, void (*db)(void* out));
// A task's outcome: its value (`size` bytes), or its failure.
int fly_spawn(fly_wait* w, int scope, void (*entry)(void* task, void* closure, void** slot), const fly_fn* f, size_t size);
void* fly_task_result(void* task);
void* fly_task_closure(void* task);
void fly_join(fly_wait* w, int task, void* out);
int fly_scope_open(void);
void fly_scope_close(fly_wait* w, int scope, bool body_failed);
void fly_panic_deadlock(void);

typedef struct { int ch; } fly_chan;
// A connection. Against a simulated world: what the other end sent, how much has been read, what
// was written to it, which is the program's output once it closes, and the peer it was made to,
// if the program connected. Otherwise its descriptor, plus one, so that a socket of zeros has none,
// and its TLS session, libssl's, if it has one.
typedef struct { fly_str input; size_t pos; int fd; fly_String out; fly_str peer; void* tls; } fly_socket;
// What a socket operation failed with: an `IoErr`, by its tag's name, or nothing.
enum { FLY_IO_OK, FLY_IO_RESET, FLY_IO_TIMED_OUT, FLY_IO_BROKEN_PIPE, FLY_IO_NOT_FOUND, FLY_IO_PERMISSION_DENIED, FLY_IO_ADDR_IN_USE, FLY_IO_REFUSED, FLY_IO_UNTRUSTED };
// A listener: against a simulated world, its port; otherwise its descriptor, plus one. Negative,
// what binding failed with.
int fly_listen(uint16_t port);
uint16_t fly_listener_port(int listener);
// The next connection, or none, ever: the world has no more, or the listener failed.
bool fly_accept(fly_wait* w, int listener, fly_socket* out);
// A connection to `host` on `port`, or what connecting failed with.
int fly_connect(fly_wait* w, fly_str host, uint16_t port, fly_socket* out);
// A connection over TLS: the peer's certificate verified, for `host`, against the system's roots.
int fly_connect_tls(fly_wait* w, fly_str host, uint16_t port, fly_socket* out);
int fly_sock_read(fly_wait* w, fly_socket* s, fly_slice buf, uint64_t* n);
int fly_sock_write(fly_wait* w, fly_socket* s, fly_slice bytes);
// A whole HTTP response of `code`, with `body`: in a simulated world, a line of the output.
int fly_sock_status(fly_wait* w, fly_socket* s, unsigned code, fly_str body);
void fly_sock_close(fly_socket* s);
// A task running a closure that gives nothing: it calls it, then drops it.
void fly_task_void(void* task, void* closure, void** slot);
// A channel, given what drops a message of its, if anything must.
fly_chan fly_channel(void (*drop)(void*));
bool fly_send(fly_wait* w, fly_chan c, const void* v, size_t size);
bool fly_recv(fly_wait* w, fly_chan c, void* out, size_t size);
void fly_close(fly_wait* w, fly_chan c);
void fly_sender_drop(fly_chan* c);
void fly_receiver_drop(fly_chan* c);
fly_chan fly_sender_clone(const fly_chan* c);

// ---- regions ----

// A region's arena: chunks bump-allocated, released all at once when the region ends. Region data
// is all `Copy`, so nothing in it needs dropping (§4.6).
typedef struct fly_chunk fly_chunk;
typedef struct { fly_chunk* head; } fly_arena;
void* fly_arena_alloc(fly_arena* a, size_t size);
void fly_arena_free(fly_arena* a);
fly_str* fly_arena_str(fly_arena* a, fly_str s);
fly_slice* fly_arena_slice(fly_arena* a, fly_slice s, size_t size);
// An append-only list in a region, whose elements never move: chunks of doubling size.
typedef struct fly_rchunk { struct fly_rchunk* next; size_t len, cap, pad; } fly_rchunk;
typedef struct { fly_arena* arena; size_t len, size; fly_rchunk *first, *last; } fly_rlist;
fly_rlist* fly_rlist_new(fly_arena* a, size_t size);
bool fly_utf8_valid(fly_slice b);
fly_String fly_utf8_lossy(fly_vec b);
void fly_rlist_push(fly_rlist* l, const void* v);
// The address of element `i`, which exists: chunks double, so few are passed on the way.
void* fly_rlist_at(const fly_rlist* l, size_t i);
// The elements of a chunk follow it.
#define FLY_RCHUNK_DATA(c) ((uint8_t*)((c) + 1))

// ---- files ----

// A file opened: all its text, read when it was opened.

// ---- the program ----

extern int fly_argc;
extern char** fly_argv;
fly_str fly_arg_str(int i);
int64_t fly_arg_int(int i);
double fly_arg_float(int i);
// The arguments from the `i`th on, as `str`s or as `String`s.
fly_slice fly_arg_strs(int i);
fly_slice fly_arg_strings(int i);
void fly_args_free(fly_slice s, bool strings);
