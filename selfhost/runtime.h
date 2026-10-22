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
// What compiled code reads and sets of the task running: the failure being raised, if any — what
// was thrown, boxed, which a function that may fail returns with set, for its caller to check;
// whether the task unwinds, a computation whose continuation was dropped; whether a generator
// stops; and the handlers in force, innermost first.
typedef struct fly_ctx { void* err; bool unwinding, stopping; fly_handler* handlers; } fly_ctx;
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
#define fly_stopping (fly_cx()->stopping)
#define fly_handlers (fly_cx()->handlers)
#define FLY_FAILED (fly_err != NULL)

// ---- failure ----

// What was thrown, boxed: its tag, for a value of a union, and the bytes of its payload, or of
// the whole value. A `catch` takes it out as the type its pattern takes apart.
void fly_err_box(uint32_t tag, const void* value, size_t size);
uint32_t fly_err_tag(void);
void fly_err_take(void* out, size_t size);

_Noreturn void fly_panic(const char* message);
_Noreturn void fly_exit(int32_t code);
_Noreturn void fly_panicf(const char* fmt, ...);

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

// What a generator function yields to: a loop's body, called with a pointer to each item, which
// says whether it wants another. One that does not makes the generator stop: it sets
// `fly_stopping` and unwinds, and the loop that started it clears it.
typedef struct { void* env; bool (*fn)(void* env, void* item); } fly_yield;

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
// A `handle` running its body on a fiber: the effect it handles, the operation the body performed
// (-1 for none), where the body keeps that operation's arguments and wants its result, the
// handlers around it, and the fiber the body is suspended in. A direct one (§5.3) has no fiber.
struct fly_handler {
  uint32_t effect;
  int op;
  void* args;
  void* result;
  fly_handler* outer;
  fly_fiber* fiber;
  fly_fiber* suspended;
  // A direct handler's arms: its body runs where it is, and each operation calls them, given its
  // frame, and returns with the result they give.
  void (*direct)(void* frame, int op, void* args, void* result);
  void* frame;
};
void fly_perform(uint32_t effect, int op, void* args, void* result);
// Whether a `handle` of `effect` is around the running code.
bool fly_handled(uint32_t effect);
// Cleanup — a `defer`, a destructor — runs to its end however its block is left: what is
// unwinding past it is set aside while it runs, so its own failures, loops and handlers work,
// and then goes on.
typedef struct { void* err; bool unwinding, stopping; } fly_unwind_state;
fly_unwind_state fly_cleanup_begin(void);
void fly_cleanup_end(fly_unwind_state s);
// Starts `h`'s body, `entry(arg)`, on a fiber of its own; runs it until it performs `h`'s effect or
// finishes, as resuming does.
void fly_handle_start(fly_handler* h, void (*entry)(void*), void* arg);
void fly_handle_resume(fly_handler* h);
bool fly_handle_done(const fly_handler* h);
// Unwinds a suspended body, running its cleanup.
void fly_handle_unwind(fly_handler* h);
void fly_handle_free(fly_handler* h);

// A continuation: the frame of the `handle` it resumes, how to resume it with the operation's
// result, and how to drop it, which unwinds the body.
typedef struct { void* frame; void* resume; void (*drop)(void* frame); } fly_cont;
void fly_cont_drop(fly_cont* k);

// `generate(f)`: a generator pulled by running `f` on a fiber until it yields.
fly_gen fly_generate(fly_fn producer, size_t size);

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
void fly_tasks_run(void (*main)(void));
void fly_point(void);
void fly_sleep(uint64_t nanos);
// The time: the simulated world's clock, or the machine's monotonic one, in nanoseconds.
uint64_t fly_now(void);
// A `Mutex`: its state on the heap after a header holding its lock, which `fly_lock` takes by the
// state's address. The body it guards performs nothing, so it holds no other lock and does not
// suspend while it holds this one.
void* fly_mutex_new(const void* value, size_t size);
void fly_mutex_free(void* state);
void fly_lock(const void* state);
void fly_unlock(const void* state);
// `join(a, b)` of `std/par`: both run, maybe at once on two cores, each putting its result where
// its `out` points; each is pure, so the order cannot be seen.
void fly_par_join(void (*a)(void* f, void* out), void* fa, void* oa, void (*b)(void* f, void* out), void* fb, void* ob);
// A task's outcome: its value (`size` bytes), or its failure.
int fly_spawn(int scope, void (*entry)(void* task, void* closure), void* closure, size_t size);
void* fly_task_result(void* task);
void* fly_task_closure(void* task);
void fly_join(int task, void* out);
int fly_scope_open(void);
void fly_scope_close(int scope, bool body_failed);
void fly_panic_deadlock(void);

typedef struct { int ch; } fly_chan;
// A connection. Against a simulated world: what the other end sent, how much has been read, what
// was written to it, which is the program's output once it closes, and the peer it was made to,
// if the program connected. Otherwise its descriptor, plus one, so that a socket of zeros has none.
typedef struct { fly_str input; size_t pos; int fd; fly_String out; fly_str peer; } fly_socket;
// What a socket operation failed with: an `IoErr`, by its tag's name, or nothing.
enum { FLY_IO_OK, FLY_IO_RESET, FLY_IO_TIMED_OUT, FLY_IO_BROKEN_PIPE, FLY_IO_NOT_FOUND, FLY_IO_PERMISSION_DENIED, FLY_IO_ADDR_IN_USE, FLY_IO_REFUSED };
// A listener: against a simulated world, its port; otherwise its descriptor, plus one. Negative,
// what binding failed with.
int fly_listen(uint16_t port);
uint16_t fly_listener_port(int listener);
// The next connection, or none, ever: the world has no more, or the listener failed.
bool fly_accept(int listener, fly_socket* out);
// A connection to `host` on `port`, or what connecting failed with.
int fly_connect(fly_str host, uint16_t port, fly_socket* out);
int fly_sock_read(fly_socket* s, fly_slice buf, uint64_t* n);
int fly_sock_write(fly_socket* s, fly_slice bytes);
// A whole HTTP response of `code`, with `body`: in a simulated world, a line of the output.
int fly_sock_status(fly_socket* s, unsigned code, fly_str body);
void fly_sock_close(fly_socket* s);
// A task running a closure that gives nothing: it calls it, then drops it.
void fly_task_void(void* task, void* closure);
// A channel, given what drops a message of its, if anything must.
fly_chan fly_channel(void (*drop)(void*));
bool fly_send(fly_chan c, const void* v, size_t size);
bool fly_recv(fly_chan c, void* out, size_t size);
void fly_close(fly_chan c);
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
void fly_rlist_push(fly_rlist* l, const void* v);
// The address of element `i`, which exists: chunks double, so few are passed on the way.
void* fly_rlist_at(const fly_rlist* l, size_t i);
// The elements of a chunk follow it.
#define FLY_RCHUNK_DATA(c) ((uint8_t*)((c) + 1))

// ---- files ----

// A file opened: all its text, read when it was opened.
typedef struct { fly_String text; } fly_File;
bool fly_read_file(fly_str path, fly_String* out);
bool fly_write_file(fly_str path, fly_str content);
void fly_File_drop(fly_File* f);

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
