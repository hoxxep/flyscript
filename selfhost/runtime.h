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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint8_t fly_unit;
typedef __int128 fly_i128;

typedef struct { const uint8_t* ptr; size_t len; } fly_str;
typedef struct { uint8_t* ptr; size_t len; size_t cap; } fly_String;
typedef struct { void* ptr; size_t len; size_t cap; } fly_vec;
typedef struct { void* ptr; size_t len; } fly_slice;
// A closure: its environment, what drops it, and its code, cast to its type where it is called.
typedef struct { void* env; void (*drop)(void*); void* fn; } fly_fn;

// ---- failure ----

// The failure being raised, if any: what was thrown, boxed. A function that may fail returns with
// this set; its caller checks it after the call.
extern void* fly_err;
#define FLY_FAILED (fly_err != NULL)

// What was thrown, boxed: its tag, for a value of a union, and the bytes of its payload, or of
// the whole value. A `catch` takes it out as the type its pattern takes apart.
void fly_err_box(uint32_t tag, const void* value, size_t size);
uint32_t fly_err_tag(void);
void fly_err_take(void* out, size_t size);

_Noreturn void fly_panic(const char* message);
_Noreturn void fly_panicf(const char* fmt, ...);

// ---- integers ----

_Noreturn void fly_overflow(fly_i128 value, const char* type);
#define FLY_CHECK(T, NAME, LO, HI, X) ({ fly_i128 fly_v_ = (X); if (fly_v_ < (fly_i128)(LO) || fly_v_ > (fly_i128)(HI)) fly_overflow(fly_v_, NAME); (T)fly_v_; })
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
fly_String fly_String_clone(const fly_String* s);
bool fly_str_eq(fly_str a, fly_str b);
int fly_str_cmp(fly_str a, fly_str b);
fly_str fly_str_slice(fly_str s, size_t lo, size_t hi);
fly_String fly_show_i128(fly_i128 v);
fly_String fly_show_u128(unsigned __int128 v);
fly_String fly_show_f64(double v);
fly_String fly_show_bool(bool v);
void fly_println(fly_str s);
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
void fly_vec_push(fly_vec* v, const void* elem, size_t size);
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
void* fly_box(const void* value, size_t size);

// ---- the program ----

extern int fly_argc;
extern char** fly_argv;
fly_str fly_arg_str(int i);
int64_t fly_arg_int(int i);
