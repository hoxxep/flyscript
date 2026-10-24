# The Flyscript standard library

**Library specification, for language version 0.63**

This document specifies the standard library as [the language specification](spec.md) specifies the core: what each export does, what it performs, when it fails or panics, and what it costs where that is part of its contract. A program may rely on what is stated here and on nothing else. The declaration files and modules under `std/` give the signatures; every name they export is specified below, which a test of the repository checks.

Throughout:

- **Effects are the contract.** A function with no `uses` clause is pure (spec §5.1): it observes nothing outside its arguments and allocates only what it returns. One that synchronizes with other tasks performs `Io` and is a *scheduling point*: another task may run there, and a cancellation may be delivered there (spec §6.1).
- **Failures are typed.** `Fail<E>` lists what a function throws. `IoErr` is `#Reset | #TimedOut | #BrokenPipe | #NotFound | #PermissionDenied | #AddrInUse | #Refused`.
- **Panics are bugs.** An index out of bounds, `unwrap()` of `#None`, integer overflow and heap exhaustion panic (spec §5.7); a function that can panic otherwise says when.
- **Positions in text are byte offsets**, and text is UTF-8. A position inside a character, where a function would split one, panics.
- **Complexity** is stated where it is a promise; *amortized* is over a sequence of calls on one value.
- **Simulated and real worlds.** Every `Io` operation means the same against the machine and against a simulated world (spec §6.4); where what they can observe differs, both are stated.

---

## 1. The prelude

In scope in every module without an import.

### 1.1 Interfaces

| Interface | Meaning |
| :--- | :--- |
| `Copy` | The value is its bits: assigning it copies it, and the original stays usable. Structural: a type is `Copy` when every part is and nothing in it implements `Drop` (spec §4.4). |
| `Send` | The value may move to another task: it holds no borrow, no `Ptr` and no runtime handle (`Cont`, `Fiber`, `Scope`). Region data is `Send`, since an outer region is frozen while tasks run. Structural (spec §4.4). |
| `LentBy<K>` | `Q extends LentBy<K>` holds when `K` is `Q` or lends `Q`: `String` lends `str`, `Vec<T>` lends `T[]`. Lookups take anything a key lends, so a `HashMap<String, V>` is searched with a `str`. |
| `Drop` | `drop(self: mut Self): void` runs when a value's owner ends. It performs no effects (spec §5.6). |
| `Eq` | `eq(self, other): bool`, an equivalence. `==` and `!=` call it on anything but a primitive. Derived, floats are equal by a total equality: `NaN` equals itself and `-0.0` equals `0.0`, as `Hash` agrees. |
| `Ord` | `cmp(self, other): Ordering`, a total order agreeing with `Eq`; `<`, `<=`, `>` and `>=` call it on anything but a primitive. Derived, it orders by fields in declaration order, then by tags in declaration order. |
| `Hash` | `hash(self, h: mut Hasher): void`, agreeing with `Eq`: equal values hash equally. |
| `Show` | `show(self, out: mut String): void` writes the value as Flyscript would: strings quoted, `Point { x: 1, y: 2 }`, `#Some(3)`. A template's `${e}` uses it for anything but a primitive or a string. |
| `Clone` | `clone(self): Self`, an independent copy. |
| `Iterable<T, row E = []>` | `each(self): void uses Yield<T>, ...E`: what `for…of` iterates (spec §5.5). |

`Eq`, `Ord`, `Hash`, `Show` and `Clone` are derived, by Flyscript code in the prelude, for every record, tuple, tag union, array and slice whose parts have them, and for a struct or enum that asks with `impl Eq for Point;` (spec §3.5, §7.3). `Ordering` is `#Less | #Equal | #Greater`. `min(a, b)` and `max(a, b)` give one of two `Ord` values, the first when they are equal. `writeQuoted(s, out)` writes `s` as `Show` writes a string: quoted, with `"`, `\` and control characters escaped.

`Hasher` is what a `hash` writes into: `Hasher.new()`, `writeInt(i64)`, `writeFloat(f64)`, `writeBool(bool)`, `writeStr(str)`, and `finish(): u64`. Its algorithm is unspecified, so a program may not store a hash or rely on one across runs.

### 1.2 Options, results and failures

`Option<T>` is `#Some(T) | #None` and `Result<T, E>` is `#Ok(T) | #Err(E)`, ordinary tag unions.

- `o.isSome()`, `o.isNone()`; `o.take()` gives what was there and leaves `#None`; `o.unwrapOr(fallback)`; `o.map(f)`, which performs what `f` does; `o.unwrap()`, which panics on `#None`. An `Option<readonly T>` of a `Clone` type has `o.cloned()`, an owned copy.
- `r.unwrap()` gives the `#Ok` value or throws the `#Err` one (`uses Fail<E>`); `r.isOk()`, `r.isErr()`.
- `Fail.capture(body)` runs `body` and gives its value as `#Ok`, or what it threw as `#Err`, passing on its other effects; `Fail.map(body, wrap)` runs `body` and throws `wrap(e)` for each failure `e` (spec §5.4).
- `panic(message): never` panics (spec §5.7).

### 1.3 Numbers

`f64` and `f32` have the arithmetic of C's `<math.h>`: `sqrt()`, `abs()`, `floor()`, `ceil()`, `round()` (halves away from zero), `trunc()`, `sin()`, `cos()`, `tan()`, `atan2(x)`, `exp()`, `ln()`, `pow(e)`, and `min(other)` and `max(other)`, which take the number when the other is `NaN`; and `toFixed(digits): String`, the number with `digits` digits after the point (at most 100), rounded to the nearest, a value exactly halfway to the even one: `(0.125).toFixed(2)` is `"0.12"`, and `NaN`, `inf` and `-inf` are written so. An `f32`'s results are rounded to its precision.

A float is written — in a template, by `println`, by `Show` — as `NaN`, `inf` or `-inf`; a whole number smaller than 10^15 with `.0` after it, `-0.0` for negative zero; and otherwise as the fewest digits that read back as the same float, the nearest of them to it, written out in full and never with an exponent: `0.1 + 0.2` is `0.30000000000000004`, `1.5e-7` is `0.00000015` and `1e21` is `1000000000000000000000`. Every implementation writes and reads floats exactly, with no help from the C library's `printf` or `strtod`.

Every integer type has `wrappingAdd`, `wrappingSub` and `wrappingMul`, which wrap at the type's width where `+`, `-` and `*` panic. `parseInt(s): Option<i64>` and `parseFloat(s): Option<f64>` read decimal text as TypeScript's functions do, without `NaN`: an optional sign and digits, and nothing else, not even spaces; `#None` otherwise, or for an integer that does not fit. A float's digits may have a point among them, before them or after them (`1.5`, `.5`, `5.`), and an exponent after them (`2.5e-3`, `1E6`); it reads as the nearest float, a value exactly halfway to the even one, and as `inf` past the largest.

### 1.4 Strings

`str` is a borrowed run of UTF-8; `String` an owned, growable one, which lends `str`.

- `String.new()`; `s.len()`, in bytes; `s.push(t)`, amortized O(length of `t`); `s.asStr()`; `s.tryReserve(n)`, room for `n` more bytes or `#OutOfMemory`; `String.fromUtf8(bytes): Option<String>`, `#None` if the bytes are not UTF-8.
- On a `str`: `len()`; `slice(lo, hi)`, which panics unless `lo <= hi <= len()`; `toString()`; `asBytes()`; the generators `bytes()`, `lines()` (each line without its `\n` or `\r\n`; a last empty line is not one) and `splitWhitespace()`; `split(sep): Vec<String>`; `trim()`, `trimStart()`, `trimEnd()`; `includes(needle)`, `startsWith(prefix)`, `endsWith(suffix)`, `indexOf(needle)`, `lastIndexOf(needle)`; `replaceAll(from, to)`; `repeat(n)`; `padStart(width)` and `padEnd(width)`, which pad with spaces to `width` characters; and `toUpperCase()` and `toLowerCase()`, which change ASCII letters only, leaving every other character as it is.
- `String` is `Eq`, `Ord` (by bytes), `Hash`, `Show` and `Clone`.

### 1.5 Arrays, slices and `Vec`

`T[N]` is an array, `T[]` a slice (a borrowed run), `Vec<T>` an owned, growable list. Arrays and `Vec`s lend slices, and every method of a slice is theirs too.

- A slice: `len()`, `iter()`, `iterMut()`, `get(i): Option<readonly T>`, `first()`, `last()`; `splitAt(at)`, two disjoint `mut` slices, which panics if `at > len()`; `swap(i, j)`; `reverse()`; `sortBy(cmp)`, stable and O(n log n); with `T extends Ord`, `sort()`; with `T extends Eq`, `includes(x)` and `indexOf(x)`; with `T extends Show`, `join(sep)`, each element shown, strings as they are. `xs[i]` panics if `i >= len()`, as `xs[lo..hi]` does outside the slice.
- A `Vec`: `Vec.new()`; `push(v)`, amortized O(1); `pop(): Option<T>`; `remove(i): T` and `insert(i, v)`, O(length), which panic if `i` is out of range; `retain(keep)`, in place; `truncate(n)`, dropping the elements past `n`; `drain()`, a generator taking every element out in order and leaving the `Vec` empty; `len()`; `iter()`; `iterMut()`; `tryReserve(n)`.
- `repeat<T extends Copy, N>(v): T[N]`, `N` copies of `v`.
- Arrays, slices and `Vec`s are `Iterable` of `readonly T`, and have every derived interface their elements have.

### 1.6 Boxes and sharing

- `Box<T>`, a value on the heap, owned: `Box.new(v)`; `Box.tryNew(v)`, `#OutOfMemory` rather than a panic; `b.get()`; `b.into()`, the value, the box gone. A box compares, orders, hashes, shows and clones as its contents.
- `Arc<T extends Send>`, a value shared by counting its owners, immutable while shared: `Arc.new(v)`, `a.get()`, and `clone()`, which shares it once more. The count is atomic, so `Arc`s are cloned and dropped on any core. It is for sharing beyond a scope's lexical reach (spec §6.2).
- `replace(place, v): T` puts `v` in `place` and gives what was there; `swap(a, b)` exchanges two places.

### 1.7 Time

`Duration` is a span of nanoseconds: `Duration.nanos(n)`, `Duration.ms(n)`, `Duration.secs(n)`, `d.toNanos()`, `d.toMs()`; it is `Eq`, `Ord` and `Show`. `Instant` is a point on the program's monotonic clock, `Eq` and `Ord`: `Io.now()` gives one, and `later.since(earlier)` the `Duration` between, which panics if `earlier` is later. Against a simulated world the clock is virtual (spec §6.4).

### 1.8 `Io`'s own types

`Fd` names a file or socket to `Io.read` and `Io.write`, and `WaitKey` names what `Io.park` waits for (spec §5.1). Their fields are private: library code makes and uses them, and programs use the library.

`Io`'s other operations are the host's file system, process and clock, on which `std/fs` and `std/process` are built: `stat(path)`, `list(path)`, `mkdir(path)`, `remove(path)`, `rename(from, to)`, `env(name)`, `cwd()`, `run(program, args, input)` and `wall()`. A program, or a test, may handle any of them itself, as it may `Io`'s others: `handle { … } with Io { stat(p) resumes k => k(#Ok(fake)) }` answers `stat` and passes every other operation on. Each is a scheduling point. `Stat` is what is at a path: `size` in bytes, `dir`, and `modified`, in nanoseconds since 1970 began. `Output` is what a program that was run did: its exit `status`, and what it wrote to standard output, `out`, and standard error, `err`. `IoErr` is what can go wrong: `#Reset`, `#TimedOut`, `#BrokenPipe`, `#NotFound`, `#PermissionDenied`, `#AddrInUse`, `#Refused`, `#Exists` (something is already at a path), `#NotEmpty` (a directory removed with entries in it) and `#Unsupported` (what the host cannot do: WebAssembly runs no programs).

### 1.9 Iteration

`Gen<T, row E>` is a pull iterator over what a generator yields (spec §5.5). `generate(producer)` makes one; nothing runs until the first `next()`.

- `next(): Option<T> uses ...E`.
- Lazy adaptors, each consuming the `Gen`: `map(f)`, `filter(keep)`, `take(n)`, `zip(other)`, `enumerate()`.
- Consumers: `collect(): Vec<T>`, `find(test)`, `findIndex(test)`, `some(test)`, `every(test)`, `reduce(f, init)`; with `T extends Show`, `join(sep)`; a `Gen<readonly T, E>` of `Clone`s has `cloned()`.
- Dropping a `Gen` runs the rest of its generator's cleanup (spec §5.6).

### 1.10 Regions

`Ref<R, T>` is a `readonly T` in region `R`, `Copy`, used as what it points at (spec §4.6); `get()` lends it. `alloc(v)` places a value; `copyUtf8(bytes)` a string, failing with `#MalformedUtf8`; `fmt(s)` a string; `allocAll(items)` a fixed list of `Copy` items. Each `uses Region<R>`.

### 1.11 Tasks

`Io.scope(body)`, `Scope.spawn(task)`, `Scope.fork(task): Fiber<T>` and `Fiber.join()` are specified in spec §6.1; each is a scheduling point.

### 1.12 Foreign code

`Ptr<T>` is a raw pointer (spec §8.2): `Ptr.fromMut(r)`, `Ptr.fromRef(r)`, `Ptr.at(address)`, `p.address()`, `p.add(n)` (`n` elements on), `p.cast<U>()`, all safe; and, performing `Unsafe`, `p.read()`, `p.write(v)` (which drops nothing), `readVolatile`, `writeVolatile`, and the atomic `loadAcquire`, `storeRelease`, `compareExchange(expected, desired): [T, bool]` (what was there, and whether it was `expected` and is now `desired`) and `fetchAdd(v)` (what was there). `sizeOf<T>()` and `alignOf<T>()` measure a type as C lays it out; `zeroed<T>()` is a value of zero bits (`Unsafe`); `fence()`, `fenceAcquire()` and `fenceRelease()` order memory. `Unsafe` is the effect `unsafe { … }` handles.

### 1.13 Reflection

`Type.info(T)` gives a `TypeInfo` to `comptime` code (spec §7.2): `#Int { signed, bits }`, `#Float(bits)`, `#Bool`, `#Str`, `#Void`, `#Fn`, `#Record(fields)`, `#Tuple(types)`, `#Union(tags)`, `#Struct { name, fields }`, `#Enum { name, tags }`, `#Array { item, len }`, `#Slice(item)`, `#Borrow { mutable, type }`, and `#Opaque { name, args }` for a type whose parts are hidden. A `Field` is `{ name, type }`, and a `TagInfo` is `{ name, payload }`.

---

## 2. `std/collections`

### `HashMap<K extends Hash & Eq, V>`

A map, without an order of its own. Lookups take anything the key type lends.

| Function | Contract |
| :--- | :--- |
| `HashMap.new()` | Empty; allocates nothing until the first insert. |
| `insert(key, val)` | Adds the entry. If an equal key is there, the entry it was in — its key and its value — is dropped and replaced. Amortized O(1) expected. |
| `get(key)`, `getMut(key)` | The value of an equal key, lent from the map, or `#None`. O(1) expected. |
| `has(key)` | Whether an equal key is in the map. |
| `remove(key)` | Takes out the entry, dropping its key and giving its value, or `#None`. |
| `len()` | How many entries it holds. |
| `keys()`, `values()`, `valuesMut()`, `entries()` | Generators over the entries in an unspecified order; the map is locked while one lives. |
| `intoEntries()` | Consumes the map: its entries as `[key, value]` pairs, in no order. |
| `sortedByValue()` | With `K` and `V` both `Ord`, consumes the map: its entries, largest value first, and equal values by key, smallest first. |
| `tryReserve(n)` | Room for `n` more entries, or `#OutOfMemory`. |

### `HashSet<T extends Hash & Eq>`

A set, a map to nothing: `HashSet.new()`, `insert(v): bool` (whether `v` was new; if not, `v` is dropped), `has(v)`, `remove(v): bool` (whether it was there), `len()`, `iter()`. Maps and sets are `Clone` when what they hold is.

---

## 3. `std/sync`

What tasks share (spec §6.2). Every operation that waits for another task performs `Io`.

### Channels

`channel<T extends Send>(): [Sender<T>, Receiver<T>]` makes a channel without a bound. Messages from one sender arrive in the order it sent them; messages from different senders, in an order the scheduler chooses.

| Function | Contract |
| :--- | :--- |
| `tx.send(v): bool` | Puts `v` in the channel and gives `true`; or, once the receiver has been dropped, drops `v` and gives `false`, so a producer may stop when no one listens. It never waits for the receiver. A scheduling point. |
| `tx.close()` | Consumes the sender, as dropping it does. A scheduling point. |
| `tx.clone()` | Another sender on the same channel. |
| dropping a `Sender` | When the last sender is gone the channel ends: the receiver drains what was sent, then sees the end. Not a scheduling point. |
| `rx.recv(): Option<T>` | The next message, waiting for one; `#None` once the channel has ended and is drained. A scheduling point. |
| `for (const m of rx)` | Receives until the channel ends. |
| dropping the `Receiver` | What is in the channel is dropped then, and what is sent from then on. The channel is freed when its senders are gone too. |

### Replies

`Reply.new<T>(): [Reply<T>, Pending<T>]` is a channel for one answer: the request and response of an actor (spec §A.6).

- `reply.send(v)` consumes the reply and delivers `v`, which is dropped if the `Pending` has been. A scheduling point.
- `pending.wait(): T` consumes the pending half and waits for the answer. If the `Reply` is dropped unsent — the actor lost the request, or the message holding it was dropped — `wait` panics.
- A `Pending` may be dropped unwaited for; the answer, if it comes, is dropped.

### `Mutex<T>`

State shared by tasks, reached only inside `lock`.

- `Mutex.new(v)`, for `T extends Send`.
- `m.lock(body): R uses Io` lends the state `mut` to `body`, a closure that performs no effects and gives back a `Send` value, and gives back what `body` gives. Because `body` performs nothing, no lock is held across a scheduling point, so no `Mutex` takes part in a deadlock. A body that panics ends the program (spec §5.7).
- `lock` is a scheduling point before it takes the lock. A task that finds the lock held spins briefly, then waits without a core, and waiting tasks are woken in the order they began to wait.
- Each `Mutex` has a lock of its own: locking one never waits for another.

### `Atomic<T>`

An integer or a flag that tasks share, for `T` `i64` or `bool`: `T extends AtomicWord`, an interface the checker decides, which those two meet and no `impl` adds a type to. Every operation is a scheduling point, then takes effect at one point among all of every task's operations, in the one order every task sees: sequentially consistent. There are no weaker orderings; `Ptr`'s acquire and release accesses (§1.12) are for foreign memory, under `unsafe`.

| Function | Contract |
| :--- | :--- |
| `Atomic.new(v)` | An atomic holding `v`. Tasks borrow it `readonly`, as they borrow a `Mutex`. |
| `a.load(): T` | What it holds. |
| `a.store(v)` | Puts `v` in it. |
| `a.swap(v): T` | Puts `v` in it and gives what was there. |
| `a.compareExchange(expected, desired): [T, bool]` | What was there, and whether it was `expected` and is now `desired`. |
| `a.fetchAdd(v): i64` | For `Atomic<i64>`: adds `v` and gives what was there. A sum that overflows panics, as `+` does, and changes nothing. |

---

## 4. `std/io`

| Function | Contract |
| :--- | :--- |
| `println(s)` | Writes `s` and a line break to standard output. Each line is written whole, so lines from tasks on different cores never mix; on worker threads, standard output is flushed at each line. |
| `eprintln(s)` | The same, to standard error, which is not buffered. |
| `exit(code): never` | Ends the program at once, every task with it, with `code` its exit status; standard output is flushed first. No cleanup runs, as for a panic (spec §5.7). |
| `File.open(path): File` | Opens a file to read: `#NotFound`, `#PermissionDenied`. |
| `f.lines()` | A generator of the file's lines, as `str.lines()` splits them. |
| `f.readText(): String` | The whole file, as text. |
| `f.readBytes(): Vec<u8>` | The whole file. |
| `writeFile(path, content)` | Creates the file, or replaces what it held: `#PermissionDenied`, or `#NotFound` for a missing directory. |

Against a simulated world, files are the world's (spec §6.4).

---

## 5. `std/fs`

The file system, over `Io`'s operations. Paths are text with `/` between their parts; a relative one is from the working directory. Against a simulated world the file system is the world's, files and the directories made, so a test needs no directory of its own (spec §6.4).

| Function | Contract |
| :--- | :--- |
| `stat(path): Stat` | What is at `path`: `#NotFound`. |
| `exists(path): bool`, `isDir(path): bool` | Whether anything, or a directory, is at `path`. |
| `listDir(path): Vec<String>` | A directory's entries, their names alone, in the order of their bytes: `#NotFound` if it is not a directory. |
| `createDir(path)` | A directory, whose parent is there: `#Exists`, `#NotFound`. |
| `createDirAll(path)` | A directory, and each directory above it that is not there. |
| `remove(path)` | A file, or a directory with nothing in it: `#NotEmpty`, `#NotFound`. |
| `removeAll(path)` | A file, or a directory and everything in it. |
| `rename(from, to)` | Moves a file or a directory to another path, replacing a file there. |
| `walk(root)` | A generator of the files under `root`, depth first, each directory's entries in order: each its path from `root`, which is part of it. |
| `join(a, b): String` | `b` after `a`, one `/` between them; `b` itself if it is absolute. |
| `parent(path): String` | All but the last part, `"/"` for a part of the root, `""` for one part. |
| `fileName(path): String` | The last part, a trailing `/` ignored. |
| `extension(path): Option<String>` | What follows the last `.` of the last part, unless that part starts with it. |

## 6. `std/process`

| Function | Contract |
| :--- | :--- |
| `env(name): Option<String>` | A variable of the process's environment; against a simulated world, the world's. |
| `cwd(): String` | The working directory, an absolute path. |
| `run(program, args): Output` | Runs `program`, found as the system finds programs, with `args`, to its end, reading nothing: `#NotFound` if there is no such program, `#Unsupported` where the host runs none. A simulated world has no programs of its own, and runs the machine's. |
| `runWith(program, args, input): Output` | The same, the program given `input` to read; what it writes is taken as it writes it, so neither side waits on the other. |

## 7. `std/time`

Instants of the time of day, dates and times of the calendar, time zones and ISO 8601 text. Only `Timestamp.now` and `zone` reach the host; the rest is arithmetic, the same on every host.

| | Contract |
| :--- | :--- |
| `Timestamp` | An instant: nanoseconds since 1970 began, in UTC, before it negative. `now()`, by `Io.wall`; `fromNanos(n)`, `fromSeconds(s)`, `toNanos()`, `seconds()` (rounded down), `plus(d)` and `minus(d)` by a `Duration`, `nanosSince(earlier)`. Equal and ordered as their instants are. |
| `DateTime` | A date of the proleptic Gregorian calendar and a time of day, `year`, `month`, `day`, `hour`, `minute`, `second`, `nanos`, as a clock `offset` seconds east of UTC shows them. |
| `civil(t, offset): DateTime` | What a clock `offset` seconds east of UTC shows at `t`. |
| `instant(d): Timestamp` | The instant a `DateTime` is, at its offset. |
| `daysFromCivil(year, month, day)`, `civilFromDays(days)` | Days since 1970 began of a date, and the date of a day. |
| `weekday(year, month, day)` | The day of the week, `0` Sunday. |
| `isLeapYear(year)` | Divisible by 4, and by 400 if by 100. |
| `Zone` | A time zone: when its kind of local time changes, and the rule it keeps after its last change. `Zone.utc()`; `Zone.fromRule(tz)`, a zone that keeps a rule of POSIX's `TZ` — `"CET-1CEST,M3.5.0,M10.5.0/3"`, its months, weeks and days, Julian days `Jn` and days `n`, and times after `/` — or `#BadZone`; `Zone.fromTzif(name, bytes)`, a zone as a file of the tz database has it (RFC 8536, version 2 or later, its 64-bit times), or `#BadZone`; `name()`; `kindAt(t)` and `offsetAt(t)`. Before its first change a zone keeps its first kind that is not daylight saving time. |
| `ZoneKind` | A kind of local time: its `offset` east of UTC in seconds, whether it is daylight saving time (`dst`), and its `name`, `"BST"`. |
| `zone(name): Zone` | A zone of the system's tz database, `zone("Europe/London")`, from the directory `TZDIR` names or `/usr/share/zoneinfo`: `#UnknownZone` if it has none of that name. `"UTC"` is always there. |
| `local(t, z): DateTime` | What a clock in the zone `z` shows at `t`. |
| `format(d): String` | ISO 8601: `2026-10-24T13:05:09Z`, `2026-10-24T14:05:09.25+01:00`, a fraction of a second only if there is one, its trailing zeros left out, and `Z` for an offset of none. |
| `parse(text): DateTime` | ISO 8601's dates, `2026-10-24`, and dates and times, `T` or a space between them, the seconds and a fraction of them, after `.` or `,`, optional, then `Z`, an offset `±hh:mm` or `±hhmm`, or nothing, which is UTC. A date that is not on the calendar, or anything else, is `#BadTime(at)`, `at` the offset in the text where it went wrong. |
| `ZoneErr`, `TimeErr` | `#UnknownZone(name) \| #BadZone(why)`; `#BadTime(at)`. |

---

## 8. `std/unicode`

Text as Unicode sees it: its code points, the characters a reader sees in it — *grapheme clusters*, as UAX #29 finds them — its normal forms NFC and NFD (UAX #15), and its cases. Every function is pure, and its tables are the Unicode Character Database's, of the version `version()` names; the repository checks them against that version's own tests of clusters and of normalization.

| | Contract |
| :--- | :--- |
| `version(): str` | The version of Unicode the tables are of, `"18.0.0"`. |
| `codePoints(s)` | Yields the code points of `s`, in order: a generator, `uses Yield<u32>`. |
| `fromCodePoints(cps): String` | Text of the code points, each as UTF-8; a surrogate or a number past U+10FFFF as U+FFFD. |
| `graphemes(s)` | Yields each grapheme cluster of `s` as a `str` lent from it, in order, by the extended clusters' rules: a letter and its marks, a pair of regional indicators, an emoji sequence joined by U+200D, a Hangul syllable of jamo, an Indic conjunct (rule GB9c) are each one. Linear in `s`. |
| `graphemeCount(s): usize` | How many clusters `graphemes(s)` yields. |
| `nfd(s): String`, `nfc(s): String` | `s` decomposed canonically, its marks in canonical order, and, for NFC, composed again; Hangul by arithmetic. Linear in `s`, but for a run of marks, which is sorted. |
| `isNfd(s)`, `isNfc(s)` | Whether `s` is in that form already. |
| `lower(s): String`, `upper(s): String` | The full, unconditional case mappings of SpecialCasing, `upper("straße")` `"STRASSE"`, and the final sigma: a capital sigma lowers to `ς` at the end of a word, after a cased letter and not before one, `case-ignorable` characters between. They depend on no locale, so the Turkish and Lithuanian rules are not applied. `str`'s own `toUpperCase` and `toLowerCase` change ASCII alone. |

---

## 9. `std/net`

TCP. Every operation that waits for the network performs `Io` and is a scheduling point; a task waiting for a socket gives its core to others until the kernel says the socket is ready.

### `Listener`

- `Listener.bind(port): Listener` listens on every address of the machine; port `0` takes a free one. `#AddrInUse` if another program holds the port, `#PermissionDenied` for one the program may not have.
- `l.port(): u16`, the port it listens on.
- `l.accept()`, a generator of connections, each a `Socket`, as clients connect. Against the machine it ends only if the listener fails; against a simulated world, once the world's requests have all been accepted.

### `Socket`

A connection. A `Socket` is `Send` and has one owner, so it is never read by one task as another closes it.

| Function | Contract |
| :--- | :--- |
| `Socket.connect(host, port): Socket` | Connects to `host`, a name or an address, on `port`, trying each address the name has in turn. `#NotFound` if the name does not resolve, `#Refused` if nothing listens, `#TimedOut`. Resolving a name may hold the task's core while the system's resolver answers. |
| `s.read(buf): usize` | Reads what has arrived, at most `buf.len()` bytes, waiting for at least one; `0` once the other end has sent all it will. `#Reset`, `#TimedOut`. |
| `s.write(bytes)` | Writes all of `bytes`, waiting as the other end takes them. `#BrokenPipe` once it has gone, `#Reset`. |
| `s.writeStatus(code, body)` | Writes a whole HTTP/1.1 response: status `code`, `Content-Length`, `Connection: close`, and `body`. |
| `s.close()` | Closes the connection; dropping a socket closes it too. |

Against a simulated world, a listener's connections are the world's requests, a connection to `host` on `port` reaches the world's peer of that name, which answers what the world says it does (`#Refused` if the world has none), and what a program writes to a connection is its output, shown when the connection closes.

---

## 10. `std/par`

Data parallelism over pure closures (spec §6.5).

- `join(a, b): [A, B]` runs both closures, at once when another core is free, and gives both results. Both are pure and what they capture is `Send`, so whether they overlapped cannot be observed.
- `par(c, f)` runs `f(view, i)` on every element of a `ParSplit` container, dividing it with `split` and running the halves with `join`; a run of fewer elements than a threshold is worked on in order.
- `parReduce(c, zero, one, both)` folds every element with `one` and combines partial results with `both`, which must be associative; `zero` is the result for no elements.
- `ParSplit` is implemented by slices, arrays, `Vec`s and `Soa`s: `len`, `slice`, `split`, `viewAt`, `readAt`, and the types `Slice`, `View` and `ReadView`.

---

## 11. `std/layout`

`Soa<T>` keeps a struct's fields in planes, one for each field: a `Vec` for a scalar field and a nested `Soa` for a struct field (spec §7.4). It has `Soa.new()`, `push(v)`, `len()`, `at(i)`, a `SoaView` that lends each field of one element, and `splitAt(at)`; `SoaSlice`, `SoaView` and `SoaRead` are its `ParSplit` views.

---

## 12. `std/region`

Mutable slots in a region (spec §4.6). `Cell<R, T extends Copy>`: `Cell.new(v)`, `c.get()`, `c.set(v)`. `RegionList<R, T>`: `RegionList.new()`, `push(v)`, `len()`, and iteration. Both are handles, `Copy`; reading and writing through one performs `Region<R>`.

---

## 13. `std/json`

JSON as library code (spec §7.5).

- `stringify(v): String` encodes any `ToJson` value. `parse<T>(text): T` decodes one, failing with `JsonError`: `#BadJson(at)` for text that is not the JSON expected, `#MissingField(name)`, `#UnknownTag(name)`, or `#OutOfRange(at)` for an integer that does not fit its type; `at` is a byte offset into the text.
- **Encodings.** Numbers and booleans are themselves. Strings are quoted, with `"`, `\` and control characters escaped (`writeString(s, out)` writes one so). A struct is an object of its fields in declaration order, and a record an object of its fields in the order of their names, as a record's fields have no order of their own. Tuples, arrays, slices and `Vec`s are arrays. `#None` is `null` and `#Some(x)` is `x`. A tag without a payload is its name, as a string, and a tag with one is `{ "Name": payload }`.
- **Decoding** accepts what encoding gives, with any whitespace and object keys in any order. Unknown keys are skipped. A missing key is `#MissingField` unless its field is an `Option`. A number that is not an integer, for an integer type, is `#BadJson`. An array type needs exactly its length of items.
- `ToJson` (`toJson(self, out)`) and `FromJson` (`fromJson(p)`) are derived for every type the encodings cover, and asked for by a struct with `impl ToJson for User;`; either may be written by hand. A hand-written `fromJson` reads through a `JsonParser`: `JsonParser.new(text)`; `peek()`, the next byte that is not whitespace, or `0` at the end; `at()`, the offset; `eatNull()`, which consumes `null` if it is next; `bool()`, `int()`, `uint()`, `float()`, `string()` and `number()` (a number's text), each failing as `parse` does; `atString()`; `beginArray()` and `nextItem()` (whether another item follows, consuming the separator); `beginObject()`, `nextKey()` and `key()` (an object's key and the `:` after it); `skip()`, one value of any kind; and `finish()`, which fails unless only whitespace is left.

---

## 14. `std/world`

Services only a simulated world provides (spec §6.4), for examples and tests: `Db.connect(): Db`; `db.fetchProfile(user): Profile`, where a `Profile` is `{ displayName: String }`, failing with `#NotFound` for a user the world does not know; and `db.checkQuota(token): Quota`, where a `Quota` is `{ allowed: bool }`. Each performs `Io` and may fail as the world's faults say.

---

## 15. The web framework

The web framework, FlyNext, is a package shipped with the compiler and specified in [web/README.md](../web/README.md): `web/http` (requests, responses and `serve`), `web/ui` (the `Ui<M>` effect, links, components and HTML), `web/dom` (pages in the browser), `web/router` (routes and their parameters) and `web/site` (pages and files answered), with the app compiler `web/flynext`.
