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

Every integer type has `wrappingAdd`, `wrappingSub` and `wrappingMul`, which wrap at the type's width where `+`, `-` and `*` panic. `parseInt(s): Option<i64>` and `parseFloat(s): Option<f64>` read decimal text as TypeScript's functions do, without `NaN`: an optional sign and digits (for a float, a fraction and an exponent too), and nothing else, not even spaces; `#None` otherwise, or for an integer that does not fit.

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

---

## 4. `std/io`

| Function | Contract |
| :--- | :--- |
| `println(s)` | Writes `s` and a line break to standard output. Each line is written whole, so lines from tasks on different cores never mix; on worker threads, standard output is flushed at each line. |
| `eprintln(s)` | The same, to standard error, which is not buffered. |
| `File.open(path): File` | Opens a file to read: `#NotFound`, `#PermissionDenied`. |
| `f.lines()` | A generator of the file's lines, as `str.lines()` splits them. |
| `f.readText(): String` | The whole file, as text. |
| `f.readBytes(): Vec<u8>` | The whole file. |
| `writeFile(path, content)` | Creates the file, or replaces what it held: `#PermissionDenied`, or `#NotFound` for a missing directory. |

Against a simulated world, files are the world's (spec §6.4).

---

## 5. `std/net`

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

## 6. `std/par`

Data parallelism over pure closures (spec §6.5).

- `join(a, b): [A, B]` runs both closures, at once when another core is free, and gives both results. Both are pure and what they capture is `Send`, so whether they overlapped cannot be observed.
- `par(c, f)` runs `f(view, i)` on every element of a `ParSplit` container, dividing it with `split` and running the halves with `join`; a run of fewer elements than a threshold is worked on in order.
- `parReduce(c, zero, one, both)` folds every element with `one` and combines partial results with `both`, which must be associative; `zero` is the result for no elements.
- `ParSplit` is implemented by slices, arrays, `Vec`s and `Soa`s: `len`, `slice`, `split`, `viewAt`, `readAt`, and the types `Slice`, `View` and `ReadView`.

---

## 7. `std/layout`

`Soa<T>` keeps a struct's fields in planes, one for each field: a `Vec` for a scalar field and a nested `Soa` for a struct field (spec §7.4). It has `Soa.new()`, `push(v)`, `len()`, `at(i)`, a `SoaView` that lends each field of one element, and `splitAt(at)`; `SoaSlice`, `SoaView` and `SoaRead` are its `ParSplit` views.

---

## 8. `std/region`

Mutable slots in a region (spec §4.6). `Cell<R, T extends Copy>`: `Cell.new(v)`, `c.get()`, `c.set(v)`. `RegionList<R, T>`: `RegionList.new()`, `push(v)`, `len()`, and iteration. Both are handles, `Copy`; reading and writing through one performs `Region<R>`.

---

## 9. `std/json`

JSON as library code (spec §7.5).

- `stringify(v): String` encodes any `ToJson` value. `parse<T>(text): T` decodes one, failing with `JsonError`: `#BadJson(at)` for text that is not the JSON expected, `#MissingField(name)`, `#UnknownTag(name)`, or `#OutOfRange(at)` for an integer that does not fit its type; `at` is a byte offset into the text.
- **Encodings.** Numbers and booleans are themselves. Strings are quoted, with `"`, `\` and control characters escaped (`writeString(s, out)` writes one so). A struct is an object of its fields in declaration order, and a record an object of its fields in the order of their names, as a record's fields have no order of their own. Tuples, arrays, slices and `Vec`s are arrays. `#None` is `null` and `#Some(x)` is `x`. A tag without a payload is its name, as a string, and a tag with one is `{ "Name": payload }`.
- **Decoding** accepts what encoding gives, with any whitespace and object keys in any order. Unknown keys are skipped. A missing key is `#MissingField` unless its field is an `Option`. A number that is not an integer, for an integer type, is `#BadJson`. An array type needs exactly its length of items.
- `ToJson` (`toJson(self, out)`) and `FromJson` (`fromJson(p)`) are derived for every type the encodings cover, and asked for by a struct with `impl ToJson for User;`; either may be written by hand. A hand-written `fromJson` reads through a `JsonParser`: `JsonParser.new(text)`; `peek()`, the next byte that is not whitespace, or `0` at the end; `at()`, the offset; `eatNull()`, which consumes `null` if it is next; `bool()`, `int()`, `uint()`, `float()`, `string()` and `number()` (a number's text), each failing as `parse` does; `atString()`; `beginArray()` and `nextItem()` (whether another item follows, consuming the separator); `beginObject()`, `nextKey()` and `key()` (an object's key and the `:` after it); `skip()`, one value of any kind; and `finish()`, which fails unless only whitespace is left.

---

## 10. `std/world`

Services only a simulated world provides (spec §6.4), for examples and tests: `Db.connect(): Db`; `db.fetchProfile(user): Profile`, where a `Profile` is `{ displayName: String }`, failing with `#NotFound` for a user the world does not know; and `db.checkQuota(token): Quota`, where a `Quota` is `{ allowed: bool }`. Each performs `Io` and may fail as the world's faults say.

---

## 11. The web framework

The web framework is library code shipped with the compiler and specified in [web/README.md](../web/README.md): `web/http` (requests, responses and `serve`), `web/ui` (the `Ui<M>` effect and HTML), `web/dom` (a view in a page) and `web/page`.
