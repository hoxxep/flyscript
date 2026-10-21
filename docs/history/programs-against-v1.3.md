# Flyscript v1.3 — eight programs and a friction log

Written strictly against v1.3 as specified. `// FRICTION n` marks every place the spec forced something awkward, ambiguous or unsound.

## P1. JSON parser (regions, recursion, tags)

```ts
// FRICTION 1: a recursive structural variant type needs equi-recursive rows,
// which v1.3 never specifies. To be safe I must use nominal `enum` — so the
// language now has two sum-type systems that look almost identical.
enum Json<region R> {
  Null, Bool(bool), Num(f64), Str(In<R, str>),
  Arr(Vec<Json<R>, R>),
  Obj(Vec<{ key: In<R, str>; value: Json<R> }, R>),
}

function parseValue<region R>(src: readonly u8[], pos: mut usize): Json<R>
  uses Alloc<R>, Fail<[ #Unexpected(usize) | #Eof | #MalformedUtf8 ]> {
  skipWs(src, mut pos);
  if (pos >= src.len) { Fail.raise(#Eof); }
  match (src[pos]) {
    '{' => parseObject(src, mut pos),
    '[' => parseArray(src, mut pos),
    '"' => Json.Str(parseString(src, mut pos)),
    't' => { expectLit(src, mut pos, "true"); Json.Bool(true) },
    _   => Fail.raise(#Unexpected(pos)),
  }
}

function parseArray<region R>(src: readonly u8[], pos: mut usize): Json<R>
  uses Alloc<R>, Fail<[ #Unexpected(usize) | #Eof | #MalformedUtf8 ]> {
  pos += 1;
  // FRICTION 2: `Vec.new()` defaults to Heap unless annotated; I must write `Vec<Json<R>, R>`
  // here even though the return type already fixes R. Type-directed is right, but the
  // expected type only flows through the *final* expression, not through a `let`.
  let items: Vec<Json<R>, R> = Vec.new();
  while (peek(src, pos) != ']') {
    items.push(parseValue(src, mut pos));
    if (peek(src, pos) == ',') { pos += 1; }
  }
  pos += 1;
  Json.Arr(items)
}
```
Ugly: the `uses Alloc<R>, Fail<[...]>` row repeats on every mutually recursive helper (private helpers can omit it: good). Two sum-type systems (FRICTION 1).

## P2. CLI word count (files, errors, generators, a map)

```ts
import { File, stdout } from "std/fs";
import { HashMap } from "std/collections";

function lines(f: mut File): void uses Io, Fail<IoErr>, Yield<str> { ... }

export function main(args: readonly String[]): void uses Io {
  let counts: HashMap<String, u64> = HashMap.new();
  handle {
    for (const path of args) {
      let f = File.open(path);
      for (const line of lines(mut f)) {
        for (const word of line.split(" ")) {
          // FRICTION 3: `word: str` borrows from `line`, which borrows `f`'s buffer.
          // Inserting needs an owned key: `word.toString()` allocates even on a hit.
          // Fine — but the entry API needs a second-class key; nothing in the spec says
          // HashMap<String,_> can be looked up by `str` (Rust's Borrow trait). Needs a story.
          counts.entry(word).orInsert(0) += 1;
        }
      }
    }
  } with Fail {
    raise(e) => { stdout.print(`error: ${e}`); }   // FRICTION 4: how is a polymorphic variant formatted? Needs a derived `Show` for rows.
  }
  // FRICTION 5: printing sorted output needs `counts.entries()` as a stream. Is that
  // `Yield<{ key: readonly String; value: readonly u64 }>` — a second-class record
  // yielded across a handler? v1.3 says Yield<T> may carry second-class views; OK.
}
```

## P3. Generator pipeline (map / filter / take / zip)

```ts
function evens(): void uses Yield<u64> { let i = 0; while (true) { Yield.yield(i); i += 2; } }

// map and take are fine: they're handlers that re-yield.
function take<T, row E>(n: usize, src: () => void uses Yield<T>, ...E): void uses Yield<T>, ...E {
  let seen = 0;
  for (const x of src()) { if (seen == n) { break; } Yield.yield(x); seen += 1; }
}

// FRICTION 6 (fundamental): zip is IMPOSSIBLE. Advancing two generators in lockstep
// requires holding a suspended generator as a value and resuming it later. v1.0 forbade
// storing `k` beyond the handler arm, so a generator can only be consumed by one
// enclosing `for`. Koka/OCaml solve this by making the continuation a first-class
// (affine) value. Without it, Flyscript has no pull-based iteration at all — no zip,
// no merge, no `iter.next()`, no parser combinators over token streams.
function zip<A, B>(a: () => void uses Yield<A>, b: () => void uses Yield<B>): void uses Yield<[A, B]> {
  ???
}
```

## P4. Game loop (SoA + par)

```ts
import { Soa } from "std/layout";
import { par } from "std/par";

struct Particle { pos: Vec2; vel: Vec2; life: f32; }

export function step(ps: mut Soa<Particle>, dt: f32): void {
  par(mut ps, (p, _i) => {
    // FRICTION 7: `pos: Vec2` is itself a record; is the view `{ pos: mut Vec2; ... }` (AoS
    // inside SoA) or flattened `pos.x` planes? The comptime Soa must choose; spec silent. Minor.
    p.pos.x += p.vel.x * dt;
    p.life -= dt;
  });
  // FRICTION 8: removing dead particles (swap-remove) is sequential and fine, but a parallel
  // *reduction* (count alive) is inexpressible: `par` bodies are pure and return void, and
  // atomics need `uses Shared`. Need `parMap`/`parReduce` with an associative combiner.
}
```
`par` itself reads beautifully. The `ParSplit` interface introduced an associated type (`type ItemView;`) — **FRICTION 9: associated types are a new language feature that appears nowhere else in the spec** (not in the grammar, not in interfaces).

## P5. Compiler symbol table: a cyclic graph in a region

```ts
struct Scope<region R> {
  parent: Option<In<R, Scope<R>>>;
  names: Vec<{ name: In<R, str>; decl: In<R, Decl<R>> }, R>;
}

function declare<region R>(s: In<R, Scope<R>>, name: In<R, str>, d: In<R, Decl<R>>): void uses Alloc<R> {
  s.names.push({ name, decl: d });   // mutating through a Copy pointer
}
```
**FRICTION 10 (soundness):** `In<R, T>` is `Copy` *and* mutable through any copy. That is shared mutable aliasing:
```ts
const a = s; const b = s;                    // two aliases
const first: readonly ... = a.names[0];      // borrow into a's Vec storage
b.names.push(x);                             // reallocates the Vec through the other alias
use(first);                                  // dangling into the old buffer (or stale data)
```
Same with enum fields: borrow the payload of `a.kind` as `Num(f64)`, overwrite `b.kind = Str(...)` through the alias, read the "f64" — type confusion. It also violates the v1.2 Shared-Mutation Law: a `uses []` function holding `readonly In<R, T>` can mutate the region through a copy. So regions as specified are unsound *and* break the purity law the whole design rests on.

## P6. Key-value store actor (channels, pools, long-lived state)

```ts
type Req = [ #Get({ key: String; reply: Sender<Option<String>> }) | #Put({ key: String; val: String }) ];

export function kvActor(inbox: mut Receiver<Req>): void uses Io {
  let store: HashMap<String, String> = HashMap.new();
  for (const req of inbox.messages()) {          // Yield-based receive: nice
    match (req) {
      #Get({ key, reply }) => reply.send(store.get(key).cloned()),
      #Put({ key, val })   => store.insert(key, val),
    }
  }
}
```
Reads well — single-owner state plus tagged messages is the natural style. **FRICTION 11:** `Channel.send` performs `Shared` per §7.1 *and* blocks the fiber, which is `Io`. Two effects for one operation; in deterministic simulation, the scheduler must control channel interleavings anyway, so `Shared` is really part of `Io`. The `Shared` effect's placeholder op (`synchronize()`) confirms it was never a real effect.

## P7. Web server accept loop (structured concurrency)

```ts
export function serve(listener: mut Listener, db: readonly DbClient): void uses Io {
  Async.scope((s) => {
    for (const conn of listener.accept()) {
      s.spawn(() => handleConnection(mut conn, db));   // FRICTION 12
    }
  });
}
```
**FRICTION 12:** `conn` is owned per iteration and must be *moved* into the spawned task, but `spawn` requires a **shared** closure (§8.1). A per-connection task is the most common concurrent program there is; it needs `once` closures that capture owned values plus `readonly` borrows of `db`. The spawn rule must be: a `once` closure whose captures are owned `Send` values or `readonly T` with `T: Send`.
**FRICTION 13:** `Async.scope` is a wrapper around `Io.runScope`: two names for one thing.

## P8. Browser UI component (Wasm)

```ts
type Msg = [ #Inc | #Dec | #SetName(String) ];
type Model = { count: i32; name: String };

function update(m: mut Model, msg: Msg): void {
  match (msg) { #Inc => m.count += 1, #Dec => m.count -= 1, #SetName(n) => m.name = n }
}
function view(m: readonly Model): Html<Msg> { ... }

export function main(): void uses Io { Dom.run({ count: 0, name: String.new() }, update, view); }
```
Beautiful: affine ownership + structural tags push you straight into the Elm architecture, with no callbacks capturing shared mutable state. No friction, and a good showcase.

## Spec-level friction (from writing all eight)

- **F14 Handler forms:** resumptive arms, abortive arms, `return(v)` arms and `finally` arms. In eight programs I never needed `return(v)` (one-shot handlers + mutable locals cover it), and `finally` duplicates `Drop` (a `defer` statement is the general tool).
- **F15 Two ways to implement interfaces:** `struct S implements I { methods }` and `impl I for S { }`.
- **F16 Pointers:** `Box<T, R>`, `In<R, T>`, `Arc<T>`, `Pool`/`Handle`. Four, without a stated organizing principle.
- **F17 Heap is an ambient, untracked `Alloc<Heap>`** while regions are tracked `Alloc<R>`: the asymmetry is unexplained, and `Alloc` is otherwise a user-visible effect nobody handles except `region`.
- **F18 The spawn "region frozen" rule** is a special case (§8.1): an enclosing region's handler is "suspended" during a scope.
- **F19 `const` vs TS:** deep immutability vs TS's binding immutability. With affine ownership there is no aliasing, so "deep" and "shallow" coincide for owned values. This is consistent, but the spec should say *why*, not present it as a difference.
