# Review: dogfood-programs-0-40

- spec: 33c553fa716c
- request: ea809b7498bc192d
- tokens: prompt 67472, cached 0, answer 3020

## Question

You are a TypeScript programmer who has just read this specification (Flyscript 0.40, included) and nothing else. Write three small but complete programs in Flyscript, each a single module with `export function main(): void uses Io` and output via `println` from "std/io":

1. **Config loader**: a `struct Config { name: String; port: u16; tags: Vec<String>; debug: bool }` that derives `FromJson`/`ToJson` (std/json), parses a JSON string literal, validates that `port` is above 1024 (a typed failure), prints the config back as JSON, and handles a malformed input in `main` with `try`/`catch`.
2. **Generic priority queue**: a `struct MinHeap<T extends Ord>` over a `Vec<T>` with `push`, `pop` returning `Option<T>`, and `len`; use it to schedule `Job { priority: u32; name: String }` values (derive what you need) and print them in order.
3. **Event-sourced account with effects**: an `effect Store { append(e: Event): void; }` and `effect Clock { now(): u64; }`; a function `deposit`/`withdraw` that performs them; replay the events to compute a balance; in `main`, handle `Store` by collecting into a `Vec<Event>` and `Clock` with a fake counter, then print the events and the final balance.

Write the code the way the spec leads you to; do not hedge. After each program, list every place where you were unsure what the spec allows, or had to guess an API name. Keep each under 80 lines. Output each program in a fenced ```ts block preceded by a line `FILE: <name>.fly`.

## Context files

- `docs/spec.md`

## Answer

###Verdicts

- **Program 1 (Config loader)**: **Agree.** Everything needed (`FromJson`, `ToJson`, open `Fail` union composition, `try`/`catch` row closing) is directly specified in §3.2, §5.4, §7.5, and A.9.
- **Program 2 (Generic priority queue)**: **Agree with changes.** Writing a heap over `Vec<T>` for non-`Copy` `T` exposes a gap in §3.1/§4.1: you cannot swap two elements of a `Vec<T>` by indexing (`const tmp = xs[i]; xs[i] = xs[j];` moves out of `xs[i]`, which §4.1 only defines for fields of structs/records, not indexed places, and there is no `swap(i, j)` method listed in §3.1).
- **Program 3 (Event-sourced account)**: **Agree.** Handlers, `with` nesting, and resumptive arms mutating outer locals (`§5.2`, `§5.3`, `A.11`) work directly as specified.

---

### Program 1: Config loader

FILE: config_loader.fly
```ts
import { println } from "std/io";
import { ToJson, FromJson, JsonError, parse, stringify } from "std/json";

struct Config {
  name: String;
  port: u16;
  tags: Vec<String>;
  debug: bool;
}
impl FromJson for Config;
impl ToJson for Config;

function loadConfig(raw: str): Config uses Fail<JsonError | #PrivilegedPort(u16)> {
  const cfg: Config = parse(raw);
  if (cfg.port <= 1024) {
    throw #PrivilegedPort(cfg.port);
  }
  cfg
}

function runOne(raw: str): void uses Io {
  try {
    const cfg = loadConfig(raw);
    println(stringify(cfg));
  } catch (e) {
    match (e) {
      #PrivilegedPort(p)   => println(`invalid port: ${p} (must be > 1024)`),
      #MissingField(field) => println(`missing field: ${field}`),
      #BadJson(at)         => println(`malformed JSON at byte ${at}`),
      _                    => println(`config error: ${e}`),
    }
  }
}

export function main(): void uses Io {
  runOne(`{"name": "api", "port": 8080, "tags": ["v1", "prod"], "debug": false}`);
  runOne(`{"name": "web", "port": 80, "tags": [], "debug": true}`);
  runOne(`{"name": "broken", "port": "not-a-port"}`);
}
```

**Unsure / Guessed in Program 1:**
1. **`println` parameter type**: §3.1 says a `String` lends `str` wherever `str` is expected, so passing `stringify(cfg)` (which returns `String`) or a template literal to `println` works if `println` takes `str`.
2. **Exact variants of `JsonError`**: §5.4 mentions `#MissingField`, `#UnknownTag`, `#BadJson`, and A.9 matches `#MissingField(field)` and `#BadJson(at)` with a `_` fallback. The full definition of `JsonError` is not in the spec, so `_` is needed for exhaustiveness, and `${e}` in the `_` arm relies on §3.5 ("an error union prints, compares and hashes with no code").

---

### Program 2: Generic priority queue

FILE: min_heap.fly
```ts
import { println } from "std/io";

struct Job {
  priority: u32;
  name: String;
}
impl Eq for Job;
impl Ord for Job;
impl Show for Job;

struct MinHeap<T extends Ord> {
  items: Vec<T>;
}

impl<T extends Ord> MinHeap<T> {
  export function new(): MinHeap<T> {
    MinHeap { items: Vec.new() }
  }

  export function len(self: readonly Self): usize {
    self.items.len()
  }

  export function push(self: mut Self, v: T): void {
    // Keep smallest at the back so `pop()` is O(1) without needing element swap on non-Copy T,
    // or insert in sorted order using Vec.insert (§3.1).
    let i: usize = 0;
    while (i < self.items.len() && self.items[i] > v) {
      i += 1;
    }
    self.items.insert(i, v);
  }

  export function pop(self: mut Self): Option<T> {
    self.items.pop()
  }
}

export function main(): void uses Io {
  let q = MinHeap.new<Job>();
  q.push(Job { priority: 30, name: "backup".toString() });
  q.push(Job { priority: 10, name: "alert".toString() });
  q.push(Job { priority: 20, name: "report".toString() });
  q.push(Job { priority: 10, name: "audit".toString() });

  while (const #Some(job) = q.pop()) {
    println(`${job.priority}: ${job.name}`);
  }
}
```

**Unsure / Guessed in Program 2:**
1. **Swapping elements in a `Vec<T>` when `T` is not `Copy`**: A binary heap's sift-up/sift-down needs to swap `self.items[i]` and `self.items[parent]`. In Flyscript, `Job` owns a `String`, so `Job` is not `Copy`. §4.1 forbids moving out of an indexed place `const tmp = self.items[i]` (and `Vec` is nominal, probably with `Drop`), and §3.1 lists `len, iter, iterMut, splitAt, last, includes, indexOf, sort, sortBy, reverse, join, push, pop, insert, remove, retain, drain` — there is **no `swap(i, j)`** on slices or `Vec`! And to replace the root on `pop()`, you can `remove(0)` (which shifts) or `pop()`, but without `swap` you cannot move the last element into `items[0]` and sift down without removing and re-inserting. I had to use `self.items.insert(i, v)` and `self.items.pop()` instead of binary sift-up/sift-down.
2. **`Ord` requires `Eq`**: §3.5 says `Ord extends Eq` and §3.4 says *"An impl of `I` for `T` requires `T` to satisfy every interface `I` extends"*, so I added `impl Eq for Job;` before `impl Ord for Job;`. I was unsure whether `impl Ord for Job;` implies `Eq` automatically or requires the explicit line.
3. **`self.items[i] > v` on borrowed place**: `self.items[i]` in a read position against `v: T` compares two `T`s via `Ord.cmp` (§3.5).

---

### Program 3: Event-sourced account with effects

FILE: account.fly
```ts
import { println } from "std/io";

type Event =
  | #Deposited { at: u64; amount: i64 }
  | #Withdrawn { at: u64; amount: i64 };

type TxErr = #InvalidAmount(i64) | #InsufficientFunds { have: i64; want: i64 };

effect Store {
  append(e: Event): void;
}

effect Clock {
  now(): u64;
}

function replay(events: readonly Event[]): i64 {
  let balance: i64 = 0;
  for (const e of events) {
    match (e) {
      #Deposited { amount } => { balance += amount; },
      #Withdrawn { amount } => { balance -= amount; },
    }
  }
  balance
}

function deposit(amount: i64): void uses Store, Clock, Fail<TxErr> {
  if (amount <= 0) { throw #InvalidAmount(amount); }
  const t = Clock.now();
  Store.append(#Deposited { at: t, amount });
}

function withdraw(currentBalance: i64, amount: i64): void uses Store, Clock, Fail<TxErr> {
  if (amount <= 0) { throw #InvalidAmount(amount); }
  if ( currentBalance < amount ) {
    throw #InsufficientFunds { have: currentBalance, want: amount };
  }
  const t = Clock.now();
  Store.append(#Withdrawn { at: t, amount });
}

export function main(): void uses Io {
  let log: Vec<Event> = Vec.new();
  let tick: u64 = 100;

  handle {
    try {
      deposit(500);
      deposit(250);
      withdraw(750, 300);
      withdraw(450, 900);
    } catch (err) {
      println(`rejected: ${err}`);
    }
  } with Store {
    append(e) resumes k => {
      log.push(e);
      k()
    },
  } with Clock {
    now() resumes k => {
      tick += 10;
      k(tick)
    },
  };

  for (const ev of log) {
    println(`event: ${ev}`);
  }
  println(`balance: ${replay(log)}`);
}
```

**Unsure / Guessed in Program 3:**
1. **Reading `log` inside the `handle` body if `withdraw` computed balance from `log`**: §5.3 (*Resuming re-enters*) says that `k(a)` uses every binding from outside the `handle` that the body or any of its arms uses, in the strongest mode any of them does. Since the `Store` arm mutates `log` (`log.push(e)`), the `handle` body itself cannot also read `log` directly without conflicting with the handler arm's `mut` use of `log` (unless reading it through another operation on `Store`, e.g. `events()`). So `withdraw` takes `currentBalance: i64` as a parameter (or `Store` would have a second operation).
2. **Record pattern ignoring fields in `match`**: `#Deposited { amount } =>` ignores `at`, which §3.2 explicitly allows (*"A record pattern names the fields it binds and ignores the rest"*).
3. **`for (const ev of log)`**: `ev` is `readonly Event` (§5.5), and `${ev}` formats it via the prelude's `Show` derivation for structural tag unions (§3.5).

---

### Problems

#### 1. Slices and `Vec<T>` have no `swap(i, j)` method (`§3.1`, `§4.1`)

Program 2 immediately hits this when trying to write a standard binary heap over `Vec<T>` where `T` is not `Copy` (such as `Job { priority: u32; name: String }`):

```ts
function siftUp<T extends Ord>(items: mut Vec<T>, idx: usize): void {
  let i = idx;
  while (i > 0) {
    const parent = (i - 1) / 2;
    if (items[i] < items[parent]) {
      // Cannot write:
      //   const tmp = items[i];
      //   items[i] = items[parent];
      //   items[parent] = tmp;
      // because `T` is not `Copy`, and moving out of `items[i]` leaves a hole in the Vec!
    }
    i = parent;
  }
}
```

In a language with affine values and no `mem::swap(&mut a, &mut b)` (since you cannot take two simultaneous `mut` borrows of `items`), `mut T[]` (and by lending, `T[N]` and `Vec<T>`) needs `swap(i: usize, j: usize): void` in §3.1, and `Vec<T>` benefits from `swapRemove(i: usize): T` for O(1) heap-root removal.

**Fix:**
In **§3.1 (Methods)**, add `swap(i, j)` to the slice methods list:
> *"Arrays, slices and `Vec`s share their methods, which are defined on slices and reached through lending (§4.1): `len`, `iter`, `iterMut`, `splitAt`, `swap(i, j)`, `last`, …"* List `swapRemove(i)` (or `swap` + `pop`) on `Vec`.
