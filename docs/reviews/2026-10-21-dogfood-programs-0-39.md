# Review: dogfood-programs-0-39

- spec: 0a2a0c92ea6a
- request: 5f0191cc07ada047
- tokens: prompt 67149, cached 0, answer 3879

## Question

You are a TypeScript programmer who has just read this specification (Flyscript 0.39, included) and nothing else. Write three small but complete programs in Flyscript, each a single module with `export function main(): void uses Io` and output via `println` from "std/io":

1. **Todo list manager**: a `struct Todo`, a `Vec<Todo>`, add/complete/remove by id, list pending items sorted by priority, with failures (`throw`) for unknown ids caught in `main`.
2. **Text statistics**: given a multi-line string literal, count words per line, find the most frequent word with a `HashMap`, and print the top three words — using generators and iteration chains where natural.
3. **Bank transfers with tasks**: accounts in an `Arc<Mutex<HashMap<String, i64>>>`, several forked tasks performing transfers, an insufficient-funds failure that cancels the scope, and a final balance print.

Write the code the way the spec leads you to; do not hedge. After each program, list every place where you were unsure what the spec allows, or where you had to guess an API name. Keep the programs under 80 lines each. Output each program in a fenced ```ts block preceded by a line `FILE: <name>.fly`.

## Context files

- `docs/spec.md`

## Answer

### Program 1: Todo list manager

FILE: todo.fly
```ts
import { println } from "std/io";

struct Todo {
  id: u32;
  title: String;
  priority: u8;
  done: bool;
}
impl Clone for Todo;

type TodoErr = #NotFound(u32);

struct TodoList {
  items: Vec<Todo>;
  nextId: u32;
}

impl TodoList {
  function new(): TodoList {
    TodoList { items: Vec.new(), nextId: 1 }
  }

  function add(self: mut Self, title: str, priority: u8): u32 {
    const id = self.nextId;
    self.nextId += 1;
    self.items.push(Todo { id, title: title.toString(), priority, done: false });
    id
  }

  function complete(self: mut Self, id: u32): void uses Fail<TodoErr> {
    for (const item of self.items.iterMut()) {
      if (item.id == id) {
        item.done = true;
        return;
      }
    }
    throw #NotFound(id);
  }

  function remove(self: mut Self, id: u32): Todo uses Fail<TodoErr> {
    let kept: Vec<Todo> = Vec.new();
    let removed: Option<Todo> = #None;
    for (const item of self.items.drain()) {
      if (item.id == id) {
        removed = #Some(item);
      } else {
        kept.push(item);
      }
    }
    self.items = kept;
    match (removed) {
      #Some(t) => t,
      #None    => throw #NotFound(id),
    }
  }

  function pendingByPriority(self: readonly Self): Vec<Todo> {
    let pending = self.items.iter().filter((t) => !t.done).cloned().collect();
    pending.sortBy((a, b) => a.priority.cmp(b.priority));
    pending
  }
}

export function main(): void uses Io {
  let list = TodoList.new();
  const a = list.add("Write spec", 2);
  const b = list.add("Fix borrow bug", 1);
  const c = list.add("Ship 1.0", 3);

  try {
    list.complete(a);
    const old = list.remove(c);
    println(`Removed: ${old.title}`);
    list.complete(99);
  } catch (e) {
    match (e) {
      #NotFound(id) => println(`Error: no todo with id ${id}`),
    }
  }

  for (const t of list.pendingByPriority()) {
    println(`[p${t.priority}] #${t.id}: ${t.title} (id=${b})`);
  }
}
```

**Where I was unsure or had to guess (Program 1):**
1. **Removing an element from `Vec<T>` by index (`§3.1`):** `§3.1` lists `push`, `pop`, and `drain` on `Vec`, plus slice methods `len`, `iter`, `iterMut`, `splitAt`, `last`, `includes`, `indexOf`, `sort`, `sortBy`, `reverse`, `join`. It does *not* list `remove(idx)` or `swapRemove(idx)` on `Vec`! So to implement `remove(id)` without assuming an unlisted `Vec.remove` method, I had to `drain()` the `Vec` into a new `Vec`.
2. **Writing the comparator in `sortBy` (`§2.1`, `§3.1`, `§3.5`):** `§3.1` says `sortBy(cmp)` takes a comparison returning `#Less`, `#Equal`, or `#Greater`, and `§3.5` says `<`, `<=`, `>`, `>=` call `Ord.cmp`. I guessed that `a.priority.cmp(b.priority)` can be called directly as a method on `u8` (or else I would have had to write `if (a.priority < b.priority) { #Less } else if (a.priority > b.priority) { #Greater } else { #Equal }`). Also, I wasn't sure whether `sortBy`'s closure parameters `(a, b)` are passed as `readonly Todo` borrows or by value.
3. **Can `Vec<readonly Todo>` exist?** In `pendingByPriority()`, I wanted to collect `self.items.iter().filter((t) => !t.done)` into a `Vec` and sort it. But `§4.2` says *"Containers hold first-class values. A nominal type's type parameters range over class-1 types unless the type is a `view`"* — so `self.items.iter()` yields `readonly Todo` (class 2), which means `.collect()` on `Gen<readonly Todo>` would try to build `Vec<readonly Todo>`, which is illegal! That forced me to add `impl Clone for Todo;` and call `.cloned().collect()` just to sort a filtered view of structs.

---

### Program 2: Text statistics

FILE: text_stats.fly
```ts
import { println } from "std/io";
import { HashMap } from "std/collections";

const SAMPLE: str = "the quick brown fox jumps over the lazy dog\nthe fox was very quick and the dog was lazy\nthe quick fox\n";

function lines(text: str): void uses Yield<str> {
  for (const line of text.split("\n")) {
    const trimmed = line.trim();
    if (trimmed.len() > 0) {
      yield trimmed;
    }
  }
}

function wordsInLine(line: str): void uses Yield<str> {
  for (const w of line.splitWhitespace()) {
    yield w;
  }
}

export function main(): void uses Io {
  let counts = HashMap.new<String, u64>();
  let lineNo: usize = 0;

  for (const line of lines(SAMPLE)) {
    lineNo += 1;
    const wordCount = generate(() => wordsInLine(line)).reduce((n, _) => n + 1, 0 as usize);
    println(`line ${lineNo}: ${wordCount} words`);

    for (const w of wordsInLine(line)) {
      match (counts.getMut(w)) {
        #Some(n) => { n += 1; },
        #None    => { counts.insert(w.toString(), 1); },
      }
    }
  }

  let pairs: Vec<[String, u64]> = counts
    .entries()
    .map(([k, v]) => [k.clone(), v])
    .collect();

  pairs.sortBy((a, b) => {
    if (b[1] < a[1]) {
      #Less
    } else if (b[1] > a[1]) {
      #Greater
    } else if (a[0] < b[0]) {
      #Less
    } else if (a[0] > b[0]) {
      #Greater
    } else {
      #Equal
    }
  });

  if (const #Some(best) = pairs.iter().next()) {
    println(`most frequent: ${best[0]} (${best[1]})`);
  }

  println("top 3:");
  for (const [word, count] of pairs.iter().take(3)) {
    println(`  ${word}: ${count}`);
  }
}
```

**Where I was unsure or had to guess (Program 2):**
1. **String line iteration (`§3.1`, `§5.5`, `A.2`):** `§5.5` says *"Slices, arrays, `Vec`, `String`'s lines, `HashMap` ... are all `Iterable`"*, and `A.2` calls `f.lines()` on a `File`, while `§6.2` calls `file.lines()`. However, `§3.1` lists all methods on `str` and `String` (`slice`, `split`, `trim`, `includes`, `startsWith`, `endsWith`, `indexOf`, `toUpperCase`, `toLowerCase`, `replaceAll`, `toString`, `asBytes`, `bytes()`, `splitWhitespace()`) and **omits `lines()`**! So I used `text.split("\n")` instead of `text.lines()`.
2. **What does `str.split(sep)` return (`§3.1`)?** `§3.1` says `str` has `split` and then says *"and the generators `bytes()` and `splitWhitespace()`"*, implying `split` might return a `Vec<str>` (which would violate `§4.2`'s rule against class-2 elements in `Vec`!) or a `Gen<str>` or ` void uses Yield<str>`. I assumed `for (const line of text.split("\n"))` works either way via `for…of`.
3. **Turning a generator function into a chain (`§5.5`, `A.3`):** A generator function `wordsInLine(line)` returns `void uses Yield<str>`, not a `Gen<str>`, so you can't write `wordsInLine(line).reduce(...)` directly — per `A.3`, you have to wrap it in `generate(() => wordsInLine(line))`. Meanwhile, built-in methods like `counts.entries()` are described in `§3.1` as *"the generators `keys()`, `values()`, `valuesMut()` and `entries()`"*, so I wasn't sure if `counts.entries().map(...)` works directly (meaning `entries()` returns a `Gen`) or if it needs `generate(() => counts.entries())`.
4. **What `HashMap.entries()` yields (`§3.1`, `A.2`):** `A.2` calls `counts.sortedByValue()` (which is not listed in `§3.1`!), so I sorted `counts.entries()` manually. Because `Vec` cannot hold borrows (`[str, u64]` is class 2), I had to clone the keys into `Vec<[String, u64]>`, and I had to guess whether `entries()` yields `[readonly K, readonly V]` (where `v: u64` copies out by `§4.1` *"Copy parts bind by copy"*).

---

### Program 3: Bank transfers with tasks

FILE: bank.fly
```ts
import { println } from "std/io";
import { HashMap } from "std/collections";
import { Arc, Mutex } from "std/sync";

type BankErr = #InsufficientFunds { fromAcct: String; needed: i64; available: i64 } | #UnknownAccount(String);

type Ledger = Arc<Mutex<HashMap<String, i64>>>;

function transfer(ledger: readonly Ledger, fromAcct: str, toAcct: str, amount: i64): void uses Io, Fail<BankErr> {
  const outcome: Result<void, BankErr> = ledger.lock((accounts) => {
    const srcBal = match (accounts.get(fromAcct)) {
      #Some(b) => b,
      #None    => return #Err(#UnknownAccount(fromAcct.toString())),
    };
    if (srcBal < amount) {
      return #Err(#InsufficientFunds {
        fromAcct: fromAcct.toString(),
        needed: amount,
        available: srcBal,
      });
    }
    const dstBal = match (accounts.get(toAcct)) {
      #Some(b) => b,
      #None    => return #Err(#UnknownAccount(toAcct.toString())),
    };
    accounts.insert(fromAcct.toString(), srcBal - amount);
    accounts.insert(toAcct.toString(), dstBal + amount);
    #Ok(())
  });
  outcome.unwrap()
}

export function main(): void uses Io {
  let initial = HashMap.new<String, i64>();
  initial.insert("alice".toString(), 500);
  initial.insert("bob".toString(), 300);
  initial.insert("carol".toString(), 200);

  const ledger = Arc.new(Mutex.new(initial));

  try {
    Io.scope((s) => {
      const t1 = s.fork(() => {
        transfer(ledger, "alice", "bob", 200);
        transfer(ledger, "bob", "carol", 100);
      });
      const t2 = s.fork(() => {
        transfer(ledger, "carol", "alice", 50);
        transfer(ledger, "bob", "alice", 900);
      });
      t1.join();
      t2.join();
    });
  } catch (e) {
    match (e) {
      #InsufficientFunds { fromAcct, needed, available } =>
        println(`Transfer failed: ${fromAcct} needed ${needed}, had ${available}`),
      #UnknownAccount(who) =>
        println(`Transfer failed: unknown account ${who}`),
    }
  }

  const snapshot = ledger.lock((accounts) => {
    let out: Vec<[String, i64]> = Vec.new();
    for (const [k, v] of accounts.entries()) {
      out.push([k.clone(), v]);
    }
    out
  });

  for (const [name, bal] of snapshot) {
    println(`${name}: ${bal}`);
  }
}
```

**Where I was unsure or had to guess (Program 3):**
1. **Where `Arc` and `Mutex` are imported from (`§4.5`, `§6.2`, `A.6`):** `§6.2` shows `Arc.new(Mutex.new(...))` and `A.6` has `import { Receiver, Reply } from "std/sync";`, but no section explicitly says whether `Arc` and `Mutex` are in the prelude or in `"std/sync"`. I guessed `import { Arc, Mutex } from "std/sync";`.
2. **Throwing inside `Mutex.lock` (`§6.2`):** `§6.2` gives the signature:
   `export function lock<R extends Send>(self: readonly Self, body: once (v: mut T) => R): R uses Io;`
   Notice that `body` has **no `uses ...E` effect row** — the spec explicitly says *"Because the body cannot perform effects..."*. That means you **cannot `throw` inside `ledger.lock((accounts) => { ... })`** because `Fail` is an effect! To fail on insufficient funds, I had to construct a `Result<void, BankErr>` inside the pure `lock` closure, return it from `lock`, and call `outcome.unwrap()` outside `lock` to turn `#Err` into `Fail<BankErr>`. That is sound, but surprising if you only wanted to abort with `throw` (which wouldn't hold a lock across a scheduling point anyway!).
3. **Constructing a `Result<void, E>` (`§2.2`, `§3.1`, `§3.2`):** When `T` is `void` in `Result<void, BankErr>`, how do you construct `#Ok(void)`? The spec has primitive type `void` (`§3.1`), but `§2.2` and `§2.3` never show a `void` literal (is it `#Ok(())`, `#Ok({})`, or `#Ok(void)`?). Similarly, I couldn't print inside `ledger.lock(...)` at the end of `main` because `println` uses `Io` and `lock`'s closure is pure, so I had to clone the entries out into a `Vec` snapshot first.
4. **Sharing `Arc` across `s.fork` tasks (`§4.5`, `§6.1`, `§6.2`):** `§6.1` Rule 6 says *"What is declared outside the scope it may borrow `readonly` ... since the scope outlives every task"*, and `§4.5` says `Arc<T>` lends `readonly T`, and `Mutex.lock` takes `self: readonly Self`. So borrowing `const ledger` declared before `Io.scope` as `readonly` in both `s.fork` tasks without `.clone()`-ing the `Arc` should work directly by `§6.1` Rule 6 — which made me wonder why `§6.2` says `then totals.clone() per task` (presumably only needed when a task is spawned from a helper or outlives a local).
