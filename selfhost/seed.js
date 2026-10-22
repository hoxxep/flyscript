"use strict";
// The runtime of Flyscript compiled to JavaScript: what compiled code calls that the standard
// library declares without a body (`$b`), and the operations code generation leaves to it (`$rt`).
//
// Values: integers are BigInts and floats numbers; a string holds one byte per character, so
// that lengths and offsets are the byte counts Flyscript defines; `void` is `undefined`. Structs
// and records are objects, tuples and lists arrays, a tag `{ $tag, $ }`. A value of type `mut T`
// is a reference: an object whose `v` reads and writes the place lent. A generator yields the
// operations it performs: `Yielded` for an item, `Op` for an effect of the program's own.
const { $rt, $b } = (() => {
  const fs = require("fs");

  class Fail {
    constructor(value) { this.value = value; }
  }
  class Panic extends Error {}
  function panic(message) { throw new Panic(message); }
  function raise(value) { throw new Fail(value); }

  // ---- references ----

  // A field or element of an object, lent `mut`.
  class FieldRef {
    constructor(o, k) { this.o = o; this.k = k; }
    get v() { return this.o[this.k]; }
    set v(x) { this.o[this.k] = x; }
  }
  // A range of a list lent `mut`: it reads as a copy and writes back.
  class RangeRef {
    constructor(a, lo, hi) { this.a = a; this.lo = lo; this.hi = hi; }
    get v() { return this.a.slice(this.lo, this.hi); }
    set v(x) { for (let i = 0; i < x.length; i++) this.a[this.lo + i] = x[i]; }
  }
  function indexRef(a, i) { return new FieldRef(a, at(a, i)); }
  // The list a reference to a list or a range of one reaches, and the range.
  function rangeOf(r) { return r instanceof RangeRef ? [r.a, r.lo, r.hi] : [r.v, 0, r.v.length]; }
  function rangeRef(a, lo, hi) {
    const l = Number(lo), h = hi === undefined ? a.length : Number(hi);
    if (l > h || h > a.length) panic(`range ${l}..${h} out of bounds (length ${a.length})`);
    return new RangeRef(a, l, h);
  }

  // ---- generators ----

  class Yielded {
    constructor(item) { this.item = item; }
  }
  class Op {
    constructor(effect, op, args) { this.effect = effect; this.op = op; this.args = args; }
  }
  const yielded = (item) => new Yielded(item);
  const isYield = (v) => v instanceof Yielded;
  const perform = (effect, op, args) => new Op(effect, op, args);

  // `return` inside a `handle`, leaving the function around it.
  class Return {
    constructor(v) { this.v = v; }
  }
  const YIELD = { name: "Yield" };

  // A `handle`: runs `body`, a generator, with `arms` handling `effect` (§5.2): deep, so a
  // continuation resumes the body with the handler still around it.
  function* handle(effect, body, arms) {
    return yield* resume(body(), undefined, effect, arms);
  }
  // Runs `g` from `v` until it ends, or performs an operation of `effect`, whose arm's value is
  // the result; any other operation is passed on, and its answer back.
  function* resume(g, v, effect, arms) {
    let r = g.next(v);
    for (;;) {
      if (r.done) return r.value;
      const op = r.value;
      const ours = effect === YIELD ? op instanceof Yielded : op instanceof Op && op.effect === effect;
      if (ours) {
        const name = effect === YIELD ? "yield" : op.op;
        const args = effect === YIELD ? [op.item] : op.args;
        const arm = arms[name];
        if (arm.length <= args.length) {
          // An arm that does not resume: the body is done, its cleanup run first (§5.2).
          if (g.return) g.return();
          return yield* arm(...args);
        }
        let resumed = false;
        const k = function* (x) {
          if (resumed) panic("a continuation resumed twice");
          resumed = true;
          return yield* resume(g, x, effect, arms);
        };
        return yield* arm(...args, k);
      }
      r = g.next(yield op);
    }
  }
  // Runs a generator where nothing can handle what it performs.
  function run(g) {
    const r = g.next();
    if (!r.done) panic("an effect performed that nothing handles");
    return r.value;
  }

  // `Gen<T, E>`: an iterator of what a generator yields.
  class Gen {
    constructor(it) { this.it = it; }
  }
  function* listOps(items) { for (const x of items) yield new Yielded(x); }
  const genOf = (items) => new Gen(listOps(items));
  // The next item of a generator, or `undefined` once it is done.
  function step(g) {
    const r = g.it.next();
    if (r.done) return undefined;
    if (!(r.value instanceof Yielded)) panic("an effect performed inside a generator that is not handled here");
    return r.value;
  }

  // What a `for` iterates directly.
  function items(v) {
    if (Array.isArray(v)) return v;
    if (v instanceof Bytes) return v.items();
    if (typeof v === "string") return Array.from(v, (c) => BigInt(c.charCodeAt(0)));
    panic(`cannot iterate over ${show(v)}`);
  }

  // ---- strings ----

  // A string's bytes, `s.asBytes()`: a view of the string, not a copy of it.
  class Bytes {
    constructor(s) { this.s = s; }
    get length() { return this.s.length; }
    items() { return Array.from(this.s, (c) => BigInt(c.charCodeAt(0))); }
  }

  // ---- integers ----

  const BOUNDS = {
    i8: [-(1n << 7n), (1n << 7n) - 1n], i16: [-(1n << 15n), (1n << 15n) - 1n], i32: [-(1n << 31n), (1n << 31n) - 1n],
    i64: [-(1n << 63n), (1n << 63n) - 1n], isize: [-(1n << 63n), (1n << 63n) - 1n], i128: [-(1n << 127n), (1n << 127n) - 1n],
    u8: [0n, 255n], u16: [0n, 65535n], u32: [0n, (1n << 32n) - 1n], u64: [0n, (1n << 64n) - 1n], usize: [0n, (1n << 64n) - 1n],
  };
  const WIDTHS = { i8: [8, true], i16: [16, true], i32: [32, true], i64: [64, true], isize: [64, true], i128: [128, true],
    u8: [8, false], u16: [16, false], u32: [32, false], u64: [64, false], usize: [64, false] };
  const checks = {}, wraps = {};
  for (const name of Object.keys(BOUNDS)) {
    const [lo, hi] = BOUNDS[name];
    const [w, signed] = WIDTHS[name];
    // Overflowing `i128`, the widest type, is overflowing whatever the static type is.
    checks[name] = (x) => {
      if (x < lo || x > hi) {
        if (x < BOUNDS.i128[0] || x > BOUNDS.i128[1]) panic("arithmetic overflow");
        panic(`arithmetic overflow: ${x} does not fit in \`${name}\``);
      }
      return x;
    };
    wraps["wrap_" + name] = signed ? (x) => BigInt.asIntN(w, x) : (x) => BigInt.asUintN(w, x);
  }
  function div(x, y, check) {
    if (y === 0n) panic("division by zero");
    return check(x / y);
  }
  function rem(x, y) {
    if (y === 0n) panic("division by zero");
    return x % y;
  }
  function fmod(x, y) { return x % y; }
  function truncFloat(f) {
    if (Number.isNaN(f)) return 0n;
    if (f >= 1.7e38) return BOUNDS.i128[1];
    if (f <= -1.7e38) return BOUNDS.i128[0];
    return BigInt(Math.trunc(f));
  }
  const toInt = (v) => (typeof v === "boolean" ? (v ? 1n : 0n) : v);

  // ---- lists ----

  function at(a, i) {
    const n = Number(i);
    if (i < 0n || n >= a.length) panic(`index ${i} out of bounds (length ${a.length})`);
    return n;
  }
  function idx(a, i) {
    const n = at(a, i);
    if (a instanceof Bytes) return BigInt(a.s.charCodeAt(n));
    if (typeof a === "string") return BigInt(a.charCodeAt(n));
    return a[n];
  }
  const continuation = (s, i) => i < s.length && (s.charCodeAt(i) & 0xc0) === 0x80;
  function slice(a, lo, hi) {
    const l = Number(lo), h = hi === undefined ? a.length : Number(hi);
    if (l > h || h > a.length) panic(`range ${l}..${h} out of bounds (length ${a.length})`);
    // A string's bounds fall between characters: not on a UTF-8 continuation byte (§3.1).
    if (typeof a === "string" && (continuation(a, l) || continuation(a, h))) panic(`range ${l}..${h} splits a character`);
    if (a instanceof Bytes) return new Bytes(a.s.slice(l, h));
    return a.slice(l, h);
  }

  // A `Copy` object copied: JavaScript shares objects, Flyscript copies `Copy` ones.
  function copy(v) {
    if (typeof v !== "object" || v === null) return v;
    if (Array.isArray(v)) return v.map(copy);
    if (Object.getPrototypeOf(v) !== Object.prototype) return v;
    const out = {};
    for (const k of Object.keys(v)) out[k] = copy(v[k]);
    return out;
  }

  // ---- display ----

  function showFloat(f) {
    if (Number.isInteger(f) && Math.abs(f) < 1e15) return f.toFixed(1);
    if (Number.isNaN(f)) return "NaN";
    if (f === Infinity) return "inf";
    if (f === -Infinity) return "-inf";
    return String(f);
  }
  function quoted(s) {
    return "\"" + s.replace(/[\\"\n\t\r]/g, (c) => ({ "\\": "\\\\", "\"": "\\\"", "\n": "\\n", "\t": "\\t", "\r": "\\r" })[c]) + "\"";
  }
  // What `Show.show` writes, as a string.
  function shown(show, v) {
    const out = { v: "" };
    show(v, out);
    return out.v;
  }
  // A value's structure, as the interpreter shows one with no `Show` to hand.
  function show(v) {
    switch (typeof v) {
      case "string": return v;
      case "bigint": case "boolean": return String(v);
      case "number": return showFloat(v);
      case "undefined": return "void";
      case "function": return "<function>";
    }
    return nested(v);
  }
  function nested(v) {
    if (typeof v === "string") return quoted(v);
    if (typeof v !== "object" || v === null) return show(v);
    if (Array.isArray(v)) return "[" + v.map(nested).join(", ") + "]";
    if (v instanceof Bytes) return nested(v.items());
    if (v.$tag !== undefined) {
      if (!("$" in v)) return "#" + v.$tag;
      if (Array.isArray(v.$)) return "#" + v.$tag + "(" + v.$.map(nested).join(", ") + ")";
      if (typeof v.$ === "object" && v.$ !== null && Object.getPrototypeOf(v.$) === Object.prototype && v.$.$tag === undefined) return "#" + v.$tag + " " + nested(v.$);
      return "#" + v.$tag + "(" + nested(v.$) + ")";
    }
    if (v instanceof HashMap) return "{ " + [...v.m.values()].map(([k, x]) => nested(k) + ": " + nested(x)).join(", ") + " }";
    const fields = Object.keys(v).sort().map((k) => k + ": " + nested(v[k]));
    return "{ " + fields.join(", ") + " }";
  }

  // ---- structural order, for what the runtime sorts ----

  function compare(a, b) {
    switch (typeof a) {
      case "number":
        if (Number.isNaN(a)) return Number.isNaN(b) ? 0 : 1;
        if (Number.isNaN(b)) return -1;
        return a < b ? -1 : a > b ? 1 : 0;
      case "bigint": case "string": case "boolean":
        return a < b ? -1 : a > b ? 1 : 0;
    }
    if (Array.isArray(a)) {
      const n = Math.min(a.length, b.length);
      for (let i = 0; i < n; i++) { const c = compare(a[i], b[i]); if (c !== 0) return c; }
      return a.length < b.length ? -1 : a.length > b.length ? 1 : 0;
    }
    return compare(keyOf(a), keyOf(b));
  }
  const ordinal = (o) => (o.$tag === "Less" ? -1 : o.$tag === "Greater" ? 1 : 0);

  // ---- maps ----

  // A key's identity: its structure, as equal values have equal structure.
  function keyOf(k) {
    switch (typeof k) {
      case "string": return "s" + k;
      case "bigint": return "i" + k;
      case "boolean": return k ? "t" : "f";
      case "number": return "n" + (k === 0 ? 0 : k);
      case "undefined": return "u";
    }
    if (Array.isArray(k)) return "[" + k.map(keyOf).join(",") + "]";
    if (k instanceof Bytes) return "s" + k.s;
    return "{" + Object.keys(k).sort().map((f) => f + ":" + keyOf(k[f])).join(",") + "}";
  }

  class HashMap {
    constructor() { this.m = new Map(); }
  }
  const none = () => ({ $tag: "None" });
  const some = (v) => ({ $tag: "Some", $: v });

  class Hasher {
    constructor() { this.h = 0xcbf29ce484222325n; }
    bytes(bs) { for (const b of bs) this.h = BigInt.asUintN(64, (this.h ^ BigInt(b)) * 0x100000001b3n); }
  }

  // ---- the simulated world ----

  let clock = 0n;

  // ---- tasks (§6.1): one runs at a time, and at each scheduling point the next is chosen by a
  // seeded generator, as the interpreter's scheduler does, so a seed reproduces an interleaving.

  // What a task's generator yields to the scheduler: a scheduling point, or a wait.
  class Point {
    constructor(wait) { this.wait = wait; }
  }
  class Cancelled extends Error {}
  const sched = {
    on: false, current: 0, ready: [], blocked: new Map(), finished: new Set(), rng: 0x5eedn, next: 1,
    tasks: new Map(), channels: new Map(), closed: new Set(), senders: new Map(), cancelled: new Set(), scopes: new Map(), scopeIds: 1,
  };
  // Hands the baton to a ready task, chosen by the seed; `false` if none can run.
  function pass() {
    if (sched.ready.length === 0) return false;
    let r = sched.rng;
    r = BigInt.asUintN(64, r ^ (r << 13n));
    r = BigInt.asUintN(64, r ^ (r >> 7n));
    r = BigInt.asUintN(64, r ^ (r << 17n));
    sched.rng = r;
    const i = Number(r % BigInt(sched.ready.length));
    sched.current = sched.ready.splice(i, 1)[0];
    return true;
  }
  function wake(kind, id) {
    for (const [t, w] of [...sched.blocked]) {
      if (w[0] === kind && w[1] === id) { sched.blocked.delete(t); sched.ready.push(t); }
    }
  }
  // A scheduling point: another ready task may run, this one again among them.
  function* point() { if (sched.on) yield new Point(undefined); }
  // Parks the task until `wait` is met.
  function* block(wait) {
    if (!sched.on) panic("deadlock: every task is waiting");
    yield new Point(wait);
  }
  function cancel(t) {
    sched.cancelled.add(t);
    if (sched.blocked.delete(t)) sched.ready.push(t);
  }
  // Runs the tasks, starting with `main`, until `main` ends.
  function runTasks(main) {
    sched.on = true;
    sched.tasks.set(0, { gen: main, input: undefined, error: undefined });
    for (;;) {
      const me = sched.current;
      const t = sched.tasks.get(me);
      let r;
      try {
        // A cancelled task unwinds at its next scheduling point; one not started never runs.
        if (t.error === undefined && sched.cancelled.has(me)) t.error = new Cancelled();
        const error = t.error, input = t.input;
        t.error = undefined;
        t.input = undefined;
        r = error !== undefined ? t.gen.throw(error) : t.gen.next(input);
      } catch (e) {
        if (me === 0) throw e;
        endTask(me, { error: e });
        continue;
      }
      if (r.done) {
        if (me === 0) return r.value;
        endTask(me, { value: r.value });
        continue;
      }
      if (!(r.value instanceof Point)) panic("an effect performed that nothing handles");
      if (r.value.wait === undefined) {
        sched.ready.push(me);
        pass();
      } else {
        sched.blocked.set(me, r.value.wait);
        if (!pass()) {
          // Nothing else can run, so nothing can ever wake this task: reported, not waited on.
          sched.blocked.delete(me);
          sched.current = me;
          t.error = new Panic("deadlock: every task is waiting");
        }
      }
    }
  }
  // Task `me` has finished: its outcome goes to its scope, and its joiners wake.
  function endTask(me, outcome) {
    const t = sched.tasks.get(me);
    const st = sched.scopes.get(t.scope);
    if (outcome.error === undefined) {
      st.fibers.set(me, { value: outcome.value });
    } else if (outcome.error instanceof Fail) {
      // The first failure cancels the scope: its body and its other tasks.
      if (st.failure === undefined) {
        st.failure = outcome.error;
        cancel(st.owner);
        for (const o of st.tasks) if (o !== me) cancel(o);
      }
      st.fibers.set(me, { error: outcome.error });
    } else if (outcome.error instanceof Panic) {
      if (st.panic === undefined) st.panic = outcome.error;
    } else if (!(outcome.error instanceof Cancelled)) {
      throw outcome.error;
    }
    sched.finished.add(me);
    wake("task", me);
    if (!pass()) panic("deadlock: every task is waiting");
  }
  function* join(t) {
    if (!sched.finished.has(t)) yield* block(["task", t]);
  }
  // A task's body: a generator, or what a plain closure gives.
  function* body(f, ...args) {
    const r = f(...args);
    if (r !== null && typeof r === "object" && typeof r.next === "function" && typeof r[Symbol.iterator] === "function") return yield* r;
    return r;
  }
  function spawnTask(sid, task) {
    const id = sched.next++;
    sched.ready.push(id);
    sched.tasks.set(id, { gen: body(task), input: undefined, error: undefined, scope: sid });
    sched.scopes.get(sid).tasks.push(id);
    return id;
  }
  function channel() {
    const id = sched.next++;
    sched.channels.set(id, []);
    sched.senders.set(id, 1);
    return id;
  }
  function* send(ch, v) {
    sched.channels.get(ch).push(v);
    wake("channel", ch);
    yield* point();
  }
  // The next message, or `undefined` once the channel is closed and drained.
  function* recv(ch) {
    for (;;) {
      const q = sched.channels.get(ch);
      if (q.length > 0) return { v: q.shift() };
      if (sched.closed.has(ch)) return undefined;
      yield* block(["channel", ch]);
    }
  }
  function* close(ch) {
    const left = Math.max(0, (sched.senders.get(ch) || 0) - 1);
    sched.senders.set(ch, left);
    if (left === 0) { sched.closed.add(ch); wake("channel", ch); }
    yield* point();
  }

  // ---- what the standard library declares without a body ----

  const $b = {
    panic,
    println(s) { process.stdout.write(Buffer.from(s + "\n", "latin1")); },
    writeFile(path, content) {
      try { fs.writeFileSync(Buffer.from(path, "latin1").toString("utf8"), Buffer.from(content, "latin1")); }
      catch (e) { throw new Fail({ $tag: "PermissionDenied" }); }
    },
    parseInt(s) { return /^[+-]?\d+$/.test(s) ? some(BigInt(s)) : none(); },
    parseFloat(s) { const f = Number(s); return s.trim() !== "" && !Number.isNaN(f) ? some(f) : none(); },
    replace(r, v) { const old = r.v; r.v = v; return old; },
    swap(a, b) { const t = a.v; a.v = b.v; b.v = t; },
    alloc: (v) => v,
    allocAll: (vs) => vs.slice(),
    fmt: (s) => s,
    copyUtf8: (bytes) => (bytes instanceof Bytes ? bytes.s : String.fromCharCode(...bytes.map(Number))),
    repeat: (v, n) => Array.from({ length: n }, () => copy(v)),
    generate: (producer) => new Gen(producer()),

    Option_isSome: (o) => o.$tag === "Some",
    Option_take(r) { const old = r.v; r.v = none(); return old; },
    Option_unwrapOr: (o, d) => (o.$tag === "Some" ? o.$ : d),
    Option_cloned: (o) => o,
    Result_unwrap: (r) => (r.$tag === "Ok" ? r.$ : raise(r.$)),
    Fail_capture(body) {
      try { return { $tag: "Ok", $: body() }; }
      catch (e) { if (e instanceof Fail) return { $tag: "Err", $: e.value }; throw e; }
    },
    Fail_map(body, wrap) {
      try { return body(); }
      catch (e) { if (e instanceof Fail) throw new Fail(wrap(e.value)); throw e; }
    },

    String_new: () => "",
    String_len: (s) => BigInt(s.length),
    String_push(r, s) { r.v = r.v + s; },
    String_asStr: (s) => s,
    String_clone: (s) => s,
    String_fromUtf8: (bytes) => some(String.fromCharCode(...bytes.map(Number))),
    str_slice: (s, i, j) => slice(s, i, j),
    str_len: (s) => BigInt(s.length),
    str_toString: (s) => s,
    *str_bytes(s) { for (let i = 0; i < s.length; i++) yield new Yielded(BigInt(s.charCodeAt(i))); },
    str_asBytes: (s) => new Bytes(s),
    *str_splitWhitespace(s) { for (const w of s.split(/[ \t\n\r]+/)) if (w !== "") yield new Yielded(w); },
    *str_lines(s) { const ls = s.split("\n"); if (ls[ls.length - 1] === "") ls.pop(); for (const l of ls) yield new Yielded(l.endsWith("\r") ? l.slice(0, -1) : l); },
    str_split: (s, sep) => s.split(sep),
    str_trim: (s) => s.replace(/^[ \t\n\r]+|[ \t\n\r]+$/g, ""),
    str_includes: (s, p) => s.includes(p),
    str_startsWith: (s, p) => s.startsWith(p),
    str_endsWith: (s, p) => s.endsWith(p),
    str_indexOf: (s, p) => { const i = s.indexOf(p); return i < 0 ? none() : some(BigInt(i)); },
    // Byte strings hold UTF-8: only ASCII letters change case.
    str_toUpperCase: (s) => s.replace(/[a-z]/g, (c) => c.toUpperCase()),
    str_toLowerCase: (s) => s.replace(/[A-Z]/g, (c) => c.toLowerCase()),
    str_replaceAll: (s, a, b) => s.split(a).join(b),

    slice_len: (a) => BigInt(a.length),
    slice_iter: (a) => genOf(items(a)),
    slice_iterMut: (r) => { const a = r.v; return new Gen((function* () { for (let i = 0; i < a.length; i++) yield new Yielded(new FieldRef(a, i)); })()); },
    slice_splitAt(r, i) { const a = r.v; const n = at(a.concat([undefined]), i); return [new RangeRef(a, 0, n), new RangeRef(a, n, a.length)]; },
    slice_sortBy(r, cmp) {
      const a = r.v;
      const sorted = a.map((x, i) => [x, i]).sort((x, y) => ordinal(cmp(x[0], y[0])) || x[1] - y[1]).map((x) => x[0]);
      r.v = sorted;
      if (r instanceof RangeRef) return;
      for (let i = 0; i < sorted.length; i++) a[i] = sorted[i];
    },
    slice_reverse(r) { r.v = r.v.slice().reverse(); },
    *slice_each(a) { for (const x of items(a)) yield new Yielded(x); },
    *array_each(a) { for (const x of a) yield new Yielded(x); },

    // `std/par`: a list split into disjoint slices, each lent `mut`.
    slice_slice: (r) => (r instanceof RangeRef ? r : new RangeRef(r.v, 0, r.v.length)),
    array_slice: (r) => $b.slice_slice(r),
    Vec_slice: (r) => $b.slice_slice(r),
    slice_split(s, i) {
      const [a, lo, hi] = rangeOf(s), n = Number(i);
      if (n > hi - lo) panic(`index ${i} out of bounds (length ${hi - lo})`);
      return [new RangeRef(a, lo, lo + n), new RangeRef(a, lo + n, hi)];
    },
    array_split: (s, i) => $b.slice_split(s, i),
    Vec_split: (s, i) => $b.slice_split(s, i),
    slice_viewAt(s, i) { const [a, lo, hi] = rangeOf(s); if (i < 0n || Number(i) >= hi - lo) panic(`index ${i} out of bounds (length ${hi - lo})`); return new FieldRef(a, lo + Number(i)); },
    array_viewAt: (s, i) => $b.slice_viewAt(s, i),
    Vec_viewAt: (s, i) => $b.slice_viewAt(s, i),
    slice_readAt: (a, i) => idx(a, i),
    array_readAt: (a, i) => idx(a, i),
    Vec_readAt: (a, i) => idx(a, i),
    array_len: (a) => BigInt(a.length),

    Vec_new: () => [],
    Vec_push(r, x) { r.v.push(x); },
    Vec_pop(r) { const a = r.v; return a.length === 0 ? none() : some(a.pop()); },
    Vec_remove(r, i) { const a = r.v; return a.splice(at(a, i), 1)[0]; },
    Vec_insert(r, i, x) { const a = r.v; if (i < 0n || Number(i) > a.length) panic(`index ${i} out of bounds (length ${a.length})`); a.splice(Number(i), 0, x); },
    Vec_retain(r, keep) { const a = r.v; let j = 0; for (const x of a) if (keep(x)) a[j++] = x; a.length = j; },
    Vec_truncate(r, n) { const a = r.v; if (a.length > Number(n)) a.length = Number(n); },
    Vec_drain(r) { const a = r.v; return genOf(a.splice(0)); },
    Vec_len: (a) => BigInt(a.length),
    Vec_iter: (a) => genOf(a),
    Vec_iterMut: (r) => $b.slice_iterMut(r),
    *Vec_each(a) { for (const x of a) yield new Yielded(x); },

    Box_new: (v) => v, Box_get: (v) => v, Box_into: (v) => v,
    Arc_new: (v) => v, Arc_get: (v) => v, Arc_clone: (v) => v,
    Ref_get: (v) => v, Ref_clone: (v) => v,

    Hasher_new: () => new Hasher(),
    Hasher_writeInt(r, i) { const b = []; let x = BigInt.asUintN(64, i); for (let k = 0; k < 8; k++) { b.push(Number(x & 255n)); x >>= 8n; } r.v.bytes(b); },
    Hasher_writeFloat(r, f) { $b.Hasher_writeStr(r, String(f === 0 ? 0 : f)); },
    Hasher_writeBool(r, b) { r.v.bytes([b ? 1 : 0]); },
    Hasher_writeStr(r, s) { r.v.bytes(Array.from(s, (c) => c.charCodeAt(0))); },
    Hasher_finish: (h) => h.h,

    HashMap_new: () => new HashMap(),
    HashMap_insert(r, k, v) { r.v.m.set(keyOf(k), [k, v]); },
    HashMap_get(m, k) { const e = m.m.get(keyOf(k)); return e === undefined ? none() : some(e[1]); },
    HashMap_getMut(r, k) { const e = r.v.m.get(keyOf(k)); return e === undefined ? none() : some(new FieldRef(e, 1)); },
    HashMap_has: (m, k) => m.m.has(keyOf(k)),
    HashMap_remove(r, k) {
      const m = r.v.m, key = keyOf(k), e = m.get(key);
      if (e === undefined) return none();
      m.delete(key);
      return some(e[1]);
    },
    HashMap_len: (m) => BigInt(m.m.size),
    HashMap_keys: (m) => genOf(Array.from(m.m.values(), (e) => e[0])),
    HashMap_values: (m) => genOf(Array.from(m.m.values(), (e) => e[1])),
    HashMap_valuesMut: (r) => genOf(Array.from(r.v.m.values(), (e) => new FieldRef(e, 1))),
    HashMap_entries: (m) => genOf(Array.from(m.m.values(), (e) => [e[0], e[1]])),
    HashMap_sortedByValue: (m) => Array.from(m.m.values(), (e) => [e[0], e[1]]).sort((a, b) => compare(b[1], a[1]) || compare(a[0], b[0])),

    Cell_new: (v) => ({ v }),
    Cell_get: (c) => c.v,
    Cell_set(c, v) { c.v = v; },
    Cell_clone: (c) => c,
    RegionList_new: () => [],
    RegionList_push(l, v) { l.push(v); },
    RegionList_len: (l) => BigInt(l.length),
    RegionList_clone: (l) => l,
    *RegionList_each(l) { for (const x of l) yield new Yielded(x); },

    Gen_next(r) { const s = step(r.v); return s === undefined ? none() : some(s.item); },
    Gen_map: (g, f) => new Gen((function* () { for (let s = step(g); s !== undefined; s = step(g)) yield new Yielded(f(s.item)); })()),
    Gen_filter: (g, keep) => new Gen((function* () { for (let s = step(g); s !== undefined; s = step(g)) if (keep(s.item)) yield s; })()),
    Gen_take: (g, n) => new Gen((function* () { let i = 0n; if (i >= n) return; for (let s = step(g); s !== undefined; s = step(g)) { yield s; if (++i >= n) return; } })()),
    Gen_zip: (g, h) => new Gen((function* () { for (let s = step(g); s !== undefined; s = step(g)) { const t = step(h); if (t === undefined) return; yield new Yielded([s.item, t.item]); } })()),
    Gen_enumerate: (g) => new Gen((function* () { let i = 0n; for (let s = step(g); s !== undefined; s = step(g)) yield new Yielded([i++, s.item]); })()),
    Gen_collect(g) { const out = []; for (let s = step(g); s !== undefined; s = step(g)) out.push(s.item); return out; },
    *Gen_each(g) { yield* g.it; },
    Gen_drop(r) { if (r.v.it.return) r.v.it.return(); },

    File_open(path) {
      try { return { text: fs.readFileSync(Buffer.from(path, "latin1").toString("utf8")).toString("latin1") }; }
      catch (e) { throw new Fail({ $tag: "NotFound" }); }
    },
    File_readText: (r) => r.v.text,
    *File_lines(r) { yield* $b.str_lines(r.v.text); },

    // ---- tasks and channels: generators, as they are scheduling points ----
    *Io_scope$g(f) {
      const sid = sched.scopeIds++;
      const st = { owner: sched.current, tasks: [], fibers: new Map(), failure: undefined, panic: undefined };
      sched.scopes.set(sid, st);
      let result, error;
      try { result = yield* body(f, { v: { sid } }); }
      catch (e) {
        // The body unwound because a task failed: the scope rethrows that failure.
        if (!(e instanceof Cancelled && st.failure !== undefined)) error = e;
      }
      sched.cancelled.delete(sched.current);
      // A scope returns only when every task started in it has finished (§6.1).
      for (const t of st.tasks) {
        for (;;) {
          try { yield* join(t); break; }
          catch (e) { if (!(e instanceof Cancelled)) throw e; sched.cancelled.delete(sched.current); }
        }
      }
      sched.cancelled.delete(sched.current);
      sched.scopes.delete(sid);
      if (st.panic !== undefined) throw st.panic;
      if (error !== undefined) throw error;
      if (st.failure !== undefined) throw st.failure;
      return result;
    },
    *Scope_spawn$g(r, task) { spawnTask(r.v.sid, task); yield* point(); },
    *Scope_fork$g(r, task) { const t = spawnTask(r.v.sid, task); yield* point(); return { task: t }; },
    *Fiber_join$g(f) {
      yield* join(f.task);
      for (const st of sched.scopes.values()) {
        const o = st.fibers.get(f.task);
        if (o !== undefined) { if (o.error !== undefined) throw o.error; return o.value; }
      }
      panic("a joined task did not finish");
    },
    channel: () => { const ch = channel(); return [{ ch }, { ch }]; },
    Reply_new: () => { const ch = channel(); return [{ ch }, { ch }]; },
    *Sender_send$g(s, v) { yield* send(s.ch, v); },
    *Reply_send$g(s, v) { yield* send(s.ch, v); },
    *Receiver_recv$g(rx) { const m = yield* recv(rx.ch); return m === undefined ? none() : some(m.v); },
    *Pending_wait$g(p) { const m = yield* recv(p.ch); if (m === undefined) panic("the reply was dropped unsent"); return m.v; },
    *Sender_close$g(s) { yield* close(s.ch); },
    *Sender_drop(r) { yield* close(r.v.ch); },
    Sender_clone: (s) => { sched.senders.set(s.ch, (sched.senders.get(s.ch) || 0) + 1); return { ch: s.ch }; },
    *Receiver_each(rx) { for (let m = yield* recv(rx.ch); m !== undefined; m = yield* recv(rx.ch)) yield new Yielded(m.v); },
    Mutex_new: (v) => ({ v }),
    *Mutex_lock$g(m, f) { yield* point(); return yield* body(f, m); },

    Io_now: () => ({ nanos: clock }),
    Io_sleep(d) { clock += d.nanos; },
    Io_write(fd, buf) {
      const s = buf instanceof Bytes ? buf.s : String.fromCharCode(...buf.map(Number));
      process.stdout.write(Buffer.from(s, "latin1"));
      return { $tag: "Ok", $: BigInt(s.length) };
    },
    Io_read: () => ({ $tag: "Ok", $: 0n }),
  };
  // The root `Io` operations are scheduling points.
  for (const op of ["Io_now", "Io_sleep", "Io_write", "Io_read"]) {
    const f = $b[op];
    $b[op + "$g"] = function* (...args) { yield* point(); return f(...args); };
  }
  // Higher-order builtins whose closures may suspend.
  $b.Fail_capture$g = function* (f) {
    try { return { $tag: "Ok", $: yield* body(f) }; }
    catch (e) { if (e instanceof Fail) return { $tag: "Err", $: e.value }; throw e; }
  };
  $b.Fail_map$g = function* (f, wrap) {
    try { return yield* body(f); }
    catch (e) { if (e instanceof Fail) throw new Fail(yield* body(wrap, e.value)); throw e; }
  };
  $b.Gen_next$g = function* (r) {
    const g = r.v;
    let answer;
    for (;;) {
      const s = g.it.next(answer);
      if (s.done) return none();
      if (s.value instanceof Yielded) return some(s.value.item);
      answer = yield s.value;
    }
  };
  // Steps a generator, passing on what it performs other than its items.
  function* items$g(g, each) {
    let answer;
    for (;;) {
      const s = g.it.next(answer);
      answer = undefined;
      if (s.done) return;
      if (s.value instanceof Yielded) { if ((yield* each(s.value.item)) === false) return; }
      else answer = yield s.value;
    }
  }
  $b.Gen_map$g = (g, f) => new Gen(items$g(g, function* (x) { yield new Yielded(yield* body(f, x)); }));
  $b.Gen_filter$g = (g, keep) => new Gen(items$g(g, function* (x) { if (yield* body(keep, x)) yield new Yielded(x); }));
  $b.Gen_collect$g = function* (g) { const out = []; yield* items$g(g, function* (x) { out.push(x); }); return out; };
  // Any other builtin, called where its caller may suspend, is the same as a generator.
  for (const k of Object.keys($b)) {
    const f = $b[k];
    if (k.endsWith("$g") || $b[k + "$g"] !== undefined || f.constructor.name === "GeneratorFunction") continue;
    $b[k + "$g"] = function* (...args) { return f(...args); };
  }
  for (const t of ["i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "usize"]) {
    const [w, signed] = WIDTHS[t];
    const wrap = signed ? (x) => BigInt.asIntN(w, x) : (x) => BigInt.asUintN(w, x);
    $b[t + "_wrappingAdd"] = (a, b) => wrap(a + b);
    $b[t + "_wrappingSub"] = (a, b) => wrap(a - b);
    $b[t + "_wrappingMul"] = (a, b) => wrap(a * b);
  }

  // ---- running a program ----

  const argv = process.argv.slice(2).map((a) => Buffer.from(a, "utf8").toString("latin1"));
  const argStr = (i) => argv[i];
  function argInt(i) { return /^-?\d+$/.test(argv[i]) ? BigInt(argv[i]) : panic(`argument ${i + 1} is not an integer`); }

  // Runs a program's `main`, as `flyc run` does.
  function start(main, suspends, tasks) {
    try {
      if (tasks) runTasks(body(main));
      else {
        const r = main();
        if (suspends) for (let s = r.next(); !s.done; s = r.next()) panic("an effect performed that nothing handles");
      }
    } catch (e) {
      if (e instanceof Panic) { process.stdout.write(Buffer.from(`<panic: ${e.message}>\n`, "latin1")); process.exit(101); }
      if (e instanceof Fail) { process.stdout.write(Buffer.from(`<uncaught: ${show(e.value)}>\n`, "latin1")); process.exit(1); }
      throw e;
    }
  }

  const $rt = {
    Fail, Panic, Return, YIELD, handle, run, panic, raise, FieldRef, indexRef, rangeRef, yielded, isYield, perform, items,
    div, rem, fmod, truncFloat, toInt, at, idx, slice, copy, showFloat, shown, show,
    unmatched: (v) => panic(`no arm matched ${show(v)}`),
    argStr, argInt, start,
    ...checks, ...wraps,
  };
  return { $rt, $b };
})();

const $c6$SYNTH_BASE = (1n << 40n);
const $c7$STD = ["std/prelude.fly", "std/region.d.fly", "std/net.d.fly", "std/io.d.fly", "std/collections.d.fly", "std/par.fly", "std/layout.fly", "std/sync.d.fly", "std/json.fly"];
const $c1$RESERVED = ["arguments", "await", "case", "catch", "class", "debugger", "default", "delete", "do", "else", "enum", "eval", "export", "extends", "finally", "function", "implements", "import", "in", "instanceof", "interface", "let", "new", "null", "package", "private", "protected", "public", "static", "super", "switch", "this", "typeof", "undefined", "var", "void", "with", "yield", "NaN", "Infinity"];
const $c3$COMPTIME_METHODS = ["len", "isEmpty", "enumerate", "map", "filter", "any"];
const $c5$PRIMS = ["i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "usize", "f32", "f64", "bool", "str", "void", "never", "Type"];
const $c2$HEX = "0123456789abcdef";
const $c9$ASSIGN = ["=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^="];
const $c4$STEP_BUDGET = 1000000n;
const $c10$KEYWORDS = ["as", "break", "catch", "comptime", "const", "continue", "defer", "dyn", "else", "enum", "export", "extends", "extern", "false", "for", "function", "if", "impl", "import", "interface", "let", "mut", "once", "readonly", "return", "struct", "throw", "true", "try", "type", "unsafe", "uses", "while", "yield"];
const $c11$PUNCT = ["...", "..", "=>", "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "{", "}", "(", ")", "[", "]", "<", ">", ",", ";", ":", ".", "=", "+", "-", "*", "/", "%", "&", "|", "^", "!", "?", "@", "~"];
const $c8$BINARY = [["||"], ["&&"], ["==", "!=", "<", ">", "<=", ">="], ["|"], ["^"], ["&"], ["<<", ">>"], ["+", "-"], ["*", "/", "%"]];
function main$0(entry, out, root) {
  try {
    compile$1(entry, out, root);
    return undefined;
  } catch ($1) {
    if (!($1 instanceof $rt.Fail)) throw $1;
    const e = $1.value;
    const $2 = e;
    m$3: {
      if (($2.$tag === "Failed")) {
        {
          return undefined;
        }
        break m$3;
      }
      if (($2.$tag === "Unreadable")) {
        const path = $2.$.path;
        return $b.println(("" + "error: cannot read or write " + path));
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
}
function compile$1(entry, out, root) {
  const p = { v: load$2([$b.str_toString(entry)], $b.String_asStr(("" + root + "/std"))) };
  if (($b.slice_len(p.v.diags) === 0n)) {
    let fid = 0n;
    while ((fid < $b.slice_len(p.v.fns))) {
      checkFn$3(p, fid);
      fid = $rt.usize(fid + 1n);
    }
  }
  if (($b.slice_len(p.v.diags) > 0n)) {
    report$4(p.v);
    throw new $rt.Fail({ $tag: "Failed" });
  }
  const runtime = ("" + root + "/selfhost/runtime.js");
  let $1;
  try {
    const f = { v: $b.File_open($b.String_asStr(runtime)) };
    $1 = $b.File_readText(f);
  } catch ($2) {
    if (!($2 instanceof $rt.Fail)) throw $2;
    throw new $rt.Fail({ $tag: "Unreadable", $: { path: runtime } });
  }
  const rt = $1;
  const file = entryFile$5(p.v, entry);
  let $3;
  const $4 = findIndex$7($b.slice_iter(p.v.modules), ((m) => {
  return eq$6(m.file, file);
  }));
  m$5: {
    if (($4.$tag === "Some")) {
      const k = $4.$;
      $3 = k;
      break m$5;
    }
    if (($4.$tag === "None")) {
      throw new $rt.Fail({ $tag: "Unreadable", $: { path: file } });
      break m$5;
    }
    $rt.unmatched($4);
  }
  const main = $3;
  let $6;
  try {
    $6 = program$8(p.v, main, $b.String_asStr(rt));
  } catch ($7) {
    if (!($7 instanceof $rt.Fail)) throw $7;
    if (!(($7.value.$tag === "Failed"))) throw $7;
    const message = $7.value.$;
    $b.println($b.String_asStr(message));
    throw new $rt.Fail({ $tag: "Failed" });
  }
  const js = $6;
  try {
    $b.writeFile(out, $b.String_asStr(js));
  } catch ($8) {
    if (!($8 instanceof $rt.Fail)) throw $8;
    throw new $rt.Fail({ $tag: "Unreadable", $: { path: $b.str_toString(out) } });
  }
  return undefined;
}
function load$2(entries, std) {
  const p = { v: { modules: $b.Vec_new(), defs: $b.Vec_new(), consts: $b.Vec_new(), fns: $b.Vec_new(), impls: $b.Vec_new(), diags: $b.Vec_new(), nextSym: 0n, known: $b.HashMap_new(), inferred: $b.HashMap_new(), checked: new$$9(), typed: $b.HashMap_new(), ifaceFns: $b.HashMap_new(), spliced: $b.Vec_new(), bodies: $b.HashMap_new(), synth: $b.HashMap_new(), nextSynth: $c6$SYNTH_BASE, nextId: $rt.usize(1n << 32n), specs: $b.HashMap_new(), assocInstances: $b.HashMap_new(), instances: $b.HashMap_new(), specOf: $b.HashMap_new(), specNotes: $b.HashMap_new(), specRequested: $b.HashMap_new(), assumedPure: $b.HashMap_new(), pendingAliases: $b.HashMap_new(), aliasing: $b.Vec_new(), note: { $tag: "None" } } };
  for (const $1 of $rt.items($c7$STD)) {
    const file = $1;
    const name = $b.str_replaceAll($b.str_replaceAll(file, ".d.fly", ""), ".fly", "");
    let $2;
    const $3 = readFile$11($b.String_asStr(joinPath$10(std, $b.str_slice(file, 4n, $b.str_len(file)))));
    m$4: {
      if (($3.$tag === "Some")) {
        const s = $3.$;
        $2 = s;
        break m$4;
      }
      if (($3.$tag === "None")) {
        $2 = $b.String_new();
        break m$4;
      }
      $rt.unmatched($3);
    }
    const source = $2;
    addModule$12(p, name, ("" + "<" + file + ">"), source, true, true);
  }
  const queue = { v: $b.Vec_new() };
  for (const $5 of $rt.items(entries)) {
    const e = $5;
    $b.Vec_push(queue, normalize$13($b.String_asStr(e)));
  }
  while (true) {
    const $6 = $b.Vec_pop(queue);
    m$7: {
      if (($6.$tag === "Some")) {
        const path = $6.$;
        {
          const name = $b.str_replaceAll(path, ".fly", "");
          if (some$14($b.slice_iter(p.v.modules), ((m) => {
  return eq$6(m.name, name);
          }))) {
            continue;
          }
          let $8;
          const $9 = readFile$11($b.String_asStr(path));
          m$10: {
            if (($9.$tag === "Some")) {
              const s = $9.$;
              $8 = s;
              break m$10;
            }
            if (($9.$tag === "None")) {
              {
                $b.Vec_push(new $rt.FieldRef(p.v, "diags"), [0xffffffffn, diag$15({ start: 0n, end: 0n }, $b.String_asStr(("" + path + ": cannot be read")))]);
                continue;
                $8 = undefined;
              }
              break m$10;
            }
            $rt.unmatched($9);
          }
          const source = $8;
          const idx = addModule$12(p, name, $b.String_clone(path), source, false, false);
          for (const $11 of $rt.items($rt.idx(p.v.modules, idx).ast.items)) {
            const item = $11;
            const $12 = item.kind;
            m$13: {
              if (($12.$tag === "Import")) {
                const from = $12.$.from;
                {
                  if (isRelative$16($b.String_asStr(from))) {
                    $b.Vec_push(queue, normalize$13($b.String_asStr(joinPath$10($b.String_asStr(parent$17($b.String_asStr(path))), $b.String_asStr(("" + from + ".fly"))))));
                  }
                }
                break m$13;
              }
              if (true) {
                {
                }
                break m$13;
              }
              $rt.unmatched($12);
            }
          }
        }
        break m$7;
      }
      if (true) {
        break;
        break m$7;
      }
      $rt.unmatched($6);
    }
  }
  declare$18(p);
  return p.v;
}
function checkFn$3(p, fid) {
  if ((has$19(p.v.checked, fid) || (!$rt.idx(p.v.fns, fid).hasBody))) {
    return;
  }
  insert$20(new $rt.FieldRef(p.v, "checked"), fid);
  if (isTemplate$21(p.v, fid)) {
    return;
  }
  const module = $rt.idx(p.v.fns, fid).module;
  const scheme = clone$22($rt.idx(p.v.fns, fid).scheme);
  let $1;
  const $2 = new $rt.FieldRef($rt.idx(p.v.fns, fid), "implId");
  const $3 = $2.v;
  m$4: {
    if (($3.$tag === "Some")) {
      const i = new $rt.FieldRef($3, "$");
      $1 = { $tag: "Some", $: clone$23($rt.idx(p.v.impls, i.v).target) };
      break m$4;
    }
    if (($3.$tag === "None")) {
      $1 = { $tag: "None" };
      break m$4;
    }
    $rt.unmatched($3);
  }
  const implTarget = $1;
  let $5;
  const $6 = fnDecl$24(p.v, fid);
  m$7: {
    if (($6.$tag === "Some")) {
      const d = $6.$;
      $5 = d;
      break m$7;
    }
    if (($6.$tag === "None")) {
      return;
      break m$7;
    }
    $rt.unmatched($6);
  }
  let fdecl = $5;
  if (fdecl.sig.isComptime) {
    return;
  }
  if ((!$b.HashMap_has(p.v.bodies, fid))) {
    const $8 = clone$25(fdecl.body);
    m$9: {
      if (($8.$tag === "Some")) {
        const b = $8.$;
        {
          if (blockHasComptime$26(b)) {
            const ex = { v: expander$27(p, module, { $tag: "None" }, $b.Vec_new()) };
            fdecl.body = body$28(ex, b);
            $b.HashMap_insert(new $rt.FieldRef(p.v, "bodies"), fid, clone$29(fdecl));
          }
        }
        break m$9;
      }
      if (true) {
        {
        }
        break m$9;
      }
      $rt.unmatched($8);
    }
  }
  let $10;
  const $11 = fdecl.body;
  m$12: {
    if (($11.$tag === "Some")) {
      const b = $11.$;
      $10 = clone$30(b);
      break m$12;
    }
    if (($11.$tag === "None")) {
      return;
      break m$12;
    }
    $rt.unmatched($11);
  }
  const body = $10;
  const $13 = new $rt.FieldRef(p.v, "note");
  let $14;
  const $15 = $b.HashMap_get(p.v.specNotes, fid);
  m$16: {
    if (($15.$tag === "Some")) {
      const n = $15.$;
      $14 = { $tag: "Some", $: $b.String_clone(n) };
      break m$16;
    }
    if (($15.$tag === "None")) {
      $14 = { $tag: "None" };
      break m$16;
    }
    $rt.unmatched($15);
  }
  const savedNote = $b.replace($13, $14);
  let base = moduleScope$31(module);
  base.selfTy = implTarget;
  let scope = withParams$32(base, scheme.tparams);
  const regions = { v: $b.Vec_new() };
  for (const $17 of $rt.items(scheme.tparams)) {
    const g = $17;
    if (eq$33(g.kind, { $tag: "Region" })) {
      $b.Vec_push(regions, clone$34(g.sym));
    }
  }
  let $18;
  if (($b.slice_len(regions.v) === 1n)) {
    $18 = { $tag: "Some", $: { $tag: "Param", $: clone$34($rt.idx(regions.v, 0n)) } };
  } else {
    {
      $18 = { $tag: "None" };
    }
  }
  scope.elidedRegion = $18;
  const bounds = { v: $b.HashMap_new() };
  for (const $19 of $rt.items(scheme.tparams)) {
    const g = $19;
    $b.HashMap_insert(bounds, g.sym.id, clone$35(g.bounds));
  }
  let $20;
  const $21 = $b.HashMap_get(p.v.specRequested, fid);
  m$22: {
    if (($21.$tag === "Some")) {
      const d = $21.$;
      $20 = { $tag: "Some", $: d };
      break m$22;
    }
    if (($21.$tag === "None")) {
      $20 = { $tag: "None" };
      break m$22;
    }
    $rt.unmatched($21);
  }
  const privileged = $20;
  const c = { v: { p: p, s: new$$36(), module: module, scopes: [$b.HashMap_new()], ret: clone$23(scheme.ret), allowed: pure$37(), scope: scope, pendingMatches: $b.Vec_new(), typed: emptyTyped$38(), pendingRegions: $b.Vec_new(), performed: $b.Vec_new(), pendingConts: $b.Vec_new(), copiesOut: $b.Vec_new(), copyBinds: $b.Vec_new(), pendingCopy: $b.Vec_new(), bounds: bounds.v, pendingTargs: $b.Vec_new(), pendingSpecs: $b.Vec_new(), pendingOps: $b.Vec_new(), privileged: privileged, inDefer: false, spans: $b.HashMap_new() } };
  const inferring = isNone$39(scheme.effects);
  let $23;
  const $24 = scheme.effects;
  m$25: {
    if (($24.$tag === "Some")) {
      const e = $24.$;
      $23 = clone$40(e);
      break m$25;
    }
    if (($24.$tag === "None")) {
      $23 = freshEffs$41(new $rt.FieldRef(c.v, "s"));
      break m$25;
    }
    $rt.unmatched($24);
  }
  c.v.allowed = $23;
  for (const $26 of $rt.items(scheme.params)) {
    const name = $26[0];
    const ty = $26[1];
    declare$42(c, $b.String_asStr(name), clone$23(ty));
  }
  const ret = clone$23(scheme.ret);
  const t = block$43(c, body, { $tag: "Some", $: clone$23(ret) });
  let $27;
  const $28 = body.tail;
  m$29: {
    if (($28.$tag === "Some")) {
      const e = $28.$;
      $27 = $rt.copy(e.span);
      break m$29;
    }
    if (($28.$tag === "None")) {
      $27 = $rt.copy(body.span);
      break m$29;
    }
    $rt.unmatched($28);
  }
  const at = $27;
  coerce$44(c, t, ret, $rt.copy(at));
  finish$45(c, fid, scheme, inferring);
  c.v.p.v.note = savedNote;
  return undefined;
}
function report$4(p) {
  for (const $1 of $rt.items(p.diags)) {
    const m = $1[0];
    const d = $1[1];
    if ((m < $b.slice_len(p.modules))) {
      $b.println($b.String_asStr(render$46(d, $b.String_asStr($rt.idx(p.modules, m).file), $b.String_asStr($rt.idx(p.modules, m).source))));
    } else {
      {
        const $2 = d;
        if (!(($2.$tag === "Diagnostic"))) $rt.unmatched($2);
        const message = $2.$.message;
        $b.println(("" + "error: " + message));
      }
    }
  }
  return undefined;
}
function entryFile$5(self, entry) {
  return normalize$13(entry);
}
function eq$6(self, other) {
  return ($b.String_asStr(self) === $b.String_asStr(other));
}
function findIndex$7(self, test) {
  let i = 0n;
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: i };
    }
    i = $rt.usize(i + 1n);
  }
  return { $tag: "None" };
}
function program$8(p, entry, runtime) {
  let $1;
  const $2 = lookup$47(p, entry, "main");
  m$3: {
    if (($2.$tag === "Some" && ($2.$.$tag === "Fn"))) {
      const f = $2.$.$;
      $1 = f;
      break m$3;
    }
    if (true) {
      throw new $rt.Fail({ $tag: "Failed", $: $b.str_toString("error: the program has no `main` function") });
      break m$3;
    }
    $rt.unmatched($2);
  }
  const mainFid = $1;
  const js = { v: new$$48(p) };
  js.v.tasks = startsTasks$49(js.v);
  const main = instance$50(js, mainFid, $b.Vec_new());
  while ((js.v.next < $b.slice_len(js.v.insts))) {
    const i = js.v.next;
    js.v.next = $rt.usize(js.v.next + 1n);
    let $4;
    try {
      emit$51(js, i);
      $4 = { $tag: "Ok" };
    } catch ($5) {
      if (!($5 instanceof $rt.Fail)) throw $5;
      const d = $5.value;
      $4 = { $tag: "Err", $: d };
    }
    const r = $4;
    const $6 = r;
    m$7: {
      if (($6.$tag === "Err")) {
        const d = $6.$;
        {
          const m = js.v.module;
          throw new $rt.Fail({ $tag: "Failed", $: render$46(d, $b.String_asStr($rt.idx(js.v.p.modules, m).file), $b.String_asStr($rt.idx(js.v.p.modules, m).source)) });
        }
        break m$7;
      }
      if (true) {
        {
        }
        break m$7;
      }
      $rt.unmatched($6);
    }
  }
  const args = startArgs$52(js.v, mainFid);
  const out = { v: $b.str_toString(runtime) };
  $b.String_push(out, "\n");
  $b.String_push(out, $b.String_asStr(js.v.head));
  $b.String_push(out, $b.String_asStr(js.v.code));
  let $8;
  if ($rt.idx(js.v.insts, main).suspends) {
    $8 = "true";
  } else {
    {
      $8 = "false";
    }
  }
  const suspends = $8;
  let $9;
  if (js.v.tasks) {
    $9 = "true";
  } else {
    {
      $9 = "false";
    }
  }
  const tasks = $9;
  $b.String_push(out, ("" + "$rt.start(() => " + $rt.idx(js.v.insts, main).js + "(" + join$53(args, ", ") + "), " + suspends + ", " + tasks + ");\n"));
  return out.v;
}
function new$$9() {
  return { map: $b.HashMap_new() };
}
function joinPath$10(dir, rel) {
  if (($b.str_len(dir) === 0n)) {
    return $b.str_toString(rel);
  } else {
    {
      return ("" + dir + "/" + rel);
    }
  }
}
function readFile$11(path) {
  try {
    const f = { v: $b.File_open(path) };
    return { $tag: "Some", $: $b.File_readText(f) };
  } catch ($1) {
    if (!($1 instanceof $rt.Fail)) throw $1;
    return { $tag: "None" };
  }
}
function addModule$12(self, name, file, source, isStd, declarations) {
  const idx = $b.slice_len(self.v.modules);
  let $1;
  try {
    if (declarations) {
      $1 = parseDeclarations$54($b.String_asStr(source));
    } else {
      {
        $1 = parseModule$55($b.String_asStr(source));
      }
    }
  } catch ($2) {
    if (!($2 instanceof $rt.Fail)) throw $2;
    const d = $2.value;
    $b.Vec_push(new $rt.FieldRef(self.v, "diags"), [idx, d]);
    $1 = { items: $b.Vec_new() };
  }
  const parsed = $1;
  $b.Vec_push(new $rt.FieldRef(self.v, "modules"), { name: name, file: file, source: source, ast: parsed, isStd: isStd, scope: $b.HashMap_new(), exports: $b.HashMap_new() });
  return idx;
}
function normalize$13(p) {
  const out = { v: $b.Vec_new() };
  const absolute = $b.str_startsWith(p, "/");
  for (const $1 of $rt.items($b.str_split(p, "/"))) {
    const c = $1;
    if (((c === "") || (c === "."))) {
      continue;
    }
    if ((c === "..")) {
      let $2;
      const $3 = last$56(out.v);
      m$4: {
        if (($3.$tag === "Some")) {
          const q = $3.$;
          $2 = (q !== "..");
          break m$4;
        }
        if (($3.$tag === "None")) {
          $2 = false;
          break m$4;
        }
        $rt.unmatched($3);
      }
      const up = $2;
      if (up) {
        $b.Vec_pop(out);
      } else {
        {
          $b.Vec_push(out, $b.str_toString(".."));
        }
      }
      continue;
    }
    $b.Vec_push(out, $b.String_clone(c));
  }
  const joined = join$53(out.v, "/");
  if (absolute) {
    return ("" + "/" + joined);
  } else {
    {
      return joined;
    }
  }
}
function some$14(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function diag$15(span, message) {
  return { $tag: "Diagnostic", $: { span: span, message: $b.str_toString(message) } };
}
function isRelative$16(path) {
  return ($b.str_startsWith(path, "./") || $b.str_startsWith(path, "../"));
}
function parent$17(p) {
  const bytes = $b.str_asBytes(p);
  let i = $b.slice_len(bytes);
  while ((i > 0n)) {
    if (($rt.idx(bytes, $rt.usize(i - 1n)) === 47n)) {
      return $b.str_toString($b.str_slice(p, 0n, $rt.usize(i - 1n)));
    }
    i = $rt.usize(i - 1n);
  }
  return $b.String_new();
}
function declare$18(self) {
  const $1 = $b.slice_len(self.v.modules);
  for (let m = 0n; m < $1; m++) {
    const items = clone$57($rt.idx(self.v.modules, m).ast.items);
    const $2 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(items)));
    let $4;
    for (let $3 = $2.next(); !$3.done; $3 = $2.next($4)) {
      $4 = undefined;
      const $5 = $3.value.item;
      const i = $5[0];
      const item = $5[1];
      let $6;
      const $7 = item.kind;
      m$8: {
        if (($7.$tag === "Struct")) {
          const s = $7.$;
          $6 = { $tag: "Some", $: [$b.String_clone(s.name.name), { $tag: "Def", $: placeholder$58(self, s.name, m) }] };
          break m$8;
        }
        if (($7.$tag === "Enum")) {
          const e = $7.$;
          $6 = { $tag: "Some", $: [$b.String_clone(e.name.name), { $tag: "Def", $: placeholder$58(self, e.name, m) }] };
          break m$8;
        }
        if (($7.$tag === "TypeAlias")) {
          const a = $7.$;
          $6 = { $tag: "Some", $: [$b.String_clone(a.name.name), { $tag: "Def", $: placeholder$58(self, a.name, m) }] };
          break m$8;
        }
        if (($7.$tag === "Interface")) {
          const x = $7.$;
          {
            const id = placeholder$58(self, x.name, m);
            const selfSym = freshSym$59(self, "Self");
            $rt.idx(self.v.defs, id).kind = { $tag: "Interface", $: { methods: $b.Vec_new(), assoc: $b.Vec_new(), selfSym: selfSym, supers: $b.Vec_new() } };
            $6 = { $tag: "Some", $: [$b.String_clone(x.name.name), { $tag: "Def", $: id }] };
          }
          break m$8;
        }
        if (($7.$tag === "Effect")) {
          const e = $7.$;
          {
            const id = placeholder$58(self, e.name, m);
            $rt.idx(self.v.defs, id).kind = { $tag: "Effect", $: { ops: $b.Vec_new() } };
            $6 = { $tag: "Some", $: [$b.String_clone(e.name.name), { $tag: "Def", $: id }] };
          }
          break m$8;
        }
        if (($7.$tag === "Const")) {
          const name = $7.$.name;
          const value = $7.$.value;
          {
            $b.Vec_push(new $rt.FieldRef(self.v, "consts"), { name: $b.String_clone(name.name), module: m, ty: { $tag: "Error" }, value: clone$60(value) });
            $6 = { $tag: "Some", $: [$b.String_clone(name.name), { $tag: "Const", $: $rt.usize($b.slice_len(self.v.consts) - 1n) }] };
          }
          break m$8;
        }
        if (($7.$tag === "Function")) {
          const f = $7.$;
          {
            const id = $b.slice_len(self.v.fns);
            $b.Vec_push(new $rt.FieldRef(self.v, "fns"), { name: $b.String_clone(f.sig.name.name), module: m, scheme: emptyScheme$61(), decl: { module: m, item: i, method: { $tag: "None" } }, exported: item.exported, implId: { $tag: "None" }, hasBody: $b.Option_isSome(f.body), iface: { $tag: "None" } });
            $6 = { $tag: "Some", $: [$b.String_clone(f.sig.name.name), { $tag: "Fn", $: id }] };
          }
          break m$8;
        }
        if (true) {
          $6 = { $tag: "None" };
          break m$8;
        }
        $rt.unmatched($7);
      }
      const named = $6;
      const $9 = named;
      m$10: {
        if (($9.$tag === "Some")) {
          const name = $9.$[0];
          const binding = $9.$[1];
          {
            if ($b.HashMap_has($rt.idx(self.v.modules, m).scope, $b.String_asStr(name))) {
              error$62(self, m, $rt.copy(item.span), $b.String_asStr(("" + "`" + name + "` is declared twice")));
            }
            $b.HashMap_insert(new $rt.FieldRef($rt.idx(self.v.modules, m), "scope"), $b.String_clone(name), clone$63(binding));
            if ((item.exported || $rt.idx(self.v.modules, m).isStd)) {
              $b.HashMap_insert(new $rt.FieldRef($rt.idx(self.v.modules, m), "exports"), name, binding);
            }
          }
          break m$10;
        }
        if (true) {
          {
          }
          break m$10;
        }
        $rt.unmatched($9);
      }
    }
  }
  let $11;
  const $12 = moduleNamed$64(self.v, "std/prelude");
  m$13: {
    if (($12.$tag === "Some")) {
      const i = $12.$;
      $11 = i;
      break m$13;
    }
    if (($12.$tag === "None")) {
      $11 = 0n;
      break m$13;
    }
    $rt.unmatched($12);
  }
  const prelude = $11;
  let $14;
  const $15 = moduleNamed$64(self.v, "std/layout");
  m$16: {
    if (($15.$tag === "Some")) {
      const i = $15.$;
      $14 = i;
      break m$16;
    }
    if (($15.$tag === "None")) {
      $14 = 0n;
      break m$16;
    }
    $rt.unmatched($15);
  }
  const layout = $14;
  for (const $17 of $rt.items(["Fail", "Yield", "Region", "Io", "String", "Ref", "Vec", "Iterable", "LentBy", "Copy", "Send", "Eq", "Show", "Ord", "Cont", "Box", "Arc"])) {
    const name = $17;
    let $18;
    const $19 = $b.HashMap_get($rt.idx(self.v.modules, prelude).exports, name);
    m$20: {
      if (($19.$tag === "Some")) {
        const b = $19.$;
        $18 = { $tag: "Some", $: clone$63(b) };
        break m$20;
      }
      if (($19.$tag === "None")) {
        const $21 = $b.HashMap_get($rt.idx(self.v.modules, layout).exports, name);
        m$22: {
          if (($21.$tag === "Some")) {
            const b = $21.$;
            $18 = { $tag: "Some", $: clone$63(b) };
            break m$22;
          }
          if (($21.$tag === "None")) {
            $18 = { $tag: "None" };
            break m$22;
          }
          $rt.unmatched($21);
        }
        break m$20;
      }
      $rt.unmatched($19);
    }
    const found = $18;
    const $23 = found;
    m$24: {
      if (($23.$tag === "Some" && ($23.$.$tag === "Def"))) {
        const d = $23.$.$;
        {
          $b.HashMap_insert(new $rt.FieldRef(self.v, "known"), $b.str_toString(name), d);
        }
        break m$24;
      }
      if (true) {
        {
        }
        break m$24;
      }
      $rt.unmatched($23);
    }
  }
  const preludeExports = { v: $b.Vec_new() };
  const $25 = $b.Gen_each($b.HashMap_entries($rt.idx(self.v.modules, prelude).exports));
  let $27;
  for (let $26 = $25.next(); !$26.done; $26 = $25.next($27)) {
    $27 = undefined;
    const $28 = $26.value.item;
    const k = $28[0];
    const v = $28[1];
    $b.Vec_push(preludeExports, [$b.String_clone(k), clone$63(v)]);
  }
  const $29 = $b.slice_len(self.v.modules);
  for (let m = 0n; m < $29; m++) {
    if ((m !== prelude)) {
      for (const $30 of $rt.items(preludeExports.v)) {
        const k = $30[0];
        const v = $30[1];
        if ((!$b.HashMap_has($rt.idx(self.v.modules, m).scope, $b.String_asStr(k)))) {
          $b.HashMap_insert(new $rt.FieldRef($rt.idx(self.v.modules, m), "scope"), $b.String_clone(k), clone$63(v));
        }
      }
    }
    const items = clone$57($rt.idx(self.v.modules, m).ast.items);
    for (const $31 of $rt.items(items)) {
      const item = $31;
      const $32 = item.kind;
      m$33: {
        if (($32.$tag === "Import")) {
          const names = $32.$.names;
          const from = $32.$.from;
          {
            let $34;
            if (isRelative$16($b.String_asStr(from))) {
              $34 = moduleNamed$64(self.v, $b.String_asStr(normalize$13($b.String_asStr(joinPath$10($b.String_asStr(parent$17($b.String_asStr($rt.idx(self.v.modules, m).name))), $b.String_asStr(from))))));
            } else {
              {
                $34 = moduleNamed$64(self.v, $b.String_asStr(from));
              }
            }
            const target = $34;
            let $35;
            const $36 = target;
            m$37: {
              if (($36.$tag === "Some")) {
                const t = $36.$;
                $35 = t;
                break m$37;
              }
              if (($36.$tag === "None")) {
                {
                  error$62(self, m, $rt.copy(item.span), $b.String_asStr(("" + "no module `" + from + "`")));
                  continue;
                  $35 = undefined;
                }
                break m$37;
              }
              $rt.unmatched($36);
            }
            const t = $35;
            for (const $38 of $rt.items(names)) {
              const n = $38[0];
              const local = $38[1];
              const $39 = $b.HashMap_get($rt.idx(self.v.modules, t).exports, $b.String_asStr(n.name));
              m$40: {
                if (($39.$tag === "Some")) {
                  const b = $39.$;
                  {
                    $b.HashMap_insert(new $rt.FieldRef($rt.idx(self.v.modules, m), "scope"), $b.String_clone(local.name), clone$63(b));
                  }
                  break m$40;
                }
                if (($39.$tag === "None")) {
                  {
                    const name = $b.String_clone(n.name);
                    const inPrelude = $b.HashMap_has($rt.idx(self.v.modules, prelude).exports, $b.String_asStr(name));
                    const home = find$65($b.slice_iter(self.v.modules), ((x) => {
  return ((x.isStd && (x.name !== "std/prelude")) && $b.HashMap_has(x.exports, $b.String_asStr(name)));
                    }));
                    let $41;
                    if (inPrelude) {
                      $41 = ("" + ": `" + name + "` is in the prelude, so it needs no import");
                    } else {
                      {
                        const $42 = home;
                        m$43: {
                          if (($42.$tag === "Some")) {
                            const h = $42.$;
                            $41 = ("" + ": it is in `" + h.name + "`");
                            break m$43;
                          }
                          if (($42.$tag === "None")) {
                            $41 = $b.String_new();
                            break m$43;
                          }
                          $rt.unmatched($42);
                        }
                      }
                    }
                    const hint = $41;
                    error$62(self, m, $rt.copy(n.span), $b.String_asStr(("" + "module `" + from + "` does not export `" + name + "`" + hint)));
                  }
                  break m$40;
                }
                $rt.unmatched($39);
              }
            }
          }
          break m$33;
        }
        if (true) {
          {
          }
          break m$33;
        }
        $rt.unmatched($32);
      }
    }
  }
  const $44 = $b.slice_len(self.v.modules);
  for (let m = 0n; m < $44; m++) {
    const items = clone$57($rt.idx(self.v.modules, m).ast.items);
    for (const $45 of $rt.items(items)) {
      const item = $45;
      elaborateParams$66(self, m, item);
    }
  }
  const $46 = $b.slice_len(self.v.modules);
  for (let m = 0n; m < $46; m++) {
    const $47 = $b.Gen_each($b.Gen_enumerate($b.slice_iter($rt.idx(self.v.modules, m).ast.items)));
    let $49;
    for (let $48 = $47.next(); !$48.done; $48 = $47.next($49)) {
      $49 = undefined;
      const $50 = $48.value.item;
      const i = $50[0];
      const item = $50[1];
      const $51 = item.kind;
      m$52: {
        if (($51.$tag === "TypeAlias")) {
          const a = $51.$;
          {
            const $53 = lookup$47(self.v, m, $b.String_asStr(a.name.name));
            m$54: {
              if (($53.$tag === "Some" && ($53.$.$tag === "Def"))) {
                const id = $53.$.$;
                {
                  $b.HashMap_insert(new $rt.FieldRef(self.v, "pendingAliases"), id, [m, i]);
                }
                break m$54;
              }
              if (true) {
                {
                }
                break m$54;
              }
              $rt.unmatched($53);
            }
          }
          break m$52;
        }
        if (true) {
          {
          }
          break m$52;
        }
        $rt.unmatched($51);
      }
    }
  }
  for (const $55 of $rt.items([true, false])) {
    const aliases = $55;
    const $56 = $b.slice_len(self.v.modules);
    for (let m = 0n; m < $56; m++) {
      const items = clone$57($rt.idx(self.v.modules, m).ast.items);
      for (const $57 of $rt.items(items)) {
        const item = $57;
        let $58;
        const $59 = item.kind;
        m$60: {
          if (($59.$tag === "TypeAlias")) {
            $58 = true;
            break m$60;
          }
          if (true) {
            $58 = false;
            break m$60;
          }
          $rt.unmatched($59);
        }
        const isAlias = $58;
        if ((isAlias === aliases)) {
          elaborateDef$67(self, m, item);
        }
      }
    }
  }
  checkViews$68(self);
  elaborateConsts$69(self);
  const $61 = $b.slice_len(self.v.modules);
  for (let m = 0n; m < $61; m++) {
    const items = clone$57($rt.idx(self.v.modules, m).ast.items);
    const $62 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(items)));
    let $64;
    for (let $63 = $62.next(); !$63.done; $63 = $62.next($64)) {
      $64 = undefined;
      const $65 = $63.value.item;
      const i = $65[0];
      const item = $65[1];
      const $66 = item.kind;
      m$67: {
        if (($66.$tag === "Impl")) {
          const imp = $66.$;
          elaborateImpl$70(self, m, i, imp);
          break m$67;
        }
        if (($66.$tag === "Function")) {
          const f = $66.$;
          {
            const scope = moduleScope$31(m);
            const scheme = elaborateSig$71(self, f.sig, scope, { $tag: "None" });
            const $68 = lookup$47(self.v, m, $b.String_asStr(f.sig.name.name));
            m$69: {
              if (($68.$tag === "Some" && ($68.$.$tag === "Fn"))) {
                const id = $68.$.$;
                {
                  const template = some$72($b.slice_iter(scheme.tparams), ((g) => {
  return g.isComptime;
                  }));
                  let s = scheme;
                  if (((item.exported || template) && isNone$39(s.effects))) {
                    s.effects = { $tag: "Some", $: pure$37() };
                  }
                  $rt.idx(self.v.fns, id).scheme = s;
                }
                break m$69;
              }
              if (true) {
                {
                }
                break m$69;
              }
              $rt.unmatched($68);
            }
          }
          break m$67;
        }
        if (true) {
          {
          }
          break m$67;
        }
        $rt.unmatched($66);
      }
    }
  }
  return undefined;
}
function has$19(self, v) {
  return $b.HashMap_has(self.map, v);
}
function insert$20(self, v) {
  if ($b.HashMap_has(self.v.map, v)) {
    return false;
  }
  $b.HashMap_insert(new $rt.FieldRef(self.v, "map"), v, true);
  return true;
}
function isTemplate$21(self, fid) {
  return ((!$b.HashMap_has(self.specOf, fid)) && some$72($b.slice_iter($rt.idx(self.fns, fid).scheme.tparams), ((g) => {
  return g.isComptime;
  })));
}
function clone$22(self) {
  {
    return { tparams: clone$73(self.tparams), params: clone$74(self.params), ret: clone$23(self.ret), effects: clone$75(self.effects), retFrom: clone$76(self.retFrom) };
  }
}
function clone$23(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Var")) {
      const x = $1.$;
      return { $tag: "Var", $: clone$77(x) };
      break m$2;
    }
    if (($1.$tag === "Param")) {
      const x = $1.$;
      return { $tag: "Param", $: clone$34(x) };
      break m$2;
    }
    if (($1.$tag === "Prim")) {
      const x = $1.$;
      return { $tag: "Prim", $: clone$78(x) };
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const x = $1.$;
      return { $tag: "Named", $: clone$79(x) };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const x = $1.$;
      return { $tag: "Record", $: clone$80(x) };
      break m$2;
    }
    if (($1.$tag === "Union")) {
      const x = $1.$;
      return { $tag: "Union", $: clone$80(x) };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const x = $1.$;
      return { $tag: "Tuple", $: clone$35(x) };
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const x = $1.$;
      return { $tag: "Array", $: clone$81(x) };
      break m$2;
    }
    if (($1.$tag === "Slice")) {
      const x = $1.$;
      return { $tag: "Slice", $: clone$82(x) };
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const x = $1.$;
      return { $tag: "Borrow", $: clone$83(x) };
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const x = $1.$;
      return { $tag: "Fn", $: clone$84(x) };
      break m$2;
    }
    if (($1.$tag === "Assoc")) {
      const x = $1.$;
      return { $tag: "Assoc", $: clone$85(x) };
      break m$2;
    }
    if (($1.$tag === "Error")) {
      return { $tag: "Error" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function fnDecl$24(self, fid) {
  const $1 = $b.HashMap_get(self.bodies, fid);
  m$2: {
    if (($1.$tag === "Some")) {
      const d = $1.$;
      {
        return { $tag: "Some", $: clone$29(d) };
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const decl = $rt.copy($rt.idx(self.fns, fid).decl);
  if ((decl.module >= $b.slice_len(self.modules))) {
    return { $tag: "None" };
  }
  if ((decl.item >= $b.slice_len($rt.idx(self.modules, decl.module).ast.items))) {
    return { $tag: "None" };
  }
  const $3 = $rt.idx($rt.idx(self.modules, decl.module).ast.items, decl.item).kind;
  m$4: {
    if (($3.$tag === "Function")) {
      const f = $3.$;
      if (isNone$86(decl.method)) {
        return { $tag: "Some", $: clone$29(f) };
      } else {
        {
          return { $tag: "None" };
        }
      }
      break m$4;
    }
    if (($3.$tag === "Impl")) {
      const imp = $3.$;
      const $5 = decl.method;
      m$6: {
        if (($5.$tag === "Some")) {
          const k = $5.$;
          return { $tag: "Some", $: clone$29($rt.idx(imp.methods, k).decl) };
          break m$6;
        }
        if (($5.$tag === "None")) {
          return { $tag: "None" };
          break m$6;
        }
        $rt.unmatched($5);
      }
      break m$4;
    }
    if (true) {
      return { $tag: "None" };
      break m$4;
    }
    $rt.unmatched($3);
  }
}
function clone$25(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$30(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function blockHasComptime$26(b) {
  let $7 = some$89($b.slice_iter(b.stmts), ((s) => {
  const $1 = s;
  m$2: {
    if (($1.$tag === "Let")) {
      const ty = $1.$.ty;
      const init = $1.$.init;
      let $3 = exprHas$87(init);
      if (!$3) {
        let $4;
        const $5 = ty;
        m$6: {
          if (($5.$tag === "Some")) {
            const t = $5.$;
            $4 = tyHas$88(t);
            break m$6;
          }
          if (($5.$tag === "None")) {
            $4 = false;
            break m$6;
          }
          $rt.unmatched($5);
        }
        $3 = $4;
      }
      return $3;
      break m$2;
    }
    if ((($1.$tag === "Defer") || ($1.$tag === "Expr"))) {
      let e;
      if (($1.$tag === "Defer")) { e = $1.$; }
      else if (($1.$tag === "Expr")) { e = $1.$; }
      return exprHas$87(e);
      break m$2;
    }
    $rt.unmatched($1);
  }
  }));
  if (!$7) {
    let $8;
    const $9 = b.tail;
    m$10: {
      if (($9.$tag === "Some")) {
        const t = $9.$;
        $8 = exprHas$87(t);
        break m$10;
      }
      if (($9.$tag === "None")) {
        $8 = false;
        break m$10;
      }
      $rt.unmatched($9);
    }
    $7 = $8;
  }
  return $7;
}
function expander$27(p, module, requested, env) {
  const e = { v: $b.Vec_new() };
  for (const $1 of $rt.items(env)) {
    const k = $1[0];
    const v = $1[1];
    $b.Vec_push(e, [$b.String_clone(k), { $tag: "Some", $: clone$90(v) }]);
  }
  return { p: p, module: module, requested: requested, env: e.v, steps: 0n };
}
function body$28(self, b) {
  try {
    return { $tag: "Some", $: block$91(self, b) };
  } catch ($1) {
    if (!($1 instanceof $rt.Fail)) throw $1;
    const s = $1.value;
    report$92(self, s);
    return { $tag: "None" };
  }
}
function clone$29(self) {
  {
    return { body: clone$25(self.body), sig: clone$93(self.sig) };
  }
}
function clone$30(self) {
  {
    return { span: clone$94(self.span), stmts: clone$95(self.stmts), tail: clone$96(self.tail) };
  }
}
function moduleScope$31(module) {
  return { module: module, params: $b.HashMap_new(), selfTy: { $tag: "None" }, elidedRegion: { $tag: "None" } };
}
function withParams$32(self, params) {
  let s = clone$97(self);
  for (const $1 of $rt.items(params)) {
    const p = $1;
    $b.HashMap_insert(new $rt.FieldRef(s, "params"), $b.String_clone(p.sym.name), [clone$34(p.sym), p.kind]);
  }
  const regions = { v: $b.Vec_new() };
  for (const $2 of $rt.items(params)) {
    const p = $2;
    if (eq$33(p.kind, { $tag: "Region" })) {
      $b.Vec_push(regions, clone$34(p.sym));
    }
  }
  if (($b.slice_len(regions.v) === 1n)) {
    s.elidedRegion = { $tag: "Some", $: { $tag: "Param", $: clone$34($rt.idx(regions.v, 0n)) } };
  }
  return s;
}
function eq$33(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Type") && ($1[1].$tag === "Type"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Region") && ($1[1].$tag === "Region"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Row") && ($1[1].$tag === "Row"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Len") && ($1[1].$tag === "Len"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$34(self) {
  {
    return { id: clone$77(self.id), name: $b.String_clone(self.name) };
  }
}
function clone$35(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$23(x));
  }
  return v.v;
}
function new$$36() {
  return { tys: $b.Vec_new(), rows: $b.Vec_new(), effs: $b.Vec_new(), regions: $b.Vec_new(), lens: $b.Vec_new() };
}
function pure$37() {
  return { effs: $b.Vec_new(), tail: { $tag: "Closed" } };
}
function emptyTyped$38() {
  return { exprs: $b.HashMap_new(), bindings: $b.HashMap_new(), params: $b.Vec_new(), ops: $b.HashMap_new(), shows: $b.HashMap_new(), calls: $b.HashMap_new(), targs: $b.HashMap_new(), slots: $b.HashMap_new(), whole: new$$9(), performs: $b.HashMap_new(), handled: $b.HashMap_new(), lentScrutinees: $b.HashMap_new(), eaches: $b.HashMap_new() };
}
function isNone$39(self) {
  return (!$b.Option_isSome(self));
}
function clone$40(self) {
  {
    return { effs: clone$98(self.effs), tail: clone$99(self.tail) };
  }
}
function freshEffs$41(self) {
  return { effs: $b.Vec_new(), tail: freshEffTail$100(self) };
}
function declare$42(self, name, ty) {
  const top = $rt.usize($b.slice_len(self.v.scopes) - 1n);
  $b.HashMap_insert($rt.indexRef(self.v.scopes, top), $b.str_toString(name), ty);
  return undefined;
}
function block$43(self, b, expected) {
  $b.Vec_push(new $rt.FieldRef(self.v, "scopes"), $b.HashMap_new());
  let diverges = false;
  for (const $1 of $rt.items(b.stmts)) {
    const stmt = $1;
    const $2 = stmt;
    m$3: {
      if (($2.$tag === "Let")) {
        const pat = $2.$.pat;
        const ty = $2.$.ty;
        const init = $2.$.init;
        {
          let $4;
          const $5 = ty;
          m$6: {
            if (($5.$tag === "Some")) {
              const t = $5.$;
              {
                const scope = clone$97(self.v.scope);
                $4 = { $tag: "Some", $: elabTy$101(self.v.p, t, scope) };
              }
              break m$6;
            }
            if (($5.$tag === "None")) {
              $4 = { $tag: "None" };
              break m$6;
            }
            $rt.unmatched($5);
          }
          const ann = $4;
          let $7;
          const $8 = ann;
          m$9: {
            if (($8.$tag === "Some")) {
              const a = $8.$;
              {
                const found = expr$102(self, init, { $tag: "Some", $: clone$23(a) });
                coerce$44(self, found, a, $rt.copy(init.span));
                $7 = a;
              }
              break m$9;
            }
            if (($8.$tag === "None")) {
              $7 = expr$102(self, init, { $tag: "None" });
              break m$9;
            }
            $rt.unmatched($8);
          }
          const t = $7;
          bind$103(self, pat, t);
        }
        break m$3;
      }
      if (($2.$tag === "Defer")) {
        const e = $2.$;
        {
          const fail = known$104(self.v, "Fail");
          const yld = known$104(self.v, "Yield");
          let row = expandEffs$105(self.v.s, clone$40(self.v.allowed));
          const kept = { v: $b.Vec_new() };
          for (const $10 of $rt.items(row.effs)) {
            const x = $10;
            if (((x.def !== fail) && (x.def !== yld))) {
              $b.Vec_push(kept, clone$106(x));
            }
          }
          row.effs = kept.v;
          const $11 = row.tail;
          m$12: {
            if (($11.$tag === "Var")) {
              {
                row.tail = { $tag: "Closed" };
              }
              break m$12;
            }
            if (true) {
              {
              }
              break m$12;
            }
            $rt.unmatched($11);
          }
          const saved = $b.replace(new $rt.FieldRef(self.v, "allowed"), row);
          const was = $b.replace(new $rt.FieldRef(self.v, "inDefer"), true);
          expr$102(self, e, { $tag: "None" });
          self.v.inDefer = was;
          self.v.allowed = saved;
          const $13 = leaves$107(e, 0n);
          m$14: {
            if (($13.$tag === "Some")) {
              const span = $13.$;
              {
                err$108(self, $rt.copy(span), "a `defer` cannot leave its block: it runs while the block is being left");
              }
              break m$14;
            }
            if (true) {
              {
              }
              break m$14;
            }
            $rt.unmatched($13);
          }
        }
        break m$3;
      }
      if (($2.$tag === "Expr")) {
        const e = $2.$;
        {
          const t = expr$102(self, e, { $tag: "None" });
          if (isNever$110(resolve$109(self.v.s, t))) {
            diverges = true;
          }
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  let $15;
  const $16 = b.tail;
  m$17: {
    if (($16.$tag === "Some")) {
      const e = $16.$;
      $15 = expr$102(self, e, expected);
      break m$17;
    }
    if (($16.$tag === "None")) {
      if (diverges) {
        $15 = neverTy$111();
      } else {
        {
          $15 = voidTy$112();
        }
      }
      break m$17;
    }
    $rt.unmatched($16);
  }
  const t = $15;
  $b.Vec_pop(new $rt.FieldRef(self.v, "scopes"));
  return t;
}
function coerce$44(self, found, expected, span) {
  const fnf = normalize$113(self.v, resolve$109(self.v.s, found));
  const fnx = normalize$113(self.v, resolve$109(self.v.s, expected));
  const $1 = [fnf, fnx];
  m$2: {
    if ((($1[0].$tag === "Fn") && ($1[1].$tag === "Fn"))) {
      const f = $1[0].$;
      const x = $1[1].$;
      {
        const snap = clone$114(self.v.s);
        let shapes = ($b.slice_len(f.params) === $b.slice_len(x.params));
        if (shapes) {
          const $3 = $b.slice_len(f.params);
          for (let i = 0n; i < $3; i++) {
            if ((!unifies$115(self, $rt.idx(f.params, i), $rt.idx(x.params, i)))) {
              shapes = false;
              break;
            }
          }
        }
        shapes = (shapes && lends$116(self, f.ret, x.ret));
        if (shapes) {
          let $4;
          try {
            effSub$117(new $rt.FieldRef(self.v, "s"), f.effects, x.effects);
            $4 = { $tag: "None" };
          } catch ($5) {
            if (!($5 instanceof $rt.Fail)) throw $5;
            if (!(($5.value.$tag === "Misfit"))) throw $5;
            const e = $5.value.$;
            $4 = { $tag: "Some", $: e };
          }
          const misfit = $4;
          const $6 = misfit;
          m$7: {
            if (($6.$tag === "Some")) {
              const e = $6.$;
              {
                const what = showEff$118(self.v, e);
                const allowedRow = zonkEffs$119(self.v.s, x.effects);
                let $8;
                if ((($b.slice_len(allowedRow.effs) === 0n) && eq$120(allowedRow.tail, { $tag: "Closed" }))) {
                  $8 = $b.str_toString("no effects");
                } else {
                  {
                    $8 = ("" + "only `" + showEffs$121(self.v, allowedRow) + "`");
                  }
                }
                const allowed = $8;
                restore$122(new $rt.FieldRef(self.v, "s"), snap);
                err$108(self, $rt.copy(span), $b.String_asStr(("" + "this function performs " + what + ", but " + allowed + " may be performed here")));
                return;
              }
              break m$7;
            }
            if (true) {
              {
              }
              break m$7;
            }
            $rt.unmatched($6);
          }
        }
        restore$122(new $rt.FieldRef(self.v, "s"), snap);
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const before = $b.slice_len(self.v.pendingCopy);
  if ((!lends$116(self, found, expected))) {
    const fs = show$123(self.v, found);
    const xs = show$123(self.v, expected);
    let hint = $b.String_new();
    let recordHint = false;
    const $9 = [strip$124(self.v, found), strip$124(self.v, expected)];
    m$10: {
      if ((($9[0].$tag === "Record") && ($9[1].$tag === "Named"))) {
        const r = $9[0].$;
        const d = $9[1].$[0];
        {
          const $11 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, d), "kind");
          const $12 = $11.v;
          m$13: {
            if (($12.$tag === "Struct" && ($12.$.fields.$tag === "Some"))) {
              const fields = new $rt.FieldRef($12.$.fields, "$");
              {
                const e = expandRow$125(self.v.s, r);
                if ((($b.slice_len(fields.v) === $b.slice_len(e.labels)) && every$127($b.slice_iter(fields.v), (($0$$14) => {
  {
    const $15 = $0$$14;
    const k = $15[0];
    return labelHas$126(e.labels, $b.String_asStr(k));
  }
                })))) {
                  const n = $b.String_clone($rt.idx(self.v.p.v.defs, d).name);
                  hint = ("" + ": a record is not a `" + n + "`; build it as one with `" + n + " { \xe2\x80\xa6 }`, or give its binding the type `" + n + "`");
                  recordHint = true;
                }
              }
              break m$13;
            }
            if (true) {
              {
              }
              break m$13;
            }
            $rt.unmatched($12);
          }
        }
        break m$10;
      }
      if (true) {
        {
        }
        break m$10;
      }
      $rt.unmatched($9);
    }
    if ((!recordHint)) {
      let $16;
      const $17 = enumHint$128(self.v, found, expected);
      m$18: {
        if (($17.$tag === "Some")) {
          const h = $17.$;
          $16 = h;
          break m$18;
        }
        if (($17.$tag === "None")) {
          $16 = $b.String_new();
          break m$18;
        }
        $rt.unmatched($17);
      }
      hint = $16;
    }
    err$108(self, $rt.copy(span), $b.String_asStr(("" + "expected `" + xs + "`, found `" + fs + "`" + hint)));
  }
  const $19 = $b.slice_len(self.v.pendingCopy);
  for (let i = before; i < $19; i++) {
    $b.Vec_push(new $rt.FieldRef(self.v, "copiesOut"), [clone$23($rt.idx(self.v.pendingCopy, i)), $rt.copy(span)]);
  }
  $b.Vec_truncate(new $rt.FieldRef(self.v, "pendingCopy"), before);
  return undefined;
}
function finish$45(self, fid, scheme, inferring) {
  const module = self.v.module;
  defaultLiterals$129(new $rt.FieldRef(self.v, "s"));
  for (const $1 of $rt.items($b.replace(new $rt.FieldRef(self.v, "pendingRegions"), $b.Vec_new()))) {
    const v = $1[0];
    const candidates = $1[1];
    const $2 = resolveRegion$130(self.v.s, { $tag: "Var", $: v });
    m$3: {
      if (($2.$tag === "Var")) {
        {
          const $4 = first$131(candidates);
          m$5: {
            if (($4.$tag === "Some")) {
              const r = $4.$;
              {
                try {
                  unifyRegion$132(new $rt.FieldRef(self.v, "s"), { $tag: "Var", $: v }, { $tag: "Param", $: clone$34(r) });
                } catch ($6) {
                  if (!($6 instanceof $rt.Fail)) throw $6;
                }
              }
              break m$5;
            }
            if (true) {
              {
              }
              break m$5;
            }
            $rt.unmatched($4);
          }
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  for (const $7 of $rt.items($b.replace(new $rt.FieldRef(self.v, "pendingMatches"), $b.Vec_new()))) {
    const scrut = $7[0];
    const arms = $7[1];
    const span = $7[2];
    exhaustive$133(self, scrut, arms, $rt.copy(span));
  }
  for (const $8 of $rt.items($b.replace(new $rt.FieldRef(self.v, "copiesOut"), $b.Vec_new()))) {
    const t = $8[0];
    const span = $8[1];
    const z = zonk$134(self.v.s, t);
    let $9 = (!isCopy$135(self.v.p.v, z));
    if ($9) {
      let $10;
      const $11 = z;
      m$12: {
        if ((($11.$tag === "Var") || ($11.$tag === "Error"))) {
          $10 = true;
          break m$12;
        }
        if (true) {
          $10 = false;
          break m$12;
        }
        $rt.unmatched($11);
      }
      $9 = (!$10);
    }
    if ($9) {
      const shown = show$136(self.v.p.v, z);
      error$62(self.v.p, module, $rt.copy(span), $b.String_asStr(("" + "cannot move a `" + shown + "` out of a borrow; it is not `Copy`")));
    }
  }
  for (const $13 of $rt.items($b.replace(new $rt.FieldRef(self.v, "pendingOps"), $b.Vec_new()))) {
    const id = $13[0];
    const span = $13[1];
    const t0 = $13[2];
    const iface = $13[3];
    const method = $13[4];
    let t = zonk$134(self.v.s, t0);
    while (true) {
      let $14;
      const $15 = t;
      m$16: {
        if (($15.$tag === "Borrow")) {
          const inner = $15.$[1];
          $14 = { $tag: "Some", $: clone$23($b.Box_get(inner)) };
          break m$16;
        }
        if (($15.$tag === "Named")) {
          const d = $15.$[0];
          const args = $15.$[1];
          if ((d === known$104(self.v, "Ref"))) {
            const $17 = get$137(args, 1n);
            m$18: {
              if (($17.$tag === "Some" && ($17.$.$tag === "Ty"))) {
                const inner = $17.$.$;
                $14 = { $tag: "Some", $: clone$23(inner) };
                break m$18;
              }
              if (true) {
                $14 = { $tag: "None" };
                break m$18;
              }
              $rt.unmatched($17);
            }
            break m$16;
          }
        }
        if (true) {
          $14 = { $tag: "None" };
          break m$16;
        }
        $rt.unmatched($15);
      }
      const next = $14;
      const $19 = next;
      m$20: {
        if (($19.$tag === "Some")) {
          const n = $19.$;
          {
            t = n;
          }
          break m$20;
        }
        if (($19.$tag === "None")) {
          break;
          break m$20;
        }
        $rt.unmatched($19);
      }
    }
    let $21;
    const $22 = t;
    m$23: {
      if ((($22.$tag === "Prim") || ($22.$tag === "Error") || ($22.$tag === "Var"))) {
        $21 = true;
        break m$23;
      }
      if (($22.$tag === "Named")) {
        const d = $22.$[0];
        $21 = ((iface === "Show") && (d === known$104(self.v, "String")));
        break m$23;
      }
      if (true) {
        $21 = false;
        break m$23;
      }
      $rt.unmatched($22);
    }
    const builtin = $21;
    if (builtin) {
      continue;
    }
    closeRows$138(new $rt.FieldRef(self.v, "s"), t);
    const tz = zonk$134(self.v.s, t);
    let $24;
    const $25 = knownDef$139(self.v.p.v, $b.String_asStr(iface));
    m$26: {
      if (($25.$tag === "Some")) {
        const d = $25.$;
        $24 = d;
        break m$26;
      }
      if (($25.$tag === "None")) {
        continue;
        break m$26;
      }
      $rt.unmatched($25);
    }
    const d = $24;
    const assumed = clone$140(self.v.bounds);
    if ((!satisfies$141(self.v.p.v, tz, { $tag: "Named", $: [d, $b.Vec_new()] }, assumed))) {
      const shown = show$136(self.v.p.v, tz);
      let hint = $b.String_new();
      const $27 = tz;
      m$28: {
        if (($27.$tag === "Named")) {
          const n = $27.$[0];
          {
            const name = $b.String_clone($rt.idx(self.v.p.v.defs, n).name);
            let missingSuper = { $tag: "None" };
            const closure = ifaceClosure$142(self.v.p.v, d);
            const $29 = $b.slice_len(closure);
            for (let k = 1n; k < $29; k++) {
              if ((isNone$86(missingSuper) && (!satisfies$141(self.v.p.v, tz, { $tag: "Named", $: [$rt.idx(closure, k), $b.Vec_new()] }, assumed)))) {
                missingSuper = { $tag: "Some", $: $rt.idx(closure, k) };
              }
            }
            let $30;
            const $31 = missingSuper;
            m$32: {
              if (($31.$tag === "Some")) {
                const sup = $31.$;
                if (deriveRequest$143(self.v.p.v, d, n)) {
                  {
                    const supName = $b.String_clone($rt.idx(self.v.p.v.defs, sup).name);
                    $30 = ("" + ": `" + iface + "` needs `" + supName + "`; ask for it with `impl " + supName + " for " + name + ";`");
                  }
                  break m$32;
                }
              }
              if (true) {
                $30 = ("" + ": ask for it with `impl " + iface + " for " + name + ";`");
                break m$32;
              }
              $rt.unmatched($31);
            }
            hint = $30;
          }
          break m$28;
        }
        if (true) {
          {
          }
          break m$28;
        }
        $rt.unmatched($27);
      }
      error$62(self.v.p, module, $rt.copy(span), $b.String_asStr(("" + "`" + shown + "` does not implement `" + iface + "`" + hint)));
      continue;
    }
    ensureImpl$144(self.v.p, d, tz, 0n);
    const $33 = $b.HashMap_get(self.v.p.v.ifaceFns, $b.String_asStr(("" + String(d) + ":" + method)));
    m$34: {
      if (($33.$tag === "Some")) {
        const f = $33.$;
        {
          if ((iface === "Show")) {
            $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "shows"), id, [f, [{ $tag: "Ty", $: clone$23(tz) }]]);
          } else {
            {
              $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "ops"), id, [f, [{ $tag: "Ty", $: clone$23(tz) }]]);
            }
          }
        }
        break m$34;
      }
      if (true) {
        {
        }
        break m$34;
      }
      $rt.unmatched($33);
    }
  }
  for (const $35 of $rt.items($b.replace(new $rt.FieldRef(self.v, "pendingTargs"), $b.Vec_new()))) {
    const call = $35;
    for (const $36 of $rt.items(call.args)) {
      const a = $36;
      const $37 = a;
      m$38: {
        if (($37.$tag === "Ty")) {
          const t = $37.$;
          {
            closeRows$138(new $rt.FieldRef(self.v, "s"), t);
          }
          break m$38;
        }
        if (true) {
          {
          }
          break m$38;
        }
        $rt.unmatched($37);
      }
    }
    for (const $39 of $rt.items(call.bounds)) {
      const t0 = $39[0];
      const b0 = $39[1];
      const t = zonk$134(self.v.s, t0);
      const b = zonk$134(self.v.s, b0);
      const assumed = clone$140(self.v.bounds);
      if ((!satisfies$141(self.v.p.v, t, b, assumed))) {
        const ts = show$136(self.v.p.v, t);
        const bs = show$136(self.v.p.v, b);
        error$62(self.v.p, module, $rt.copy(call.span), $b.String_asStr(("" + "`" + ts + "` does not implement `" + bs + "`")));
      } else {
        const $40 = b;
        m$41: {
          if (($40.$tag === "Named")) {
            const d = $40.$[0];
            {
              let $42;
              const $43 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, d), "kind");
              const $44 = $43.v;
              m$45: {
                if (($44.$tag === "Interface")) {
                  $42 = true;
                  break m$45;
                }
                if (true) {
                  $42 = false;
                  break m$45;
                }
                $rt.unmatched($44);
              }
              if ($42) {
                ensureImpl$144(self.v.p, d, t, 0n);
              }
            }
            break m$41;
          }
          if (true) {
            {
            }
            break m$41;
          }
          $rt.unmatched($40);
        }
      }
    }
    const zonked = { v: $b.Vec_new() };
    for (const $46 of $rt.items(call.args)) {
      const a = $46;
      $b.Vec_push(zonked, zonkArg$145(self.v.s, a));
    }
    $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "targs"), call.id, zonked.v);
  }
  for (const $47 of $rt.items($b.replace(new $rt.FieldRef(self.v, "pendingSpecs"), $b.Vec_new()))) {
    const id = $47[0];
    const span = $47[1];
    const tfid = $47[2];
    const args = $47[3];
    const tparams = clone$73($rt.idx(self.v.p.v.fns, tfid).scheme.tparams);
    const binds = { v: $b.HashMap_new() };
    const $48 = min$146($b.slice_len(tparams), $b.slice_len(args));
    for (let i = 0n; i < $48; i++) {
      $b.HashMap_insert(binds, $rt.idx(tparams, i).sym.id, zonkArg$145(self.v.s, $rt.idx(args, i)));
    }
    let $49;
    const $50 = comptimeArgs$147(self.v.p.v, tfid, binds.v);
    m$51: {
      if (($50.$tag === "Some")) {
        const c = $50.$;
        $49 = c;
        break m$51;
      }
      if (($50.$tag === "None")) {
        continue;
        break m$51;
      }
      $rt.unmatched($50);
    }
    const ct = $49;
    const $54 = find$149($b.slice_iter(ct), (($0$$52) => {
  {
    const $53 = $0$$52;
    const t = $53[1];
    return containsParams$148(t);
  }
    }));
    m$55: {
      if (($54.$tag === "Some")) {
        const s = $54.$[0];
        {
          error$62(self.v.p, module, $rt.copy(span), $b.String_asStr(("" + "the `comptime` type `" + s.name + "` must be known here; it cannot depend on a generic parameter")));
          continue;
        }
        break m$55;
      }
      if (true) {
        {
        }
        break m$55;
      }
      $rt.unmatched($54);
    }
    const spec = specializeFor$150(self.v.p, tfid, ct);
    $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "calls"), id, spec);
    const rest = { v: $b.Vec_new() };
    const $56 = min$146($b.slice_len(tparams), $b.slice_len(args));
    for (let i = 0n; i < $56; i++) {
      if ((!$rt.idx(tparams, i).isComptime)) {
        $b.Vec_push(rest, zonkArg$145(self.v.s, $rt.idx(args, i)));
      }
    }
    $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "targs"), id, rest.v);
  }
  for (const $57 of $rt.items(scheme.params)) {
    const name = $57[0];
    const ty = $57[1];
    $b.Vec_push(new $rt.FieldRef(self.v.typed, "params"), [$b.String_clone(name), clone$23(ty)]);
  }
  let typed = $b.replace(new $rt.FieldRef(self.v, "typed"), emptyTyped$38());
  const exprs = { v: $b.HashMap_new() };
  const $58 = $b.Gen_each($b.HashMap_entries(typed.exprs));
  let $60;
  for (let $59 = $58.next(); !$59.done; $59 = $58.next($60)) {
    $60 = undefined;
    const $61 = $59.value.item;
    const k = $61[0];
    const t = $61[1];
    $b.HashMap_insert(exprs, k, zonk$134(self.v.s, t));
  }
  typed.exprs = exprs.v;
  const bindings = { v: $b.HashMap_new() };
  const $62 = $b.Gen_each($b.HashMap_entries(typed.bindings));
  let $64;
  for (let $63 = $62.next(); !$63.done; $63 = $62.next($64)) {
    $64 = undefined;
    const $65 = $63.value.item;
    const k = $65[0];
    const t = $65[1];
    $b.HashMap_insert(bindings, k, zonk$134(self.v.s, t));
  }
  typed.bindings = bindings.v;
  const slots = { v: $b.HashMap_new() };
  const $66 = $b.Gen_each($b.HashMap_entries(typed.slots));
  let $68;
  for (let $67 = $66.next(); !$67.done; $67 = $66.next($68)) {
    $68 = undefined;
    const $69 = $67.value.item;
    const k = $69[0];
    const t = $69[1];
    $b.HashMap_insert(slots, k, zonk$134(self.v.s, t));
  }
  typed.slots = slots.v;
  for (const $70 of $rt.items($b.replace(new $rt.FieldRef(self.v, "copyBinds"), $b.Vec_new()))) {
    const id = $70;
    const $71 = $b.HashMap_get(typed.bindings, id);
    m$72: {
      if (($71.$tag === "Some" && ($71.$.$tag === "Borrow" && $71.$.$[0] === false))) {
        const inner = $71.$.$[1];
        {
          const i = clone$23($b.Box_get(inner));
          let $73 = settled$151(i);
          if ($73) {
            let $74;
            const $75 = i;
            m$76: {
              if (($75.$tag === "Param")) {
                $74 = true;
                break m$76;
              }
              if (true) {
                $74 = false;
                break m$76;
              }
              $rt.unmatched($75);
            }
            $73 = (!$74);
          }
          if (($73 && isCopy$135(self.v.p.v, i))) {
            $b.HashMap_insert(new $rt.FieldRef(typed, "bindings"), id, i);
          }
        }
        break m$72;
      }
      if (true) {
        {
        }
        break m$72;
      }
      $rt.unmatched($71);
    }
  }
  const found = { v: $b.Vec_new() };
  const $77 = $b.Gen_each($b.HashMap_entries(typed.exprs));
  let $79;
  for (let $78 = $77.next(); !$78.done; $78 = $77.next($79)) {
    $79 = undefined;
    const $80 = $78.value.item;
    const id = $80[0];
    const t = $80[1];
    const $81 = $b.HashMap_get(self.v.spans, id);
    m$82: {
      if (($81.$tag === "Some")) {
        const sp = $81.$;
        {
          $b.Vec_push(found, [$rt.copy(sp), clone$23(t)]);
        }
        break m$82;
      }
      if (true) {
        {
        }
        break m$82;
      }
      $rt.unmatched($81);
    }
  }
  const $83 = $b.Gen_each($b.HashMap_entries(typed.bindings));
  let $85;
  for (let $84 = $83.next(); !$84.done; $84 = $83.next($85)) {
    $85 = undefined;
    const $86 = $84.value.item;
    const id = $86[0];
    const t = $86[1];
    const $87 = $b.HashMap_get(self.v.spans, id);
    m$88: {
      if (($87.$tag === "Some")) {
        const sp = $87.$;
        {
          $b.Vec_push(found, [$rt.copy(sp), clone$23(t)]);
        }
        break m$88;
      }
      if (true) {
        {
        }
        break m$88;
      }
      $rt.unmatched($87);
    }
  }
  $b.slice_sortBy(found, ((a, b) => {
  const $89 = cmp$152($rt.idx(a, 0n).start, $rt.idx(b, 0n).start);
  m$90: {
    if (($89.$tag === "Equal")) {
      return cmp$152($rt.idx(a, 0n).end, $rt.idx(b, 0n).end);
      break m$90;
    }
    if (true) {
      const o = $89;
      return o;
      break m$90;
    }
    $rt.unmatched($89);
  }
  }));
  for (const $91 of $rt.items(found.v)) {
    const sp = $91[0];
    const t = $91[1];
    const $92 = borrowInContainer$153(self.v.p.v, t);
    m$93: {
      if (($92.$tag === "Some")) {
        const d = $92.$[0];
        const arg = $92.$[1];
        {
          const msg = containerMessage$154(self.v.p.v, d, arg);
          error$62(self.v.p, module, $rt.copy(sp), $b.String_asStr(msg));
          break;
        }
        break m$93;
      }
      if (true) {
        {
        }
        break m$93;
      }
      $rt.unmatched($92);
    }
  }
  $b.HashMap_insert(new $rt.FieldRef(self.v.p.v, "typed"), fid, typed);
  if (inferring) {
    let row = zonkEffs$119(self.v.s, clone$40(self.v.allowed));
    row.tail = { $tag: "Closed" };
    if (($b.slice_len(row.effs) > 0n)) {
      const $94 = $b.HashMap_get(self.v.p.v.assumedPure, fid);
      m$95: {
        if (($94.$tag === "Some")) {
          const m = $94.$[0];
          const span = $94.$[1];
          {
            const name = $b.String_clone($rt.idx(self.v.p.v.fns, fid).name);
            const what = showEffs$121(self.v, row);
            error$62(self.v.p, m, $rt.copy(span), $b.String_asStr(("" + "`" + name + "` calls itself and performs `" + what + "`, so it must declare its effects with `uses`")));
          }
          break m$95;
        }
        if (true) {
          {
          }
          break m$95;
        }
        $rt.unmatched($94);
      }
    }
    $b.HashMap_insert(new $rt.FieldRef(self.v.p.v, "inferred"), fid, { $tag: "Some", $: row });
    return undefined;
  }
}
function render$46(d, file, source) {
  const $1 = d;
  if (!(($1.$tag === "Diagnostic"))) $rt.unmatched($1);
  const span = $1.$.span;
  const message = $1.$.message;
  const $2 = lineCol$155(source, span.start);
  const line = $2[0];
  const col = $2[1];
  const lines = $b.str_split(source, "\n");
  let $3;
  if (($rt.usize(line - 1n) < $b.slice_len(lines))) {
    $3 = $b.String_clone($rt.idx(lines, $rt.usize(line - 1n)));
  } else {
    {
      $3 = $b.String_new();
    }
  }
  const text = $3;
  let $4;
  if ((span.end > span.start)) {
    $4 = $rt.usize(span.end - span.start);
  } else {
    {
      $4 = 1n;
    }
  }
  let width = $4;
  let $5;
  if (($b.String_len(text) >= col)) {
    $5 = $rt.usize($b.String_len(text) - $rt.usize(col - 1n));
  } else {
    {
      $5 = 1n;
    }
  }
  const room = $5;
  width = min$146(width, max$156(room, 1n));
  const out = { v: ("" + file + ":" + String(line) + ":" + String(col) + ": " + message + "\n  " + text + "\n  ") };
  const $6 = col;
  for (let $7$$8 = 1n; $7$$8 < $6; $7$$8++) {
    $b.String_push(out, " ");
  }
  const $9 = width;
  for (let $10$$11 = 0n; $10$$11 < $9; $10$$11++) {
    $b.String_push(out, "^");
  }
  return out.v;
}
function lookup$47(self, module, name) {
  const $1 = $b.HashMap_get($rt.idx(self.modules, module).scope, name);
  m$2: {
    if (($1.$tag === "Some")) {
      const b = $1.$;
      return { $tag: "Some", $: clone$63(b) };
      break m$2;
    }
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function new$$48(p) {
  return { p: p, insts: $b.Vec_new(), instIndex: $b.HashMap_new(), tasks: false, next: 0n, consts: $b.HashMap_new(), head: $b.String_new(), code: $b.String_new(), fid: 0n, map: $b.HashMap_new(), module: 0n, suspends: false, ret: { $tag: "Prim", $: { $tag: "Void" } }, fnRet: { $tag: "Prim", $: { $tag: "Void" } }, inHandle: false, out: $b.String_new(), indent: 0n, tmp: 0n, scopes: $b.Vec_new(), cells: new$$9(), cellParams: new$$9() };
}
function startsTasks$49(self) {
  const $1 = $b.Gen_each($b.HashMap_entries(self.p.typed));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const t = $4[1];
    const $5 = $b.Gen_each($b.HashMap_entries(t.calls));
    let $7;
    for (let $6 = $5.next(); !$6.done; $6 = $5.next($7)) {
      $7 = undefined;
      const $8 = $6.value.item;
      const f = $8[1];
      const key = builtinKey$157(self, f);
      if (((((key === "Io_scope") || (key === "channel")) || (key === "Reply_new")) || (key === "Mutex_new"))) {
        return true;
      }
    }
  }
  return false;
}
function instance$50(self, fid, args) {
  const key = ("" + String(fid) + "|" + keyArgs$159(eraseArgs$158(args, self.v.p, self.v.tasks)));
  const $1 = $b.HashMap_get(self.v.instIndex, $b.String_asStr(key));
  m$2: {
    if (($1.$tag === "Some")) {
      const i = $1.$;
      {
        return i;
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  if ((!has$19(self.v.p.checked, fid))) {
    checkFn$3(new $rt.FieldRef(self.v, "p"), fid);
  }
  const i = $b.slice_len(self.v.insts);
  const suspends = fnSuspends$160(self.v, fid, args);
  const js = ("" + mangle$161($b.String_asStr($rt.idx(self.v.p.fns, fid).name)) + "$" + String(i));
  $b.Vec_push(new $rt.FieldRef(self.v, "insts"), { fid: fid, args: args, js: js, suspends: suspends });
  $b.HashMap_insert(new $rt.FieldRef(self.v, "instIndex"), key, i);
  return i;
}
function emit$51(self, i) {
  const fid = $rt.idx(self.v.insts, i).fid;
  let $1;
  const $2 = fnDecl$24(self.v.p, fid);
  m$3: {
    if (($2.$tag === "Some")) {
      const d = $2.$;
      $1 = d;
      break m$3;
    }
    if (($2.$tag === "None")) {
      return;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const decl = $1;
  let $4;
  const $5 = decl.body;
  m$6: {
    if (($5.$tag === "Some")) {
      const b = $5.$;
      $4 = b;
      break m$6;
    }
    if (($5.$tag === "None")) {
      return;
      break m$6;
    }
    $rt.unmatched($5);
  }
  const body = $4;
  self.v.fid = fid;
  self.v.module = $rt.idx(self.v.p.fns, fid).module;
  self.v.map = substMap$162($rt.idx(self.v.p.fns, fid).scheme.tparams, $rt.idx(self.v.insts, i).args);
  self.v.suspends = $rt.idx(self.v.insts, i).suspends;
  self.v.ret = concrete$163(self.v, $rt.idx(self.v.p.fns, fid).scheme.ret);
  self.v.fnRet = clone$23(self.v.ret);
  self.v.inHandle = false;
  self.v.tmp = 0n;
  self.v.indent = 1n;
  self.v.out = $b.String_new();
  self.v.scopes = $b.Vec_new();
  self.v.cells = new$$9();
  self.v.cellParams = new$$9();
  findCells$164(self, decl);
  push$165(self);
  const params = { v: $b.Vec_new() };
  const celled = { v: $b.Vec_new() };
  for (const $7 of $rt.items(decl.sig.params)) {
    const p = $7;
    const cell = has$19(self.v.cellParams, p.name.span.start);
    const js = declare$166(self, $b.String_asStr(p.name.name), cell);
    if (cell) {
      const raw = fresh$167(self);
      $b.Vec_push(params, $b.String_clone(raw));
      $b.Vec_push(celled, [js, raw]);
    } else {
      {
        $b.Vec_push(params, js);
      }
    }
  }
  for (const $8 of $rt.items(celled.v)) {
    const js = $8[0];
    const raw = $8[1];
    line$168(self, ("" + "const " + js + " = { v: " + raw + " };"));
  }
  stmtsFrom$169(self, body, 0n, { $tag: "Return" });
  pop$170(self);
  const inner = $b.replace(new $rt.FieldRef(self.v, "out"), $b.String_new());
  const js = $b.String_clone($rt.idx(self.v.insts, i).js);
  const $9 = new $rt.FieldRef(self.v, "code");
  let $10;
  if ($rt.idx(self.v.insts, i).suspends) {
    $10 = "*";
  } else {
    {
      $10 = "";
    }
  }
  $b.String_push($9, ("" + "function" + $10 + " " + js + "(" + join$53(params.v, ", ") + ") {\n"));
  $b.String_push(new $rt.FieldRef(self.v, "code"), $b.String_asStr(inner));
  $b.String_push(new $rt.FieldRef(self.v, "code"), "}\n");
  return undefined;
}
function startArgs$52(self, fid) {
  const out = { v: $b.Vec_new() };
  const $1 = $b.Gen_each($b.Gen_enumerate($b.slice_iter($rt.idx(self.p.fns, fid).scheme.params)));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const i = $4[0];
    const t = $4[1][1];
    const $5 = out;
    let $6;
    if ($b.Option_isSome(intPrim$171(t))) {
      $6 = ("" + "$rt.argInt(" + String(i) + ")");
    } else {
      {
        $6 = ("" + "$rt.argStr(" + String(i) + ")");
      }
    }
    $b.Vec_push($5, $6);
  }
  return out.v;
}
function join$53(self, sep) {
  const out = { v: $b.String_new() };
  let first = true;
  for (const $1 of $rt.items(self)) {
    const x = $1;
    if ((!first)) {
      $b.String_push(out, sep);
    }
    $b.String_push(out, ("" + x));
    first = false;
  }
  return out.v;
}
function parseDeclarations$54(src) {
  return parse$172(src, true);
}
function parseModule$55(src) {
  return parse$172(src, false);
}
function last$56(self) {
  if (($b.slice_len(self) === 0n)) {
    return { $tag: "None" };
  } else {
    {
      return { $tag: "Some", $: $rt.idx(self, $rt.usize($b.slice_len(self) - 1n)) };
    }
  }
}
function clone$57(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$173(x));
  }
  return v.v;
}
function placeholder$58(self, name, module) {
  $b.Vec_push(new $rt.FieldRef(self.v, "defs"), { name: $b.String_clone(name.name), module: module, params: $b.Vec_new(), kind: { $tag: "Struct", $: { fields: { $tag: "None" } } }, span: $rt.copy(name.span), private: $b.Vec_new(), view: false, tagOrder: $b.Vec_new(), templateFields: { $tag: "None" } });
  return $rt.usize($b.slice_len(self.v.defs) - 1n);
}
function freshSym$59(self, name) {
  self.v.nextSym = $rt.u32(self.v.nextSym + 1n);
  return { id: self.v.nextSym, name: $b.str_toString(name) };
}
function clone$60(self) {
  {
    return { id: clone$174(self.id), kind: clone$175(self.kind), span: clone$94(self.span) };
  }
}
function emptyScheme$61() {
  return { tparams: $b.Vec_new(), params: $b.Vec_new(), ret: { $tag: "Error" }, effects: { $tag: "None" }, retFrom: $b.Vec_new() };
}
function error$62(self, module, span, msg) {
  const at = sourceSpan$176(self.v, $rt.copy(span));
  let message = $b.str_toString(msg);
  const $1 = new $rt.FieldRef(self.v, "note");
  const $2 = $1.v;
  m$3: {
    if (($2.$tag === "Some")) {
      const n = new $rt.FieldRef($2, "$");
      {
        message = ("" + message + " (" + n.v + ")");
      }
      break m$3;
    }
    if (true) {
      {
      }
      break m$3;
    }
    $rt.unmatched($2);
  }
  const d = diag$15($rt.copy(at), $b.String_asStr(message));
  if ((!some$178($b.slice_iter(self.v.diags), (($0$$4) => {
  {
    const $5 = $0$$4;
    const m = $5[0];
    const e = $5[1];
    return ((m === module) && eq$177(e, d));
  }
  })))) {
    $b.Vec_push(new $rt.FieldRef(self.v, "diags"), [module, d]);
    return undefined;
  }
}
function clone$63(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Def")) {
      const x = $1.$;
      return { $tag: "Def", $: clone$174(x) };
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const x = $1.$;
      return { $tag: "Fn", $: clone$174(x) };
      break m$2;
    }
    if (($1.$tag === "Const")) {
      const x = $1.$;
      return { $tag: "Const", $: clone$174(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function moduleNamed$64(self, name) {
  return findIndex$7($b.slice_iter(self.modules), ((m) => {
  return (m.name === name);
  }));
}
function find$65(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function elaborateParams$66(self, m, item) {
  const scope = moduleScope$31(m);
  let $1;
  const $2 = item.kind;
  m$3: {
    if (($2.$tag === "Struct")) {
      const s = $2.$;
      $1 = [$b.String_clone(s.name.name), clone$179(s.params)];
      break m$3;
    }
    if (($2.$tag === "Enum")) {
      const e = $2.$;
      $1 = [$b.String_clone(e.name.name), clone$179(e.params)];
      break m$3;
    }
    if (($2.$tag === "TypeAlias")) {
      const a = $2.$;
      $1 = [$b.String_clone(a.name.name), clone$179(a.params)];
      break m$3;
    }
    if (($2.$tag === "Interface")) {
      const x = $2.$;
      $1 = [$b.String_clone(x.name.name), clone$179(x.params)];
      break m$3;
    }
    if (($2.$tag === "Effect")) {
      const e = $2.$;
      $1 = [$b.String_clone(e.name.name), clone$179(e.params)];
      break m$3;
    }
    if (true) {
      return;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const $4 = $1;
  const name = $4[0];
  const params = $4[1];
  const $5 = lookup$47(self.v, m, $b.String_asStr(name));
  m$6: {
    if (($5.$tag === "Some" && ($5.$.$tag === "Def"))) {
      const id = $5.$.$;
      {
        const gps = typeParams$180(self, params, scope);
        $rt.idx(self.v.defs, id).params = gps;
        return undefined;
      }
      break m$6;
    }
    if (true) {
      {
        return undefined;
      }
      break m$6;
    }
    $rt.unmatched($5);
  }
}
function elaborateDef$67(self, m, item) {
  const scope = moduleScope$31(m);
  let $1;
  const $2 = item.kind;
  m$3: {
    if (($2.$tag === "Struct")) {
      const s = $2.$;
      $1 = $b.String_clone(s.name.name);
      break m$3;
    }
    if (($2.$tag === "Enum")) {
      const e = $2.$;
      $1 = $b.String_clone(e.name.name);
      break m$3;
    }
    if (($2.$tag === "TypeAlias")) {
      const a = $2.$;
      $1 = $b.String_clone(a.name.name);
      break m$3;
    }
    if (($2.$tag === "Interface")) {
      const x = $2.$;
      $1 = $b.String_clone(x.name.name);
      break m$3;
    }
    if (($2.$tag === "Effect")) {
      const e = $2.$;
      $1 = $b.String_clone(e.name.name);
      break m$3;
    }
    if (true) {
      return;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const name = $1;
  let $4;
  const $5 = lookup$47(self.v, m, $b.String_asStr(name));
  m$6: {
    if (($5.$tag === "Some" && ($5.$.$tag === "Def"))) {
      const d = $5.$.$;
      $4 = d;
      break m$6;
    }
    if (true) {
      return;
      break m$6;
    }
    $rt.unmatched($5);
  }
  const id = $4;
  const gparams = clone$73($rt.idx(self.v.defs, id).params);
  const inner = withParams$32(scope, gparams);
  const $7 = item.kind;
  m$8: {
    if (($7.$tag === "Struct")) {
      const s = $7.$;
      {
        $rt.idx(self.v.defs, id).view = s.view;
        const private$ = { v: $b.Vec_new() };
        const $9 = s.fields;
        m$10: {
          if (($9.$tag === "Some")) {
            const fs = $9.$;
            {
              for (const $11 of $rt.items(fs)) {
                const f = $11;
                if (f.private) {
                  $b.Vec_push(private$, $b.String_clone(f.name.name));
                }
              }
            }
            break m$10;
          }
          if (true) {
            {
            }
            break m$10;
          }
          $rt.unmatched($9);
        }
        $rt.idx(self.v.defs, id).private = private$.v;
        let $12;
        const $13 = s.fields;
        m$14: {
          if (($13.$tag === "Some")) {
            const fs = $13.$;
            $12 = some$181($b.slice_iter(fs), ((f) => {
  return ($b.Option_isSome(f.generate) || $b.Option_isSome(f.computed));
            }));
            break m$14;
          }
          if (($13.$tag === "None")) {
            $12 = false;
            break m$14;
          }
          $rt.unmatched($13);
        }
        const generated = $12;
        if ((generated || some$72($b.slice_iter(gparams), ((g) => {
  return g.isComptime;
        })))) {
          $rt.idx(self.v.defs, id).templateFields = clone$182(s.fields);
          $rt.idx(self.v.defs, id).kind = { $tag: "Struct", $: { fields: { $tag: "Some", $: $b.Vec_new() } } };
          return;
        }
        let $15;
        const $16 = s.fields;
        m$17: {
          if (($16.$tag === "Some")) {
            const fs = $16.$;
            {
              const out = { v: $b.Vec_new() };
              for (const $18 of $rt.items(fs)) {
                const f = $18;
                $b.Vec_push(out, [$b.String_clone(f.name.name), elabTy$101(self, f.ty, inner)]);
              }
              $15 = { $tag: "Some", $: out.v };
            }
            break m$17;
          }
          if (($16.$tag === "None")) {
            $15 = { $tag: "None" };
            break m$17;
          }
          $rt.unmatched($16);
        }
        const fields = $15;
        $rt.idx(self.v.defs, id).kind = { $tag: "Struct", $: { fields: fields } };
        return undefined;
      }
      break m$8;
    }
    if (($7.$tag === "Enum")) {
      const e = $7.$;
      {
        $rt.idx(self.v.defs, id).view = e.view;
        const order = { v: $b.Vec_new() };
        for (const $19 of $rt.items(e.tags)) {
          const t = $19;
          $b.Vec_push(order, $b.String_clone(t.name.name));
        }
        $rt.idx(self.v.defs, id).tagOrder = order.v;
        const tags = { v: $b.Vec_new() };
        for (const $20 of $rt.items(e.tags)) {
          const t = $20;
          const payload = elabPayload$183(self, t.payload, inner);
          labelSet$184(tags, $b.String_asStr(t.name.name), payload);
        }
        $rt.idx(self.v.defs, id).kind = { $tag: "Enum", $: { tags: tags.v } };
        return undefined;
      }
      break m$8;
    }
    if (($7.$tag === "TypeAlias")) {
      const a = $7.$;
      {
        if (isNone$185($b.HashMap_remove(new $rt.FieldRef(self.v, "pendingAliases"), id))) {
          return;
        }
        $b.Vec_push(new $rt.FieldRef(self.v, "aliasing"), id);
        const ty = elabTy$101(self, a.ty, inner);
        $b.Vec_pop(new $rt.FieldRef(self.v, "aliasing"));
        $rt.idx(self.v.defs, id).kind = { $tag: "Alias", $: { ty: ty } };
        return undefined;
      }
      break m$8;
    }
    if (($7.$tag === "Interface")) {
      const x = $7.$;
      {
        let $21;
        const $22 = new $rt.FieldRef($rt.idx(self.v.defs, id), "kind");
        const $23 = $22.v;
        m$24: {
          if (($23.$tag === "Interface")) {
            const selfSym = new $rt.FieldRef($23.$, "selfSym");
            $21 = clone$34(selfSym.v);
            break m$24;
          }
          if (true) {
            return;
            break m$24;
          }
          $rt.unmatched($23);
        }
        const selfSym = $21;
        const supers = { v: $b.Vec_new() };
        for (const $25 of $rt.items(x.extends)) {
          const t = $25;
          $b.Vec_push(supers, elabTy$101(self, t, inner));
        }
        let selfScope = clone$97(inner);
        selfScope.selfTy = { $tag: "Some", $: { $tag: "Param", $: clone$34(selfSym) } };
        const methods = { v: $b.Vec_new() };
        const assoc = { v: $b.Vec_new() };
        for (const $26 of $rt.items(x.members)) {
          const member = $26;
          const $27 = member;
          m$28: {
            if (($27.$tag === "Method")) {
              const sig = $27.$;
              {
                const s = elaborateSig$71(self, sig, selfScope, { $tag: "None" });
                $b.Vec_push(methods, [$b.String_clone(sig.name.name), s]);
              }
              break m$28;
            }
            if (($27.$tag === "AssocType")) {
              const name$$29 = $27.$.name;
              $b.Vec_push(assoc, $b.String_clone(name$$29.name));
              break m$28;
            }
            $rt.unmatched($27);
          }
        }
        declareIfaceFns$186(self, id, m, methods.v, selfSym);
        $rt.idx(self.v.defs, id).kind = { $tag: "Interface", $: { methods: methods.v, assoc: assoc.v, selfSym: selfSym, supers: supers.v } };
        return undefined;
      }
      break m$8;
    }
    if (($7.$tag === "Effect")) {
      const e = $7.$;
      {
        const ops = { v: $b.Vec_new() };
        for (const $30 of $rt.items(e.ops)) {
          const sig = $30;
          const s = elaborateSig$71(self, sig, inner, { $tag: "None" });
          $b.Vec_push(ops, [$b.String_clone(sig.name.name), s]);
        }
        $rt.idx(self.v.defs, id).kind = { $tag: "Effect", $: { ops: ops.v } };
        return undefined;
      }
      break m$8;
    }
    if (true) {
      {
        return undefined;
      }
      break m$8;
    }
    $rt.unmatched($7);
  }
}
function checkViews$68(self) {
  const $1 = $b.slice_len(self.v.defs);
  for (let d = 0n; d < $1; d++) {
    const module = $rt.idx(self.v.defs, d).module;
    if ($rt.idx(self.v.modules, module).isStd) {
      continue;
    }
    let $2;
    const $3 = new $rt.FieldRef($rt.idx(self.v.defs, d), "kind");
    const $4 = $3.v;
    m$5: {
      if (($4.$tag === "Struct" && ($4.$.fields.$tag === "Some"))) {
        const fs = new $rt.FieldRef($4.$.fields, "$");
        $2 = clone$74(fs.v);
        break m$5;
      }
      if (($4.$tag === "Enum")) {
        const tags = new $rt.FieldRef($4.$, "tags");
        {
          const out = { v: $b.Vec_new() };
          for (const $6 of $rt.items(tags.v)) {
            const k = $6[0];
            const t = $6[1];
            $b.Vec_push(out, [("" + "#" + k), clone$23(t)]);
          }
          $2 = out.v;
        }
        break m$5;
      }
      if (true) {
        continue;
        break m$5;
      }
      $rt.unmatched($4);
    }
    const parts = $2;
    for (const $7 of $rt.items(parts)) {
      const ty = $7[1];
      const $8 = borrowInContainer$153(self.v, ty);
      m$9: {
        if (($8.$tag === "Some")) {
          const c = $8.$[0];
          const arg = $8.$[1];
          {
            const msg = containerMessage$154(self.v, c, arg);
            error$62(self, module, $rt.copy($rt.idx(self.v.defs, d).span), $b.String_asStr(msg));
          }
          break m$9;
        }
        if (true) {
          {
          }
          break m$9;
        }
        $rt.unmatched($8);
      }
    }
    if ($rt.idx(self.v.defs, d).view) {
      continue;
    }
    for (const $10 of $rt.items(parts)) {
      const name = $10[0];
      const ty = $10[1];
      if ((class$$187(self.v, ty) === 2n)) {
        const shown = show$136(self.v, ty);
        let $11;
        if (($b.str_includes(shown, "str") && (!$b.str_includes(shown, "u8")))) {
          $11 = "use an owned `String`";
        } else {
          {
            $11 = "use an owned type such as `Vec<T>`";
          }
        }
        const hint = $11;
        const tname = $b.String_clone($rt.idx(self.v.defs, d).name);
        error$62(self, module, $rt.copy($rt.idx(self.v.defs, d).span), $b.String_asStr(("" + "`" + tname + "` holds a borrow in `" + name + "` (`" + shown + "`): " + hint + ", or declare `view` if `" + tname + "` is a temporary view")));
        break;
      }
    }
  }
  return undefined;
}
function elaborateConsts$69(self) {
  const $1 = $b.slice_len(self.v.consts);
  for (let c = 0n; c < $1; c++) {
    const m = $rt.idx(self.v.consts, c).module;
    const cname = $b.String_clone($rt.idx(self.v.consts, c).name);
    let ann = { $tag: "None" };
    for (const $2 of $rt.items($rt.idx(self.v.modules, m).ast.items)) {
      const it = $2;
      const $3 = it.kind;
      m$4: {
        if (($3.$tag === "Const")) {
          const name = $3.$.name;
          const ty = $3.$.ty;
          {
            if (eq$6(name.name, cname)) {
              ann = clone$188(ty);
              break;
            }
          }
          break m$4;
        }
        if (true) {
          {
          }
          break m$4;
        }
        $rt.unmatched($3);
      }
    }
    const scope = moduleScope$31(m);
    let $5;
    const $6 = ann;
    m$7: {
      if (($6.$tag === "Some")) {
        const t = $6.$;
        $5 = elabTy$101(self, t, scope);
        break m$7;
      }
      if (($6.$tag === "None")) {
        const $8 = new $rt.FieldRef($rt.idx(self.v.consts, c).value, "kind");
        const $9 = $8.v;
        m$10: {
          if (($9.$tag === "Int")) {
            $5 = { $tag: "Prim", $: { $tag: "I32" } };
            break m$10;
          }
          if (($9.$tag === "Float")) {
            $5 = { $tag: "Prim", $: { $tag: "F64" } };
            break m$10;
          }
          if (($9.$tag === "Str")) {
            $5 = { $tag: "Prim", $: { $tag: "Str" } };
            break m$10;
          }
          if (($9.$tag === "Bool")) {
            $5 = boolTy$189();
            break m$10;
          }
          if (($9.$tag === "Byte")) {
            $5 = { $tag: "Prim", $: { $tag: "U8" } };
            break m$10;
          }
          if (true) {
            {
              error$62(self, m, $rt.copy($rt.idx(self.v.consts, c).value.span), "give this constant a type: `const NAME: Type = \xe2\x80\xa6;`");
              $5 = { $tag: "Error" };
            }
            break m$10;
          }
          $rt.unmatched($9);
        }
        break m$7;
      }
      $rt.unmatched($6);
    }
    const ty = $5;
    $rt.idx(self.v.consts, c).ty = ty;
  }
  return undefined;
}
function elaborateImpl$70(self, m, item, imp) {
  const scope = moduleScope$31(m);
  const params = typeParams$180(self, imp.params, scope);
  const inner = withParams$32(scope, params);
  const target = elabTy$101(self, imp.target, inner);
  let iface = { $tag: "None" };
  const $1 = imp.iface;
  m$2: {
    if (($1.$tag === "Some")) {
      const t = $1.$;
      {
        const $3 = t.kind;
        m$4: {
          if (($3.$tag === "Path")) {
            const segments = $3.$.segments;
            const args = $3.$.args;
            {
              if (($b.slice_len(segments) === 1n)) {
                const $5 = lookup$47(self.v, m, $b.String_asStr($rt.idx(segments, 0n).name));
                m$6: {
                  if (($5.$tag === "Some" && ($5.$.$tag === "Def"))) {
                    const d = $5.$.$;
                    let $7;
                    const $8 = new $rt.FieldRef($rt.idx(self.v.defs, d), "kind");
                    const $9 = $8.v;
                    m$10: {
                      if (($9.$tag === "Interface")) {
                        $7 = true;
                        break m$10;
                      }
                      if (true) {
                        $7 = false;
                        break m$10;
                      }
                      $rt.unmatched($9);
                    }
                    if ($7) {
                      {
                        const gargs = elabArgs$190(self, d, args, inner, $rt.copy(t.span));
                        iface = { $tag: "Some", $: [d, gargs] };
                      }
                      break m$6;
                    }
                  }
                  if (true) {
                    const found = $5;
                    {
                      const name = $b.String_clone($rt.idx(segments, 0n).name);
                      let $11;
                      if (isNone$191(found)) {
                        $11 = unknown$192(self.v, "interface", $b.String_asStr(name));
                      } else {
                        {
                          $11 = ("" + "`" + name + "` is not an interface");
                        }
                      }
                      const msg = $11;
                      error$62(self, m, $rt.copy(t.span), $b.String_asStr(msg));
                    }
                    break m$6;
                  }
                  $rt.unmatched($5);
                }
              }
            }
            break m$4;
          }
          if (true) {
            {
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const id = $b.slice_len(self.v.impls);
  const template = some$72($b.slice_iter(params), ((g) => {
  return g.isComptime;
  }));
  const assocTys = { v: $b.HashMap_new() };
  if ((!template)) {
    for (const $12 of $rt.items(imp.assoc)) {
      const n = $12[0];
      const t = $12[1];
      const at = elabTy$101(self, t, inner);
      $b.HashMap_insert(assocTys, $b.String_clone(n.name), at);
    }
  }
  const assoc = { v: $b.Vec_new() };
  for (const $13 of $rt.items(imp.assoc)) {
    const n = $13[0];
    const t = $13[1];
    $b.Vec_push(assoc, [$b.String_clone(n.name), clone$193(t)]);
  }
  const hasIface = $b.Option_isSome(imp.iface);
  $b.Vec_push(new $rt.FieldRef(self.v, "impls"), { derived: imp.derived, assoc: assoc.v, assocTys: assocTys.v, module: m, params: clone$73(params), target: clone$23(target), iface: iface, methods: $b.Vec_new() });
  let methodScope = clone$97(inner);
  methodScope.selfTy = { $tag: "Some", $: target };
  const $14 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(imp.methods)));
  let $16;
  for (let $15 = $14.next(); !$15.done; $15 = $14.next($16)) {
    $16 = undefined;
    const $17 = $15.value.item;
    const k = $17[0];
    const method = $17[1];
    let scheme = elaborateSig$71(self, method.decl.sig, methodScope, { $tag: "Some", $: clone$73(params) });
    const fid = $b.slice_len(self.v.fns);
    const exported = ((method.exported || $rt.idx(self.v.modules, m).isStd) || hasIface);
    if ((exported && isNone$39(scheme.effects))) {
      scheme.effects = { $tag: "Some", $: pure$37() };
    }
    $b.Vec_push(new $rt.FieldRef(self.v, "fns"), { name: $b.String_clone(method.decl.sig.name.name), module: m, scheme: scheme, decl: { module: m, item: item, method: { $tag: "Some", $: k } }, exported: exported, implId: { $tag: "Some", $: id }, hasBody: $b.Option_isSome(method.decl.body), iface: { $tag: "None" } });
    $b.Vec_push(new $rt.FieldRef($rt.idx(self.v.impls, id), "methods"), fid);
  }
  return undefined;
}
function elaborateSig$71(self, sig, scope, outer) {
  const own = typeParams$180(self, sig.typeParams, scope);
  let inner = withParams$32(scope, own);
  let $1;
  const $2 = outer;
  m$3: {
    if (($2.$tag === "Some")) {
      const o = $2.$;
      $1 = o;
      break m$3;
    }
    if (($2.$tag === "None")) {
      $1 = $b.Vec_new();
      break m$3;
    }
    $rt.unmatched($2);
  }
  const all = { v: $1 };
  for (const $4 of $rt.items(own)) {
    const g = $4;
    $b.Vec_push(all, clone$194(g));
  }
  const regions = { v: $b.Vec_new() };
  for (const $5 of $rt.items(all.v)) {
    const g = $5;
    if (eq$33(g.kind, { $tag: "Region" })) {
      $b.Vec_push(regions, clone$34(g.sym));
    }
  }
  if (($b.slice_len(regions.v) === 1n)) {
    inner.elidedRegion = { $tag: "Some", $: { $tag: "Param", $: clone$34($rt.idx(regions.v, 0n)) } };
  }
  const params = { v: $b.Vec_new() };
  for (const $6 of $rt.items(sig.params)) {
    const p = $6;
    let $7;
    const $8 = p.ty;
    m$9: {
      if (($8.$tag === "Some")) {
        const t = $8.$;
        $7 = elabTy$101(self, t, inner);
        break m$9;
      }
      if (($8.$tag === "None")) {
        $7 = { $tag: "Error" };
        break m$9;
      }
      $rt.unmatched($8);
    }
    const ty = $7;
    $b.Vec_push(params, [$b.String_clone(p.name.name), ty]);
  }
  const ret = elabTy$101(self, sig.ret.ty, inner);
  let $10;
  const $11 = sig.uses;
  m$12: {
    if (($11.$tag === "Some")) {
      const row = $11.$;
      $10 = { $tag: "Some", $: elabEffects$195(self, row, inner) };
      break m$12;
    }
    if (($11.$tag === "None")) {
      $10 = { $tag: "None" };
      break m$12;
    }
    $rt.unmatched($11);
  }
  const effects = $10;
  const retFrom = { v: $b.Vec_new() };
  for (const $13 of $rt.items(sig.ret.from)) {
    const i = $13;
    $b.Vec_push(retFrom, $b.String_clone(i.name));
  }
  return { tparams: all.v, params: params.v, ret: ret, effects: effects, retFrom: retFrom.v };
}
function some$72(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function clone$73(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$194(x));
  }
  return v.v;
}
function clone$74(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$196(x));
  }
  return v.v;
}
function clone$75(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$40(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$76(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, $b.String_clone(x));
  }
  return v.v;
}
function clone$77(self) {
  return self;
}
function clone$78(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "I8")) {
      return { $tag: "I8" };
      break m$2;
    }
    if (($1.$tag === "I16")) {
      return { $tag: "I16" };
      break m$2;
    }
    if (($1.$tag === "I32")) {
      return { $tag: "I32" };
      break m$2;
    }
    if (($1.$tag === "I64")) {
      return { $tag: "I64" };
      break m$2;
    }
    if (($1.$tag === "I128")) {
      return { $tag: "I128" };
      break m$2;
    }
    if (($1.$tag === "Isize")) {
      return { $tag: "Isize" };
      break m$2;
    }
    if (($1.$tag === "U8")) {
      return { $tag: "U8" };
      break m$2;
    }
    if (($1.$tag === "U16")) {
      return { $tag: "U16" };
      break m$2;
    }
    if (($1.$tag === "U32")) {
      return { $tag: "U32" };
      break m$2;
    }
    if (($1.$tag === "U64")) {
      return { $tag: "U64" };
      break m$2;
    }
    if (($1.$tag === "Usize")) {
      return { $tag: "Usize" };
      break m$2;
    }
    if (($1.$tag === "F32")) {
      return { $tag: "F32" };
      break m$2;
    }
    if (($1.$tag === "F64")) {
      return { $tag: "F64" };
      break m$2;
    }
    if (($1.$tag === "Bool")) {
      return { $tag: "Bool" };
      break m$2;
    }
    if (($1.$tag === "Str")) {
      return { $tag: "Str" };
      break m$2;
    }
    if (($1.$tag === "Void")) {
      return { $tag: "Void" };
      break m$2;
    }
    if (($1.$tag === "Never")) {
      return { $tag: "Never" };
      break m$2;
    }
    if (($1.$tag === "Type")) {
      return { $tag: "Type" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$79(self) {
  {
    const v = [clone$174($rt.idx(self, 0n)), clone$197($rt.idx(self, 1n))];
    return v;
  }
}
function clone$80(self) {
  {
    return { labels: clone$74(self.labels), tail: clone$99(self.tail) };
  }
}
function clone$81(self) {
  {
    const v = [clone$82($rt.idx(self, 0n)), clone$198($rt.idx(self, 1n))];
    return v;
  }
}
function clone$82(self) {
  return $b.Box_new(clone$23($b.Box_get(self)));
}
function clone$83(self) {
  {
    const v = [clone$199($rt.idx(self, 0n)), clone$82($rt.idx(self, 1n))];
    return v;
  }
}
function clone$84(self) {
  return $b.Box_new(clone$200($b.Box_get(self)));
}
function clone$85(self) {
  {
    const v = [clone$82($rt.idx(self, 0n)), $b.String_clone($rt.idx(self, 1n))];
    return v;
  }
}
function isNone$86(self) {
  return (!$b.Option_isSome(self));
}
function exprHas$87(e) {
  const $1 = e.kind;
  m$2: {
    if ((($1.$tag === "Comptime") || ($1.$tag === "FieldAt") || ($1.$tag === "TagAt"))) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Template")) {
      const ps = $1.$;
      return some$201($b.slice_iter(ps), ((p) => {
  const $3 = p;
  m$4: {
    if (($3.$tag === "Expr")) {
      const x = $3.$;
      return exprHas$87(x);
      break m$4;
    }
    if (true) {
      return false;
      break m$4;
    }
    $rt.unmatched($3);
  }
      }));
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const args = $1.$.args;
      const $5 = args;
      m$6: {
        if (($5.$tag === "None")) {
          return false;
          break m$6;
        }
        if (($5.$tag === "Tuple")) {
          const es = $5.$;
          return some$202($b.slice_iter(es), ((x) => {
  return exprHas$87(x);
          }));
          break m$6;
        }
        if (($5.$tag === "Record")) {
          const fs = $5.$;
          return initsHave$203(fs);
          break m$6;
        }
        $rt.unmatched($5);
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      return initsHave$203(fields);
      break m$2;
    }
    if (($1.$tag === "List")) {
      const es = $1.$;
      return some$202($b.slice_iter(es), ((x) => {
  return exprHas$87(x);
      }));
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      return exprHas$87(target);
      break m$2;
    }
    if (($1.$tag === "Index")) {
      const target = $1.$.target;
      const index = $1.$.index;
      return (exprHas$87(target) || exprHas$87(index));
      break m$2;
    }
    if (($1.$tag === "Call")) {
      const callee = $1.$.callee;
      const typeArgs = $1.$.typeArgs;
      const args = $1.$.args;
      return ((exprHas$87(callee) || some$202($b.slice_iter(args), ((x) => {
  return exprHas$87(x);
      }))) || some$204($b.slice_iter(typeArgs), ((t) => {
  return tyHas$88(t);
      })));
      break m$2;
    }
    if (($1.$tag === "Unary")) {
      const operand = $1.$.operand;
      return exprHas$87(operand);
      break m$2;
    }
    if ((($1.$tag === "BorrowMut") || ($1.$tag === "Throw") || ($1.$tag === "Yield"))) {
      let x;
      if (($1.$tag === "BorrowMut")) { x = $1.$; }
      else if (($1.$tag === "Throw")) { x = $1.$; }
      else if (($1.$tag === "Yield")) { x = $1.$; }
      return exprHas$87(x);
      break m$2;
    }
    if (($1.$tag === "Binary")) {
      const lhs = $1.$.lhs;
      const rhs = $1.$.rhs;
      return (exprHas$87(lhs) || exprHas$87(rhs));
      break m$2;
    }
    if (($1.$tag === "Assign")) {
      const target = $1.$.target;
      const value = $1.$.value;
      return (exprHas$87(target) || exprHas$87(value));
      break m$2;
    }
    if (($1.$tag === "Cast")) {
      const expr = $1.$.expr;
      const ty = $1.$.ty;
      return (exprHas$87(expr) || tyHas$88(ty));
      break m$2;
    }
    if (($1.$tag === "Range")) {
      const lo = $1.$.lo;
      const hi = $1.$.hi;
      return (optHas$205(lo) || optHas$205(hi));
      break m$2;
    }
    if (($1.$tag === "Lambda")) {
      const body = $1.$.body;
      return exprHas$87(body);
      break m$2;
    }
    if ((($1.$tag === "Block") || ($1.$tag === "Unsafe"))) {
      let b;
      if (($1.$tag === "Block")) { b = $1.$; }
      else if (($1.$tag === "Unsafe")) { b = $1.$; }
      return blockHasComptime$26(b);
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const body = $1.$.body;
      return blockHasComptime$26(body);
      break m$2;
    }
    if (($1.$tag === "If")) {
      const cond = $1.$.cond;
      const then = $1.$.then;
      const otherwise = $1.$.otherwise;
      return ((exprHas$87(cond) || blockHasComptime$26(then)) || optHas$205(otherwise));
      break m$2;
    }
    if (($1.$tag === "While")) {
      const cond = $1.$.cond;
      const body = $1.$.body;
      return (exprHas$87(cond) || blockHasComptime$26(body));
      break m$2;
    }
    if (($1.$tag === "For")) {
      const iter = $1.$.iter;
      const body = $1.$.body;
      return (exprHas$87(iter) || blockHasComptime$26(body));
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const scrutinee = $1.$.scrutinee;
      const arms = $1.$.arms;
      return (exprHas$87(scrutinee) || some$207($b.slice_iter(arms), ((a) => {
  {
    let $7 = $b.Option_isSome(a.generate);
    if (!$7) {
      let $8;
      const $9 = a.pat.kind;
      m$10: {
        if ((($9.$tag === "TagAt") || ($9.$tag === "Lit"))) {
          $8 = true;
          break m$10;
        }
        if (true) {
          $8 = false;
          break m$10;
        }
        $rt.unmatched($9);
      }
      $7 = ($8 && patHas$206(a.pat));
    }
    let $11 = ($7 || exprHas$87(a.body));
    if (!$11) {
      let $12;
      const $13 = a.guard;
      m$14: {
        if (($13.$tag === "Some")) {
          const g = $13.$;
          $12 = exprHas$87(g);
          break m$14;
        }
        if (($13.$tag === "None")) {
          $12 = false;
          break m$14;
        }
        $rt.unmatched($13);
      }
      $11 = $12;
    }
    return $11;
  }
      })));
      break m$2;
    }
    if (($1.$tag === "Try")) {
      const body = $1.$.body;
      const handler = $1.$.handler;
      return (blockHasComptime$26(body) || blockHasComptime$26(handler));
      break m$2;
    }
    if (($1.$tag === "Return")) {
      const x = $1.$;
      return optHas$205(x);
      break m$2;
    }
    if (($1.$tag === "Handle")) {
      const body = $1.$.body;
      const arms = $1.$.arms;
      return (blockHasComptime$26(body) || some$208($b.slice_iter(arms), ((a) => {
  return blockHasComptime$26(a.body);
      })));
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function tyHas$88(t) {
  const $1 = t.kind;
  m$2: {
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      return some$181($b.slice_iter(fields), ((f) => {
  return (($b.Option_isSome(f.generate) || $b.Option_isSome(f.computed)) || tyHas$88(f.ty));
      }));
      break m$2;
    }
    if (($1.$tag === "Path")) {
      const args = $1.$.args;
      return some$204($b.slice_iter(args), ((a) => {
  return tyHas$88(a);
      }));
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      return some$204($b.slice_iter(ts), ((x) => {
  return tyHas$88(x);
      }));
      break m$2;
    }
    if ((($1.$tag === "Mut") || ($1.$tag === "Readonly") || ($1.$tag === "Ptr"))) {
      let x;
      if (($1.$tag === "Mut")) { x = $1.$; }
      else if (($1.$tag === "Readonly")) { x = $1.$; }
      else if (($1.$tag === "Ptr")) { x = $1.$; }
      return tyHas$88(x);
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const elem = $1.$.elem;
      return tyHas$88(elem);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function some$89(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function clone$90(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Unit")) {
      return { $tag: "Unit" };
      break m$2;
    }
    if (($1.$tag === "Bool")) {
      const x = $1.$;
      return { $tag: "Bool", $: clone$199(x) };
      break m$2;
    }
    if (($1.$tag === "Int")) {
      const x = $1.$;
      return { $tag: "Int", $: clone$209(x) };
      break m$2;
    }
    if (($1.$tag === "Str")) {
      const x = $1.$;
      return { $tag: "Str", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "List")) {
      const x = $1.$;
      return { $tag: "List", $: clone$210(x) };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const x = $1.$;
      return { $tag: "Record", $: clone$211(x) };
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const x = $1.$;
      return { $tag: "Tag", $: clone$212(x) };
      break m$2;
    }
    if (($1.$tag === "Type")) {
      const x = $1.$;
      return { $tag: "Type", $: clone$23(x) };
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const x = $1.$;
      return { $tag: "Fn", $: clone$174(x) };
      break m$2;
    }
    if (($1.$tag === "Closure")) {
      const x = $1.$;
      return { $tag: "Closure", $: clone$213(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function block$91(self, b) {
  const depth = $b.slice_len(self.v.env);
  const span = sp$214(self, $rt.copy(b.span));
  const stmts = { v: $b.Vec_new() };
  for (const $1 of $rt.items(b.stmts)) {
    const st = $1;
    const $2 = stmts;
    let $3;
    const $4 = st;
    m$5: {
      if (($4.$tag === "Let")) {
        const mutable = $4.$.mutable;
        const pat = $4.$.pat;
        const ty = $4.$.ty;
        const init = $4.$.init;
        const s = $4.$.span;
        {
          const at = sp$214(self, $rt.copy(s));
          const i = expr$215(self, init);
          let $6;
          const $7 = ty;
          m$8: {
            if (($7.$tag === "Some")) {
              const x = $7.$;
              $6 = { $tag: "Some", $: ty$216(self, x) };
              break m$8;
            }
            if (($7.$tag === "None")) {
              $6 = { $tag: "None" };
              break m$8;
            }
            $rt.unmatched($7);
          }
          const t = $6;
          const q = pattern$217(self, pat);
          $3 = { $tag: "Let", $: { mutable: mutable, pat: q, ty: t, init: i, span: $rt.copy(at) } };
        }
        break m$5;
      }
      if (($4.$tag === "Defer")) {
        const e = $4.$;
        $3 = { $tag: "Defer", $: expr$215(self, e) };
        break m$5;
      }
      if (($4.$tag === "Expr")) {
        const e = $4.$;
        $3 = { $tag: "Expr", $: expr$215(self, e) };
        break m$5;
      }
      $rt.unmatched($4);
    }
    $b.Vec_push($2, $3);
  }
  let $9;
  const $10 = b.tail;
  m$11: {
    if (($10.$tag === "Some")) {
      const t = $10.$;
      $9 = { $tag: "Some", $: $b.Box_new(expr$215(self, t)) };
      break m$11;
    }
    if (($10.$tag === "None")) {
      $9 = { $tag: "None" };
      break m$11;
    }
    $rt.unmatched($10);
  }
  const tail = $9;
  $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
  return { stmts: stmts.v, tail: tail, span: span };
}
function report$92(self, s) {
  const $1 = s;
  m$2: {
    if (($1.$tag === "CtError")) {
      const span = $1.$[0];
      const msg = $1.$[1];
      {
        const m = self.v.module;
        error$62(self.v.p, m, $rt.copy(span), $b.String_asStr(msg));
        return undefined;
      }
      break m$2;
    }
    if (true) {
      {
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$93(self) {
  {
    return { isComptime: clone$199(self.isComptime), name: clone$218(self.name), params: clone$219(self.params), ret: clone$220(self.ret), span: clone$94(self.span), typeParams: clone$179(self.typeParams), uses: clone$221(self.uses) };
  }
}
function clone$94(self) {
  {
    return { end: clone$174(self.end), start: clone$174(self.start) };
  }
}
function clone$95(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$222(x));
  }
  return v.v;
}
function clone$96(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$223(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$97(self) {
  {
    return { module: clone$174(self.module), params: clone$224(self.params), selfTy: clone$225(self.selfTy), elidedRegion: clone$226(self.elidedRegion) };
  }
}
function clone$98(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$106(x));
  }
  return v.v;
}
function clone$99(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Closed")) {
      return { $tag: "Closed" };
      break m$2;
    }
    if (($1.$tag === "Var")) {
      const x = $1.$;
      return { $tag: "Var", $: clone$77(x) };
      break m$2;
    }
    if (($1.$tag === "Param")) {
      const x = $1.$;
      return { $tag: "Param", $: clone$34(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function freshEffTail$100(self) {
  $b.Vec_push(new $rt.FieldRef(self.v, "effs"), { $tag: "None" });
  return { $tag: "Var", $: $rt.wrap_u32($rt.usize($b.slice_len(self.v.effs) - 1n)) };
}
function elabTy$101(self, t, scope) {
  const m = scope.module;
  const $1 = t.kind;
  m$2: {
    if (($1.$tag === "Spliced")) {
      const i = $1.$;
      return clone$23($rt.idx(self.v.spliced, i));
      break m$2;
    }
    if (($1.$tag === "Path")) {
      const segments = $1.$.segments;
      const args = $1.$.args;
      if (($b.slice_len(segments) === 2n)) {
        {
          const base = { kind: { $tag: "Path", $: { segments: [clone$218($rt.idx(segments, 0n))], args: $b.Vec_new() } }, span: $rt.copy($rt.idx(segments, 0n).span) };
          const b = elabTy$101(self, base, scope);
          if (($b.slice_len(args) > 0n)) {
            error$62(self, m, $rt.copy(t.span), "an associated type takes no arguments");
          }
          return { $tag: "Assoc", $: [$b.Box_new(b), $b.String_clone($rt.idx(segments, 1n).name)] };
        }
        break m$2;
      }
    }
    if (($1.$tag === "Path")) {
      const segments = $1.$.segments;
      const args = $1.$.args;
      {
        const name = $b.String_clone($rt.idx(segments, 0n).name);
        const $3 = primFromName$227($b.String_asStr(name));
        m$4: {
          if (($3.$tag === "Some")) {
            const p = $3.$;
            {
              if ((!eq$228(p, { $tag: "Type" }) || (!$b.HashMap_has($rt.idx(self.v.modules, m).scope, $b.String_asStr(name))))) {
                return { $tag: "Prim", $: p };
              }
            }
            break m$4;
          }
          if (true) {
            {
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
        if ((name === "Self")) {
          const $5 = scope.selfTy;
          m$6: {
            if (($5.$tag === "Some")) {
              const s = $5.$;
              return clone$23(s);
              break m$6;
            }
            if (($5.$tag === "None")) {
              {
                error$62(self, m, $rt.copy(t.span), "`Self` is only meaningful in an `impl` or `interface`");
                return { $tag: "Error" };
              }
              break m$6;
            }
            $rt.unmatched($5);
          }
        }
        const $7 = $b.HashMap_get(scope.params, $b.String_asStr(name));
        m$8: {
          if (($7.$tag === "Some")) {
            const sym = $7.$[0];
            const kind = $7.$[1];
            {
              if (!eq$33(kind, { $tag: "Type" })) {
                error$62(self, m, $rt.copy(t.span), $b.String_asStr(("" + "`" + name + "` is not a type")));
                return { $tag: "Error" };
              }
              return { $tag: "Param", $: clone$34(sym) };
            }
            break m$8;
          }
          if (true) {
            {
            }
            break m$8;
          }
          $rt.unmatched($7);
        }
        const found = lookup$47(self.v, m, $b.String_asStr(name));
        const $9 = found;
        m$10: {
          if (($9.$tag === "Some" && ($9.$.$tag === "Def"))) {
            const d = $9.$.$;
            {
              if (includes$229(self.v.aliasing, d)) {
                error$62(self, m, $rt.copy(t.span), $b.String_asStr(("" + "`" + name + "` refers to itself, but a type alias names a structural type, which cannot be recursive: declare it as an `enum` or a `struct` (\xc2\xa73.3)")));
                return { $tag: "Error" };
              }
              const $11 = $b.HashMap_get(self.v.pendingAliases, d);
              m$12: {
                if (($11.$tag === "Some")) {
                  const am = $11.$[0];
                  const ai = $11.$[1];
                  {
                    const aliasItem = clone$173($rt.idx($rt.idx(self.v.modules, am).ast.items, ai));
                    elaborateDef$67(self, am, aliasItem);
                  }
                  break m$12;
                }
                if (true) {
                  {
                  }
                  break m$12;
                }
                $rt.unmatched($11);
              }
            }
            break m$10;
          }
          if (true) {
            {
            }
            break m$10;
          }
          $rt.unmatched($9);
        }
        const $13 = found;
        m$14: {
          if (($13.$tag === "Some" && ($13.$.$tag === "Def"))) {
            const d = $13.$.$;
            {
              const gargs = elabArgs$190(self, d, args, scope, $rt.copy(t.span));
              const $15 = new $rt.FieldRef($rt.idx(self.v.defs, d), "kind");
              const $16 = $15.v;
              m$17: {
                if (($16.$tag === "Alias")) {
                  const ty = new $rt.FieldRef($16.$, "ty");
                  {
                    const aty = clone$23(ty.v);
                    const params = clone$73($rt.idx(self.v.defs, d).params);
                    return substParams$230(aty, params, gargs);
                  }
                  break m$17;
                }
                if ((($16.$tag === "Struct") || ($16.$tag === "Enum"))) {
                  {
                    ensureInstance$231(self, d, gargs);
                    return { $tag: "Named", $: [d, gargs] };
                  }
                  break m$17;
                }
                if (true) {
                  return { $tag: "Named", $: [d, gargs] };
                  break m$17;
                }
                $rt.unmatched($16);
              }
            }
            break m$14;
          }
          if (($13.$tag === "Some" && ($13.$.$tag === "Fn"))) {
            {
              error$62(self, m, $rt.copy(t.span), $b.String_asStr(("" + "`" + name + "` is a function, not a type")));
              return { $tag: "Error" };
            }
            break m$14;
          }
          if (($13.$tag === "Some" && ($13.$.$tag === "Const"))) {
            {
              error$62(self, m, $rt.copy(t.span), $b.String_asStr(("" + "`" + name + "` is a constant, not a type")));
              return { $tag: "Error" };
            }
            break m$14;
          }
          if (($13.$tag === "None")) {
            {
              const msg = unknown$192(self.v, "type", $b.String_asStr(name));
              error$62(self, m, $rt.copy(t.span), $b.String_asStr(msg));
              return { $tag: "Error" };
            }
            break m$14;
          }
          $rt.unmatched($13);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      const rest = $1.$.rest;
      {
        const labels = { v: $b.Vec_new() };
        for (const $18 of $rt.items(fields)) {
          const f = $18;
          const ft = elabTy$101(self, f.ty, scope);
          labelSet$184(labels, $b.String_asStr(f.name.name), ft);
        }
        let $19;
        const $20 = rest;
        m$21: {
          if (($20.$tag === "Some")) {
            const r = $20.$;
            $19 = rowTail$232(self, r, scope);
            break m$21;
          }
          if (($20.$tag === "None")) {
            $19 = { $tag: "Closed" };
            break m$21;
          }
          $rt.unmatched($20);
        }
        const tail = $19;
        return { $tag: "Record", $: { labels: labels.v, tail: tail } };
      }
      break m$2;
    }
    if (($1.$tag === "Union")) {
      const tags = $1.$.tags;
      const includes = $1.$.includes;
      const rest = $1.$.rest;
      {
        const labels = { v: $b.Vec_new() };
        for (const $22 of $rt.items(tags)) {
          const tg = $22;
          const pt = elabPayload$183(self, tg.payload, scope);
          labelSet$184(labels, $b.String_asStr(tg.name.name), pt);
        }
        for (const $23 of $rt.items(includes)) {
          const inc = $23;
          const $24 = elabTy$101(self, inc, scope);
          m$25: {
            if (($24.$tag === "Union")) {
              const r = $24.$;
              if (eq$120(r.tail, { $tag: "Closed" })) {
                {
                  for (const $26 of $rt.items(r.labels)) {
                    const k = $26[0];
                    const v = $26[1];
                    const $27 = labelGet$233(labels.v, $b.String_asStr(k));
                    m$28: {
                      if (($27.$tag === "Some")) {
                        const w = $27.$;
                        {
                          if (!eq$234(w, v)) {
                            error$62(self, m, $rt.copy(inc.span), $b.String_asStr(("" + "`#" + k + "` is in this union twice, carrying different payloads")));
                          }
                        }
                        break m$28;
                      }
                      if (true) {
                        {
                        }
                        break m$28;
                      }
                      $rt.unmatched($27);
                    }
                    labelSet$184(labels, $b.String_asStr(k), clone$23(v));
                  }
                }
                break m$25;
              }
            }
            if (($24.$tag === "Error")) {
              {
              }
              break m$25;
            }
            if (true) {
              error$62(self, m, $rt.copy(inc.span), "only a closed tag union can be part of a union: an enum is a type of its own");
              break m$25;
            }
            $rt.unmatched($24);
          }
        }
        let $29;
        const $30 = rest;
        m$31: {
          if (($30.$tag === "Some")) {
            const r = $30.$;
            $29 = rowTail$232(self, r, scope);
            break m$31;
          }
          if (($30.$tag === "None")) {
            $29 = { $tag: "Closed" };
            break m$31;
          }
          $rt.unmatched($30);
        }
        const tail = $29;
        return { $tag: "Union", $: { labels: labels.v, tail: tail } };
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $32 of $rt.items(ts)) {
          const x = $32;
          $b.Vec_push(out, elabTy$101(self, x, scope));
        }
        return { $tag: "Tuple", $: out.v };
      }
      break m$2;
    }
    if (($1.$tag === "EmptyRow")) {
      {
        error$62(self, m, $rt.copy(t.span), "`[]` is an empty effect row, not a type");
        return { $tag: "Error" };
      }
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const mode = $1.$.mode;
      const params = $1.$.params;
      const ret = $1.$.ret;
      const row = $1.$.uses;
      {
        let $33;
        const $34 = mode;
        m$35: {
          if (($34.$tag === "Shared")) {
            $33 = { $tag: "Shared" };
            break m$35;
          }
          if (($34.$tag === "Mut")) {
            $33 = { $tag: "Mut" };
            break m$35;
          }
          if (($34.$tag === "Once")) {
            $33 = { $tag: "Once" };
            break m$35;
          }
          $rt.unmatched($34);
        }
        const fmode = $33;
        const ps = { v: $b.Vec_new() };
        for (const $36 of $rt.items(params)) {
          const p = $36;
          const $37 = ps;
          let $38;
          const $39 = p.ty;
          m$40: {
            if (($39.$tag === "Some")) {
              const pt = $39.$;
              $38 = elabTy$101(self, pt, scope);
              break m$40;
            }
            if (($39.$tag === "None")) {
              $38 = { $tag: "Error" };
              break m$40;
            }
            $rt.unmatched($39);
          }
          $b.Vec_push($37, $38);
        }
        const r = elabTy$101(self, ret.ty, scope);
        let $41;
        const $42 = row;
        m$43: {
          if (($42.$tag === "Some")) {
            const u = $42.$;
            $41 = elabEffects$195(self, u, scope);
            break m$43;
          }
          if (($42.$tag === "None")) {
            $41 = pure$37();
            break m$43;
          }
          $rt.unmatched($42);
        }
        const effects = $41;
        return { $tag: "Fn", $: $b.Box_new({ mode: fmode, params: ps.v, ret: r, effects: effects }) };
      }
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const elem = $1.$.elem;
      const len = $1.$.len;
      {
        const e = elabTy$101(self, elem, scope);
        const $44 = len;
        m$45: {
          if (($44.$tag === "None")) {
            return { $tag: "Slice", $: $b.Box_new(e) };
            break m$45;
          }
          if (($44.$tag === "Some")) {
            const x = $44.$;
            return { $tag: "Array", $: [$b.Box_new(e), elabLen$235(self, x, scope)] };
            break m$45;
          }
          $rt.unmatched($44);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Mut")) {
      const inner = $1.$;
      return { $tag: "Borrow", $: [true, $b.Box_new(elabTy$101(self, inner, scope))] };
      break m$2;
    }
    if (($1.$tag === "Readonly")) {
      const inner = $1.$;
      return { $tag: "Borrow", $: [false, $b.Box_new(elabTy$101(self, inner, scope))] };
      break m$2;
    }
    if ((($1.$tag === "Ptr") || ($1.$tag === "Dyn"))) {
      {
        error$62(self, m, $rt.copy(t.span), "raw pointers and `dyn` are not supported yet");
        return { $tag: "Error" };
      }
      break m$2;
    }
    if (($1.$tag === "Expr")) {
      {
        error$62(self, m, $rt.copy(t.span), "expected a type");
        return { $tag: "Error" };
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function expr$102(self, e, expected) {
  const t = exprInner$236(self, e, expected);
  $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "exprs"), e.id, clone$23(t));
  $b.HashMap_insert(new $rt.FieldRef(self.v, "spans"), e.id, $rt.copy(e.span));
  return t;
}
function bind$103(self, pat, t) {
  const resolved = resolve$109(self.v.s, t);
  let $1;
  const $2 = resolved;
  m$3: {
    if (($2.$tag === "Borrow")) {
      const m = $2.$[0];
      const i = $2.$[1];
      $1 = [{ $tag: "Some", $: m }, clone$23($b.Box_get(i))];
      break m$3;
    }
    if (true) {
      const other = $2;
      $1 = [{ $tag: "None" }, clone$23(other)];
      break m$3;
    }
    $rt.unmatched($2);
  }
  const $4 = $1;
  const mode = $4[0];
  const inner = $4[1];
  const wrap = ((ty) => {
  const $5 = mode;
  m$6: {
    if (($5.$tag === "Some")) {
      const m = $5.$;
      let $7;
      const $8 = ty;
      m$9: {
        if (($8.$tag === "Borrow")) {
          $7 = true;
          break m$9;
        }
        if (true) {
          $7 = false;
          break m$9;
        }
        $rt.unmatched($8);
      }
      if ((!$7)) {
        return { $tag: "Borrow", $: [m, $b.Box_new(ty)] };
        break m$6;
      }
    }
    if (true) {
      return ty;
      break m$6;
    }
    $rt.unmatched($5);
  }
  });
  const $10 = pat.kind;
  m$11: {
    if (($10.$tag === "Wild")) {
      {
        return undefined;
      }
      break m$11;
    }
    if (($10.$tag === "TagAt")) {
      return err$108(self, $rt.copy(pat.span), "a computed name `[e]` belongs in code that `comptime` generates");
      break m$11;
    }
    if (($10.$tag === "Bind")) {
      const name = $10.$;
      {
        let bound = clone$23(t);
        const $12 = resolved;
        m$13: {
          if (($12.$tag === "Borrow" && $12.$[0] === false)) {
            const i = $12.$[1];
            {
              const z = zonk$134(self.v.s, i);
              let $14 = settled$151(z);
              if ($14) {
                let $15;
                const $16 = z;
                m$17: {
                  if (($16.$tag === "Param")) {
                    $15 = true;
                    break m$17;
                  }
                  if (true) {
                    $15 = false;
                    break m$17;
                  }
                  $rt.unmatched($16);
                }
                $14 = (!$15);
              }
              if (($14 && isCopy$135(self.v.p.v, z))) {
                bound = z;
              } else {
                {
                  $b.Vec_push(new $rt.FieldRef(self.v, "copyBinds"), pat.id);
                }
              }
            }
            break m$13;
          }
          if (true) {
            {
            }
            break m$13;
          }
          $rt.unmatched($12);
        }
        $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "bindings"), pat.id, clone$23(bound));
        $b.HashMap_insert(new $rt.FieldRef(self.v, "spans"), pat.id, $rt.copy(pat.span));
        declare$42(self, $b.String_asStr(name), bound);
        return undefined;
      }
      break m$11;
    }
    if (($10.$tag === "Lit")) {
      const e = $10.$;
      {
        const v = strip$124(self.v, t);
        const lt = expr$102(self, e, { $tag: "Some", $: clone$23(v) });
        if ((eq$234(resolve$109(self.v.s, lt), { $tag: "Prim", $: { $tag: "Str" } }) && lends$116(self, v, { $tag: "Prim", $: { $tag: "Str" } }))) {
          return;
        }
        if ((!tryUnify$237(self, lt, v))) {
          const a = show$123(self.v, v);
          const b = show$123(self.v, lt);
          err$108(self, $rt.copy(pat.span), $b.String_asStr(("" + "pattern of type `" + b + "` cannot match `" + a + "`")));
          return undefined;
        }
      }
      break m$11;
    }
    if (($10.$tag === "Tuple")) {
      const pats = $10.$;
      {
        let $18;
        const $19 = strip$124(self.v, inner);
        m$20: {
          if (($19.$tag === "Tuple")) {
            const ts = $19.$;
            if (($b.slice_len(ts) === $b.slice_len(pats))) {
              $18 = ts;
              break m$20;
            }
          }
          if (($19.$tag === "Array" && ($19.$[1].$tag === "Known"))) {
            const e = $19.$[0];
            const n = $19.$[1].$;
            if (($rt.wrap_usize(n) === $b.slice_len(pats))) {
              {
                const out = { v: $b.Vec_new() };
                const $21 = $b.slice_len(pats);
                for (let $22$$23 = 0n; $22$$23 < $21; $22$$23++) {
                  $b.Vec_push(out, clone$23($b.Box_get(e)));
                }
                $18 = out.v;
              }
              break m$20;
            }
          }
          if (($19.$tag === "Var")) {
            {
              const ts = { v: $b.Vec_new() };
              const $24 = $b.slice_len(pats);
              for (let $25$$26 = 0n; $25$$26 < $24; $25$$26++) {
                $b.Vec_push(ts, fresh$238(new $rt.FieldRef(self.v, "s")));
              }
              try {
                unify$239(new $rt.FieldRef(self.v, "s"), inner, { $tag: "Tuple", $: clone$35(ts.v) });
              } catch ($27) {
                if (!($27 instanceof $rt.Fail)) throw $27;
              }
              $18 = ts.v;
            }
            break m$20;
          }
          if (true) {
            const other = $19;
            {
              const shown = show$123(self.v, other);
              err$108(self, $rt.copy(pat.span), $b.String_asStr(("" + "a tuple pattern cannot match `" + shown + "`")));
              const out = { v: $b.Vec_new() };
              const $28 = $b.slice_len(pats);
              for (let $29$$30 = 0n; $29$$30 < $28; $29$$30++) {
                $b.Vec_push(out, { $tag: "Error" });
              }
              $18 = out.v;
            }
            break m$20;
          }
          $rt.unmatched($19);
        }
        const elems = $18;
        const $31 = $b.slice_len(pats);
        for (let i = 0n; i < $31; i++) {
          bind$103(self, $rt.idx(pats, i), wrap(clone$23($rt.idx(elems, i))));
        }
        return undefined;
      }
      break m$11;
    }
    if (($10.$tag === "Record")) {
      const fields = $10.$.fields;
      {
        const $32 = strip$124(self.v, inner);
        m$33: {
          if (($32.$tag === "Named")) {
            const d = $32.$[0];
            {
              unsealed$240(self, d, "taken apart", $rt.copy(pat.span));
            }
            break m$33;
          }
          if (true) {
            {
            }
            break m$33;
          }
          $rt.unmatched($32);
        }
        for (const $34 of $rt.items(fields)) {
          const name = $34[0];
          const sub = $34[1];
          const ft = field$241(self, inner, $b.String_asStr(name.name), $rt.copy(name.span));
          const $35 = sub;
          m$36: {
            if (($35.$tag === "Some")) {
              const q = $35.$;
              bind$103(self, q, wrap(ft));
              break m$36;
            }
            if (($35.$tag === "None")) {
              {
                self.v.p.v.nextId = $rt.usize(self.v.p.v.nextId + 1n);
                const q = { kind: { $tag: "Bind", $: $b.String_clone(name.name) }, span: $rt.copy(name.span), id: self.v.p.v.nextId };
                bind$103(self, q, wrap(ft));
              }
              break m$36;
            }
            $rt.unmatched($35);
          }
        }
        return undefined;
      }
      break m$11;
    }
    if (($10.$tag === "Tag")) {
      const name = $10.$.name;
      const args = $10.$.args;
      {
        let $37;
        const $38 = tagPayloads$242(self, inner);
        m$39: {
          if (($38.$tag === "Some")) {
            const tags = $38.$[0];
            const tail = $38.$[1];
            const $40 = labelGet$233(tags, $b.String_asStr(name));
            m$41: {
              if (($40.$tag === "Some")) {
                const p = $40.$;
                $37 = p;
                break m$41;
              }
              if (($40.$tag === "None")) {
                {
                  if (eq$120(tail, { $tag: "Closed" })) {
                    const shown = show$123(self.v, inner);
                    err$108(self, $rt.copy(pat.span), $b.String_asStr(("" + "`#" + name + "` is not a tag of `" + shown + "`")));
                    $37 = { $tag: "Error" };
                  } else {
                    {
                      const p = fresh$238(new $rt.FieldRef(self.v, "s"));
                      const one = { v: $b.Vec_new() };
                      labelSet$184(one, $b.String_asStr(name), clone$23(p));
                      const tl = freshRowTail$243(new $rt.FieldRef(self.v, "s"));
                      try {
                        unify$239(new $rt.FieldRef(self.v, "s"), inner, { $tag: "Union", $: { labels: one.v, tail: tl } });
                      } catch ($42) {
                        if (!($42 instanceof $rt.Fail)) throw $42;
                      }
                      $37 = p;
                    }
                  }
                }
                break m$41;
              }
              $rt.unmatched($40);
            }
            break m$39;
          }
          if (($38.$tag === "None")) {
            {
              const shown = show$123(self.v, inner);
              if (!eq$234(resolve$109(self.v.s, inner), { $tag: "Error" })) {
                err$108(self, $rt.copy(pat.span), $b.String_asStr(("" + "a tag pattern cannot match `" + shown + "`")));
              }
              $37 = { $tag: "Error" };
            }
            break m$39;
          }
          $rt.unmatched($38);
        }
        const payload = $37;
        const rp = resolve$109(self.v.s, payload);
        const $43 = args;
        m$44: {
          if (($43.$tag === "None")) {
            {
              return undefined;
            }
            break m$44;
          }
          if (($43.$tag === "Tuple")) {
            const pats = $43.$;
            {
              let $45 = ($b.slice_len(pats) === 1n);
              if ($45) {
                let $46;
                const $47 = rp;
                m$48: {
                  if (($47.$tag === "Record")) {
                    $46 = true;
                    break m$48;
                  }
                  if (true) {
                    $46 = false;
                    break m$48;
                  }
                  $rt.unmatched($47);
                }
                $45 = $46;
              }
              let $49 = $45;
              if (!$49) {
                let $50;
                const $51 = rp;
                m$52: {
                  if (($51.$tag === "Tuple")) {
                    const ts = $51.$;
                    $50 = (($b.slice_len(ts) !== 1n) && ($b.slice_len(pats) === 1n));
                    break m$52;
                  }
                  if (true) {
                    $50 = false;
                    break m$52;
                  }
                  $rt.unmatched($51);
                }
                $49 = $50;
              }
              const whole = $49;
              if (whole) {
                bind$103(self, $rt.idx(pats, 0n), wrap(clone$23(rp)));
                return undefined;
              } else {
                {
                  let $53;
                  const $54 = rp;
                  m$55: {
                    if (($54.$tag === "Tuple")) {
                      const ts = $54.$;
                      if (($b.slice_len(ts) === $b.slice_len(pats))) {
                        $53 = clone$35(ts);
                        break m$55;
                      }
                    }
                    if (($54.$tag === "Error")) {
                      {
                        const out = { v: $b.Vec_new() };
                        const $56 = $b.slice_len(pats);
                        for (let $57$$58 = 0n; $57$$58 < $56; $57$$58++) {
                          $b.Vec_push(out, { $tag: "Error" });
                        }
                        $53 = out.v;
                      }
                      break m$55;
                    }
                    if (true) {
                      const other = $54;
                      {
                        const shown = show$123(self.v, other);
                        err$108(self, $rt.copy(pat.span), $b.String_asStr(("" + "`#" + name + "` carries `" + shown + "`")));
                        const out = { v: $b.Vec_new() };
                        const $59 = $b.slice_len(pats);
                        for (let $60$$61 = 0n; $60$$61 < $59; $60$$61++) {
                          $b.Vec_push(out, { $tag: "Error" });
                        }
                        $53 = out.v;
                      }
                      break m$55;
                    }
                    $rt.unmatched($54);
                  }
                  const parts = $53;
                  const $62 = $b.slice_len(pats);
                  for (let i = 0n; i < $62; i++) {
                    bind$103(self, $rt.idx(pats, i), wrap(clone$23($rt.idx(parts, i))));
                  }
                  return undefined;
                }
              }
            }
            break m$44;
          }
          if (($43.$tag === "Record")) {
            const fields = $43.$;
            {
              for (const $63 of $rt.items(fields)) {
                const fname = $63[0];
                const sub = $63[1];
                const ft = field$241(self, payload, $b.String_asStr(fname.name), $rt.copy(fname.span));
                const $64 = sub;
                m$65: {
                  if (($64.$tag === "Some")) {
                    const q = $64.$;
                    bind$103(self, q, wrap(ft));
                    break m$65;
                  }
                  if (($64.$tag === "None")) {
                    declare$42(self, $b.String_asStr(fname.name), wrap(ft));
                    break m$65;
                  }
                  $rt.unmatched($64);
                }
              }
              return undefined;
            }
            break m$44;
          }
          $rt.unmatched($43);
        }
      }
      break m$11;
    }
    if (($10.$tag === "Or")) {
      const alts = $10.$;
      {
        for (const $66 of $rt.items(alts)) {
          const a = $66;
          bind$103(self, a, t);
        }
        return undefined;
      }
      break m$11;
    }
    $rt.unmatched($10);
  }
}
function known$104(self, name) {
  const $1 = knownDef$139(self.p.v, name);
  m$2: {
    if (($1.$tag === "Some")) {
      const d = $1.$;
      return d;
      break m$2;
    }
    if (($1.$tag === "None")) {
      return 0xffffffffn;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function expandEffs$105(self, r) {
  const effs = { v: clone$98(r.effs) };
  let tail = clone$99(r.tail);
  while (true) {
    const $1 = tail;
    m$2: {
      if (($1.$tag === "Var")) {
        const v = $1.$;
        {
          const $3 = $rt.idx(self.effs, $rt.wrap_usize(v));
          m$4: {
            if (($3.$tag === "Some")) {
              const b = $3.$;
              {
                for (const $5 of $rt.items(b.effs)) {
                  const e = $5;
                  $b.Vec_push(effs, clone$106(e));
                }
                tail = clone$99(b.tail);
              }
              break m$4;
            }
            if (($3.$tag === "None")) {
              break;
              break m$4;
            }
            $rt.unmatched($3);
          }
        }
        break m$2;
      }
      if (true) {
        break;
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  return { effs: effs.v, tail: tail };
}
function clone$106(self) {
  {
    return { def: clone$174(self.def), regions: clone$244(self.regions), args: clone$35(self.args) };
  }
}
function leaves$107(e, loops) {
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "Return")) {
      return { $tag: "Some", $: $rt.copy(e.span) };
      break m$2;
    }
    if ((($1.$tag === "Break") || ($1.$tag === "Continue"))) {
      if ((loops === 0n)) {
        return { $tag: "Some", $: $rt.copy(e.span) };
        break m$2;
      }
    }
    if (($1.$tag === "Lambda")) {
      return { $tag: "None" };
      break m$2;
    }
    if ((($1.$tag === "Block") || ($1.$tag === "Unsafe"))) {
      let b;
      if (($1.$tag === "Block")) { b = $1.$; }
      else if (($1.$tag === "Unsafe")) { b = $1.$; }
      return blockLeaves$245(b, loops);
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const body = $1.$.body;
      return blockLeaves$245(body, loops);
      break m$2;
    }
    if (($1.$tag === "If")) {
      const cond = $1.$.cond;
      const then = $1.$.then;
      const otherwise = $1.$.otherwise;
      return firstOf3$247(leaves$107(cond, loops), blockLeaves$245(then, loops), optLeaves$246(otherwise, loops));
      break m$2;
    }
    if (($1.$tag === "While")) {
      const cond = $1.$.cond;
      const body = $1.$.body;
      return firstOf3$247(leaves$107(cond, loops), blockLeaves$245(body, $rt.usize(loops + 1n)), { $tag: "None" });
      break m$2;
    }
    if (($1.$tag === "For")) {
      const iter = $1.$.iter;
      const body = $1.$.body;
      return firstOf3$247(leaves$107(iter, loops), blockLeaves$245(body, $rt.usize(loops + 1n)), { $tag: "None" });
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const scrutinee = $1.$.scrutinee;
      const arms = $1.$.arms;
      {
        const $3 = leaves$107(scrutinee, loops);
        m$4: {
          if (($3.$tag === "Some")) {
            const s = $3.$;
            {
              return { $tag: "Some", $: $rt.copy(s) };
            }
            break m$4;
          }
          if (true) {
            {
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
        for (const $5 of $rt.items(arms)) {
          const a = $5;
          const $6 = leaves$107(a.body, loops);
          m$7: {
            if (($6.$tag === "Some")) {
              const s = $6.$;
              {
                return { $tag: "Some", $: $rt.copy(s) };
              }
              break m$7;
            }
            if (true) {
              {
              }
              break m$7;
            }
            $rt.unmatched($6);
          }
        }
        return { $tag: "None" };
      }
      break m$2;
    }
    if (($1.$tag === "Try")) {
      const body = $1.$.body;
      const handler = $1.$.handler;
      return firstOf3$247(blockLeaves$245(body, loops), blockLeaves$245(handler, loops), { $tag: "None" });
      break m$2;
    }
    if (($1.$tag === "Handle")) {
      const body = $1.$.body;
      const arms = $1.$.arms;
      {
        const $8 = blockLeaves$245(body, loops);
        m$9: {
          if (($8.$tag === "Some")) {
            const s = $8.$;
            {
              return { $tag: "Some", $: $rt.copy(s) };
            }
            break m$9;
          }
          if (true) {
            {
            }
            break m$9;
          }
          $rt.unmatched($8);
        }
        for (const $10 of $rt.items(arms)) {
          const a = $10;
          const $11 = blockLeaves$245(a.body, loops);
          m$12: {
            if (($11.$tag === "Some")) {
              const s = $11.$;
              {
                return { $tag: "Some", $: $rt.copy(s) };
              }
              break m$12;
            }
            if (true) {
              {
              }
              break m$12;
            }
            $rt.unmatched($11);
          }
        }
        return { $tag: "None" };
      }
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      return leaves$107(target, loops);
      break m$2;
    }
    if (($1.$tag === "Index")) {
      const target = $1.$.target;
      const index = $1.$.index;
      return firstOf3$247(leaves$107(target, loops), leaves$107(index, loops), { $tag: "None" });
      break m$2;
    }
    if (($1.$tag === "Call")) {
      const callee = $1.$.callee;
      const args = $1.$.args;
      {
        const $13 = leaves$107(callee, loops);
        m$14: {
          if (($13.$tag === "Some")) {
            const s = $13.$;
            {
              return { $tag: "Some", $: $rt.copy(s) };
            }
            break m$14;
          }
          if (true) {
            {
            }
            break m$14;
          }
          $rt.unmatched($13);
        }
        return listLeaves$248(args, loops);
      }
      break m$2;
    }
    if (($1.$tag === "Unary")) {
      const operand = $1.$.operand;
      return leaves$107(operand, loops);
      break m$2;
    }
    if ((($1.$tag === "BorrowMut") || ($1.$tag === "Throw") || ($1.$tag === "Yield") || ($1.$tag === "Comptime"))) {
      let x;
      if (($1.$tag === "BorrowMut")) { x = $1.$; }
      else if (($1.$tag === "Throw")) { x = $1.$; }
      else if (($1.$tag === "Yield")) { x = $1.$; }
      else if (($1.$tag === "Comptime")) { x = $1.$; }
      return leaves$107(x, loops);
      break m$2;
    }
    if (($1.$tag === "Binary")) {
      const lhs = $1.$.lhs;
      const rhs = $1.$.rhs;
      return firstOf3$247(leaves$107(lhs, loops), leaves$107(rhs, loops), { $tag: "None" });
      break m$2;
    }
    if (($1.$tag === "Assign")) {
      const target = $1.$.target;
      const value = $1.$.value;
      return firstOf3$247(leaves$107(target, loops), leaves$107(value, loops), { $tag: "None" });
      break m$2;
    }
    if (($1.$tag === "Cast")) {
      const expr = $1.$.expr;
      return leaves$107(expr, loops);
      break m$2;
    }
    if (($1.$tag === "Range")) {
      const lo = $1.$.lo;
      const hi = $1.$.hi;
      return firstOf3$247(optLeaves$246(lo, loops), optLeaves$246(hi, loops), { $tag: "None" });
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const args = $1.$.args;
      const $15 = args;
      m$16: {
        if (($15.$tag === "Tuple")) {
          const items = $15.$;
          return listLeaves$248(items, loops);
          break m$16;
        }
        if (($15.$tag === "Record")) {
          const fields = $15.$;
          return initsLeave$249(fields, loops);
          break m$16;
        }
        if (($15.$tag === "None")) {
          return { $tag: "None" };
          break m$16;
        }
        $rt.unmatched($15);
      }
      break m$2;
    }
    if (($1.$tag === "List")) {
      const items = $1.$;
      return listLeaves$248(items, loops);
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      return initsLeave$249(fields, loops);
      break m$2;
    }
    if (($1.$tag === "Template")) {
      const pieces = $1.$;
      {
        for (const $17 of $rt.items(pieces)) {
          const p = $17;
          const $18 = p;
          m$19: {
            if (($18.$tag === "Expr")) {
              const x = $18.$;
              {
                const $20 = leaves$107(x, loops);
                m$21: {
                  if (($20.$tag === "Some")) {
                    const s = $20.$;
                    {
                      return { $tag: "Some", $: $rt.copy(s) };
                    }
                    break m$21;
                  }
                  if (true) {
                    {
                    }
                    break m$21;
                  }
                  $rt.unmatched($20);
                }
              }
              break m$19;
            }
            if (true) {
              {
              }
              break m$19;
            }
            $rt.unmatched($18);
          }
        }
        return { $tag: "None" };
      }
      break m$2;
    }
    if (true) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function err$108(self, span, msg) {
  const m = self.v.module;
  error$62(self.v.p, m, $rt.copy(span), msg);
  return undefined;
}
function resolve$109(self, t) {
  let t$$1 = clone$23(t);
  while (true) {
    const $2 = t$$1;
    m$3: {
      if (($2.$tag === "Var")) {
        const v = $2.$;
        {
          const $4 = $rt.idx($rt.idx(self.tys, $rt.wrap_usize(v)), 0n);
          m$5: {
            if (($4.$tag === "Some")) {
              const b = $4.$;
              {
                t$$1 = clone$23(b);
              }
              break m$5;
            }
            if (($4.$tag === "None")) {
              return t$$1;
              break m$5;
            }
            $rt.unmatched($4);
          }
        }
        break m$3;
      }
      if (true) {
        break;
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return t$$1;
}
function isNever$110(t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Prim" && ($1.$.$tag === "Never"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function neverTy$111() {
  return { $tag: "Prim", $: { $tag: "Never" } };
}
function voidTy$112() {
  return { $tag: "Prim", $: { $tag: "Void" } };
}
function normalize$113(self, t) {
  const $1 = resolve$109(self.s, t);
  m$2: {
    if (($1.$tag === "Assoc")) {
      const base = $1.$[0];
      const name = $1.$[1];
      {
        const b = resolve$109(self.s, base);
        const known = zonk$134(self.s, b);
        const $3 = assocType$250(self.p.v, known, $b.String_asStr(name));
        m$4: {
          if (($3.$tag === "Some")) {
            const x = $3.$;
            {
              return normalize$113(self, x);
            }
            break m$4;
          }
          if (true) {
            {
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
        return { $tag: "Assoc", $: [$b.Box_new(b), name] };
      }
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      {
        const params = { v: $b.Vec_new() };
        for (const $5 of $rt.items(f.params)) {
          const x = $5;
          $b.Vec_push(params, normalize$113(self, x));
        }
        return { $tag: "Fn", $: $b.Box_new({ mode: f.mode, params: params.v, ret: normalize$113(self, f.ret), effects: clone$40(f.effects) }) };
      }
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const inner = $1.$[1];
      const $6 = normalize$113(self, inner);
      m$7: {
        if (($6.$tag === "Borrow")) {
          const m2 = $6.$[0];
          const x = $6.$[1];
          return { $tag: "Borrow", $: [(m && m2), x] };
          break m$7;
        }
        if (true) {
          const x = $6;
          return { $tag: "Borrow", $: [m, $b.Box_new(x)] };
          break m$7;
        }
        $rt.unmatched($6);
      }
      break m$2;
    }
    if (true) {
      const other = $1;
      return other;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$114(self) {
  {
    return { tys: clone$251(self.tys), rows: clone$252(self.rows), effs: clone$253(self.effs), regions: clone$254(self.regions), lens: clone$255(self.lens) };
  }
}
function unifies$115(self, a, b) {
  try {
    unify$239(new $rt.FieldRef(self.v, "s"), a, b);
    return true;
  } catch ($1) {
    if (!($1 instanceof $rt.Fail)) throw $1;
    return false;
  }
}
function lends$116(self, found, expected) {
  if (tryUnify$237(self, found, expected)) {
    return true;
  }
  const f = normalize$113(self.v, resolve$109(self.v.s, found));
  const x = normalize$113(self.v, resolve$109(self.v.s, expected));
  if (isNever$110(f)) {
    return true;
  }
  const snap = clone$114(self.v.s);
  let $1;
  const $2 = [clone$23(f), clone$23(x)];
  m$3: {
    if ((($2[0].$tag === "Fn") && ($2[1].$tag === "Fn"))) {
      const ff = $2[0].$;
      const xf = $2[1].$;
      if (($b.slice_len(ff.params) === $b.slice_len(xf.params))) {
        {
          let all = true;
          const $4 = $b.slice_len(ff.params);
          for (let i = 0n; i < $4; i++) {
            if ((!(unifies$115(self, $rt.idx(ff.params, i), $rt.idx(xf.params, i)) || lends$116(self, $rt.idx(xf.params, i), $rt.idx(ff.params, i))))) {
              all = false;
              break;
            }
          }
          let $5 = (all && lends$116(self, ff.ret, xf.ret));
          if ($5) {
            let $6;
            try {
              effSub$117(new $rt.FieldRef(self.v, "s"), ff.effects, xf.effects);
              $6 = true;
            } catch ($7) {
              if (!($7 instanceof $rt.Fail)) throw $7;
              $6 = false;
            }
            $5 = $6;
          }
          $1 = $5;
        }
        break m$3;
      }
    }
    if ((($2[0].$tag === "Borrow") && ($2[1].$tag === "Borrow"))) {
      const fm = $2[0].$[0];
      const fi = $2[0].$[1];
      const xm = $2[1].$[0];
      const xi = $2[1].$[1];
      if ((fm || (!xm))) {
        $1 = lends$116(self, fi, xi);
        break m$3;
      }
    }
    if ((($2[0].$tag === "Borrow"))) {
      const fi = $2[0].$[1];
      {
        const r = lends$116(self, fi, x);
        let $8 = r;
        if ($8) {
          let $9;
          const $10 = x;
          m$11: {
            if ((($10.$tag === "Prim" && ($10.$.$tag === "Str")) || ($10.$tag === "Slice"))) {
              $9 = true;
              break m$11;
            }
            if (true) {
              $9 = false;
              break m$11;
            }
            $rt.unmatched($10);
          }
          $8 = (!$9);
        }
        if ($8) {
          $b.Vec_push(new $rt.FieldRef(self.v, "pendingCopy"), clone$23($b.Box_get(fi)));
        }
        $1 = r;
      }
      break m$3;
    }
    if ((($2[0].$tag === "Named") && ($2[1].$tag === "Borrow" && $2[1].$[0] === true))) {
      const d = $2[0].$[0];
      if (((d === known$104(self.v, "Ref")) || (d === known$104(self.v, "Arc")))) {
        $1 = false;
        break m$3;
      }
    }
    if ((($2[1].$tag === "Borrow"))) {
      const xi = $2[1].$[1];
      $1 = lends$116(self, f, xi);
      break m$3;
    }
    if ((($2[0].$tag === "Named"))) {
      const d = $2[0].$[0];
      const args = $2[0].$[1];
      if ((((d === known$104(self.v, "Ref")) || (d === known$104(self.v, "Box"))) || (d === known$104(self.v, "Arc")))) {
        {
          const $12 = last$256(args);
          m$13: {
            if (($12.$tag === "Some" && ($12.$.$tag === "Ty"))) {
              const inner = $12.$.$;
              $1 = lends$116(self, inner, x);
              break m$13;
            }
            if (true) {
              $1 = false;
              break m$13;
            }
            $rt.unmatched($12);
          }
        }
        break m$3;
      }
    }
    if ((($2[0].$tag === "Named") && ($2[1].$tag === "Prim" && ($2[1].$.$tag === "Str")))) {
      const d = $2[0].$[0];
      $1 = (d === known$104(self.v, "String"));
      break m$3;
    }
    if ((($2[0].$tag === "Tuple") && ($2[1].$tag === "Tuple"))) {
      const fs = $2[0].$;
      const xs = $2[1].$;
      if (($b.slice_len(fs) === $b.slice_len(xs))) {
        {
          let all = true;
          const $14 = $b.slice_len(fs);
          for (let i = 0n; i < $14; i++) {
            if ((!lends$116(self, $rt.idx(fs, i), $rt.idx(xs, i)))) {
              all = false;
              break;
            }
          }
          $1 = all;
        }
        break m$3;
      }
    }
    if ((($2[0].$tag === "Array") && ($2[1].$tag === "Slice"))) {
      const e = $2[0].$[0];
      const xe = $2[1].$;
      $1 = unifies$115(self, e, xe);
      break m$3;
    }
    if ((($2[0].$tag === "Union") && ($2[1].$tag === "Union"))) {
      const r = $2[0].$;
      if (eq$120(expandRow$125(self.v.s, r).tail, { $tag: "Closed" })) {
        try {
          unionSub$257(new $rt.FieldRef(self.v, "s"), f, x);
          $1 = true;
        } catch ($15) {
          if (!($15 instanceof $rt.Fail)) throw $15;
          $1 = false;
        }
        break m$3;
      }
    }
    if ((($2[0].$tag === "Named") && ($2[1].$tag === "Slice"))) {
      const d = $2[0].$[0];
      const args = $2[0].$[1];
      const xe = $2[1].$;
      if ((d === known$104(self.v, "Vec"))) {
        const $16 = first$258(args);
        m$17: {
          if (($16.$tag === "Some" && ($16.$.$tag === "Ty"))) {
            const e = $16.$.$;
            $1 = unifies$115(self, e, xe);
            break m$17;
          }
          if (true) {
            $1 = false;
            break m$17;
          }
          $rt.unmatched($16);
        }
        break m$3;
      }
    }
    if (true) {
      $1 = false;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const ok = $1;
  if ((!ok)) {
    restore$122(new $rt.FieldRef(self.v, "s"), snap);
  }
  return ok;
}
function effSub$117(self, actual, allowed) {
  const act = expandEffs$105(self.v, actual);
  for (const $1 of $rt.items(act.effs)) {
    const eff = $1;
    const row = expandEffs$105(self.v, allowed);
    let candidate = { $tag: "None" };
    for (const $2 of $rt.items(row.effs)) {
      const c = $2;
      if (((c.def === eff.def) && regionsEqual$259(self.v, c.regions, eff.regions))) {
        candidate = { $tag: "Some", $: clone$106(c) };
        break;
      }
    }
    if (isNone$260(candidate)) {
      for (const $3 of $rt.items(row.effs)) {
        const c = $3;
        if (((c.def === eff.def) && regionsUnify$261(self.v, c.regions, eff.regions))) {
          candidate = { $tag: "Some", $: clone$106(c) };
          break;
        }
      }
    }
    const $4 = candidate;
    m$5: {
      if (($4.$tag === "Some")) {
        const c = $4.$;
        {
          try {
            const $6 = min$146($b.slice_len(c.regions), $b.slice_len(eff.regions));
            for (let i = 0n; i < $6; i++) {
              unifyRegion$132(self, $rt.idx(c.regions, i), $rt.idx(eff.regions, i));
            }
            const $7 = min$146($b.slice_len(eff.args), $b.slice_len(c.args));
            for (let i = 0n; i < $7; i++) {
              let $8;
              const $9 = [resolve$109(self.v, $rt.idx(eff.args, i)), resolve$109(self.v, $rt.idx(c.args, i))];
              m$10: {
                if ((($9[0].$tag === "Union") && ($9[1].$tag === "Union"))) {
                  $8 = true;
                  break m$10;
                }
                if (true) {
                  $8 = false;
                  break m$10;
                }
                $rt.unmatched($9);
              }
              const unions = $8;
              if (unions) {
                unionSub$257(self, $rt.idx(eff.args, i), $rt.idx(c.args, i));
              } else {
                {
                  unify$239(self, $rt.idx(eff.args, i), $rt.idx(c.args, i));
                }
              }
            }
          } catch ($11) {
            if (!($11 instanceof $rt.Fail)) throw $11;
            throw new $rt.Fail({ $tag: "Misfit", $: clone$106(eff) });
          }
        }
        break m$5;
      }
      if (($4.$tag === "None")) {
        const $12 = row.tail;
        m$13: {
          if (($12.$tag === "Var")) {
            const v = $12.$;
            {
              const rest = freshEffTail$100(self);
              const one = { v: $b.Vec_new() };
              $b.Vec_push(one, clone$106(eff));
              const $14 = self.v.effs;
              $14[$rt.at($14, $rt.wrap_usize(v))] = { $tag: "Some", $: { effs: one.v, tail: rest } };
            }
            break m$13;
          }
          if (true) {
            throw new $rt.Fail({ $tag: "Misfit", $: clone$106(eff) });
            break m$13;
          }
          $rt.unmatched($12);
        }
        break m$5;
      }
      $rt.unmatched($4);
    }
  }
  const row = expandEffs$105(self.v, allowed);
  const $15 = [clone$99(act.tail), clone$99(row.tail)];
  m$16: {
    if ((($15[0].$tag === "Var") && ($15[1].$tag === "Var"))) {
      const x = $15[0].$;
      const y = $15[1].$;
      if ((x === y)) {
        {
          return undefined;
        }
        break m$16;
      }
    }
    if ((($15[0].$tag === "Var"))) {
      const v = $15[0].$;
      const t = $15[1];
      {
        const $17 = self.v.effs;
        $17[$rt.at($17, $rt.wrap_usize(v))] = { $tag: "Some", $: { effs: $b.Vec_new(), tail: clone$99(t) } };
        return undefined;
      }
      break m$16;
    }
    if ((($15[0].$tag === "Closed"))) {
      {
        return undefined;
      }
      break m$16;
    }
    if ((($15[0].$tag === "Param") && ($15[1].$tag === "Param"))) {
      const p = $15[0].$;
      const q = $15[1].$;
      if (eq$262(p, q)) {
        {
          return undefined;
        }
        break m$16;
      }
    }
    if ((($15[0].$tag === "Param") && ($15[1].$tag === "Var"))) {
      const v = $15[1].$;
      {
        const $18 = self.v.effs;
        $18[$rt.at($18, $rt.wrap_usize(v))] = { $tag: "Some", $: { effs: $b.Vec_new(), tail: clone$99(act.tail) } };
        return undefined;
      }
      break m$16;
    }
    if ((($15[0].$tag === "Param"))) {
      const p = $15[0].$;
      {
        const args = { v: $b.Vec_new() };
        $b.Vec_push(args, { $tag: "Param", $: clone$34(p) });
        throw new $rt.Fail({ $tag: "Misfit", $: { def: 0xffffffffn, regions: $b.Vec_new(), args: args.v } });
        return undefined;
      }
      break m$16;
    }
    $rt.unmatched($15);
  }
}
function showEff$118(self, e) {
  if ((e.def === 0xffffffffn)) {
    let $1;
    const $2 = first$263(e.args);
    m$3: {
      if (($2.$tag === "Some")) {
        const t = $2.$;
        $1 = show$123(self, t);
        break m$3;
      }
      if (($2.$tag === "None")) {
        $1 = $b.String_new();
        break m$3;
      }
      $rt.unmatched($2);
    }
    return ("" + "the effects `..." + $1 + "`");
  }
  const regions = { v: $b.Vec_new() };
  for (const $4 of $rt.items(e.regions)) {
    const r = $4;
    $b.Vec_push(regions, resolveRegion$130(self.s, r));
  }
  const args = { v: $b.Vec_new() };
  for (const $5 of $rt.items(e.args)) {
    const t = $5;
    $b.Vec_push(args, zonk$134(self.s, t));
  }
  const out = { v: $b.String_new() };
  writeEff$265({ def: e.def, regions: regions.v, args: args.v }, defNames$264(self.p.v), out);
  return ("" + "`" + out.v + "`");
}
function zonkEffs$119(self, r) {
  const e = expandEffs$105(self, r);
  const effs = { v: $b.Vec_new() };
  for (const $1 of $rt.items(e.effs)) {
    const x = $1;
    const regions = { v: $b.Vec_new() };
    for (const $2 of $rt.items(x.regions)) {
      const g = $2;
      $b.Vec_push(regions, resolveRegion$130(self, g));
    }
    const args = { v: $b.Vec_new() };
    for (const $3 of $rt.items(x.args)) {
      const t = $3;
      $b.Vec_push(args, zonk$134(self, t));
    }
    $b.Vec_push(effs, { def: x.def, regions: regions.v, args: args.v });
  }
  return { effs: effs.v, tail: e.tail };
}
function eq$120(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Closed") && ($1[1].$tag === "Closed"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Var") && ($1[1].$tag === "Var"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$266(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Param") && ($1[1].$tag === "Param"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$262(a, b);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function showEffs$121(self, r) {
  const out = { v: $b.String_new() };
  writeEffs$267(r, defNames$264(self.p.v), out);
  return out.v;
}
function restore$122(self, s) {
  self.v.tys = s.tys;
  self.v.rows = s.rows;
  self.v.effs = s.effs;
  self.v.regions = s.regions;
  self.v.lens = s.lens;
  return undefined;
}
function show$123(self, t) {
  return show$136(self.p.v, zonk$134(self.s, t));
}
function strip$124(self, t) {
  let x = resolve$109(self.s, t);
  while (true) {
    const $1 = x;
    m$2: {
      if (($1.$tag === "Borrow")) {
        const inner = $1.$[1];
        {
          x = resolve$109(self.s, inner);
        }
        break m$2;
      }
      if (($1.$tag === "Named")) {
        const d = $1.$[0];
        const args = $1.$[1];
        if ((d === known$104(self, "Ref"))) {
          const $3 = get$137(args, 1n);
          m$4: {
            if (($3.$tag === "Some" && ($3.$.$tag === "Ty"))) {
              const inner = $3.$.$;
              {
                x = resolve$109(self.s, inner);
              }
              break m$4;
            }
            if (true) {
              return x;
              break m$4;
            }
            $rt.unmatched($3);
          }
          break m$2;
        }
      }
      if (true) {
        return normalize$113(self, x);
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  return x;
}
function expandRow$125(self, r) {
  const labels = { v: clone$74(r.labels) };
  let tail = clone$99(r.tail);
  while (true) {
    const $1 = tail;
    m$2: {
      if (($1.$tag === "Var")) {
        const v = $1.$;
        {
          const $3 = $rt.idx(self.rows, $rt.wrap_usize(v));
          m$4: {
            if (($3.$tag === "Some")) {
              const b = $3.$;
              {
                for (const $5 of $rt.items(b.labels)) {
                  const k = $5[0];
                  const t = $5[1];
                  labelSet$184(labels, $b.String_asStr(k), clone$23(t));
                }
                tail = clone$99(b.tail);
              }
              break m$4;
            }
            if (($3.$tag === "None")) {
              break;
              break m$4;
            }
            $rt.unmatched($3);
          }
        }
        break m$2;
      }
      if (true) {
        break;
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  return { labels: labels.v, tail: tail };
}
function labelHas$126(labels, k) {
  return $b.Option_isSome(labelIndex$268(labels, k));
}
function every$127(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if ((!test(x))) {
      return false;
    }
  }
  return true;
}
function enumHint$128(self, found, expected) {
  let $1;
  const $2 = [strip$124(self, found), strip$124(self, expected)];
  m$3: {
    if ((($2[0].$tag === "Union") && ($2[1].$tag === "Named"))) {
      const r = $2[0].$;
      const d = $2[1].$[0];
      $1 = [r, d];
      break m$3;
    }
    if (true) {
      return { $tag: "None" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const $4 = $1;
  const r = $4[0];
  const d = $4[1];
  let $5;
  const $6 = $rt.idx(self.p.v.defs, d).kind;
  m$7: {
    if (($6.$tag === "Enum")) {
      const tags = $6.$.tags;
      $5 = clone$74(tags);
      break m$7;
    }
    if (true) {
      return { $tag: "None" };
      break m$7;
    }
    $rt.unmatched($6);
  }
  const tags = $5;
  const e = expandRow$125(self.s, r);
  if ((!every$127($b.slice_iter(e.labels), (($0$$8) => {
  {
    const $9 = $0$$8;
    const k = $9[0];
    return labelHas$126(tags, $b.String_asStr(k));
  }
  })))) {
    return { $tag: "None" };
  }
  const n = $b.String_clone($rt.idx(self.p.v.defs, d).name);
  return { $tag: "Some", $: ("" + ": tags built where no type was expected are a union, not a `" + n + "`; give the binding the type `" + n + "` (`const e: " + n + " = \xe2\x80\xa6`) so they are built as one") };
}
function defaultLiterals$129(self) {
  const $1 = $b.slice_len(self.v.tys);
  for (let i = 0n; i < $1; i++) {
    if (isNone$269($rt.idx($rt.idx(self.v.tys, i), 0n))) {
      const $2 = $rt.indexRef($rt.idx(self.v.tys, i), 1n);
      const $3 = $2.v;
      m$4: {
        if (($3.$tag === "Int")) {
          {
            const $5 = $rt.idx(self.v.tys, i);
            $5[$rt.at($5, 0n)] = { $tag: "Some", $: { $tag: "Prim", $: { $tag: "I32" } } };
          }
          break m$4;
        }
        if (($3.$tag === "Float")) {
          {
            const $6 = $rt.idx(self.v.tys, i);
            $6[$rt.at($6, 0n)] = { $tag: "Some", $: { $tag: "Prim", $: { $tag: "F64" } } };
          }
          break m$4;
        }
        if (($3.$tag === "Any")) {
          {
          }
          break m$4;
        }
        $rt.unmatched($3);
      }
    }
  }
  return undefined;
}
function resolveRegion$130(self, r) {
  return resolveRegionIn$270(self.regions, r);
}
function first$131(self) {
  if (($b.slice_len(self) === 0n)) {
    return { $tag: "None" };
  } else {
    {
      return { $tag: "Some", $: $rt.idx(self, 0n) };
    }
  }
}
function unifyRegion$132(self, a, b) {
  unifyRegionIn$271(new $rt.FieldRef(self.v, "regions"), a, b);
  return undefined;
}
function exhaustive$133(self, scrut, arms, span) {
  const st = strip$124(self.v, scrut);
  const $1 = tagPayloads$242(self, st);
  m$2: {
    if (($1.$tag === "Some" && (($1.$[1].$tag === "Var")))) {
      {
        closeUnion$272(new $rt.FieldRef(self.v, "s"), st);
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const unguarded = { v: $b.Vec_new() };
  for (const $3 of $rt.items(arms)) {
    const a = $3;
    if (isNone$273(a.guard)) {
      $b.Vec_push(unguarded, clone$274(a.pat));
    }
  }
  const $4 = tagPayloads$242(self, st);
  m$5: {
    if (($4.$tag === "Some" && (($4.$[1].$tag === "Param")))) {
      {
        if ((!some$275($b.slice_iter(unguarded.v), ((p) => {
  const $6 = p.kind;
  m$7: {
    if ((($6.$tag === "Wild") || ($6.$tag === "Bind"))) {
      return true;
      break m$7;
    }
    if (true) {
      return false;
      break m$7;
    }
    $rt.unmatched($6);
  }
        })))) {
          const shown = show$123(self.v, st);
          err$108(self, $rt.copy(span), $b.String_asStr(("" + "this `match` needs a `_` arm: `" + shown + "` may hold more tags")));
          return;
        }
      }
      break m$5;
    }
    if (true) {
      {
      }
      break m$5;
    }
    $rt.unmatched($4);
  }
  const rows = { v: $b.Vec_new() };
  for (const $8 of $rt.items(unguarded.v)) {
    const p = $8;
    $b.Vec_push(rows, [lowerPat$276(self, p, st)]);
  }
  const $9 = missing$277(self, rows.v, [clone$23(st)]);
  m$10: {
    if (($9.$tag === "Some")) {
      const w = $9.$;
      {
        const shown = showWitness$278($rt.idx(w, 0n));
        if (eq$234(st, boolTy$189())) {
          err$108(self, $rt.copy(span), "this `match` does not cover every case of `bool`");
          return undefined;
        } else {
          if ((shown === "_")) {
            err$108(self, $rt.copy(span), "this `match` needs a `_` arm to be exhaustive");
            return undefined;
          } else {
            {
              err$108(self, $rt.copy(span), $b.String_asStr(("" + "this `match` does not handle `" + shown + "`")));
              return undefined;
            }
          }
        }
      }
      break m$10;
    }
    if (true) {
      {
        return undefined;
      }
      break m$10;
    }
    $rt.unmatched($9);
  }
}
function zonk$134(self, t) {
  const $1 = resolve$109(self, t);
  m$2: {
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        const out = { v: $b.Vec_new() };
        for (const $3 of $rt.items(args)) {
          const a = $3;
          $b.Vec_push(out, zonkArg$145(self, a));
        }
        return { $tag: "Named", $: [d, out.v] };
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const r = $1.$;
      return { $tag: "Record", $: zonkRow$279(self, r) };
      break m$2;
    }
    if (($1.$tag === "Union")) {
      const r = $1.$;
      return { $tag: "Union", $: zonkRow$279(self, r) };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $4 of $rt.items(ts)) {
          const x = $4;
          $b.Vec_push(out, zonk$134(self, x));
        }
        if ((($b.slice_len(out.v) === 1n) && eq$234($rt.idx(out.v, 0n), voidTy$112()))) {
          return voidTy$112();
        } else {
          {
            return { $tag: "Tuple", $: out.v };
          }
        }
      }
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const e = $1.$[0];
      const l = $1.$[1];
      return { $tag: "Array", $: [$b.Box_new(zonk$134(self, e)), resolveLen$280(self, l)] };
      break m$2;
    }
    if (($1.$tag === "Slice")) {
      const e = $1.$;
      return { $tag: "Slice", $: $b.Box_new(zonk$134(self, e)) };
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const e = $1.$[1];
      return { $tag: "Borrow", $: [m, $b.Box_new(zonk$134(self, e))] };
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      {
        const params = { v: $b.Vec_new() };
        for (const $5 of $rt.items(f.params)) {
          const p = $5;
          $b.Vec_push(params, zonk$134(self, p));
        }
        return { $tag: "Fn", $: $b.Box_new({ mode: f.mode, params: params.v, ret: zonk$134(self, f.ret), effects: zonkEffs$119(self, f.effects) }) };
      }
      break m$2;
    }
    if (($1.$tag === "Assoc")) {
      const base = $1.$[0];
      const n = $1.$[1];
      return { $tag: "Assoc", $: [$b.Box_new(zonk$134(self, base)), n] };
      break m$2;
    }
    if (true) {
      const other = $1;
      return other;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function isCopy$135(self, t) {
  const seen = { v: new$$281() };
  return copyIn$282(self, t, seen);
}
function show$136(self, t) {
  return showTy$283(t, defNames$264(self));
}
function get$137(self, i) {
  if ((i < $b.slice_len(self))) {
    return { $tag: "Some", $: $rt.idx(self, i) };
  } else {
    {
      return { $tag: "None" };
    }
  }
}
function closeRows$138(self, t) {
  const $1 = resolve$109(self.v, t);
  m$2: {
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      {
        const e = expandRow$125(self.v, r);
        const $3 = e.tail;
        m$4: {
          if (($3.$tag === "Var")) {
            {
              try {
                bindRowTail$284(self, e.tail, $b.Vec_new(), { $tag: "Closed" });
              } catch ($5) {
                if (!($5 instanceof $rt.Fail)) throw $5;
              }
            }
            break m$4;
          }
          if (true) {
            {
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
        for (const $6 of $rt.items(e.labels)) {
          const x = $6[1];
          closeRows$138(self, x);
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const args = $1.$[1];
      {
        for (const $7 of $rt.items(args)) {
          const a = $7;
          const $8 = a;
          m$9: {
            if (($8.$tag === "Ty")) {
              const x = $8.$;
              {
                closeRows$138(self, x);
              }
              break m$9;
            }
            if (true) {
              {
              }
              break m$9;
            }
            $rt.unmatched($8);
          }
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        for (const $10 of $rt.items(ts)) {
          const x = $10;
          closeRows$138(self, x);
        }
        return undefined;
      }
      break m$2;
    }
    if ((($1.$tag === "Array") || ($1.$tag === "Slice") || ($1.$tag === "Borrow"))) {
      let x;
      if (($1.$tag === "Array")) { x = $1.$[0]; }
      else if (($1.$tag === "Slice")) { x = $1.$; }
      else if (($1.$tag === "Borrow")) { x = $1.$[1]; }
      return closeRows$138(self, x);
      break m$2;
    }
    if (true) {
      {
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function knownDef$139(self, name) {
  const $1 = $b.HashMap_get(self.known, name);
  m$2: {
    if (($1.$tag === "Some")) {
      const d = $1.$;
      return { $tag: "Some", $: d };
      break m$2;
    }
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$140(self) {
  const m = { v: $b.HashMap_new() };
  const $1 = $b.Gen_each($b.HashMap_entries(self));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const k = $4[0];
    const v = $4[1];
    $b.HashMap_insert(m, clone$77(k), clone$35(v));
  }
  return m.v;
}
function satisfies$141(self, ty, bound, assumed) {
  return satisfiesDepth$285(self, ty, bound, assumed, 0n);
}
function ifaceClosure$142(self, iface) {
  const out = { v: [iface] };
  let i = 0n;
  while ((i < $b.slice_len(out.v))) {
    const $1 = $rt.idx(self.defs, $rt.idx(out.v, i)).kind;
    m$2: {
      if (($1.$tag === "Interface")) {
        const supers = $1.$.supers;
        {
          for (const $3 of $rt.items(supers)) {
            const e = $3;
            const $4 = e;
            m$5: {
              if (($4.$tag === "Named")) {
                const d = $4.$[0];
                {
                  if ((!includes$229(out.v, d))) {
                    $b.Vec_push(out, d);
                  }
                }
                break m$5;
              }
              if (true) {
                {
                }
                break m$5;
              }
              $rt.unmatched($4);
            }
          }
        }
        break m$2;
      }
      if (true) {
        {
        }
        break m$2;
      }
      $rt.unmatched($1);
    }
    i = $rt.usize(i + 1n);
  }
  return out.v;
}
function deriveRequest$143(self, iface, d) {
  return some$286($b.slice_iter(self.impls), ((r) => {
  let $1 = r.derived;
  if ($1) {
    let $2;
    const $3 = r.iface;
    m$4: {
      if (($3.$tag === "Some")) {
        const i = $3.$[0];
        $2 = (i === iface);
        break m$4;
      }
      if (($3.$tag === "None")) {
        $2 = false;
        break m$4;
      }
      $rt.unmatched($3);
    }
    $1 = $2;
  }
  let $5 = $1;
  if ($5) {
    let $6;
    const $7 = r.target;
    m$8: {
      if (($7.$tag === "Named")) {
        const x = $7.$[0];
        $6 = (x === d);
        break m$8;
      }
      if (true) {
        $6 = false;
        break m$8;
      }
      $rt.unmatched($7);
    }
    $5 = $6;
  }
  return $5;
  }));
}
function ensureImpl$144(self, iface, ty, depth) {
  if (((depth > 16n) || containsParams$148(ty))) {
    return;
  }
  let $1;
  const $2 = resolveImpl$287(self.v, iface, ty);
  m$3: {
    if (($2.$tag === "Some")) {
      const r = $2.$;
      $1 = r;
      break m$3;
    }
    if (($2.$tag === "None")) {
      return;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const $4 = $1;
  const imp = $4[0];
  const binds = $4[1];
  if (isTemplateImpl$288(self.v, imp)) {
    const names = { v: $b.Vec_new() };
    for (const $5 of $rt.items($rt.idx(self.v.impls, imp).methods)) {
      const f = $5;
      $b.Vec_push(names, $b.String_clone($rt.idx(self.v.fns, f).name));
    }
    for (const $6 of $rt.items(names.v)) {
      const n = $6;
      methodForMut$289(self, imp, $b.String_asStr(n), binds);
    }
  }
  const params = clone$73($rt.idx(self.v.impls, imp).params);
  const args = { v: $b.Vec_new() };
  for (const $7 of $rt.items(params)) {
    const g = $7;
    const $8 = args;
    let $9;
    const $10 = $b.HashMap_get(binds, g.sym.id);
    m$11: {
      if (($10.$tag === "Some")) {
        const a = $10.$;
        $9 = clone$290(a);
        break m$11;
      }
      if (($10.$tag === "None")) {
        $9 = paramArg$291(g);
        break m$11;
      }
      $rt.unmatched($10);
    }
    $b.Vec_push($8, $9);
  }
  const $12 = $b.slice_len(params);
  for (let k = 0n; k < $12; k++) {
    const $13 = $rt.idx(args.v, k);
    m$14: {
      if (($13.$tag === "Ty")) {
        const t = $13.$;
        {
          for (const $15 of $rt.items($rt.idx(params, k).bounds)) {
            const b = $15;
            const $16 = substParams$230(b, params, args.v);
            m$17: {
              if (($16.$tag === "Named")) {
                const d = $16.$[0];
                {
                  let $18;
                  const $19 = new $rt.FieldRef($rt.idx(self.v.defs, d), "kind");
                  const $20 = $19.v;
                  m$21: {
                    if (($20.$tag === "Interface")) {
                      $18 = true;
                      break m$21;
                    }
                    if (true) {
                      $18 = false;
                      break m$21;
                    }
                    $rt.unmatched($20);
                  }
                  if ($18) {
                    ensureImpl$144(self, d, t, $rt.usize(depth + 1n));
                  }
                }
                break m$17;
              }
              if (true) {
                {
                }
                break m$17;
              }
              $rt.unmatched($16);
            }
          }
        }
        break m$14;
      }
      if (true) {
        {
        }
        break m$14;
      }
      $rt.unmatched($13);
    }
  }
  return undefined;
}
function zonkArg$145(self, a) {
  const $1 = a;
  m$2: {
    if (($1.$tag === "Ty")) {
      const t = $1.$;
      return { $tag: "Ty", $: zonk$134(self, t) };
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const r = $1.$;
      return { $tag: "Region", $: resolveRegion$130(self, r) };
      break m$2;
    }
    if (($1.$tag === "Row")) {
      const r = $1.$;
      return { $tag: "Row", $: zonkEffs$119(self, r) };
      break m$2;
    }
    if (($1.$tag === "Len")) {
      const l = $1.$;
      return { $tag: "Len", $: resolveLen$280(self, l) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function min$146(a, b) {
  if ((b < a)) {
    return b;
  } else {
    {
      return a;
    }
  }
}
function comptimeArgs$147(self, fid, args) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items($rt.idx(self.fns, fid).scheme.tparams)) {
    const g = $1;
    if (g.isComptime) {
      const $2 = $b.HashMap_get(args, g.sym.id);
      m$3: {
        if (($2.$tag === "Some" && ($2.$.$tag === "Ty"))) {
          const t = $2.$.$;
          $b.Vec_push(out, [clone$34(g.sym), clone$23(t)]);
          break m$3;
        }
        if (true) {
          return { $tag: "None" };
          break m$3;
        }
        $rt.unmatched($2);
      }
    }
  }
  return { $tag: "Some", $: out.v };
}
function containsParams$148(t) {
  const $1 = t;
  m$2: {
    if ((($1.$tag === "Param") || ($1.$tag === "Var"))) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const args = $1.$[1];
      return some$292($b.slice_iter(args), ((a) => {
  const $3 = a;
  m$4: {
    if (($3.$tag === "Ty")) {
      const x = $3.$;
      return containsParams$148(x);
      break m$4;
    }
    if (true) {
      return false;
      break m$4;
    }
    $rt.unmatched($3);
  }
      }));
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      return some$293($b.slice_iter(ts), ((x) => {
  return containsParams$148(x);
      }));
      break m$2;
    }
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      return some$294($b.slice_iter(r.labels), (($0$$5) => {
  {
    const $6 = $0$$5;
    const x = $6[1];
    return containsParams$148(x);
  }
      }));
      break m$2;
    }
    if ((($1.$tag === "Array") || ($1.$tag === "Slice") || ($1.$tag === "Borrow"))) {
      let e;
      if (($1.$tag === "Array")) { e = $1.$[0]; }
      else if (($1.$tag === "Slice")) { e = $1.$; }
      else if (($1.$tag === "Borrow")) { e = $1.$[1]; }
      return containsParams$148(e);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function find$149(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function specializeFor$150(self, fid, ct) {
  const implId = $rt.idx(self.v.fns, fid).implId;
  let $1;
  const $2 = implId;
  m$3: {
    if (($2.$tag === "Some")) {
      const i = $2.$;
      $1 = isTemplateImpl$288(self.v, i);
      break m$3;
    }
    if (($2.$tag === "None")) {
      $1 = false;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const fromTemplateImpl = $1;
  let $4;
  if ((fromTemplateImpl && ($b.slice_len(ct) > 0n))) {
    const $5 = stripBorrows$295($rt.idx($rt.idx(ct, 0n), 1n));
    m$6: {
      if (($5.$tag === "Named")) {
        const d = $5.$[0];
        $4 = { $tag: "Some", $: d };
        break m$6;
      }
      if (true) {
        $4 = { $tag: "None" };
        break m$6;
      }
      $rt.unmatched($5);
    }
  } else {
    {
      $4 = { $tag: "None" };
    }
  }
  const requested = $4;
  return specialize$296(self, fid, ct, requested);
}
function settled$151(t) {
  const $1 = t;
  m$2: {
    if ((($1.$tag === "Var") || ($1.$tag === "Error"))) {
      return false;
      break m$2;
    }
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      return (eq$120(r.tail, { $tag: "Closed" }) && every$127($b.slice_iter(r.labels), (($0$$3) => {
  {
    const $4 = $0$$3;
    const x = $4[1];
    return settled$151(x);
  }
      })));
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      return every$297($b.slice_iter(ts), ((x) => {
  return settled$151(x);
      }));
      break m$2;
    }
    if ((($1.$tag === "Array") || ($1.$tag === "Slice") || ($1.$tag === "Borrow"))) {
      let e;
      if (($1.$tag === "Array")) { e = $1.$[0]; }
      else if (($1.$tag === "Slice")) { e = $1.$; }
      else if (($1.$tag === "Borrow")) { e = $1.$[1]; }
      return settled$151(e);
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const args = $1.$[1];
      return every$298($b.slice_iter(args), ((a) => {
  const $5 = a;
  m$6: {
    if (($5.$tag === "Ty")) {
      const x = $5.$;
      return settled$151(x);
      break m$6;
    }
    if (true) {
      return true;
      break m$6;
    }
    $rt.unmatched($5);
  }
      }));
      break m$2;
    }
    if (true) {
      return true;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function cmp$152(self, other) {
  if ((self < other)) {
    return { $tag: "Less" };
  } else {
    if ((self === other)) {
      return { $tag: "Equal" };
    } else {
      {
        return { $tag: "Greater" };
      }
    }
  }
}
function borrowInContainer$153(self, t) {
  const seen = { v: new$$281() };
  return containerIn$299(self, t, seen);
}
function containerMessage$154(p, d, arg) {
  const shown = show$136(p, arg);
  let $1;
  if (($b.str_includes(shown, "str") && (!$b.str_includes(shown, "u8")))) {
    $1 = "an owned `String`";
  } else {
    {
      $1 = "an owned value";
    }
  }
  const hint = $1;
  return ("" + "`" + $rt.idx(p.defs, d).name + "` cannot hold `" + shown + "`, which borrows: it holds owned values, so use " + hint + " (\xc2\xa74.2)");
}
function lineCol$155(source, offset) {
  const bytes = $b.str_asBytes(source);
  const at = min$146(offset, $b.slice_len(bytes));
  let line = 1n;
  let lineStart = 0n;
  const $1 = at;
  for (let i = 0n; i < $1; i++) {
    if (($rt.idx(bytes, i) === 10n)) {
      line = $rt.usize(line + 1n);
      lineStart = $rt.usize(i + 1n);
    }
  }
  let col = 1n;
  const $2 = at;
  for (let i = lineStart; i < $2; i++) {
    if ((($rt.idx(bytes, i) & 0xc0n) !== 0x80n)) {
      col = $rt.usize(col + 1n);
    }
  }
  return [line, col];
}
function max$156(a, b) {
  if ((b > a)) {
    return b;
  } else {
    {
      return a;
    }
  }
}
function builtinKey$157(self, fid) {
  const name = $b.String_clone($rt.idx(self.p.fns, fid).name);
  let $1;
  const $2 = $rt.idx(self.p.fns, fid).implId;
  m$3: {
    if (($2.$tag === "Some")) {
      const i = $2.$;
      $1 = i;
      break m$3;
    }
    if (($2.$tag === "None")) {
      return name;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const imp = $1;
  let $4;
  const $5 = $rt.idx(self.p.impls, imp).target;
  m$6: {
    if (($5.$tag === "Named")) {
      const d = $5.$[0];
      $4 = $b.String_clone($rt.idx(self.p.defs, d).name);
      break m$6;
    }
    if (($5.$tag === "Prim")) {
      const p = $5.$;
      $4 = $b.str_toString(primName$300(p));
      break m$6;
    }
    if (($5.$tag === "Slice")) {
      $4 = $b.str_toString("slice");
      break m$6;
    }
    if (($5.$tag === "Array")) {
      $4 = $b.str_toString("array");
      break m$6;
    }
    if (($5.$tag === "Union")) {
      const r = $5.$;
      if ($b.Option_isSome(labelGet$233(r.labels, "Some"))) {
        $4 = $b.str_toString("Option");
      } else {
        if ($b.Option_isSome(labelGet$233(r.labels, "Ok"))) {
          $4 = $b.str_toString("Result");
        } else {
          {
            $4 = $b.str_toString("union");
          }
        }
      }
      break m$6;
    }
    if (true) {
      $4 = $b.str_toString("any");
      break m$6;
    }
    $rt.unmatched($5);
  }
  const target = $4;
  return ("" + target + "_" + name);
}
function eraseArgs$158(args, p, tasks) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(args)) {
    const a = $1;
    const $2 = out;
    let $3;
    const $4 = a;
    m$5: {
      if (($4.$tag === "Ty")) {
        const t = $4.$;
        $3 = { $tag: "Ty", $: eraseTy$301(t, p, tasks) };
        break m$5;
      }
      if (($4.$tag === "Region")) {
        $3 = { $tag: "Region", $: { $tag: "Heap" } };
        break m$5;
      }
      if (($4.$tag === "Row")) {
        const r = $4.$;
        $3 = { $tag: "Row", $: eraseEffs$302(r, p, tasks) };
        break m$5;
      }
      if (($4.$tag === "Len")) {
        const l = $4.$;
        $3 = { $tag: "Len", $: clone$198(l) };
        break m$5;
      }
      $rt.unmatched($4);
    }
    $b.Vec_push($2, $3);
  }
  return out.v;
}
function keyArgs$159(args) {
  const out = { v: $b.String_new() };
  for (const $1 of $rt.items(args)) {
    const a = $1;
    writeKeyArg$303(a, out);
    $b.String_push(out, ";");
  }
  return out.v;
}
function fnSuspends$160(self, fid, args) {
  const row = substEffs$305(fnEffects$304(self, fid), substMap$162($rt.idx(self.p.fns, fid).scheme.tparams, args));
  return rowSuspends$306(self.p, row, self.tasks);
}
function mangle$161(n) {
  if (some$307($b.slice_iter($c1$RESERVED), ((r) => {
  return (r === n);
  }))) {
    return ("" + n + "$");
  } else {
    {
      return $b.str_toString(n);
    }
  }
}
function substMap$162(params, args) {
  const map = { v: $b.HashMap_new() };
  const $1 = min$146($b.slice_len(params), $b.slice_len(args));
  for (let i = 0n; i < $1; i++) {
    $b.HashMap_insert(map, $rt.idx(params, i).sym.id, clone$290($rt.idx(args, i)));
  }
  return map.v;
}
function concrete$163(self, t) {
  const s = subst$308(t, self.map);
  return resolveAssoc$309(self, s);
}
function findCells$164(self, decl) {
  const scopes = { v: $b.Vec_new() };
  const top = { v: $b.HashMap_new() };
  for (const $1 of $rt.items(decl.sig.params)) {
    const p = $1;
    $b.HashMap_insert(top, $b.String_clone(p.name.name), [true, p.name.span.start]);
  }
  $b.Vec_push(scopes, top.v);
  const $2 = decl.body;
  m$3: {
    if (($2.$tag === "Some")) {
      const b = $2.$;
      {
        cellsBlock$310(self, b, scopes);
        return undefined;
      }
      break m$3;
    }
    if (true) {
      {
        return undefined;
      }
      break m$3;
    }
    $rt.unmatched($2);
  }
}
function push$165(self) {
  $b.Vec_push(new $rt.FieldRef(self.v, "scopes"), $b.HashMap_new());
  return undefined;
}
function declare$166(self, name, cell) {
  const top = $rt.usize($b.slice_len(self.v.scopes) - 1n);
  let $1;
  if ((name === "_")) {
    $1 = fresh$167(self);
  } else {
    {
      $1 = mangle$161(name);
    }
  }
  let js = $1;
  if (($b.Option_isSome(local$311(self.v, name)) || $b.str_startsWith($b.String_asStr(js), "$"))) {
    js = ("" + js + "$" + fresh$167(self));
  }
  $b.HashMap_insert($rt.indexRef(self.v.scopes, top), $b.str_toString(name), { js: $b.String_clone(js), cell: cell });
  return js;
}
function fresh$167(self) {
  self.v.tmp = $rt.usize(self.v.tmp + 1n);
  return ("" + "$" + String(self.v.tmp));
}
function line$168(self, s) {
  const $1 = self.v.indent;
  for (let $2$$3 = 0n; $2$$3 < $1; $2$$3++) {
    $b.String_push(new $rt.FieldRef(self.v, "out"), "  ");
  }
  $b.String_push(new $rt.FieldRef(self.v, "out"), s);
  $b.String_push(new $rt.FieldRef(self.v, "out"), "\n");
  return undefined;
}
function stmtsFrom$169(self, b, from, dest) {
  let i = from;
  while ((i < $b.slice_len(b.stmts))) {
    const $1 = $rt.idx(b.stmts, i);
    m$2: {
      if (($1.$tag === "Let")) {
        const mutable = $1.$.mutable;
        const pat = $1.$.pat;
        const init = $1.$.init;
        {
          const $3 = pat.kind;
          m$4: {
            if (($3.$tag === "Bind")) {
              const n = $3.$;
              {
                const want = bindingTy$312(self.v, pat.id);
                let $5;
                const $6 = want;
                m$7: {
                  if (($6.$tag === "Error")) {
                    $5 = value$313(self, init);
                    break m$7;
                  }
                  if (true) {
                    $5 = exAs$314(self, init, want);
                    break m$7;
                  }
                  $rt.unmatched($6);
                }
                const v = $5;
                const cell = has$19(self.v.cells, pat.id);
                const js = declare$166(self, n, cell);
                if (cell) {
                  line$168(self, ("" + "const " + js + " = { v: " + v + " };"));
                } else {
                  {
                    const $8 = self;
                    let $9;
                    if (mutable) {
                      $9 = "let";
                    } else {
                      {
                        $9 = "const";
                      }
                    }
                    line$168($8, ("" + $9 + " " + js + " = " + v + ";"));
                  }
                }
              }
              break m$4;
            }
            if (true) {
              {
                const v = value$313(self, init);
                let $10;
                if ((isPlace$315(init) && copiedObject$318(self.v, stripBorrow$317(exprTy$316(self.v, init.id))))) {
                  $10 = ("" + "$rt.copy(" + v + ")");
                } else {
                  {
                    $10 = v;
                  }
                }
                const copied = $10;
                const t = save$319(self, copied);
                const c = cond$320(self, pat, t);
                if ((c !== "true")) {
                  line$168(self, ("" + "if (!(" + c + ")) $rt.unmatched(" + t + ");"));
                }
                binds$321(self, pat, t, { $tag: "None" }, mutable);
              }
              break m$4;
            }
            $rt.unmatched($3);
          }
        }
        break m$2;
      }
      if (($1.$tag === "Expr")) {
        const e = $1.$;
        into$322(self, e, { $tag: "Discard" });
        break m$2;
      }
      if (($1.$tag === "Defer")) {
        const e = $1.$;
        {
          line$168(self, "try {");
          self.v.indent = $rt.usize(self.v.indent + 1n);
          stmtsFrom$169(self, b, $rt.usize(i + 1n), dest);
          self.v.indent = $rt.usize(self.v.indent - 1n);
          line$168(self, "} finally {");
          self.v.indent = $rt.usize(self.v.indent + 1n);
          into$322(self, e, { $tag: "Discard" });
          self.v.indent = $rt.usize(self.v.indent - 1n);
          line$168(self, "}");
          return;
        }
        break m$2;
      }
      $rt.unmatched($1);
    }
    i = $rt.usize(i + 1n);
  }
  const $11 = b.tail;
  m$12: {
    if (($11.$tag === "Some")) {
      const t = $11.$;
      return into$322(self, t, dest);
      break m$12;
    }
    if (($11.$tag === "None")) {
      return deliver$323(self, "undefined", dest);
      break m$12;
    }
    $rt.unmatched($11);
  }
}
function pop$170(self) {
  $b.Vec_pop(new $rt.FieldRef(self.v, "scopes"));
  return undefined;
}
function intPrim$171(t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Prim")) {
      const p = $1.$;
      if (isInt$324(p)) {
        return { $tag: "Some", $: p };
      } else {
        {
          return { $tag: "None" };
        }
      }
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const inner = $1.$[1];
      return intPrim$171(inner);
      break m$2;
    }
    if (true) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function parse$172(src, declarations) {
  const p = { v: { src: src, toks: lex$325(src), pos: 0n, declarations: declarations, nextId: 0n, guardArrow: { $tag: "None" } } };
  const items = { v: $b.Vec_new() };
  while ((!atEof$326(p.v))) {
    $b.Vec_push(items, item$327(p));
  }
  return { items: items.v };
}
function clone$173(self) {
  {
    return { exported: clone$199(self.exported), kind: clone$328(self.kind), span: clone$94(self.span) };
  }
}
function clone$174(self) {
  return self;
}
function clone$175(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Int")) {
      const x = $1.$;
      return { $tag: "Int", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Float")) {
      const x = $1.$;
      return { $tag: "Float", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Byte")) {
      const x = $1.$;
      return { $tag: "Byte", $: clone$329(x) };
      break m$2;
    }
    if (($1.$tag === "Str")) {
      const x = $1.$;
      return { $tag: "Str", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Template")) {
      const x = $1.$;
      return { $tag: "Template", $: clone$330(x) };
      break m$2;
    }
    if (($1.$tag === "Bool")) {
      const x = $1.$;
      return { $tag: "Bool", $: clone$199(x) };
      break m$2;
    }
    if (($1.$tag === "Ident")) {
      const x = $1.$;
      return { $tag: "Ident", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const x = $1.$;
      return { $tag: "Tag", $: clone$331(x) };
      break m$2;
    }
    if (($1.$tag === "TagAt")) {
      const x = $1.$;
      return { $tag: "TagAt", $: clone$332(x) };
      break m$2;
    }
    if (($1.$tag === "TypeRef")) {
      const x = $1.$;
      return { $tag: "TypeRef", $: clone$174(x) };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const x = $1.$;
      return { $tag: "Record", $: clone$333(x) };
      break m$2;
    }
    if (($1.$tag === "List")) {
      const x = $1.$;
      return { $tag: "List", $: clone$334(x) };
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const x = $1.$;
      return { $tag: "Field", $: clone$335(x) };
      break m$2;
    }
    if (($1.$tag === "FieldAt")) {
      const x = $1.$;
      return { $tag: "FieldAt", $: clone$336(x) };
      break m$2;
    }
    if (($1.$tag === "Index")) {
      const x = $1.$;
      return { $tag: "Index", $: clone$337(x) };
      break m$2;
    }
    if (($1.$tag === "Call")) {
      const x = $1.$;
      return { $tag: "Call", $: clone$338(x) };
      break m$2;
    }
    if (($1.$tag === "Unary")) {
      const x = $1.$;
      return { $tag: "Unary", $: clone$339(x) };
      break m$2;
    }
    if (($1.$tag === "BorrowMut")) {
      const x = $1.$;
      return { $tag: "BorrowMut", $: clone$223(x) };
      break m$2;
    }
    if (($1.$tag === "Binary")) {
      const x = $1.$;
      return { $tag: "Binary", $: clone$340(x) };
      break m$2;
    }
    if (($1.$tag === "Assign")) {
      const x = $1.$;
      return { $tag: "Assign", $: clone$341(x) };
      break m$2;
    }
    if (($1.$tag === "Cast")) {
      const x = $1.$;
      return { $tag: "Cast", $: clone$342(x) };
      break m$2;
    }
    if (($1.$tag === "Range")) {
      const x = $1.$;
      return { $tag: "Range", $: clone$343(x) };
      break m$2;
    }
    if (($1.$tag === "Lambda")) {
      const x = $1.$;
      return { $tag: "Lambda", $: clone$344(x) };
      break m$2;
    }
    if (($1.$tag === "Block")) {
      const x = $1.$;
      return { $tag: "Block", $: clone$30(x) };
      break m$2;
    }
    if (($1.$tag === "If")) {
      const x = $1.$;
      return { $tag: "If", $: clone$345(x) };
      break m$2;
    }
    if (($1.$tag === "While")) {
      const x = $1.$;
      return { $tag: "While", $: clone$346(x) };
      break m$2;
    }
    if (($1.$tag === "For")) {
      const x = $1.$;
      return { $tag: "For", $: clone$347(x) };
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const x = $1.$;
      return { $tag: "Match", $: clone$348(x) };
      break m$2;
    }
    if (($1.$tag === "Try")) {
      const x = $1.$;
      return { $tag: "Try", $: clone$349(x) };
      break m$2;
    }
    if (($1.$tag === "Throw")) {
      const x = $1.$;
      return { $tag: "Throw", $: clone$223(x) };
      break m$2;
    }
    if (($1.$tag === "Yield")) {
      const x = $1.$;
      return { $tag: "Yield", $: clone$223(x) };
      break m$2;
    }
    if (($1.$tag === "Return")) {
      const x = $1.$;
      return { $tag: "Return", $: clone$96(x) };
      break m$2;
    }
    if (($1.$tag === "Break")) {
      return { $tag: "Break" };
      break m$2;
    }
    if (($1.$tag === "Continue")) {
      return { $tag: "Continue" };
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const x = $1.$;
      return { $tag: "Region", $: clone$350(x) };
      break m$2;
    }
    if (($1.$tag === "Handle")) {
      const x = $1.$;
      return { $tag: "Handle", $: clone$351(x) };
      break m$2;
    }
    if (($1.$tag === "Unsafe")) {
      const x = $1.$;
      return { $tag: "Unsafe", $: clone$30(x) };
      break m$2;
    }
    if (($1.$tag === "Comptime")) {
      const x = $1.$;
      return { $tag: "Comptime", $: clone$223(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function sourceSpan$176(self, span) {
  if ((span.start < $c6$SYNTH_BASE)) {
    return $rt.copy(span);
  }
  const $1 = $b.HashMap_get(self.synth, span.start);
  m$2: {
    if (($1.$tag === "Some")) {
      const s = $1.$;
      return $rt.copy(s);
      break m$2;
    }
    if (($1.$tag === "None")) {
      return { start: 0n, end: 0n };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eq$177(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Diagnostic") && ($1[1].$tag === "Diagnostic"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$352(a, b);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function some$178(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function clone$179(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$353(x));
  }
  return v.v;
}
function typeParams$180(self, params, scope) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(params)) {
    const p = $1;
    let $2;
    const $3 = p;
    m$4: {
      if (($3.$tag === "Region")) {
        const name = $3.$.name;
        $2 = [clone$218(name), { $tag: "Region" }, false];
        break m$4;
      }
      if (($3.$tag === "Row")) {
        const name = $3.$.name;
        $2 = [clone$218(name), { $tag: "Row" }, false];
        break m$4;
      }
      if (($3.$tag === "Comptime")) {
        const name = $3.$.name;
        const ty = $3.$.ty;
        const $5 = ty.kind;
        m$6: {
          if (($5.$tag === "Path")) {
            const segments = $5.$.segments;
            if ((($b.slice_len(segments) === 1n) && ($rt.idx(segments, 0n).name === "Type"))) {
              $2 = [clone$218(name), { $tag: "Type" }, true];
              break m$6;
            }
          }
          if (true) {
            $2 = [clone$218(name), { $tag: "Len" }, false];
            break m$6;
          }
          $rt.unmatched($5);
        }
        break m$4;
      }
      if (($3.$tag === "Type")) {
        const name = $3.$.name;
        $2 = [clone$218(name), { $tag: "Type" }, false];
        break m$4;
      }
      $rt.unmatched($3);
    }
    const $7 = $2;
    const name = $7[0];
    const kind = $7[1];
    const isComptime = $7[2];
    const sym = freshSym$59(self, $b.String_asStr(name.name));
    $b.Vec_push(out, { sym: sym, kind: kind, bounds: $b.Vec_new(), default: { $tag: "None" }, isComptime: isComptime });
  }
  const inner = withParams$32(scope, out.v);
  const $8 = $b.slice_len(out.v);
  for (let i = 0n; i < $8; i++) {
    const $9 = $rt.idx(params, i);
    m$10: {
      if (($9.$tag === "Type")) {
        const bounds = $9.$.bounds;
        const default$ = $9.$.default;
        {
          const bs = { v: $b.Vec_new() };
          for (const $11 of $rt.items(bounds)) {
            const b = $11;
            $b.Vec_push(bs, elabTy$101(self, b, inner));
          }
          $rt.idx(out.v, i).bounds = bs.v;
          const $12 = default$;
          m$13: {
            if (($12.$tag === "Some")) {
              const d = $12.$;
              {
                $rt.idx(out.v, i).default = { $tag: "Some", $: { $tag: "Ty", $: elabTy$101(self, d, inner) } };
              }
              break m$13;
            }
            if (true) {
              {
              }
              break m$13;
            }
            $rt.unmatched($12);
          }
        }
        break m$10;
      }
      if (($9.$tag === "Row")) {
        const bounds = $9.$.bounds;
        const default$ = $9.$.default;
        {
          const bs = { v: $b.Vec_new() };
          for (const $14 of $rt.items(bounds)) {
            const b = $14;
            $b.Vec_push(bs, elabTy$101(self, b, inner));
          }
          $rt.idx(out.v, i).bounds = bs.v;
          const $15 = default$;
          m$16: {
            if (($15.$tag === "Some")) {
              const d = $15.$;
              {
                $rt.idx(out.v, i).default = { $tag: "Some", $: { $tag: "Row", $: elabRowType$354(self, d, inner) } };
              }
              break m$16;
            }
            if (true) {
              {
              }
              break m$16;
            }
            $rt.unmatched($15);
          }
        }
        break m$10;
      }
      if (($9.$tag === "Region" && ($9.$.default.$tag === "Some"))) {
        const d = $9.$.default.$;
        {
          $rt.idx(out.v, i).default = { $tag: "Some", $: { $tag: "Region", $: elabRegion$355(self, d, inner) } };
        }
        break m$10;
      }
      if (true) {
        {
        }
        break m$10;
      }
      $rt.unmatched($9);
    }
  }
  return out.v;
}
function some$181(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function clone$182(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$356(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function elabPayload$183(self, p, scope) {
  const $1 = p;
  m$2: {
    if (($1.$tag === "None")) {
      return voidTy$112();
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $3 of $rt.items(ts)) {
          const t = $3;
          $b.Vec_push(out, elabTy$101(self, t, scope));
        }
        return { $tag: "Tuple", $: out.v };
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fs = $1.$;
      {
        const labels = { v: $b.Vec_new() };
        for (const $4 of $rt.items(fs)) {
          const f = $4;
          const ft = elabTy$101(self, f.ty, scope);
          labelSet$184(labels, $b.String_asStr(f.name.name), ft);
        }
        return { $tag: "Record", $: { labels: labels.v, tail: { $tag: "Closed" } } };
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function labelSet$184(labels, k, t) {
  let i = 0n;
  while ((i < $b.slice_len(labels.v))) {
    if (($rt.idx($rt.idx(labels.v, i), 0n) === k)) {
      const $1 = labels.v;
      $1[$rt.at($1, i)] = [$b.str_toString(k), t];
      return;
    }
    if (eq$357(cmp$358($b.String_asStr($rt.idx($rt.idx(labels.v, i), 0n)), k), { $tag: "Greater" })) {
      break;
    }
    i = $rt.usize(i + 1n);
  }
  $b.Vec_insert(labels, i, [$b.str_toString(k), t]);
  return undefined;
}
function isNone$185(self) {
  return (!$b.Option_isSome(self));
}
function declareIfaceFns$186(self, iface, module, methods, selfSym) {
  const iparams = clone$73($rt.idx(self.v.defs, iface).params);
  const iargs = { v: $b.Vec_new() };
  for (const $1 of $rt.items(iparams)) {
    const g = $1;
    $b.Vec_push(iargs, paramArg$291(g));
  }
  const bound = { $tag: "Named", $: [iface, iargs.v] };
  for (const $2 of $rt.items(methods)) {
    const name = $2[0];
    const scheme = $2[1];
    const tparams = { v: [{ sym: clone$34(selfSym), kind: { $tag: "Type" }, bounds: [clone$23(bound)], default: { $tag: "None" }, isComptime: false }] };
    for (const $3 of $rt.items(iparams)) {
      const g = $3;
      $b.Vec_push(tparams, clone$194(g));
    }
    for (const $4 of $rt.items(scheme.tparams)) {
      const g = $4;
      $b.Vec_push(tparams, clone$194(g));
    }
    const id = $b.slice_len(self.v.fns);
    let s = clone$22(scheme);
    s.tparams = tparams.v;
    if (isNone$39(s.effects)) {
      s.effects = { $tag: "Some", $: pure$37() };
    }
    $b.Vec_push(new $rt.FieldRef(self.v, "fns"), { name: $b.String_clone(name), module: module, scheme: s, decl: { module: module, item: 0xffffffffn, method: { $tag: "None" } }, exported: true, implId: { $tag: "None" }, hasBody: false, iface: { $tag: "Some", $: iface } });
    $b.HashMap_insert(new $rt.FieldRef(self.v, "ifaceFns"), ("" + String(iface) + ":" + name), id);
  }
  return undefined;
}
function class$$187(self, t) {
  const seen = { v: new$$281() };
  return classIn$359(self, t, seen);
}
function clone$188(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$193(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function boolTy$189() {
  return { $tag: "Prim", $: { $tag: "Bool" } };
}
function elabArgs$190(self, def, args, scope, span) {
  const params = clone$73($rt.idx(self.v.defs, def).params);
  let regions = 0n;
  for (const $1 of $rt.items(params)) {
    const p = $1;
    if (eq$33(p.kind, { $tag: "Region" })) {
      regions = $rt.usize(regions + 1n);
    }
  }
  const elide = (((($b.slice_len(args) < $b.slice_len(params)) && (regions > 0n)) && ($rt.usize($b.slice_len(args) + regions) <= $b.slice_len(params))) && $b.Option_isSome(scope.elidedRegion));
  let given = 0n;
  const out = { v: $b.Vec_new() };
  for (const $2 of $rt.items(params)) {
    const p = $2;
    if ((eq$33(p.kind, { $tag: "Region" }) && elide)) {
      const $3 = out;
      let $4;
      const $5 = scope.elidedRegion;
      m$6: {
        if (($5.$tag === "Some")) {
          const r = $5.$;
          $4 = clone$360(r);
          break m$6;
        }
        if (($5.$tag === "None")) {
          $4 = { $tag: "Heap" };
          break m$6;
        }
        $rt.unmatched($5);
      }
      $b.Vec_push($3, { $tag: "Region", $: $4 });
      continue;
    }
    let $7;
    if ((given < $b.slice_len(args))) {
      const a = clone$193($rt.idx(args, given));
      given = $rt.usize(given + 1n);
      const $8 = p.kind;
      m$9: {
        if (($8.$tag === "Type")) {
          $7 = { $tag: "Ty", $: elabTy$101(self, a, scope) };
          break m$9;
        }
        if (($8.$tag === "Region")) {
          $7 = { $tag: "Region", $: elabRegion$355(self, a, scope) };
          break m$9;
        }
        if (($8.$tag === "Row")) {
          $7 = { $tag: "Row", $: elabRowType$354(self, a, scope) };
          break m$9;
        }
        if (($8.$tag === "Len")) {
          const $10 = a.kind;
          m$11: {
            if (($10.$tag === "Expr")) {
              const e = $10.$;
              $7 = { $tag: "Len", $: elabLen$235(self, e, scope) };
              break m$11;
            }
            if (($10.$tag === "Path")) {
              const segments = $10.$.segments;
              {
                self.v.nextId = $rt.usize(self.v.nextId + 1n);
                const e = { kind: { $tag: "Ident", $: $b.String_clone($rt.idx(segments, 0n).name) }, span: $rt.copy(a.span), id: self.v.nextId };
                $7 = { $tag: "Len", $: elabLen$235(self, e, scope) };
              }
              break m$11;
            }
            if (true) {
              $7 = { $tag: "Len", $: { $tag: "Known", $: 0n } };
              break m$11;
            }
            $rt.unmatched($10);
          }
          break m$9;
        }
        $rt.unmatched($8);
      }
    } else {
      {
        const $12 = p.default;
        m$13: {
          if (($12.$tag === "Some")) {
            const d = $12.$;
            $7 = clone$290(d);
            break m$13;
          }
          if (($12.$tag === "None")) {
            {
              if (($b.slice_len(args) > 0n)) {
                error$62(self, scope.module, $rt.copy(span), $b.String_asStr(("" + "`" + $rt.idx(self.v.defs, def).name + "` takes " + String($b.slice_len(params)) + " arguments")));
              }
              const $14 = p.kind;
              m$15: {
                if (($14.$tag === "Type")) {
                  $7 = { $tag: "Ty", $: { $tag: "Error" } };
                  break m$15;
                }
                if (($14.$tag === "Region")) {
                  $7 = { $tag: "Region", $: { $tag: "Heap" } };
                  break m$15;
                }
                if (($14.$tag === "Row")) {
                  $7 = { $tag: "Row", $: pure$37() };
                  break m$15;
                }
                if (($14.$tag === "Len")) {
                  $7 = { $tag: "Len", $: { $tag: "Known", $: 0n } };
                  break m$15;
                }
                $rt.unmatched($14);
              }
            }
            break m$13;
          }
          $rt.unmatched($12);
        }
      }
    }
    const arg = $7;
    $b.Vec_push(out, arg);
  }
  if ((given < $b.slice_len(args))) {
    error$62(self, scope.module, $rt.copy(span), $b.String_asStr(("" + "`" + $rt.idx(self.v.defs, def).name + "` takes " + String($b.slice_len(params)) + " arguments")));
  }
  return out.v;
}
function isNone$191(self) {
  return (!$b.Option_isSome(self));
}
function unknown$192(self, what, name) {
  const $1 = find$65($b.slice_iter(self.modules), ((m) => {
  return ((m.isStd && (m.name !== "std/prelude")) && $b.HashMap_has(m.exports, name));
  }));
  m$2: {
    if (($1.$tag === "Some")) {
      const m = $1.$;
      return ("" + "unknown " + what + " `" + name + "`: import it with `import { " + name + " } from \"" + m.name + "\";`");
      break m$2;
    }
    if (($1.$tag === "None")) {
      return ("" + "unknown " + what + " `" + name + "`");
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$193(self) {
  {
    return { kind: clone$361(self.kind), span: clone$94(self.span) };
  }
}
function clone$194(self) {
  {
    return { sym: clone$34(self.sym), kind: clone$362(self.kind), bounds: clone$35(self.bounds), default: clone$363(self.default), isComptime: clone$199(self.isComptime) };
  }
}
function elabEffects$195(self, row, scope) {
  const effs = { v: $b.Vec_new() };
  let tail = { $tag: "Closed" };
  for (const $1 of $rt.items(row)) {
    const item = $1;
    const $2 = item;
    m$3: {
      if (($2.$tag === "Spread")) {
        const name = $2.$;
        {
          tail = rowTail$232(self, name, scope);
        }
        break m$3;
      }
      if (($2.$tag === "Effect")) {
        const t = $2.$;
        {
          const $4 = t.kind;
          m$5: {
            if (($4.$tag === "Path")) {
              const segments = $4.$.segments;
              const args = $4.$.args;
              {
                const name = $b.String_clone($rt.idx(segments, 0n).name);
                const $6 = lookup$47(self.v, scope.module, $b.String_asStr(name));
                m$7: {
                  if (($6.$tag === "Some" && ($6.$.$tag === "Def"))) {
                    const d = $6.$.$;
                    let $8;
                    const $9 = new $rt.FieldRef($rt.idx(self.v.defs, d), "kind");
                    const $10 = $9.v;
                    m$11: {
                      if (($10.$tag === "Effect")) {
                        $8 = true;
                        break m$11;
                      }
                      if (true) {
                        $8 = false;
                        break m$11;
                      }
                      $rt.unmatched($10);
                    }
                    if ($8) {
                      {
                        const gargs = elabArgs$190(self, d, args, scope, $rt.copy(t.span));
                        const regions = { v: $b.Vec_new() };
                        const targs = { v: $b.Vec_new() };
                        for (const $12 of $rt.items(gargs)) {
                          const a = $12;
                          const $13 = a;
                          m$14: {
                            if (($13.$tag === "Region")) {
                              const r = $13.$;
                              $b.Vec_push(regions, clone$360(r));
                              break m$14;
                            }
                            if (($13.$tag === "Ty")) {
                              const x = $13.$;
                              $b.Vec_push(targs, clone$23(x));
                              break m$14;
                            }
                            if (true) {
                              {
                              }
                              break m$14;
                            }
                            $rt.unmatched($13);
                          }
                        }
                        $b.Vec_push(effs, { def: d, regions: regions.v, args: targs.v });
                      }
                      break m$7;
                    }
                  }
                  if (true) {
                    error$62(self, scope.module, $rt.copy(t.span), $b.String_asStr(("" + "`" + name + "` is not an effect")));
                    break m$7;
                  }
                  $rt.unmatched($6);
                }
              }
              break m$5;
            }
            if (true) {
              {
              }
              break m$5;
            }
            $rt.unmatched($4);
          }
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return { effs: effs.v, tail: tail };
}
function clone$196(self) {
  {
    const v = [$b.String_clone($rt.idx(self, 0n)), clone$23($rt.idx(self, 1n))];
    return v;
  }
}
function clone$197(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$290(x));
  }
  return v.v;
}
function clone$198(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Known")) {
      const x = $1.$;
      return { $tag: "Known", $: clone$364(x) };
      break m$2;
    }
    if (($1.$tag === "Var")) {
      const x = $1.$;
      return { $tag: "Var", $: clone$77(x) };
      break m$2;
    }
    if (($1.$tag === "Param")) {
      const x = $1.$;
      return { $tag: "Param", $: clone$34(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$199(self) {
  return self;
}
function clone$200(self) {
  {
    return { mode: clone$365(self.mode), params: clone$35(self.params), ret: clone$23(self.ret), effects: clone$40(self.effects) };
  }
}
function some$201(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function some$202(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function initsHave$203(fs) {
  return some$366($b.slice_iter(fs), ((f) => {
  let $1 = ($b.Option_isSome(f.generate) || $b.Option_isSome(f.computed));
  if (!$1) {
    let $2;
    const $3 = f.value;
    m$4: {
      if (($3.$tag === "Some")) {
        const v = $3.$;
        $2 = exprHas$87(v);
        break m$4;
      }
      if (($3.$tag === "None")) {
        $2 = false;
        break m$4;
      }
      $rt.unmatched($3);
    }
    $1 = $2;
  }
  return $1;
  }));
}
function some$204(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function optHas$205(e) {
  const $1 = e;
  m$2: {
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return exprHas$87(x);
      break m$2;
    }
    if (($1.$tag === "None")) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function patHas$206(p) {
  const $1 = p.kind;
  m$2: {
    if (($1.$tag === "TagAt")) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Lit")) {
      const e = $1.$;
      const $3 = e.kind;
      m$4: {
        if (($3.$tag === "Comptime")) {
          return true;
          break m$4;
        }
        if (true) {
          return false;
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function some$207(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function some$208(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function clone$209(self) {
  return self;
}
function clone$210(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$90(x));
  }
  return v.v;
}
function clone$211(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$367(x));
  }
  return v.v;
}
function clone$212(self) {
  {
    const v = [$b.String_clone($rt.idx(self, 0n)), clone$368($rt.idx(self, 1n))];
    return v;
  }
}
function clone$213(self) {
  {
    const v = [clone$76($rt.idx(self, 0n)), clone$223($rt.idx(self, 1n)), clone$369($rt.idx(self, 2n))];
    return v;
  }
}
function sp$214(self, orig) {
  const o = sourceSpan$176(self.v.p.v, $rt.copy(orig));
  const s = self.v.p.v.nextSynth;
  self.v.p.v.nextSynth = $rt.usize(self.v.p.v.nextSynth + 1n);
  $b.HashMap_insert(new $rt.FieldRef(self.v.p.v, "synth"), s, $rt.copy(o));
  return { start: s, end: $rt.usize(s + 1n) };
}
function expr$215(self, e) {
  const span = sp$214(self, $rt.copy(e.span));
  let $1;
  const $2 = e.kind;
  m$3: {
    if ((($2.$tag === "Int") || ($2.$tag === "Float") || ($2.$tag === "Byte") || ($2.$tag === "Str") || ($2.$tag === "Bool") || ($2.$tag === "Break") || ($2.$tag === "Continue") || ($2.$tag === "TypeRef"))) {
      $1 = clone$175(e.kind);
      break m$3;
    }
    if (($2.$tag === "Template")) {
      const pieces = $2.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $4 of $rt.items(pieces)) {
          const p = $4;
          const $5 = out;
          let $6;
          const $7 = p;
          m$8: {
            if (($7.$tag === "Lit")) {
              const s = $7.$;
              $6 = { $tag: "Lit", $: $b.String_clone(s) };
              break m$8;
            }
            if (($7.$tag === "Expr")) {
              const x = $7.$;
              $6 = { $tag: "Expr", $: expr$215(self, x) };
              break m$8;
            }
            $rt.unmatched($7);
          }
          $b.Vec_push($5, $6);
        }
        $1 = { $tag: "Template", $: out.v };
      }
      break m$3;
    }
    if (($2.$tag === "Ident")) {
      const n = $2.$;
      const $9 = ctValue$370(self.v, $b.String_asStr(n));
      m$10: {
        if (($9.$tag === "Some")) {
          const v = $9.$;
          return splice$371(self, v, $rt.copy(e.span));
          break m$10;
        }
        if (($9.$tag === "None")) {
          $1 = { $tag: "Ident", $: $b.String_clone(n) };
          break m$10;
        }
        $rt.unmatched($9);
      }
      break m$3;
    }
    if (($2.$tag === "Tag")) {
      const name = $2.$.name;
      const args = $2.$.args;
      $1 = { $tag: "Tag", $: { name: $b.String_clone(name), args: tagArgs$372(self, args) } };
      break m$3;
    }
    if (($2.$tag === "TagAt")) {
      const name = $2.$.name;
      const args = $2.$.args;
      {
        const n = ctName$373(self, name);
        $1 = { $tag: "Tag", $: { name: n, args: tagArgs$372(self, args) } };
      }
      break m$3;
    }
    if (($2.$tag === "Record")) {
      const name = $2.$.name;
      const fields = $2.$.fields;
      {
        let $11;
        const $12 = name;
        m$13: {
          if (($12.$tag === "Some")) {
            const ps = $12.$;
            {
              const out = { v: $b.Vec_new() };
              for (const $14 of $rt.items(ps)) {
                const i = $14;
                $b.Vec_push(out, ident$374(self, i));
              }
              $11 = { $tag: "Some", $: out.v };
            }
            break m$13;
          }
          if (($12.$tag === "None")) {
            $11 = { $tag: "None" };
            break m$13;
          }
          $rt.unmatched($12);
        }
        const path = $11;
        $1 = { $tag: "Record", $: { name: path, fields: inits$375(self, fields) } };
      }
      break m$3;
    }
    if (($2.$tag === "List")) {
      const items = $2.$;
      $1 = { $tag: "List", $: list$376(self, items) };
      break m$3;
    }
    if (($2.$tag === "Field")) {
      const target = $2.$.target;
      const name = $2.$.name;
      if (isCt$377(self.v, target)) {
        {
          const v = eval$$378(self, target);
          const $15 = v;
          m$16: {
            if (($15.$tag === "Type")) {
              const t = $15.$;
              {
                const i = spliceTy$379(self, t);
                const ts = sp$214(self, $rt.copy(target.span));
                const tgt = mk$380(self, { $tag: "TypeRef", $: i }, $rt.copy(ts));
                $1 = { $tag: "Field", $: { target: $b.Box_new(tgt), name: ident$374(self, name) } };
              }
              break m$16;
            }
            if (true) {
              {
                const fv = fieldOf$381(self, v, $b.String_asStr(name.name), $rt.copy(name.span));
                return splice$371(self, fv, $rt.copy(e.span));
                $1 = undefined;
              }
              break m$16;
            }
            $rt.unmatched($15);
          }
        }
        break m$3;
      }
    }
    if (($2.$tag === "Field")) {
      const target = $2.$.target;
      const name = $2.$.name;
      $1 = { $tag: "Field", $: { target: $b.Box_new(expr$215(self, target)), name: ident$374(self, name) } };
      break m$3;
    }
    if (($2.$tag === "FieldAt")) {
      const target = $2.$.target;
      const name = $2.$.name;
      {
        const n = ctName$373(self, name);
        const nm = { name: n, span: sp$214(self, $rt.copy(name.span)) };
        $1 = { $tag: "Field", $: { target: $b.Box_new(expr$215(self, target)), name: nm } };
      }
      break m$3;
    }
    if (($2.$tag === "Index")) {
      const target = $2.$.target;
      const index = $2.$.index;
      $1 = { $tag: "Index", $: { target: $b.Box_new(expr$215(self, target)), index: $b.Box_new(expr$215(self, index)) } };
      break m$3;
    }
    if (($2.$tag === "Call")) {
      const callee = $2.$.callee;
      const typeArgs = $2.$.typeArgs;
      const args = $2.$.args;
      {
        const $17 = callee.kind;
        m$18: {
          if (($17.$tag === "Field")) {
            const target = $17.$.target;
            const name = $17.$.name;
            {
              if ((isCt$377(self.v, target) && includes$382($c3$COMPTIME_METHODS, $b.String_asStr(name.name)))) {
                const recv = eval$$378(self, target);
                let $19;
                const $20 = recv;
                m$21: {
                  if (($20.$tag === "Type")) {
                    $19 = true;
                    break m$21;
                  }
                  if (true) {
                    $19 = false;
                    break m$21;
                  }
                  $rt.unmatched($20);
                }
                if ((!$19)) {
                  const v = eval$$378(self, e);
                  return splice$371(self, v, $rt.copy(e.span));
                }
              }
            }
            break m$18;
          }
          if (true) {
            {
            }
            break m$18;
          }
          $rt.unmatched($17);
        }
        const tas = { v: $b.Vec_new() };
        for (const $22 of $rt.items(typeArgs)) {
          const t = $22;
          $b.Vec_push(tas, ty$216(self, t));
        }
        let $23;
        const $24 = callee.kind;
        m$25: {
          if (($24.$tag === "Field")) {
            const target = $24.$.target;
            const name = $24.$.name;
            let $26 = isCt$377(self.v, target);
            if ($26) {
              let $27;
              const $28 = eval$$378(self, target);
              m$29: {
                if (($28.$tag === "Type")) {
                  $27 = true;
                  break m$29;
                }
                if (true) {
                  $27 = false;
                  break m$29;
                }
                $rt.unmatched($28);
              }
              $26 = (!$27);
            }
            if ($26) {
              {
                const v = eval$$378(self, target);
                const cs = sp$214(self, $rt.copy(callee.span));
                const recv = splice$371(self, v, $rt.copy(target.span));
                const nm = ident$374(self, name);
                $23 = mk$380(self, { $tag: "Field", $: { target: $b.Box_new(recv), name: nm } }, $rt.copy(cs));
              }
              break m$25;
            }
          }
          if (true) {
            $23 = expr$215(self, callee);
            break m$25;
          }
          $rt.unmatched($24);
        }
        const c = $23;
        $1 = { $tag: "Call", $: { callee: $b.Box_new(c), typeArgs: tas.v, args: exprs$383(self, args) } };
      }
      break m$3;
    }
    if (($2.$tag === "Unary")) {
      const op = $2.$.op;
      const operand = $2.$.operand;
      $1 = { $tag: "Unary", $: { op: $b.String_clone(op), operand: $b.Box_new(expr$215(self, operand)) } };
      break m$3;
    }
    if (($2.$tag === "BorrowMut")) {
      const x = $2.$;
      $1 = { $tag: "BorrowMut", $: $b.Box_new(expr$215(self, x)) };
      break m$3;
    }
    if (($2.$tag === "Binary")) {
      const op = $2.$.op;
      const lhs = $2.$.lhs;
      const rhs = $2.$.rhs;
      $1 = { $tag: "Binary", $: { op: $b.String_clone(op), lhs: $b.Box_new(expr$215(self, lhs)), rhs: $b.Box_new(expr$215(self, rhs)) } };
      break m$3;
    }
    if (($2.$tag === "Assign")) {
      const op = $2.$.op;
      const target = $2.$.target;
      const value = $2.$.value;
      $1 = { $tag: "Assign", $: { op: $b.String_clone(op), target: $b.Box_new(expr$215(self, target)), value: $b.Box_new(expr$215(self, value)) } };
      break m$3;
    }
    if (($2.$tag === "Cast")) {
      const expr = $2.$.expr;
      const ty = $2.$.ty;
      $1 = { $tag: "Cast", $: { expr: $b.Box_new(expr$215(self, expr)), ty: ty$216(self, ty) } };
      break m$3;
    }
    if (($2.$tag === "Range")) {
      const lo = $2.$.lo;
      const hi = $2.$.hi;
      $1 = { $tag: "Range", $: { lo: optExpr$384(self, lo), hi: optExpr$384(self, hi) } };
      break m$3;
    }
    if (($2.$tag === "Lambda")) {
      const params = $2.$.params;
      const body = $2.$.body;
      {
        const depth = $b.slice_len(self.v.env);
        const ps = params$385(self, params);
        const b = expr$215(self, body);
        $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
        $1 = { $tag: "Lambda", $: { params: ps, body: $b.Box_new(b) } };
      }
      break m$3;
    }
    if (($2.$tag === "Block")) {
      const b = $2.$;
      $1 = { $tag: "Block", $: scopedBlock$386(self, b) };
      break m$3;
    }
    if (($2.$tag === "If")) {
      const cond = $2.$.cond;
      const then = $2.$.then;
      const otherwise = $2.$.otherwise;
      $1 = { $tag: "If", $: { cond: $b.Box_new(expr$215(self, cond)), then: scopedBlock$386(self, then), otherwise: optExpr$384(self, otherwise) } };
      break m$3;
    }
    if (($2.$tag === "While")) {
      const cond = $2.$.cond;
      const body = $2.$.body;
      $1 = { $tag: "While", $: { cond: $b.Box_new(expr$215(self, cond)), body: scopedBlock$386(self, body) } };
      break m$3;
    }
    if (($2.$tag === "For")) {
      const mutable = $2.$.mutable;
      const pat = $2.$.pat;
      const iter = $2.$.iter;
      const body = $2.$.body;
      {
        const it = expr$215(self, iter);
        const depth = $b.slice_len(self.v.env);
        const q = pattern$217(self, pat);
        const b = block$91(self, body);
        $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
        $1 = { $tag: "For", $: { mutable: mutable, pat: q, iter: $b.Box_new(it), body: b } };
      }
      break m$3;
    }
    if (($2.$tag === "Match")) {
      const scrutinee = $2.$.scrutinee;
      const arms = $2.$.arms;
      $1 = { $tag: "Match", $: { scrutinee: $b.Box_new(expr$215(self, scrutinee)), arms: arms$387(self, arms) } };
      break m$3;
    }
    if (($2.$tag === "Try")) {
      const body = $2.$.body;
      const pat = $2.$.pat;
      const handler = $2.$.handler;
      {
        const b = scopedBlock$386(self, body);
        const depth = $b.slice_len(self.v.env);
        const q = pattern$217(self, pat);
        const h = block$91(self, handler);
        $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
        $1 = { $tag: "Try", $: { body: b, pat: q, handler: h } };
      }
      break m$3;
    }
    if (($2.$tag === "Throw")) {
      const x = $2.$;
      $1 = { $tag: "Throw", $: $b.Box_new(expr$215(self, x)) };
      break m$3;
    }
    if (($2.$tag === "Yield")) {
      const x = $2.$;
      $1 = { $tag: "Yield", $: $b.Box_new(expr$215(self, x)) };
      break m$3;
    }
    if (($2.$tag === "Return")) {
      const x = $2.$;
      $1 = { $tag: "Return", $: optExpr$384(self, x) };
      break m$3;
    }
    if (($2.$tag === "Region")) {
      const name = $2.$.name;
      const body = $2.$.body;
      $1 = { $tag: "Region", $: { name: ident$374(self, name), body: scopedBlock$386(self, body) } };
      break m$3;
    }
    if (($2.$tag === "Handle")) {
      const body = $2.$.body;
      const effect = $2.$.effect;
      const arms = $2.$.arms;
      {
        const b = scopedBlock$386(self, body);
        const eff = ty$216(self, effect);
        const out = { v: $b.Vec_new() };
        for (const $30 of $rt.items(arms)) {
          const a = $30;
          const depth = $b.slice_len(self.v.env);
          for (const $31 of $rt.items(a.params)) {
            const p = $31;
            shadow$388(self, $b.String_asStr(p.name));
          }
          const $32 = a.resumes;
          m$33: {
            if (($32.$tag === "Some")) {
              const k = $32.$;
              {
                shadow$388(self, $b.String_asStr(k.name));
              }
              break m$33;
            }
            if (true) {
              {
              }
              break m$33;
            }
            $rt.unmatched($32);
          }
          const ps = { v: $b.Vec_new() };
          for (const $34 of $rt.items(a.params)) {
            const i = $34;
            $b.Vec_push(ps, ident$374(self, i));
          }
          let $35;
          const $36 = a.resumes;
          m$37: {
            if (($36.$tag === "Some")) {
              const i = $36.$;
              $35 = { $tag: "Some", $: ident$374(self, i) };
              break m$37;
            }
            if (($36.$tag === "None")) {
              $35 = { $tag: "None" };
              break m$37;
            }
            $rt.unmatched($36);
          }
          const resumes = $35;
          const op = ident$374(self, a.op);
          const ab = block$91(self, a.body);
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
          $b.Vec_push(out, { op: op, params: ps.v, resumes: resumes, body: ab });
        }
        $1 = { $tag: "Handle", $: { body: b, effect: eff, arms: out.v } };
      }
      break m$3;
    }
    if (($2.$tag === "Unsafe")) {
      const b = $2.$;
      $1 = { $tag: "Unsafe", $: scopedBlock$386(self, b) };
      break m$3;
    }
    if (($2.$tag === "Comptime")) {
      const inner = $2.$;
      return comptime$389(self, inner, $rt.copy(e.span));
      break m$3;
    }
    $rt.unmatched($2);
  }
  const kind = $1;
  return mk$380(self, kind, $rt.copy(span));
}
function ty$216(self, t) {
  const span = sp$214(self, $rt.copy(t.span));
  let $1;
  const $2 = t.kind;
  m$3: {
    if (($2.$tag === "Path")) {
      const segments = $2.$.segments;
      const args = $2.$.args;
      let $4;
      const $5 = lookup$390(self.v, $b.String_asStr($rt.idx(segments, 0n).name));
      m$6: {
        if (($5.$tag === "Some" && ($5.$.$tag === "Some"))) {
          $4 = true;
          break m$6;
        }
        if (true) {
          $4 = false;
          break m$6;
        }
        $rt.unmatched($5);
      }
      if ($4) {
        {
          let e = mk$380(self, { $tag: "Ident", $: $b.String_clone($rt.idx(segments, 0n).name) }, $rt.copy($rt.idx(segments, 0n).span));
          const $7 = $b.slice_len(segments);
          for (let i = 1n; i < $7; i++) {
            const s = clone$218($rt.idx(segments, i));
            const at = $rt.copy(s.span);
            e = mk$380(self, { $tag: "Field", $: { target: $b.Box_new(e), name: s } }, $rt.copy(at));
          }
          if (($b.slice_len(args) > 0n)) {
            fail$391($rt.copy(t.span), "a `comptime` type takes no type arguments");
          }
          const $8 = eval$$378(self, e);
          m$9: {
            if (($8.$tag === "Type")) {
              const x = $8.$;
              $1 = { $tag: "Spliced", $: spliceTy$379(self, x) };
              break m$9;
            }
            if (true) {
              const v = $8;
              $1 = fail$391($rt.copy(t.span), $b.String_asStr(("" + "expected a type, found " + cvKind$392(v))));
              break m$9;
            }
            $rt.unmatched($8);
          }
        }
        break m$3;
      }
    }
    if (($2.$tag === "Path")) {
      const segments = $2.$.segments;
      const args = $2.$.args;
      {
        const segs = { v: $b.Vec_new() };
        for (const $10 of $rt.items(segments)) {
          const i = $10;
          $b.Vec_push(segs, ident$374(self, i));
        }
        const tas = { v: $b.Vec_new() };
        for (const $11 of $rt.items(args)) {
          const a = $11;
          $b.Vec_push(tas, ty$216(self, a));
        }
        $1 = { $tag: "Path", $: { segments: segs.v, args: tas.v } };
      }
      break m$3;
    }
    if (($2.$tag === "Record")) {
      const fields = $2.$.fields;
      const rest = $2.$.rest;
      const $12 = fields$393(self, fields);
      let $13;
      const $14 = rest;
      m$15: {
        if (($14.$tag === "Some")) {
          const r = $14.$;
          $13 = { $tag: "Some", $: ident$374(self, r) };
          break m$15;
        }
        if (($14.$tag === "None")) {
          $13 = { $tag: "None" };
          break m$15;
        }
        $rt.unmatched($14);
      }
      $1 = { $tag: "Record", $: { fields: $12, rest: $13 } };
      break m$3;
    }
    if (($2.$tag === "Union")) {
      const tags = $2.$.tags;
      const includes = $2.$.includes;
      const rest = $2.$.rest;
      {
        const incs = { v: $b.Vec_new() };
        for (const $16 of $rt.items(includes)) {
          const x = $16;
          $b.Vec_push(incs, ty$216(self, x));
        }
        const ts = { v: $b.Vec_new() };
        for (const $17 of $rt.items(tags)) {
          const tg = $17;
          let $18;
          const $19 = tg.payload;
          m$20: {
            if (($19.$tag === "None")) {
              $18 = { $tag: "None" };
              break m$20;
            }
            if (($19.$tag === "Tuple")) {
              const xs = $19.$;
              {
                const out = { v: $b.Vec_new() };
                for (const $21 of $rt.items(xs)) {
                  const x = $21;
                  $b.Vec_push(out, ty$216(self, x));
                }
                $18 = { $tag: "Tuple", $: out.v };
              }
              break m$20;
            }
            if (($19.$tag === "Record")) {
              const fs = $19.$;
              $18 = { $tag: "Record", $: fields$393(self, fs) };
              break m$20;
            }
            $rt.unmatched($19);
          }
          const payload = $18;
          $b.Vec_push(ts, { name: ident$374(self, tg.name), payload: payload });
        }
        const $22 = ts.v;
        const $23 = incs.v;
        let $24;
        const $25 = rest;
        m$26: {
          if (($25.$tag === "Some")) {
            const r = $25.$;
            $24 = { $tag: "Some", $: ident$374(self, r) };
            break m$26;
          }
          if (($25.$tag === "None")) {
            $24 = { $tag: "None" };
            break m$26;
          }
          $rt.unmatched($25);
        }
        $1 = { $tag: "Union", $: { tags: $22, includes: $23, rest: $24 } };
      }
      break m$3;
    }
    if (($2.$tag === "Tuple")) {
      const ts = $2.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $27 of $rt.items(ts)) {
          const x = $27;
          $b.Vec_push(out, ty$216(self, x));
        }
        $1 = { $tag: "Tuple", $: out.v };
      }
      break m$3;
    }
    if (($2.$tag === "EmptyRow")) {
      $1 = { $tag: "EmptyRow" };
      break m$3;
    }
    if (($2.$tag === "Fn")) {
      const mode = $2.$.mode;
      const params = $2.$.params;
      const ret = $2.$.ret;
      const row = $2.$.uses;
      {
        const depth = $b.slice_len(self.v.env);
        const ps = params$385(self, params);
        const from = { v: $b.Vec_new() };
        for (const $28 of $rt.items(ret.from)) {
          const i = $28;
          $b.Vec_push(from, ident$374(self, i));
        }
        const r = { ty: ty$216(self, ret.ty), from: from.v };
        $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
        $1 = { $tag: "Fn", $: { mode: clone$394(mode), params: ps, ret: $b.Box_new(r), uses: uses$395(self, row) } };
      }
      break m$3;
    }
    if (($2.$tag === "Array")) {
      const elem = $2.$.elem;
      const len = $2.$.len;
      $1 = { $tag: "Array", $: { elem: $b.Box_new(ty$216(self, elem)), len: optExpr$384(self, len) } };
      break m$3;
    }
    if (($2.$tag === "Mut")) {
      const x = $2.$;
      $1 = { $tag: "Mut", $: $b.Box_new(ty$216(self, x)) };
      break m$3;
    }
    if (($2.$tag === "Readonly")) {
      const x = $2.$;
      $1 = { $tag: "Readonly", $: $b.Box_new(ty$216(self, x)) };
      break m$3;
    }
    if (($2.$tag === "Ptr")) {
      const x = $2.$;
      $1 = { $tag: "Ptr", $: $b.Box_new(ty$216(self, x)) };
      break m$3;
    }
    if (($2.$tag === "Dyn")) {
      const path = $2.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $29 of $rt.items(path)) {
          const i = $29;
          $b.Vec_push(out, ident$374(self, i));
        }
        $1 = { $tag: "Dyn", $: out.v };
      }
      break m$3;
    }
    if (($2.$tag === "Expr")) {
      const e = $2.$;
      $1 = { $tag: "Expr", $: $b.Box_new(expr$215(self, e)) };
      break m$3;
    }
    if (($2.$tag === "Spliced")) {
      const i = $2.$;
      $1 = { $tag: "Spliced", $: i };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const kind = $1;
  return { kind: kind, span: span };
}
function pattern$217(self, p) {
  const span = sp$214(self, $rt.copy(p.span));
  let $1;
  const $2 = p.kind;
  m$3: {
    if (($2.$tag === "Wild")) {
      $1 = { $tag: "Wild" };
      break m$3;
    }
    if (($2.$tag === "Bind")) {
      const n = $2.$;
      {
        shadow$388(self, $b.String_asStr(n));
        $1 = { $tag: "Bind", $: $b.String_clone(n) };
      }
      break m$3;
    }
    if (($2.$tag === "Lit")) {
      const e = $2.$;
      const $4 = e.kind;
      m$5: {
        if (($4.$tag === "Comptime")) {
          const inner = $4.$;
          {
            const v = eval$$378(self, inner);
            $1 = { $tag: "Lit", $: $b.Box_new(splice$371(self, v, $rt.copy(e.span))) };
          }
          break m$5;
        }
        if (true) {
          $1 = { $tag: "Lit", $: $b.Box_new(expr$215(self, e)) };
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$3;
    }
    if (($2.$tag === "Tag")) {
      const name = $2.$.name;
      const args = $2.$.args;
      $1 = { $tag: "Tag", $: { name: $b.String_clone(name), args: tagPats$396(self, args) } };
      break m$3;
    }
    if (($2.$tag === "TagAt")) {
      const name = $2.$.name;
      const args = $2.$.args;
      {
        const n = ctName$373(self, name);
        $1 = { $tag: "Tag", $: { name: n, args: tagPats$396(self, args) } };
      }
      break m$3;
    }
    if (($2.$tag === "Tuple")) {
      const ps = $2.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $6 of $rt.items(ps)) {
          const x = $6;
          $b.Vec_push(out, pattern$217(self, x));
        }
        $1 = { $tag: "Tuple", $: out.v };
      }
      break m$3;
    }
    if (($2.$tag === "Record")) {
      const name = $2.$.name;
      const fields = $2.$.fields;
      {
        let $7;
        const $8 = name;
        m$9: {
          if (($8.$tag === "Some")) {
            const ps = $8.$;
            {
              const out = { v: $b.Vec_new() };
              for (const $10 of $rt.items(ps)) {
                const i = $10;
                $b.Vec_push(out, ident$374(self, i));
              }
              $7 = { $tag: "Some", $: out.v };
            }
            break m$9;
          }
          if (($8.$tag === "None")) {
            $7 = { $tag: "None" };
            break m$9;
          }
          $rt.unmatched($8);
        }
        const path = $7;
        $1 = { $tag: "Record", $: { name: path, fields: fieldPats$397(self, fields) } };
      }
      break m$3;
    }
    if (($2.$tag === "Or")) {
      const ps = $2.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $11 of $rt.items(ps)) {
          const x = $11;
          $b.Vec_push(out, pattern$217(self, x));
        }
        $1 = { $tag: "Or", $: out.v };
      }
      break m$3;
    }
    $rt.unmatched($2);
  }
  const kind = $1;
  return { kind: kind, span: span, id: id$398(self) };
}
function clone$218(self) {
  {
    return { name: $b.String_clone(self.name), span: clone$94(self.span) };
  }
}
function clone$219(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$399(x));
  }
  return v.v;
}
function clone$220(self) {
  {
    return { from: clone$400(self.from), ty: clone$193(self.ty) };
  }
}
function clone$221(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$401(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$222(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Let")) {
      const x = $1.$;
      return { $tag: "Let", $: clone$402(x) };
      break m$2;
    }
    if (($1.$tag === "Defer")) {
      const x = $1.$;
      return { $tag: "Defer", $: clone$60(x) };
      break m$2;
    }
    if (($1.$tag === "Expr")) {
      const x = $1.$;
      return { $tag: "Expr", $: clone$60(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$223(self) {
  return $b.Box_new(clone$60($b.Box_get(self)));
}
function clone$224(self) {
  const m = { v: $b.HashMap_new() };
  const $1 = $b.Gen_each($b.HashMap_entries(self));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const k = $4[0];
    const v = $4[1];
    $b.HashMap_insert(m, $b.String_clone(k), clone$403(v));
  }
  return m.v;
}
function clone$225(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$23(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$226(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$360(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function primFromName$227(s) {
  const $1 = indexOf$404($c5$PRIMS, s);
  m$2: {
    if (($1.$tag === "Some")) {
      const i = $1.$;
      return { $tag: "Some", $: primAt$405(i) };
      break m$2;
    }
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eq$228(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "I8") && ($1[1].$tag === "I8"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "I16") && ($1[1].$tag === "I16"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "I32") && ($1[1].$tag === "I32"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "I64") && ($1[1].$tag === "I64"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "I128") && ($1[1].$tag === "I128"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Isize") && ($1[1].$tag === "Isize"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "U8") && ($1[1].$tag === "U8"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "U16") && ($1[1].$tag === "U16"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "U32") && ($1[1].$tag === "U32"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "U64") && ($1[1].$tag === "U64"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Usize") && ($1[1].$tag === "Usize"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "F32") && ($1[1].$tag === "F32"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "F64") && ($1[1].$tag === "F64"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Bool") && ($1[1].$tag === "Bool"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Str") && ($1[1].$tag === "Str"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Void") && ($1[1].$tag === "Void"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Never") && ($1[1].$tag === "Never"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Type") && ($1[1].$tag === "Type"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function includes$229(self, x) {
  for (const $1 of $rt.items(self)) {
    const y = $1;
    if ((y === x)) {
      return true;
    }
  }
  return false;
}
function substParams$230(t, params, args) {
  return subst$308(t, substMap$162(params, args));
}
function ensureInstance$231(self, d, args) {
  let $1;
  const $2 = new $rt.FieldRef($rt.idx(self.v.defs, d), "templateFields");
  const $3 = $2.v;
  m$4: {
    if (($3.$tag === "Some")) {
      const fs = new $rt.FieldRef($3, "$");
      $1 = clone$356(fs.v);
      break m$4;
    }
    if (($3.$tag === "None")) {
      return;
      break m$4;
    }
    $rt.unmatched($3);
  }
  const fields = $1;
  const key = ("" + String(d) + "|" + keyArgs$159(args));
  if (($b.HashMap_has(self.v.instances, $b.String_asStr(key)) || (!every$298($b.slice_iter(args), ((a) => {
  return concreteArg$406(a);
  }))))) {
    return;
  }
  $b.HashMap_insert(new $rt.FieldRef(self.v, "instances"), $b.String_clone(key), $b.Vec_new());
  const params = clone$73($rt.idx(self.v.defs, d).params);
  const module = $rt.idx(self.v.defs, d).module;
  const env = { v: $b.Vec_new() };
  const $5 = min$146($b.slice_len(params), $b.slice_len(args));
  for (let i = 0n; i < $5; i++) {
    const $6 = $rt.idx(args, i);
    m$7: {
      if (($6.$tag === "Ty")) {
        const t = $6.$;
        if ($rt.idx(params, i).isComptime) {
          $b.Vec_push(env, [$b.String_clone($rt.idx(params, i).sym.name), { $tag: "Type", $: clone$23(t) }]);
          break m$7;
        }
      }
      if (($6.$tag === "Len" && ($6.$.$tag === "Known"))) {
        const n = $6.$.$;
        $b.Vec_push(env, [$b.String_clone($rt.idx(params, i).sym.name), { $tag: "Int", $: $rt.wrap_i128(n) }]);
        break m$7;
      }
      if (true) {
        {
        }
        break m$7;
      }
      $rt.unmatched($6);
    }
  }
  const ex = { v: expander$27(self, module, { $tag: "None" }, env.v) };
  let $8;
  const $9 = structFields$407(ex, fields);
  m$10: {
    if (($9.$tag === "Some")) {
      const fs = $9.$;
      $8 = fs;
      break m$10;
    }
    if (($9.$tag === "None")) {
      {
        $b.HashMap_remove(new $rt.FieldRef(self.v, "instances"), $b.String_asStr(key));
        return;
        $8 = undefined;
      }
      break m$10;
    }
    $rt.unmatched($9);
  }
  const expanded = $8;
  const scope = withParams$32(moduleScope$31(module), params);
  const fs = { v: $b.Vec_new() };
  for (const $11 of $rt.items(expanded)) {
    const f = $11;
    const t = elabTy$101(self, f.ty, scope);
    $b.Vec_push(fs, [$b.String_clone(f.name.name), substParams$230(t, params, args)]);
  }
  if ((!$rt.idx(self.v.defs, d).view)) {
    const $14 = find$408($b.slice_iter(fs.v), (($0$$12) => {
  {
    const $13 = $0$$12;
    const t = $13[1];
    return (class$$187(self.v, t) === 2n);
  }
    }));
    m$15: {
      if (($14.$tag === "Some")) {
        const name = $14.$[0];
        const t = $14.$[1];
        {
          const shown = show$136(self.v, { $tag: "Named", $: [d, clone$197(args)] });
          const ft = show$136(self.v, t);
          error$62(self, module, $rt.copy($rt.idx(self.v.defs, d).span), $b.String_asStr(("" + "`" + shown + "` holds a borrow in `" + name + "` (`" + ft + "`): declare it `view struct` if it is a temporary view")));
        }
        break m$15;
      }
      if (true) {
        {
        }
        break m$15;
      }
      $rt.unmatched($14);
    }
  }
  $b.HashMap_insert(new $rt.FieldRef(self.v, "instances"), key, fs.v);
  return undefined;
}
function rowTail$232(self, name, scope) {
  const $1 = $b.HashMap_get(scope.params, $b.String_asStr(name.name));
  m$2: {
    if (($1.$tag === "Some" && (($1.$[1].$tag === "Row")))) {
      const sym = $1.$[0];
      return { $tag: "Param", $: clone$34(sym) };
      break m$2;
    }
    if (true) {
      {
        error$62(self, scope.module, $rt.copy(name.span), $b.String_asStr(("" + "`" + name.name + "` is not a row parameter")));
        return { $tag: "Closed" };
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function labelGet$233(labels, k) {
  const $1 = labelIndex$268(labels, k);
  m$2: {
    if (($1.$tag === "Some")) {
      const i = $1.$;
      return { $tag: "Some", $: clone$23($rt.idx($rt.idx(labels, i), 1n)) };
      break m$2;
    }
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eq$234(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Var") && ($1[1].$tag === "Var"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$266(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Param") && ($1[1].$tag === "Param"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$262(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Prim") && ($1[1].$tag === "Prim"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$228(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Named") && ($1[1].$tag === "Named"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$409(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Record") && ($1[1].$tag === "Record"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$410(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Union") && ($1[1].$tag === "Union"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$410(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Tuple") && ($1[1].$tag === "Tuple"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$411(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Array") && ($1[1].$tag === "Array"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$412(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Slice") && ($1[1].$tag === "Slice"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$413(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Borrow") && ($1[1].$tag === "Borrow"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$414(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Fn") && ($1[1].$tag === "Fn"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$415(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Assoc") && ($1[1].$tag === "Assoc"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$416(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Error") && ($1[1].$tag === "Error"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function elabLen$235(self, e, scope) {
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "Int")) {
      const s = $1.$;
      let $3;
      const $4 = $b.parseInt($b.String_asStr(s));
      m$5: {
        if (($4.$tag === "Some")) {
          const n = $4.$;
          $3 = $rt.wrap_u64(n);
          break m$5;
        }
        if (($4.$tag === "None")) {
          $3 = 0n;
          break m$5;
        }
        $rt.unmatched($4);
      }
      return { $tag: "Known", $: $3 };
      break m$2;
    }
    if (($1.$tag === "Ident")) {
      const n = $1.$;
      const $6 = $b.HashMap_get(scope.params, $b.String_asStr(n));
      m$7: {
        if (($6.$tag === "Some" && (($6.$[1].$tag === "Len")))) {
          const sym = $6.$[0];
          return { $tag: "Param", $: clone$34(sym) };
          break m$7;
        }
        if (true) {
          {
            error$62(self, scope.module, $rt.copy(e.span), $b.String_asStr(("" + "`" + n + "` is not a `comptime` length")));
            return { $tag: "Known", $: 0n };
          }
          break m$7;
        }
        $rt.unmatched($6);
      }
      break m$2;
    }
    if (true) {
      {
        error$62(self, scope.module, $rt.copy(e.span), "array lengths must be literals or `comptime` parameters for now");
        return { $tag: "Known", $: 0n };
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function exprInner$236(self, e, expected) {
  const span = $rt.copy(e.span);
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "TypeRef")) {
      const i = $1.$;
      {
        const shown = show$123(self.v, clone$23($rt.idx(self.v.p.v.spliced, i)));
        err$108(self, $rt.copy(span), $b.String_asStr(("" + "the type `" + shown + "` is not a value")));
        return { $tag: "Error" };
      }
      break m$2;
    }
    if ((($1.$tag === "FieldAt") || ($1.$tag === "TagAt"))) {
      {
        err$108(self, $rt.copy(span), "a computed name `[e]` belongs in code that `comptime` generates");
        return { $tag: "Error" };
      }
      break m$2;
    }
    if (($1.$tag === "Int")) {
      let $3;
      const $4 = expected;
      m$5: {
        if (($4.$tag === "Some")) {
          const x = $4.$;
          $3 = { $tag: "Some", $: strip$124(self.v, x) };
          break m$5;
        }
        if (($4.$tag === "None")) {
          $3 = { $tag: "None" };
          break m$5;
        }
        $rt.unmatched($4);
      }
      const $6 = $3;
      m$7: {
        if (($6.$tag === "Some" && ($6.$.$tag === "Prim"))) {
          const p = $6.$.$;
          if (isFloat$417(p)) {
            return { $tag: "Prim", $: p };
            break m$7;
          }
        }
        if (true) {
          return freshKind$418(new $rt.FieldRef(self.v, "s"), { $tag: "Int" });
          break m$7;
        }
        $rt.unmatched($6);
      }
      break m$2;
    }
    if (($1.$tag === "Float")) {
      return freshKind$418(new $rt.FieldRef(self.v, "s"), { $tag: "Float" });
      break m$2;
    }
    if (($1.$tag === "Byte")) {
      return { $tag: "Prim", $: { $tag: "U8" } };
      break m$2;
    }
    if (($1.$tag === "Str")) {
      return { $tag: "Prim", $: { $tag: "Str" } };
      break m$2;
    }
    if (($1.$tag === "Bool")) {
      return boolTy$189();
      break m$2;
    }
    if (($1.$tag === "Template")) {
      const pieces = $1.$;
      {
        for (const $8 of $rt.items(pieces)) {
          const piece = $8;
          const $9 = piece;
          m$10: {
            if (($9.$tag === "Expr")) {
              const x = $9.$;
              {
                const t = expr$102(self, x, { $tag: "None" });
                $b.Vec_push(new $rt.FieldRef(self.v, "pendingOps"), [x.id, $rt.copy(x.span), t, $b.str_toString("Show"), $b.str_toString("show")]);
              }
              break m$10;
            }
            if (true) {
              {
              }
              break m$10;
            }
            $rt.unmatched($9);
          }
        }
        return stringTy$419(self.v);
      }
      break m$2;
    }
    if (($1.$tag === "Ident")) {
      const name = $1.$;
      return ident$420(self, $b.String_asStr(name), $rt.copy(span), { $tag: "Some", $: e.id });
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const name = $1.$.name;
      const args = $1.$.args;
      return tag$421(self, $b.String_asStr(name), args, expected, $rt.copy(span), e.id);
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const name = $1.$.name;
      const fields = $1.$.fields;
      return record$422(self, name, fields, expected, $rt.copy(span));
      break m$2;
    }
    if (($1.$tag === "List")) {
      const items = $1.$;
      return list$423(self, items, expected);
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      const name = $1.$.name;
      {
        const t = expr$102(self, target, { $tag: "None" });
        return field$241(self, t, $b.String_asStr(name.name), $rt.copy(name.span));
      }
      break m$2;
    }
    if (($1.$tag === "Index")) {
      const target = $1.$.target;
      const index = $1.$.index;
      return index$424(self, target, index, $rt.copy(span));
      break m$2;
    }
    if (($1.$tag === "Call")) {
      const callee = $1.$.callee;
      const typeArgs = $1.$.typeArgs;
      const args = $1.$.args;
      return call$425(self, callee, typeArgs, args, expected, e);
      break m$2;
    }
    if (($1.$tag === "Unary")) {
      const op = $1.$.op;
      const operand = $1.$.operand;
      {
        const t = expr$102(self, operand, { $tag: "None" });
        const v = strip$124(self.v, t);
        if ((op === "!")) {
          coerce$44(self, v, boolTy$189(), $rt.copy(operand.span));
          return boolTy$189();
        } else {
          {
            return v;
          }
        }
      }
      break m$2;
    }
    if (($1.$tag === "BorrowMut")) {
      const inner = $1.$;
      {
        let $11;
        const $12 = expected;
        m$13: {
          if (($12.$tag === "Some")) {
            const x = $12.$;
            $11 = { $tag: "Some", $: strip$124(self.v, x) };
            break m$13;
          }
          if (($12.$tag === "None")) {
            $11 = { $tag: "None" };
            break m$13;
          }
          $rt.unmatched($12);
        }
        const want = $11;
        const t = expr$102(self, inner, want);
        const $14 = resolve$109(self.v.s, t);
        m$15: {
          if (($14.$tag === "Borrow" && $14.$[0] === true)) {
            return t;
            break m$15;
          }
          if (($14.$tag === "Borrow" && $14.$[0] === false)) {
            {
              err$108(self, $rt.copy(span), "cannot lend a `readonly` borrow as `mut`");
              return t;
            }
            break m$15;
          }
          if (true) {
            const other = $14;
            return { $tag: "Borrow", $: [true, $b.Box_new(other)] };
            break m$15;
          }
          $rt.unmatched($14);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Binary")) {
      const op = $1.$.op;
      const lhs = $1.$.lhs;
      const rhs = $1.$.rhs;
      return binary$426(self, $b.String_asStr(op), lhs, rhs, e);
      break m$2;
    }
    if (($1.$tag === "Assign")) {
      const op = $1.$.op;
      const target = $1.$.target;
      const value = $1.$.value;
      {
        const t = expr$102(self, target, { $tag: "None" });
        const v = strip$124(self.v, t);
        const found0 = expr$102(self, value, { $tag: "Some", $: clone$23(v) });
        let $16;
        if ((op === "=")) {
          $16 = found0;
        } else {
          {
            $16 = strip$124(self.v, found0);
          }
        }
        const found = $16;
        coerce$44(self, found, v, $rt.copy(value.span));
        return voidTy$112();
      }
      break m$2;
    }
    if (($1.$tag === "Cast")) {
      const expr = $1.$.expr;
      const ty = $1.$.ty;
      {
        expr$102(self, expr, { $tag: "None" });
        const scope = clone$97(self.v.scope);
        return elabTy$101(self.v.p, ty, scope);
      }
      break m$2;
    }
    if (($1.$tag === "Range")) {
      {
        err$108(self, $rt.copy(span), "a range can only be used to index");
        return { $tag: "Error" };
      }
      break m$2;
    }
    if (($1.$tag === "Lambda")) {
      const params = $1.$.params;
      const body = $1.$.body;
      return lambda$427(self, params, body, expected);
      break m$2;
    }
    if (($1.$tag === "Block")) {
      const b = $1.$;
      return block$43(self, b, expected);
      break m$2;
    }
    if (($1.$tag === "If")) {
      const cond = $1.$.cond;
      const then = $1.$.then;
      const otherwise = $1.$.otherwise;
      {
        check$428(self, cond, boolTy$189());
        const $17 = otherwise;
        m$18: {
          if (($17.$tag === "Some")) {
            const o = $17.$;
            if (((unknown$429(self.v, expected) && tagBuiltBlock$430(then)) && (!tagBuilt$431(o)))) {
              {
                const b = expr$102(self, o, { $tag: "None" });
                let $19;
                if (isNever$110(resolve$109(self.v.s, b))) {
                  $19 = { $tag: "None" };
                } else {
                  {
                    $19 = { $tag: "Some", $: clone$23(b) };
                  }
                }
                const anchor = $19;
                const a = block$43(self, then, anchor);
                return join$432(self, [[a, $rt.copy(then.span)], [b, $rt.copy(o.span)]], expected);
              }
              break m$18;
            }
          }
          if (($17.$tag === "Some")) {
            const o = $17.$;
            {
              const a = block$43(self, then, clone$225(expected));
              let $20;
              if (isNever$110(resolve$109(self.v.s, a))) {
                $20 = { $tag: "None" };
              } else {
                {
                  $20 = { $tag: "Some", $: clone$23(a) };
                }
              }
              const first = $20;
              let $21;
              const $22 = expected;
              m$23: {
                if (($22.$tag === "Some")) {
                  const x = $22.$;
                  $21 = { $tag: "Some", $: clone$23(x) };
                  break m$23;
                }
                if (($22.$tag === "None")) {
                  $21 = first;
                  break m$23;
                }
                $rt.unmatched($22);
              }
              const want = $21;
              const b = expr$102(self, o, want);
              return join$432(self, [[a, $rt.copy(then.span)], [b, $rt.copy(o.span)]], expected);
            }
            break m$18;
          }
          if (($17.$tag === "None")) {
            {
              block$43(self, then, expected);
              return voidTy$112();
            }
            break m$18;
          }
          $rt.unmatched($17);
        }
      }
      break m$2;
    }
    if (($1.$tag === "While")) {
      const cond = $1.$.cond;
      const body = $1.$.body;
      {
        check$428(self, cond, boolTy$189());
        block$43(self, body, { $tag: "None" });
        return voidTy$112();
      }
      break m$2;
    }
    if (($1.$tag === "For")) {
      const pat = $1.$.pat;
      const iter = $1.$.iter;
      const body = $1.$.body;
      return forOf$433(self, pat, iter, body);
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const scrutinee = $1.$.scrutinee;
      const arms = $1.$.arms;
      return matchExpr$434(self, scrutinee, arms, expected, $rt.copy(span));
      break m$2;
    }
    if (($1.$tag === "Try")) {
      const body = $1.$.body;
      const pat = $1.$.pat;
      const handler = $1.$.handler;
      return tryCatch$435(self, body, pat, handler, expected);
      break m$2;
    }
    if (($1.$tag === "Throw")) {
      const value = $1.$;
      {
        const t = expr$102(self, value, { $tag: "None" });
        let $24;
        const $25 = strip$124(self.v, t);
        m$26: {
          if ((($25.$tag === "Record") || ($25.$tag === "Tuple") || ($25.$tag === "Array") || ($25.$tag === "Slice") || ($25.$tag === "Fn"))) {
            $24 = true;
            break m$26;
          }
          if (($25.$tag === "Prim")) {
            const p = $25.$;
            $24 = !eq$228(p, { $tag: "Never" });
            break m$26;
          }
          if (($25.$tag === "Named")) {
            const d = $25.$[0];
            const $27 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, d), "kind");
            const $28 = $27.v;
            m$29: {
              if (($28.$tag === "Struct")) {
                $24 = true;
                break m$29;
              }
              if (true) {
                $24 = false;
                break m$29;
              }
              $rt.unmatched($28);
            }
            break m$26;
          }
          if (true) {
            $24 = false;
            break m$26;
          }
          $rt.unmatched($25);
        }
        const notATag = $24;
        if (notATag) {
          const shown = show$123(self.v, t);
          err$108(self, $rt.copy(value.span), $b.String_asStr(("" + "a failure is a tag union (\xc2\xa75.4), and `" + shown + "` is not: throw a tag, such as `#Failed { \xe2\x80\xa6 }`")));
        }
        const row = { effs: [eff$436(self.v, "Fail", $b.Vec_new(), [t])], tail: { $tag: "Closed" } };
        perform$437(self, row, $rt.copy(span), e.id);
        return neverTy$111();
      }
      break m$2;
    }
    if (($1.$tag === "Yield")) {
      const value = $1.$;
      {
        const yieldDef = known$104(self.v, "Yield");
        const declared = find$438($b.slice_iter(expandEffs$105(self.v.s, clone$40(self.v.allowed)).effs), ((x) => {
  return (x.def === yieldDef);
        }));
        let $30;
        let $31;
        const $32 = declared;
        m$33: {
          if (($32.$tag === "Some")) {
            const d = $32.$;
            const $34 = first$263(d.args);
            m$35: {
              if (($34.$tag === "Some")) {
                const a = $34.$;
                $31 = { $tag: "Some", $: clone$23(a) };
                break m$35;
              }
              if (($34.$tag === "None")) {
                $31 = { $tag: "None" };
                break m$35;
              }
              $rt.unmatched($34);
            }
            break m$33;
          }
          if (($32.$tag === "None")) {
            $31 = { $tag: "None" };
            break m$33;
          }
          $rt.unmatched($32);
        }
        const $36 = $31;
        m$37: {
          if (($36.$tag === "Some")) {
            const item = $36.$;
            {
              check$428(self, value, item);
              $30 = item;
            }
            break m$37;
          }
          if (($36.$tag === "None")) {
            $30 = expr$102(self, value, { $tag: "None" });
            break m$37;
          }
          $rt.unmatched($36);
        }
        const t = $30;
        const row = { effs: [eff$436(self.v, "Yield", $b.Vec_new(), [t])], tail: { $tag: "Closed" } };
        perform$437(self, row, $rt.copy(span), e.id);
        return voidTy$112();
      }
      break m$2;
    }
    if (($1.$tag === "Return")) {
      const value = $1.$;
      {
        const ret = clone$23(self.v.ret);
        const $38 = value;
        m$39: {
          if (($38.$tag === "Some")) {
            const v = $38.$;
            {
              check$428(self, v, ret);
            }
            break m$39;
          }
          if (($38.$tag === "None")) {
            coerce$44(self, voidTy$112(), ret, $rt.copy(span));
            break m$39;
          }
          $rt.unmatched($38);
        }
        return neverTy$111();
      }
      break m$2;
    }
    if ((($1.$tag === "Break") || ($1.$tag === "Continue"))) {
      return neverTy$111();
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const name = $1.$.name;
      const body = $1.$.body;
      return region$439(self, name, body, expected, $rt.copy(span));
      break m$2;
    }
    if (($1.$tag === "Handle")) {
      const body = $1.$.body;
      const effect = $1.$.effect;
      const arms = $1.$.arms;
      return handle$440(self, body, effect, arms, expected, e);
      break m$2;
    }
    if (($1.$tag === "Unsafe")) {
      const b = $1.$;
      return block$43(self, b, expected);
      break m$2;
    }
    if (($1.$tag === "Comptime")) {
      const inner = $1.$;
      return expr$102(self, inner, expected);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function tryUnify$237(self, a, b) {
  return tryUnify$441(new $rt.FieldRef(self.v, "s"), a, b);
}
function fresh$238(self) {
  return freshKind$418(self, { $tag: "Any" });
}
function unify$239(self, a, b) {
  const x = resolve$109(self.v, a);
  const y = resolve$109(self.v, b);
  const $1 = [x, y];
  m$2: {
    if (((($1[0].$tag === "Error")) || (($1[1].$tag === "Error")))) {
      {
        return undefined;
      }
      break m$2;
    }
    if (((($1[0].$tag === "Prim" && ($1[0].$.$tag === "Never"))) || (($1[1].$tag === "Prim" && ($1[1].$.$tag === "Never"))))) {
      {
        return undefined;
      }
      break m$2;
    }
    if (((($1[0].$tag === "Var")) || (($1[1].$tag === "Var")))) {
      let v, other;
      if ((($1[0].$tag === "Var"))) { v = $1[0].$; other = $1[1]; }
      else if ((($1[1].$tag === "Var"))) { v = $1[1].$; other = $1[0]; }
      return bindTy$442(self, v, other);
      break m$2;
    }
    if (((($1[0].$tag === "Tuple") && ($1[1].$tag === "Prim" && ($1[1].$.$tag === "Void"))) || (($1[0].$tag === "Prim" && ($1[0].$.$tag === "Void")) && ($1[1].$tag === "Tuple")))) {
      let ts;
      if ((($1[0].$tag === "Tuple") && ($1[1].$tag === "Prim" && ($1[1].$.$tag === "Void")))) { ts = $1[0].$; }
      else if ((($1[0].$tag === "Prim" && ($1[0].$.$tag === "Void")) && ($1[1].$tag === "Tuple"))) { ts = $1[1].$; }
      if (($b.slice_len(ts) === 1n)) {
        return unify$239(self, $rt.idx(ts, 0n), voidTy$112());
        break m$2;
      }
    }
    if ((($1[0].$tag === "Param") && ($1[1].$tag === "Param"))) {
      const p = $1[0].$;
      const q = $1[1].$;
      if (eq$262(p, q)) {
        {
          return undefined;
        }
        break m$2;
      }
    }
    if ((($1[0].$tag === "Prim") && ($1[1].$tag === "Prim"))) {
      const p = $1[0].$;
      const q = $1[1].$;
      if (eq$228(p, q)) {
        {
          return undefined;
        }
        break m$2;
      }
    }
    if ((($1[0].$tag === "Named") && ($1[1].$tag === "Named"))) {
      const d1 = $1[0].$[0];
      const a1 = $1[0].$[1];
      const d2 = $1[1].$[0];
      const a2 = $1[1].$[1];
      if (((d1 === d2) && ($b.slice_len(a1) === $b.slice_len(a2)))) {
        {
          const $3 = $b.slice_len(a1);
          for (let i = 0n; i < $3; i++) {
            unifyArg$443(self, $rt.idx(a1, i), $rt.idx(a2, i));
          }
          return undefined;
        }
        break m$2;
      }
    }
    if (((($1[0].$tag === "Record") && ($1[1].$tag === "Record")) || (($1[0].$tag === "Union") && ($1[1].$tag === "Union")))) {
      let r1, r2;
      if ((($1[0].$tag === "Record") && ($1[1].$tag === "Record"))) { r1 = $1[0].$; r2 = $1[1].$; }
      else if ((($1[0].$tag === "Union") && ($1[1].$tag === "Union"))) { r1 = $1[0].$; r2 = $1[1].$; }
      return unifyRows$444(self, r1, r2);
      break m$2;
    }
    if ((($1[0].$tag === "Tuple") && ($1[1].$tag === "Tuple"))) {
      const t1 = $1[0].$;
      const t2 = $1[1].$;
      if (($b.slice_len(t1) === $b.slice_len(t2))) {
        {
          const $4 = $b.slice_len(t1);
          for (let i = 0n; i < $4; i++) {
            unify$239(self, $rt.idx(t1, i), $rt.idx(t2, i));
          }
          return undefined;
        }
        break m$2;
      }
    }
    if ((($1[0].$tag === "Array") && ($1[1].$tag === "Array"))) {
      const t1 = $1[0].$[0];
      const l1 = $1[0].$[1];
      const t2 = $1[1].$[0];
      const l2 = $1[1].$[1];
      {
        unify$239(self, t1, t2);
        unifyLen$445(self, l1, l2);
        return undefined;
      }
      break m$2;
    }
    if ((($1[0].$tag === "Slice") && ($1[1].$tag === "Slice"))) {
      const t1 = $1[0].$;
      const t2 = $1[1].$;
      return unify$239(self, t1, t2);
      break m$2;
    }
    if ((($1[0].$tag === "Borrow") && ($1[1].$tag === "Borrow"))) {
      const m1 = $1[0].$[0];
      const t1 = $1[0].$[1];
      const m2 = $1[1].$[0];
      const t2 = $1[1].$[1];
      if ((m1 === m2)) {
        return unify$239(self, t1, t2);
        break m$2;
      }
    }
    if ((($1[0].$tag === "Fn") && ($1[1].$tag === "Fn"))) {
      const f1 = $1[0].$;
      const f2 = $1[1].$;
      if (($b.slice_len(f1.params) === $b.slice_len(f2.params))) {
        {
          const $5 = $b.slice_len(f1.params);
          for (let i = 0n; i < $5; i++) {
            unify$239(self, $rt.idx(f1.params, i), $rt.idx(f2.params, i));
          }
          unify$239(self, f1.ret, f2.ret);
          effSubOrMismatch$446(self, f1.effects, f2.effects);
          effSubOrMismatch$446(self, f2.effects, f1.effects);
          return undefined;
        }
        break m$2;
      }
    }
    if ((($1[0].$tag === "Assoc") && ($1[1].$tag === "Assoc"))) {
      const t1 = $1[0].$[0];
      const n1 = $1[0].$[1];
      const t2 = $1[1].$[0];
      const n2 = $1[1].$[1];
      if (eq$6(n1, n2)) {
        return unify$239(self, t1, t2);
        break m$2;
      }
    }
    if (true) {
      throw new $rt.Fail({ $tag: "Mismatch" });
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function unsealed$240(self, d, verb, span) {
  if (((($rt.idx(self.v.p.v.defs, d).module !== self.v.module) && ($b.slice_len($rt.idx(self.v.p.v.defs, d).private) > 0n)) && !eq$447(self.v.privileged, { $tag: "Some", $: d }))) {
    const msg = ("" + "`" + $rt.idx(self.v.p.v.defs, d).name + "` has private fields, so it cannot be " + verb + " outside its module");
    err$108(self, $rt.copy(span), $b.String_asStr(msg));
    return undefined;
  }
}
function field$241(self, t, name, span) {
  const base = strip$124(self.v, t);
  const $1 = base;
  m$2: {
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        if (((d === known$104(self.v, "Box")) || (d === known$104(self.v, "Arc")))) {
          const $3 = first$258(args);
          m$4: {
            if (($3.$tag === "Some" && ($3.$.$tag === "Ty"))) {
              const inner = $3.$.$;
              {
                return field$241(self, clone$23(inner), name, $rt.copy(span));
              }
              break m$4;
            }
            if (true) {
              {
              }
              break m$4;
            }
            $rt.unmatched($3);
          }
        }
        const zonked = { v: $b.Vec_new() };
        for (const $5 of $rt.items(args)) {
          const a = $5;
          $b.Vec_push(zonked, zonkArg$145(self.v.s, a));
        }
        ensureInstance$231(self.v.p, d, zonked.v);
        if (failedInstance$448(self.v.p.v, d, zonked.v)) {
          return { $tag: "Error" };
        }
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const $6 = base;
  m$7: {
    if (($6.$tag === "Named")) {
      const d = $6.$[0];
      const args = $6.$[1];
      const $8 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, d), "kind");
      const $9 = $8.v;
      m$10: {
        if (($9.$tag === "Struct" && ($9.$.fields.$tag === "Some"))) {
          {
            const zonked = { v: $b.Vec_new() };
            for (const $11 of $rt.items(args)) {
              const a = $11;
              $b.Vec_push(zonked, zonkArg$145(self.v.s, a));
            }
            let $12;
            const $13 = structFields$449(self.v.p.v, d, zonked.v);
            m$14: {
              if (($13.$tag === "Some")) {
                const fs = $13.$;
                $12 = fs;
                break m$14;
              }
              if (($13.$tag === "None")) {
                $12 = $b.Vec_new();
                break m$14;
              }
              $rt.unmatched($13);
            }
            const fields = $12;
            const $17 = find$408($b.slice_iter(fields), (($0$$15) => {
  {
    const $16 = $0$$15;
    const k = $16[0];
    return (k === name);
  }
            }));
            m$18: {
              if (($17.$tag === "Some")) {
                const ft = $17.$[1];
                {
                  const hidden = ((($rt.idx(self.v.p.v.defs, d).module !== self.v.module) && some$450($b.slice_iter($rt.idx(self.v.p.v.defs, d).private), ((f) => {
  return (f === name);
                  }))) && !eq$447(self.v.privileged, { $tag: "Some", $: d }));
                  if (hidden) {
                    err$108(self, $rt.copy(span), $b.String_asStr(("" + "`" + name + "` is a private field of `" + $rt.idx(self.v.p.v.defs, d).name + "`")));
                  }
                  return substParams$230(ft, $rt.idx(self.v.p.v.defs, d).params, args);
                }
                break m$18;
              }
              if (true) {
                {
                }
                break m$18;
              }
              $rt.unmatched($17);
            }
          }
          break m$10;
        }
        if (($9.$tag === "Struct" && ($9.$.fields.$tag === "None"))) {
          {
            err$108(self, $rt.copy(span), $b.String_asStr(("" + "the fields of `" + $rt.idx(self.v.p.v.defs, d).name + "` are private")));
            return { $tag: "Error" };
          }
          break m$10;
        }
        if (true) {
          {
          }
          break m$10;
        }
        $rt.unmatched($9);
      }
      break m$7;
    }
    if (($6.$tag === "Record")) {
      const r = $6.$;
      {
        const x = expandRow$125(self.v.s, r);
        const $19 = labelGet$233(x.labels, name);
        m$20: {
          if (($19.$tag === "Some")) {
            const ft = $19.$;
            {
              return ft;
            }
            break m$20;
          }
          if (true) {
            {
            }
            break m$20;
          }
          $rt.unmatched($19);
        }
        const $21 = x.tail;
        m$22: {
          if (($21.$tag === "Var")) {
            {
              const ft = fresh$238(new $rt.FieldRef(self.v, "s"));
              const one = { v: $b.Vec_new() };
              labelSet$184(one, name, clone$23(ft));
              const tail = freshRowTail$243(new $rt.FieldRef(self.v, "s"));
              let $23;
              try {
                unifyRows$444(new $rt.FieldRef(self.v, "s"), x, { labels: one.v, tail: tail });
                $23 = true;
              } catch ($24) {
                if (!($24 instanceof $rt.Fail)) throw $24;
                $23 = false;
              }
              const ok = $23;
              if (ok) {
                return ft;
              }
            }
            break m$22;
          }
          if (true) {
            {
            }
            break m$22;
          }
          $rt.unmatched($21);
        }
      }
      break m$7;
    }
    if (($6.$tag === "Tuple")) {
      const ts = $6.$;
      let $25;
      const $26 = $b.parseInt(name);
      m$27: {
        if (($26.$tag === "Some")) {
          const i = $26.$;
          $25 = ((i >= 0n) && ($rt.wrap_usize(i) < $b.slice_len(ts)));
          break m$27;
        }
        if (($26.$tag === "None")) {
          $25 = false;
          break m$27;
        }
        $rt.unmatched($26);
      }
      if ($25) {
        {
          const $28 = ts;
          let $29;
          const $30 = $b.parseInt(name);
          m$31: {
            if (($30.$tag === "Some")) {
              const i = $30.$;
              $29 = $rt.wrap_usize(i);
              break m$31;
            }
            if (($30.$tag === "None")) {
              $29 = 0n;
              break m$31;
            }
            $rt.unmatched($30);
          }
          return clone$23($rt.idx($28, $29));
        }
        break m$7;
      }
    }
    if (($6.$tag === "Error")) {
      return { $tag: "Error" };
      break m$7;
    }
    if (($6.$tag === "Var")) {
      {
        err$108(self, $rt.copy(span), $b.String_asStr(("" + "cannot infer the type that has field `" + name + "`; add a type annotation")));
        return { $tag: "Error" };
      }
      break m$7;
    }
    if (true) {
      {
      }
      break m$7;
    }
    $rt.unmatched($6);
  }
  const shown = show$123(self.v, base);
  err$108(self, $rt.copy(span), $b.String_asStr(("" + "no field `" + name + "` on `" + shown + "`")));
  return { $tag: "Error" };
}
function tagPayloads$242(self, scrut) {
  const $1 = strip$124(self.v, scrut);
  m$2: {
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      const $3 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, d), "kind");
      const $4 = $3.v;
      m$5: {
        if (($4.$tag === "Enum")) {
          const tags = new $rt.FieldRef($4.$, "tags");
          {
            const out = { v: $b.Vec_new() };
            for (const $6 of $rt.items(tags.v)) {
              const k = $6[0];
              const t = $6[1];
              $b.Vec_push(out, [$b.String_clone(k), substParams$230(t, $rt.idx(self.v.p.v.defs, d).params, args)]);
            }
            return { $tag: "Some", $: [out.v, { $tag: "Closed" }] };
          }
          break m$5;
        }
        if (true) {
          return { $tag: "None" };
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$2;
    }
    if (($1.$tag === "Union")) {
      const r = $1.$;
      {
        const x = expandRow$125(self.v.s, r);
        return { $tag: "Some", $: [x.labels, x.tail] };
      }
      break m$2;
    }
    if (true) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function freshRowTail$243(self) {
  $b.Vec_push(new $rt.FieldRef(self.v, "rows"), { $tag: "None" });
  return { $tag: "Var", $: $rt.wrap_u32($rt.usize($b.slice_len(self.v.rows) - 1n)) };
}
function clone$244(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$360(x));
  }
  return v.v;
}
function blockLeaves$245(b, loops) {
  for (const $1 of $rt.items(b.stmts)) {
    const st = $1;
    let $2;
    const $3 = st;
    m$4: {
      if (($3.$tag === "Let")) {
        const init = $3.$.init;
        $2 = leaves$107(init, loops);
        break m$4;
      }
      if ((($3.$tag === "Defer") || ($3.$tag === "Expr"))) {
        let x;
        if (($3.$tag === "Defer")) { x = $3.$; }
        else if (($3.$tag === "Expr")) { x = $3.$; }
        $2 = leaves$107(x, loops);
        break m$4;
      }
      $rt.unmatched($3);
    }
    const found = $2;
    if ($b.Option_isSome(found)) {
      return found;
    }
  }
  return optLeaves$246(b.tail, loops);
}
function optLeaves$246(e, loops) {
  const $1 = e;
  m$2: {
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return leaves$107(x, loops);
      break m$2;
    }
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function firstOf3$247(a, b, c) {
  if ($b.Option_isSome(a)) {
    return a;
  } else {
    if ($b.Option_isSome(b)) {
      return b;
    } else {
      {
        return c;
      }
    }
  }
}
function listLeaves$248(es, loops) {
  for (const $1 of $rt.items(es)) {
    const x = $1;
    const $2 = leaves$107(x, loops);
    m$3: {
      if (($2.$tag === "Some")) {
        const s = $2.$;
        {
          return { $tag: "Some", $: $rt.copy(s) };
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return { $tag: "None" };
}
function initsLeave$249(fs, loops) {
  for (const $1 of $rt.items(fs)) {
    const f = $1;
    const $2 = f.value;
    m$3: {
      if (($2.$tag === "Some")) {
        const v = $2.$;
        {
          const $4 = leaves$107(v, loops);
          m$5: {
            if (($4.$tag === "Some")) {
              const s = $4.$;
              {
                return { $tag: "Some", $: $rt.copy(s) };
              }
              break m$5;
            }
            if (true) {
              {
              }
              break m$5;
            }
            $rt.unmatched($4);
          }
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return { $tag: "None" };
}
function assocType$250(self, base, name) {
  let $1;
  const $2 = assocImpl$451(self, base, name);
  m$3: {
    if (($2.$tag === "Some")) {
      const r = $2.$;
      $1 = r;
      break m$3;
    }
    if (($2.$tag === "None")) {
      return { $tag: "None" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const $4 = $1;
  const imp = $4[0];
  const binds = $4[1];
  if (isTemplateImpl$288(self, imp)) {
    const $5 = $b.HashMap_get(self.assocInstances, $b.String_asStr(("" + String(imp) + "|" + bindsKey$452(binds) + "|" + name)));
    m$6: {
      if (($5.$tag === "Some")) {
        const t = $5.$;
        return { $tag: "Some", $: clone$23(t) };
        break m$6;
      }
      if (($5.$tag === "None")) {
        return { $tag: "None" };
        break m$6;
      }
      $rt.unmatched($5);
    }
  }
  const $7 = $b.HashMap_get($rt.idx(self.impls, imp).assocTys, name);
  m$8: {
    if (($7.$tag === "Some")) {
      const t = $7.$;
      return { $tag: "Some", $: subst$308(t, bindsMap$453(binds)) };
      break m$8;
    }
    if (($7.$tag === "None")) {
      return { $tag: "None" };
      break m$8;
    }
    $rt.unmatched($7);
  }
}
function clone$251(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$454(x));
  }
  return v.v;
}
function clone$252(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$455(x));
  }
  return v.v;
}
function clone$253(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$75(x));
  }
  return v.v;
}
function clone$254(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$226(x));
  }
  return v.v;
}
function clone$255(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$456(x));
  }
  return v.v;
}
function last$256(self) {
  if (($b.slice_len(self) === 0n)) {
    return { $tag: "None" };
  } else {
    {
      return { $tag: "Some", $: $rt.idx(self, $rt.usize($b.slice_len(self) - 1n)) };
    }
  }
}
function unionSub$257(self, actual, allowed) {
  const a = resolve$109(self.v, actual);
  const b = resolve$109(self.v, allowed);
  let $1;
  const $2 = [clone$23(a), clone$23(b)];
  m$3: {
    if ((($2[0].$tag === "Union") && ($2[1].$tag === "Union"))) {
      const x = $2[0].$;
      const y = $2[1].$;
      $1 = [x, y];
      break m$3;
    }
    if (true) {
      return unify$239(self, a, b);
      break m$3;
    }
    $rt.unmatched($2);
  }
  const $4 = $1;
  const ra0 = $4[0];
  const rb0 = $4[1];
  const ra = expandRow$125(self.v, ra0);
  let rb = expandRow$125(self.v, rb0);
  for (const $5 of $rt.items(ra.labels)) {
    const k = $5[0];
    const ta = $5[1];
    const $6 = labelGet$233(rb.labels, $b.String_asStr(k));
    m$7: {
      if (($6.$tag === "Some")) {
        const tb = $6.$;
        unify$239(self, ta, tb);
        break m$7;
      }
      if (($6.$tag === "None")) {
        {
          const $8 = rb.tail;
          m$9: {
            if (($8.$tag === "Var")) {
              {
                const rest = freshRowTail$243(self);
                const one = { v: $b.Vec_new() };
                $b.Vec_push(one, [$b.String_clone(k), clone$23(ta)]);
                bindRowTail$284(self, rb.tail, one.v, rest);
                rb = expandRow$125(self.v, rb);
              }
              break m$9;
            }
            if (true) {
              {
                throw new $rt.Fail({ $tag: "Mismatch" });
              }
              break m$9;
            }
            $rt.unmatched($8);
          }
        }
        break m$7;
      }
      $rt.unmatched($6);
    }
  }
  const $10 = [clone$99(ra.tail), clone$99(rb.tail)];
  m$11: {
    if ((($10[0].$tag === "Var"))) {
      const t = $10[1];
      return bindRowTail$284(self, ra.tail, $b.Vec_new(), clone$99(t));
      break m$11;
    }
    if ((($10[0].$tag === "Closed"))) {
      {
        return undefined;
      }
      break m$11;
    }
    if ((($10[0].$tag === "Param") && ($10[1].$tag === "Param"))) {
      const p = $10[0].$;
      const q = $10[1].$;
      if (eq$262(p, q)) {
        {
          return undefined;
        }
        break m$11;
      }
    }
    if ((($10[0].$tag === "Param") && ($10[1].$tag === "Var"))) {
      return bindRowTail$284(self, rb.tail, $b.Vec_new(), clone$99(ra.tail));
      break m$11;
    }
    if (true) {
      throw new $rt.Fail({ $tag: "Mismatch" });
      break m$11;
    }
    $rt.unmatched($10);
  }
}
function first$258(self) {
  if (($b.slice_len(self) === 0n)) {
    return { $tag: "None" };
  } else {
    {
      return { $tag: "Some", $: $rt.idx(self, 0n) };
    }
  }
}
function regionsEqual$259(self, a, b) {
  if (($b.slice_len(a) !== $b.slice_len(b))) {
    return false;
  }
  const $1 = $b.slice_len(a);
  for (let i = 0n; i < $1; i++) {
    if (!eq$457(resolveRegion$130(self, $rt.idx(a, i)), resolveRegion$130(self, $rt.idx(b, i)))) {
      return false;
    }
  }
  return true;
}
function isNone$260(self) {
  return (!$b.Option_isSome(self));
}
function regionsUnify$261(self, a, b) {
  const probe = { v: clone$254(self.regions) };
  try {
    const $1 = min$146($b.slice_len(a), $b.slice_len(b));
    for (let i = 0n; i < $1; i++) {
      unifyRegionIn$271(probe, $rt.idx(a, i), $rt.idx(b, i));
    }
    return true;
  } catch ($2) {
    if (!($2 instanceof $rt.Fail)) throw $2;
    return false;
  }
}
function eq$262(self, other) {
  {
    {
      {
        if ((!eq$266(self.id, other.id))) {
          return false;
        }
      }
      {
        if ((!eq$6(self.name, other.name))) {
          return false;
        }
      }
    }
    return true;
  }
}
function first$263(self) {
  if (($b.slice_len(self) === 0n)) {
    return { $tag: "None" };
  } else {
    {
      return { $tag: "Some", $: $rt.idx(self, 0n) };
    }
  }
}
function defNames$264(self) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self.defs)) {
    const d = $1;
    $b.Vec_push(out, $b.String_clone(d.name));
  }
  return out.v;
}
function writeEff$265(e, names, out) {
  $b.String_push(out, defName$458(names, e.def));
  if ((($b.slice_len(e.regions) > 0n) || ($b.slice_len(e.args) > 0n))) {
    $b.String_push(out, "<");
    const $1 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(e.regions)));
    let $3;
    for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
      $3 = undefined;
      const $4 = $2.value.item;
      const i = $4[0];
      const r = $4[1];
      if ((i > 0n)) {
        $b.String_push(out, ", ");
      }
      writeRegion$459(r, out);
    }
    if ((($b.slice_len(e.regions) > 0n) && ($b.slice_len(e.args) > 0n))) {
      $b.String_push(out, ", ");
    }
    writeList$460(e.args, names, out);
    $b.String_push(out, ">");
    return undefined;
  }
}
function eq$266(self, other) {
  return (self === other);
}
function writeEffs$267(r, names, out) {
  const $1 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(r.effs)));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const i = $4[0];
    const e = $4[1];
    if ((i > 0n)) {
      $b.String_push(out, ", ");
    }
    writeEff$265(e, names, out);
  }
  if (!eq$120(r.tail, { $tag: "Closed" })) {
    if (($b.slice_len(r.effs) > 0n)) {
      $b.String_push(out, ", ");
    }
    writeTail$461(r.tail, "...", "e", out);
    return undefined;
  }
}
function labelIndex$268(labels, k) {
  return findIndex$462($b.slice_iter(labels), (($0$$1) => {
  {
    const $2 = $0$$1;
    const n = $2[0];
    return (n === k);
  }
  }));
}
function isNone$269(self) {
  return (!$b.Option_isSome(self));
}
function resolveRegionIn$270(regions, r) {
  let r$$1 = clone$360(r);
  while (true) {
    const $2 = r$$1;
    m$3: {
      if (($2.$tag === "Var")) {
        const v = $2.$;
        {
          const $4 = $rt.idx(regions, $rt.wrap_usize(v));
          m$5: {
            if (($4.$tag === "Some")) {
              const b = $4.$;
              {
                r$$1 = clone$360(b);
              }
              break m$5;
            }
            if (($4.$tag === "None")) {
              return r$$1;
              break m$5;
            }
            $rt.unmatched($4);
          }
        }
        break m$3;
      }
      if (true) {
        break;
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return r$$1;
}
function unifyRegionIn$271(regions, a, b) {
  const x = resolveRegionIn$270(regions.v, a);
  const y = resolveRegionIn$270(regions.v, b);
  if (eq$457(x, y)) {
    return;
  }
  const $1 = x;
  m$2: {
    if (($1.$tag === "Var")) {
      const v = $1.$;
      {
        const $3 = regions.v;
        $3[$rt.at($3, $rt.wrap_usize(v))] = { $tag: "Some", $: y };
        return;
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const $4 = y;
  m$5: {
    if (($4.$tag === "Var")) {
      const v = $4.$;
      {
        const $6 = regions.v;
        $6[$rt.at($6, $rt.wrap_usize(v))] = { $tag: "Some", $: x };
        return undefined;
      }
      break m$5;
    }
    if (true) {
      throw new $rt.Fail({ $tag: "Mismatch" });
      break m$5;
    }
    $rt.unmatched($4);
  }
}
function closeUnion$272(self, t) {
  const $1 = resolve$109(self.v, t);
  m$2: {
    if (($1.$tag === "Union")) {
      const r = $1.$;
      {
        const e = expandRow$125(self.v, r);
        const $3 = e.tail;
        m$4: {
          if (($3.$tag === "Var")) {
            {
              try {
                bindRowTail$284(self, e.tail, $b.Vec_new(), { $tag: "Closed" });
                return undefined;
              } catch ($5) {
                if (!($5 instanceof $rt.Fail)) throw $5;
                return undefined;
              }
            }
            break m$4;
          }
          if (true) {
            {
              return undefined;
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
      }
      break m$2;
    }
    if (true) {
      {
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function isNone$273(self) {
  return (!$b.Option_isSome(self));
}
function clone$274(self) {
  {
    return { id: clone$174(self.id), kind: clone$463(self.kind), span: clone$94(self.span) };
  }
}
function some$275(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function lowerPat$276(self, p, t0) {
  const t = strip$124(self.v, t0);
  const $1 = p.kind;
  m$2: {
    if ((($1.$tag === "Wild") || ($1.$tag === "Bind"))) {
      return { $tag: "Wild" };
      break m$2;
    }
    if (($1.$tag === "Or")) {
      const ps = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $3 of $rt.items(ps)) {
          const q = $3;
          $b.Vec_push(out, lowerPat$276(self, q, t));
        }
        return { $tag: "Or", $: out.v };
      }
      break m$2;
    }
    if (($1.$tag === "Lit")) {
      const e = $1.$;
      const $4 = e.kind;
      m$5: {
        if (($4.$tag === "Bool")) {
          const b = $4.$;
          return { $tag: "Ctor", $: [{ $tag: "Bool", $: b }, $b.Vec_new()] };
          break m$5;
        }
        if (true) {
          return { $tag: "Ctor", $: [{ $tag: "Lit" }, $b.Vec_new()] };
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ps = $1.$;
      const $6 = t;
      m$7: {
        if (($6.$tag === "Tuple")) {
          const ts = $6.$;
          if (($b.slice_len(ts) === $b.slice_len(ps))) {
            {
              const out = { v: $b.Vec_new() };
              const $8 = $b.slice_len(ps);
              for (let i = 0n; i < $8; i++) {
                $b.Vec_push(out, lowerPat$276(self, $rt.idx(ps, i), $rt.idx(ts, i)));
              }
              return { $tag: "Ctor", $: [{ $tag: "Tuple" }, out.v] };
            }
            break m$7;
          }
        }
        if (($6.$tag === "Array" && ($6.$[1].$tag === "Known"))) {
          const e = $6.$[0];
          const n = $6.$[1].$;
          if (($rt.wrap_usize(n) === $b.slice_len(ps))) {
            {
              const out = { v: $b.Vec_new() };
              for (const $9 of $rt.items(ps)) {
                const q = $9;
                $b.Vec_push(out, lowerPat$276(self, q, e));
              }
              return { $tag: "Ctor", $: [{ $tag: "Tuple" }, out.v] };
            }
            break m$7;
          }
        }
        if (true) {
          return { $tag: "Never" };
          break m$7;
        }
        $rt.unmatched($6);
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      {
        let $10;
        const $11 = ctors$464(self, t);
        m$12: {
          if (($11.$tag === "Some")) {
            const cs = $11.$;
            const $13 = first$465(cs);
            m$14: {
              if (($13.$tag === "Some" && (($13.$[0].$tag === "Record")))) {
                const fts = $13.$[1];
                $10 = clone$35(fts);
                break m$14;
              }
              if (true) {
                return { $tag: "Never" };
                break m$14;
              }
              $rt.unmatched($13);
            }
            break m$12;
          }
          if (($11.$tag === "None")) {
            return { $tag: "Never" };
            break m$12;
          }
          $rt.unmatched($11);
        }
        const all = $10;
        const labels = recordLabels$466(self, t);
        const subs = { v: $b.Vec_new() };
        const $15 = min$146($b.slice_len(labels), $b.slice_len(all));
        for (let i = 0n; i < $15; i++) {
          const $18 = find$467($b.slice_iter(fields), (($0$$16) => {
  {
    const $17 = $0$$16;
    const n = $17[0];
    return eq$6(n.name, $rt.idx(labels, i));
  }
          }));
          m$19: {
            if (($18.$tag === "Some" && (($18.$[1].$tag === "Some")))) {
              const q = $18.$[1].$;
              $b.Vec_push(subs, lowerPat$276(self, q, $rt.idx(all, i)));
              break m$19;
            }
            if (true) {
              $b.Vec_push(subs, { $tag: "Wild" });
              break m$19;
            }
            $rt.unmatched($18);
          }
        }
        return { $tag: "Ctor", $: [{ $tag: "Record" }, subs.v] };
      }
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const name = $1.$.name;
      const args = $1.$.args;
      {
        let $20;
        const $21 = tagPayloads$242(self, t);
        m$22: {
          if (($21.$tag === "Some")) {
            const tags = $21.$[0];
            $20 = tags;
            break m$22;
          }
          if (($21.$tag === "None")) {
            return { $tag: "Never" };
            break m$22;
          }
          $rt.unmatched($21);
        }
        const tags = $20;
        let $23;
        const $24 = labelGet$233(tags, $b.String_asStr(name));
        m$25: {
          if (($24.$tag === "Some")) {
            const x = $24.$;
            $23 = resolve$109(self.v.s, x);
            break m$25;
          }
          if (($24.$tag === "None")) {
            return { $tag: "Never" };
            break m$25;
          }
          $rt.unmatched($24);
        }
        const payload = $23;
        const fields = payloadFields$468(payload);
        let $26;
        const $27 = [args, clone$23(payload)];
        m$28: {
          if ((($27[0].$tag === "None"))) {
            {
              const out = { v: $b.Vec_new() };
              const $29 = $b.slice_len(fields);
              for (let $30$$31 = 0n; $30$$31 < $29; $30$$31++) {
                $b.Vec_push(out, { $tag: "Wild" });
              }
              $26 = out.v;
            }
            break m$28;
          }
          if ((($27[0].$tag === "Tuple") && ($27[1].$tag === "Tuple"))) {
            const ps = $27[0].$;
            const ts = $27[1].$;
            if (($b.slice_len(ps) === $b.slice_len(ts))) {
              {
                const out = { v: $b.Vec_new() };
                const $32 = $b.slice_len(ps);
                for (let i = 0n; i < $32; i++) {
                  $b.Vec_push(out, lowerPat$276(self, $rt.idx(ps, i), $rt.idx(ts, i)));
                }
                $26 = out.v;
              }
              break m$28;
            }
          }
          if ((($27[0].$tag === "Tuple"))) {
            const ps = $27[0].$;
            if (($b.slice_len(ps) === 1n)) {
              const $33 = lowerPat$276(self, $rt.idx(ps, 0n), payload);
              m$34: {
                if (($33.$tag === "Wild")) {
                  {
                    const out = { v: $b.Vec_new() };
                    const $35 = $b.slice_len(fields);
                    for (let $36$$37 = 0n; $36$$37 < $35; $36$$37++) {
                      $b.Vec_push(out, { $tag: "Wild" });
                    }
                    $26 = out.v;
                  }
                  break m$34;
                }
                if ((($33.$tag === "Ctor" && ($33.$[0].$tag === "Tuple")) || ($33.$tag === "Ctor" && ($33.$[0].$tag === "Record")))) {
                  let subs;
                  if (($33.$tag === "Ctor" && ($33.$[0].$tag === "Tuple"))) { subs = $33.$[1]; }
                  else if (($33.$tag === "Ctor" && ($33.$[0].$tag === "Record"))) { subs = $33.$[1]; }
                  $26 = subs;
                  break m$34;
                }
                if (true) {
                  return { $tag: "Never" };
                  break m$34;
                }
                $rt.unmatched($33);
              }
              break m$28;
            }
          }
          if ((($27[0].$tag === "Record") && ($27[1].$tag === "Record"))) {
            const fs = $27[0].$;
            const r = $27[1].$;
            {
              const out = { v: $b.Vec_new() };
              const $38 = min$146($b.slice_len(r.labels), $b.slice_len(fields));
              for (let i = 0n; i < $38; i++) {
                const $41 = find$467($b.slice_iter(fs), (($0$$39) => {
  {
    const $40 = $0$$39;
    const n = $40[0];
    return eq$6(n.name, $rt.idx($rt.idx(r.labels, i), 0n));
  }
                }));
                m$42: {
                  if (($41.$tag === "Some" && (($41.$[1].$tag === "Some")))) {
                    const q = $41.$[1].$;
                    $b.Vec_push(out, lowerPat$276(self, q, $rt.idx(fields, i)));
                    break m$42;
                  }
                  if (true) {
                    $b.Vec_push(out, { $tag: "Wild" });
                    break m$42;
                  }
                  $rt.unmatched($41);
                }
              }
              $26 = out.v;
            }
            break m$28;
          }
          if (true) {
            return { $tag: "Never" };
            break m$28;
          }
          $rt.unmatched($27);
        }
        const subs = $26;
        return { $tag: "Ctor", $: [{ $tag: "Tag", $: $b.String_clone(name) }, subs] };
      }
      break m$2;
    }
    if (($1.$tag === "TagAt")) {
      return { $tag: "Never" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function missing$277(self, rows0, tys) {
  if (($b.slice_len(tys) === 0n)) {
    if (($b.slice_len(rows0) === 0n)) {
      return { $tag: "Some", $: $b.Vec_new() };
    } else {
      {
        return { $tag: "None" };
      }
    }
  }
  const t0 = clone$23($rt.idx(tys, 0n));
  const rows = { v: $b.Vec_new() };
  for (const $1 of $rt.items(rows0)) {
    const r = $1;
    const $2 = $rt.idx(r, 0n);
    m$3: {
      if (($2.$tag === "Or")) {
        const alts = $2.$;
        {
          for (const $4 of $rt.items(alts)) {
            const a = $4;
            const r2 = { v: [clone$469(a)] };
            const $5 = $b.slice_len(r);
            for (let k = 1n; k < $5; k++) {
              $b.Vec_push(r2, clone$469($rt.idx(r, k)));
            }
            $b.Vec_push(rows, r2.v);
          }
        }
        break m$3;
      }
      if (true) {
        $b.Vec_push(rows, clone$470(r));
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  const restTys = { v: $b.Vec_new() };
  const $6 = $b.slice_len(tys);
  for (let k = 1n; k < $6; k++) {
    $b.Vec_push(restTys, clone$23($rt.idx(tys, k)));
  }
  const used = { v: $b.Vec_new() };
  for (const $7 of $rt.items(rows.v)) {
    const r = $7;
    const $8 = $rt.idx(r, 0n);
    m$9: {
      if (($8.$tag === "Ctor")) {
        const c = $8.$[0];
        {
          $b.Vec_push(used, clone$471(c));
        }
        break m$9;
      }
      if (true) {
        {
        }
        break m$9;
      }
      $rt.unmatched($8);
    }
  }
  const defaults = { v: $b.Vec_new() };
  for (const $10 of $rt.items(rows.v)) {
    const r = $10;
    const $11 = $rt.idx(r, 0n);
    m$12: {
      if (($11.$tag === "Wild")) {
        {
          const rest = { v: $b.Vec_new() };
          const $13 = $b.slice_len(r);
          for (let k = 1n; k < $13; k++) {
            $b.Vec_push(rest, clone$469($rt.idx(r, k)));
          }
          $b.Vec_push(defaults, rest.v);
        }
        break m$12;
      }
      if (true) {
        {
        }
        break m$12;
      }
      $rt.unmatched($11);
    }
  }
  const $14 = ctors$464(self, t0);
  m$15: {
    if (($14.$tag === "Some")) {
      const all = $14.$;
      if (every$473($b.slice_iter(all), (($0$$16) => {
  {
    const $17 = $0$$16;
    const c = $17[0];
    return includes$472(used.v, c);
  }
      }))) {
        {
          for (const $18 of $rt.items(all)) {
            const c = $18[0];
            const ftys = $18[1];
            const n = $b.slice_len(ftys);
            const spec = { v: $b.Vec_new() };
            for (const $19 of $rt.items(rows.v)) {
              const r = $19;
              const $20 = $rt.idx(r, 0n);
              m$21: {
                if (($20.$tag === "Ctor")) {
                  const c2 = $20.$[0];
                  const subs = $20.$[1];
                  if (eq$474(c2, c)) {
                    {
                      const row = { v: clone$470(subs) };
                      const $22 = $b.slice_len(r);
                      for (let k = 1n; k < $22; k++) {
                        $b.Vec_push(row, clone$469($rt.idx(r, k)));
                      }
                      $b.Vec_push(spec, row.v);
                    }
                    break m$21;
                  }
                }
                if (($20.$tag === "Wild")) {
                  {
                    const row = { v: $b.Vec_new() };
                    const $23 = n;
                    for (let $24$$25 = 0n; $24$$25 < $23; $24$$25++) {
                      $b.Vec_push(row, { $tag: "Wild" });
                    }
                    const $26 = $b.slice_len(r);
                    for (let k = 1n; k < $26; k++) {
                      $b.Vec_push(row, clone$469($rt.idx(r, k)));
                    }
                    $b.Vec_push(spec, row.v);
                  }
                  break m$21;
                }
                if (true) {
                  {
                  }
                  break m$21;
                }
                $rt.unmatched($20);
              }
            }
            const subTys = { v: clone$35(ftys) };
            for (const $27 of $rt.items(restTys.v)) {
              const x = $27;
              $b.Vec_push(subTys, clone$23(x));
            }
            const $28 = missing$277(self, spec.v, subTys.v);
            m$29: {
              if (($28.$tag === "Some")) {
                const w = $28.$;
                {
                  const head = { v: $b.Vec_new() };
                  const $30 = n;
                  for (let k = 0n; k < $30; k++) {
                    $b.Vec_push(head, clone$475($rt.idx(w, k)));
                  }
                  const out = { v: [{ $tag: "Ctor", $: [clone$471(c), head.v] }] };
                  const $31 = $b.slice_len(w);
                  for (let k = n; k < $31; k++) {
                    $b.Vec_push(out, clone$475($rt.idx(w, k)));
                  }
                  return { $tag: "Some", $: out.v };
                }
                break m$29;
              }
              if (true) {
                {
                }
                break m$29;
              }
              $rt.unmatched($28);
            }
          }
          return { $tag: "None" };
        }
        break m$15;
      }
    }
    if (($14.$tag === "Some")) {
      const all = $14.$;
      {
        let $32;
        const $33 = missing$277(self, defaults.v, restTys.v);
        m$34: {
          if (($33.$tag === "Some")) {
            const w = $33.$;
            $32 = w;
            break m$34;
          }
          if (($33.$tag === "None")) {
            return { $tag: "None" };
            break m$34;
          }
          $rt.unmatched($33);
        }
        const w = $32;
        let $35;
        const $38 = find$476($b.slice_iter(all), (($0$$36) => {
  {
    const $37 = $0$$36;
    const c = $37[0];
    return (!includes$472(used.v, c));
  }
        }));
        m$39: {
          if (($38.$tag === "Some")) {
            const x = $38.$;
            $35 = clone$477(x);
            break m$39;
          }
          if (($38.$tag === "None")) {
            return { $tag: "None" };
            break m$39;
          }
          $rt.unmatched($38);
        }
        const $40 = $35;
        const c = $40[0];
        const ftys = $40[1];
        const wilds = { v: $b.Vec_new() };
        const $41 = $b.slice_len(ftys);
        for (let $42$$43 = 0n; $42$$43 < $41; $42$$43++) {
          $b.Vec_push(wilds, { $tag: "Wild" });
        }
        const out = { v: [{ $tag: "Ctor", $: [c, wilds.v] }] };
        for (const $44 of $rt.items(w)) {
          const x = $44;
          $b.Vec_push(out, clone$475(x));
        }
        return { $tag: "Some", $: out.v };
      }
      break m$15;
    }
    if (($14.$tag === "None")) {
      {
        let $45;
        const $46 = missing$277(self, defaults.v, restTys.v);
        m$47: {
          if (($46.$tag === "Some")) {
            const w = $46.$;
            $45 = w;
            break m$47;
          }
          if (($46.$tag === "None")) {
            return { $tag: "None" };
            break m$47;
          }
          $rt.unmatched($46);
        }
        const w = $45;
        const out = { v: [{ $tag: "Wild" }] };
        for (const $48 of $rt.items(w)) {
          const x = $48;
          $b.Vec_push(out, clone$475(x));
        }
        return { $tag: "Some", $: out.v };
      }
      break m$15;
    }
    $rt.unmatched($14);
  }
}
function showWitness$278(w) {
  const $1 = w;
  m$2: {
    if (($1.$tag === "Wild")) {
      return $b.str_toString("_");
      break m$2;
    }
    if (($1.$tag === "Ctor" && ($1.$[0].$tag === "Bool"))) {
      const b = $1.$[0].$;
      return ("" + String(b));
      break m$2;
    }
    if (($1.$tag === "Ctor" && ($1.$[0].$tag === "Tag"))) {
      const n = $1.$[0].$;
      const subs = $1.$[1];
      {
        if (($b.slice_len(subs) === 0n)) {
          return ("" + "#" + n);
        }
        if (every$478($b.slice_iter(subs), ((x) => {
  const $3 = x;
  m$4: {
    if (($3.$tag === "Wild")) {
      return true;
      break m$4;
    }
    if (true) {
      return false;
      break m$4;
    }
    $rt.unmatched($3);
  }
        }))) {
          return ("" + "#" + n + "(_)");
        }
        const parts = { v: $b.Vec_new() };
        for (const $5 of $rt.items(subs)) {
          const x = $5;
          $b.Vec_push(parts, showWitness$278(x));
        }
        return ("" + "#" + n + "(" + join$53(parts.v, ", ") + ")");
      }
      break m$2;
    }
    if (($1.$tag === "Ctor" && ($1.$[0].$tag === "Tuple"))) {
      const subs = $1.$[1];
      {
        const parts = { v: $b.Vec_new() };
        for (const $6 of $rt.items(subs)) {
          const x = $6;
          $b.Vec_push(parts, showWitness$278(x));
        }
        return ("" + "[" + join$53(parts.v, ", ") + "]");
      }
      break m$2;
    }
    if (($1.$tag === "Ctor" && ($1.$[0].$tag === "Record"))) {
      return $b.str_toString("{ \xe2\x80\xa6 }");
      break m$2;
    }
    if (($1.$tag === "Ctor" && ($1.$[0].$tag === "Lit"))) {
      return $b.str_toString("_");
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function zonkRow$279(self, r) {
  const e = expandRow$125(self, r);
  const labels = { v: $b.Vec_new() };
  for (const $1 of $rt.items(e.labels)) {
    const k = $1[0];
    const t = $1[1];
    $b.Vec_push(labels, [$b.String_clone(k), zonk$134(self, t)]);
  }
  return { labels: labels.v, tail: e.tail };
}
function resolveLen$280(self, l) {
  let l$$1 = clone$198(l);
  while (true) {
    const $2 = l$$1;
    m$3: {
      if (($2.$tag === "Var")) {
        const v = $2.$;
        {
          const $4 = $rt.idx(self.lens, $rt.wrap_usize(v));
          m$5: {
            if (($4.$tag === "Some")) {
              const b = $4.$;
              {
                l$$1 = clone$198(b);
              }
              break m$5;
            }
            if (($4.$tag === "None")) {
              return l$$1;
              break m$5;
            }
            $rt.unmatched($4);
          }
        }
        break m$3;
      }
      if (true) {
        break;
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return l$$1;
}
function new$$281() {
  return { map: $b.HashMap_new() };
}
function copyIn$282(self, t, seen) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Prim")) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      return (!m);
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      return every$297($b.slice_iter(ts), ((x) => {
  return copyIn$282(self, x, seen);
      }));
      break m$2;
    }
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      return every$127($b.slice_iter(r.labels), (($0$$3) => {
  {
    const $4 = $0$$3;
    const x = $4[1];
    return copyIn$282(self, x, seen);
  }
      }));
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const e = $1.$[0];
      return copyIn$282(self, e, seen);
      break m$2;
    }
    if (($1.$tag === "Slice")) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        if ((isKnown$479(self, d, "Ref") || defNamed$480(self, d, ["Cell", "RegionList"]))) {
          return true;
        }
        if (hasDrop$481(self, d)) {
          return false;
        }
        if ((!insert$483(seen, keyTy$482(t)))) {
          return true;
        }
        const $5 = components$484(self, d, args);
        m$6: {
          if (($5.$tag === "Some")) {
            const cs = $5.$;
            return every$297($b.slice_iter(cs), ((c) => {
  return copyIn$282(self, c, seen);
            }));
            break m$6;
          }
          if (($5.$tag === "None")) {
            return defNamed$480(self, d, ["Hasher"]);
            break m$6;
          }
          $rt.unmatched($5);
        }
      }
      break m$2;
    }
    if ((($1.$tag === "Param") || ($1.$tag === "Var") || ($1.$tag === "Fn") || ($1.$tag === "Assoc"))) {
      return false;
      break m$2;
    }
    if (($1.$tag === "Error")) {
      return true;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function showTy$283(t, names) {
  const out = { v: $b.String_new() };
  writeTy$485(t, names, out);
  return out.v;
}
function bindRowTail$284(self, tail, labels, rest) {
  const $1 = tail;
  m$2: {
    if (($1.$tag === "Var")) {
      const v = $1.$;
      {
        if ((($b.slice_len(labels) === 0n) && eq$120(rest, tail))) {
          return;
        }
        const $3 = self.v.rows;
        $3[$rt.at($3, $rt.wrap_usize(v))] = { $tag: "Some", $: { labels: labels, tail: rest } };
        return undefined;
      }
      break m$2;
    }
    if (true) {
      {
        if ((!(($b.slice_len(labels) === 0n) && eq$120(rest, tail)))) {
          throw new $rt.Fail({ $tag: "Mismatch" });
          return undefined;
        }
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function satisfiesDepth$285(self, ty, bound, assumed, depth) {
  let $1;
  const $2 = bound;
  m$3: {
    if (($2.$tag === "Named")) {
      const d = $2.$[0];
      $1 = d;
      break m$3;
    }
    if (true) {
      return true;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const d = $1;
  const send = knownDef$139(self, "Send");
  const sendParams = { v: $b.Vec_new() };
  const $4 = ty;
  m$5: {
    if (($4.$tag === "Param")) {
      const s = $4.$;
      {
        const bySend = some$293($b.slice_iter(assumedOf$486(assumed, s.id)), ((b) => {
  const $6 = b;
  m$7: {
    if (($6.$tag === "Named")) {
      const x = $6.$[0];
      return some$487($b.slice_iter(ifaceClosure$142(self, x)), ((i) => {
  return eq$447({ $tag: "Some", $: i }, send);
      }));
      break m$7;
    }
    if (true) {
      return false;
      break m$7;
    }
    $rt.unmatched($6);
  }
        }));
        if (bySend) {
          $b.Vec_push(sendParams, s.id);
        }
      }
      break m$5;
    }
    if (true) {
      {
      }
      break m$5;
    }
    $rt.unmatched($4);
  }
  const name = $b.String_clone($rt.idx(self.defs, d).name);
  if (isStdDef$488(self, d)) {
    if ((name === "Send")) {
      let $8 = isSendGiven$489(self, ty, sendParams.v);
      if (!$8) {
        let $9;
        const $10 = ty;
        m$11: {
          if ((($10.$tag === "Error") || ($10.$tag === "Var"))) {
            $9 = true;
            break m$11;
          }
          if (true) {
            $9 = false;
            break m$11;
          }
          $rt.unmatched($10);
        }
        $8 = $9;
      }
      return $8;
    }
    if ((name === "Copy")) {
      let $12 = isCopy$135(self, ty);
      if (!$12) {
        let $13;
        const $14 = ty;
        m$15: {
          if ((($14.$tag === "Param") || ($14.$tag === "Var"))) {
            $13 = true;
            break m$15;
          }
          if (true) {
            $13 = false;
            break m$15;
          }
          $rt.unmatched($14);
        }
        $12 = $13;
      }
      return $12;
    }
    if ((name === "LentBy")) {
      let $16;
      const $17 = bound;
      m$18: {
        if (($17.$tag === "Named")) {
          const args = $17.$[1];
          const $19 = first$258(args);
          m$20: {
            if (($19.$tag === "Some" && ($19.$.$tag === "Ty"))) {
              const k = $19.$.$;
              $16 = clone$23(k);
              break m$20;
            }
            if (true) {
              return true;
              break m$20;
            }
            $rt.unmatched($19);
          }
          break m$18;
        }
        if (true) {
          return true;
          break m$18;
        }
        $rt.unmatched($17);
      }
      const k = $16;
      return lentBy$490(self, stripBorrows$295(ty), stripBorrows$295(k));
    }
  }
  let $21;
  const $22 = $rt.idx(self.defs, d).kind;
  m$23: {
    if (($22.$tag === "Interface")) {
      $21 = true;
      break m$23;
    }
    if (true) {
      $21 = false;
      break m$23;
    }
    $rt.unmatched($22);
  }
  if ((!$21)) {
    return true;
  }
  const $24 = stripBorrows$295(ty);
  m$25: {
    if (($24.$tag === "Param")) {
      const s = $24.$;
      return some$293($b.slice_iter(assumedOf$486(assumed, s.id)), ((b) => {
  const $26 = b;
  m$27: {
    if (($26.$tag === "Named")) {
      const x = $26.$[0];
      return includes$229(ifaceClosure$142(self, x), d);
      break m$27;
    }
    if (true) {
      return false;
      break m$27;
    }
    $rt.unmatched($26);
  }
      }));
      break m$25;
    }
    if ((($24.$tag === "Var") || ($24.$tag === "Error"))) {
      return true;
      break m$25;
    }
    if (true) {
      const t = $24;
      return $b.Option_isSome(resolveDepth$491(self, d, t, depth));
      break m$25;
    }
    $rt.unmatched($24);
  }
}
function some$286(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function resolveImpl$287(self, iface, ty) {
  return resolveDepth$491(self, iface, ty, 0n);
}
function isTemplateImpl$288(self, imp) {
  return some$72($b.slice_iter($rt.idx(self.impls, imp).params), ((g) => {
  return g.isComptime;
  }));
}
function methodForMut$289(self, imp, name, binds) {
  let $1;
  const $2 = implMethod$492(self.v, imp, name);
  m$3: {
    if (($2.$tag === "Some")) {
      const m = $2.$;
      $1 = m;
      break m$3;
    }
    if (($2.$tag === "None")) {
      return { $tag: "None" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const m = $1;
  if ((!isTemplate$21(self.v, m))) {
    return { $tag: "Some", $: m };
  }
  let $4;
  const $5 = comptimeArgs$147(self.v, m, binds);
  m$6: {
    if (($5.$tag === "Some")) {
      const c = $5.$;
      $4 = c;
      break m$6;
    }
    if (($5.$tag === "None")) {
      return { $tag: "None" };
      break m$6;
    }
    $rt.unmatched($5);
  }
  const ct = $4;
  return { $tag: "Some", $: specializeFor$150(self, m, ct) };
}
function clone$290(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Ty")) {
      const x = $1.$;
      return { $tag: "Ty", $: clone$23(x) };
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const x = $1.$;
      return { $tag: "Region", $: clone$360(x) };
      break m$2;
    }
    if (($1.$tag === "Row")) {
      const x = $1.$;
      return { $tag: "Row", $: clone$40(x) };
      break m$2;
    }
    if (($1.$tag === "Len")) {
      const x = $1.$;
      return { $tag: "Len", $: clone$198(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function paramArg$291(g) {
  const $1 = g.kind;
  m$2: {
    if (($1.$tag === "Type")) {
      return { $tag: "Ty", $: { $tag: "Param", $: clone$34(g.sym) } };
      break m$2;
    }
    if (($1.$tag === "Region")) {
      return { $tag: "Region", $: { $tag: "Param", $: clone$34(g.sym) } };
      break m$2;
    }
    if (($1.$tag === "Row")) {
      return { $tag: "Row", $: { effs: $b.Vec_new(), tail: { $tag: "Param", $: clone$34(g.sym) } } };
      break m$2;
    }
    if (($1.$tag === "Len")) {
      return { $tag: "Len", $: { $tag: "Param", $: clone$34(g.sym) } };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function some$292(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function some$293(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function some$294(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function stripBorrows$295(t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Borrow")) {
      const inner = $1.$[1];
      return stripBorrows$295(inner);
      break m$2;
    }
    if (true) {
      const other = $1;
      return clone$23(other);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function specialize$296(self, fid, ct, requested) {
  const key = ("" + String(fid) + "|" + specKey$493(ct));
  const $1 = $b.HashMap_get(self.v.specs, $b.String_asStr(key));
  m$2: {
    if (($1.$tag === "Some")) {
      const f = $1.$;
      {
        return f;
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const map = { v: $b.HashMap_new() };
  for (const $3 of $rt.items(ct)) {
    const s = $3[0];
    const t = $3[1];
    $b.HashMap_insert(map, s.id, { $tag: "Ty", $: clone$23(t) });
  }
  const info = clone$22($rt.idx(self.v.fns, fid).scheme);
  const tparams = { v: $b.Vec_new() };
  for (const $4 of $rt.items(info.tparams)) {
    const g = $4;
    if ((!g.isComptime)) {
      $b.Vec_push(tparams, clone$194(g));
    }
  }
  const params = { v: $b.Vec_new() };
  for (const $5 of $rt.items(info.params)) {
    const n = $5[0];
    const t = $5[1];
    $b.Vec_push(params, [$b.String_clone(n), subst$308(t, map.v)]);
  }
  let $6;
  const $7 = info.effects;
  m$8: {
    if (($7.$tag === "Some")) {
      const e = $7.$;
      $6 = { $tag: "Some", $: substEffs$305(e, map.v) };
      break m$8;
    }
    if (($7.$tag === "None")) {
      $6 = { $tag: "None" };
      break m$8;
    }
    $rt.unmatched($7);
  }
  const effects = $6;
  const scheme = { tparams: tparams.v, params: params.v, ret: subst$308(info.ret, map.v), effects: effects, retFrom: clone$76(info.retFrom) };
  const module = $rt.idx(self.v.fns, fid).module;
  const spec = { name: $b.String_clone($rt.idx(self.v.fns, fid).name), module: module, scheme: scheme, decl: $rt.copy($rt.idx(self.v.fns, fid).decl), exported: $rt.idx(self.v.fns, fid).exported, implId: $rt.idx(self.v.fns, fid).implId, hasBody: true, iface: { $tag: "None" } };
  const id = $b.slice_len(self.v.fns);
  $b.Vec_push(new $rt.FieldRef(self.v, "fns"), spec);
  $b.HashMap_insert(new $rt.FieldRef(self.v, "specs"), key, id);
  $b.HashMap_insert(new $rt.FieldRef(self.v, "specOf"), id, fid);
  const shown = { v: $b.Vec_new() };
  for (const $9 of $rt.items(ct)) {
    const t = $9[1];
    $b.Vec_push(shown, show$136(self.v, t));
  }
  let note = ("" + "in `" + $rt.idx(self.v.fns, fid).name + "` for `" + join$53(shown.v, ", ") + "`");
  const $10 = new $rt.FieldRef(self.v, "note");
  const $11 = $10.v;
  m$12: {
    if (($11.$tag === "Some")) {
      const outer = new $rt.FieldRef($11, "$");
      {
        const chain = $b.str_split(outer.v, ", from ");
        const kept = { v: $b.Vec_new() };
        const $13 = min$146(2n, $b.slice_len(chain));
        for (let i = 0n; i < $13; i++) {
          $b.Vec_push(kept, $b.String_clone($rt.idx(chain, i)));
        }
        const joined = join$53(kept.v, ", from ");
        let $14;
        if ($b.str_startsWith(joined, "in ")) {
          $14 = $b.str_toString($b.str_slice(joined, 3n, $b.String_len(joined)));
        } else {
          {
            $14 = joined;
          }
        }
        const trimmed = $14;
        note = ("" + note + ", from " + trimmed);
      }
      break m$12;
    }
    if (true) {
      {
      }
      break m$12;
    }
    $rt.unmatched($11);
  }
  $b.HashMap_insert(new $rt.FieldRef(self.v, "specNotes"), id, $b.String_clone(note));
  const $15 = requested;
  m$16: {
    if (($15.$tag === "Some")) {
      const d = $15.$;
      {
        $b.HashMap_insert(new $rt.FieldRef(self.v, "specRequested"), id, d);
      }
      break m$16;
    }
    if (true) {
      {
      }
      break m$16;
    }
    $rt.unmatched($15);
  }
  const saved = $b.replace(new $rt.FieldRef(self.v, "note"), { $tag: "Some", $: note });
  const $17 = fnDecl$24(self.v, fid);
  m$18: {
    if (($17.$tag === "Some")) {
      const decl = $17.$;
      {
        const env = { v: $b.Vec_new() };
        for (const $19 of $rt.items(ct)) {
          const s = $19[0];
          const t = $19[1];
          $b.Vec_push(env, [$b.String_clone(s.name), { $tag: "Type", $: clone$23(t) }]);
        }
        let d = decl;
        const $20 = clone$25(d.body);
        m$21: {
          if (($20.$tag === "Some")) {
            const b = $20.$;
            {
              const ex = { v: expander$27(self, module, requested, env.v) };
              d.body = body$28(ex, b);
            }
            break m$21;
          }
          if (true) {
            {
            }
            break m$21;
          }
          $rt.unmatched($20);
        }
        $b.HashMap_insert(new $rt.FieldRef(self.v, "bodies"), id, d);
      }
      break m$18;
    }
    if (true) {
      {
      }
      break m$18;
    }
    $rt.unmatched($17);
  }
  self.v.note = saved;
  return id;
}
function every$297(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if ((!test(x))) {
      return false;
    }
  }
  return true;
}
function every$298(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if ((!test(x))) {
      return false;
    }
  }
  return true;
}
function containerIn$299(self, t, seen) {
  const $1 = t;
  m$2: {
    if ((($1.$tag === "Borrow") || ($1.$tag === "Slice") || ($1.$tag === "Array"))) {
      let e;
      if (($1.$tag === "Borrow")) { e = $1.$[1]; }
      else if (($1.$tag === "Slice")) { e = $1.$; }
      else if (($1.$tag === "Array")) { e = $1.$[0]; }
      return containerIn$299(self, e, seen);
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        for (const $3 of $rt.items(ts)) {
          const x = $3;
          const $4 = containerIn$299(self, x, seen);
          m$5: {
            if (($4.$tag === "Some")) {
              const r = $4.$;
              {
                return { $tag: "Some", $: r };
              }
              break m$5;
            }
            if (true) {
              {
              }
              break m$5;
            }
            $rt.unmatched($4);
          }
        }
        return { $tag: "None" };
      }
      break m$2;
    }
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      {
        for (const $6 of $rt.items(r.labels)) {
          const x = $6[1];
          const $7 = containerIn$299(self, x, seen);
          m$8: {
            if (($7.$tag === "Some")) {
              const found = $7.$;
              {
                return { $tag: "Some", $: found };
              }
              break m$8;
            }
            if (true) {
              {
              }
              break m$8;
            }
            $rt.unmatched($7);
          }
        }
        return { $tag: "None" };
      }
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      {
        for (const $9 of $rt.items(f.params)) {
          const x = $9;
          const $10 = containerIn$299(self, x, seen);
          m$11: {
            if (($10.$tag === "Some")) {
              const found = $10.$;
              {
                return { $tag: "Some", $: found };
              }
              break m$11;
            }
            if (true) {
              {
              }
              break m$11;
            }
            $rt.unmatched($10);
          }
        }
        return containerIn$299(self, f.ret, seen);
      }
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        if (((!$rt.idx(self.defs, d).view) && (!isKnown$479(self, d, "Ref")))) {
          for (const $12 of $rt.items(argTypes$494(args))) {
            const a = $12;
            if ((class$$187(self, a) === 2n)) {
              return { $tag: "Some", $: [d, clone$23(a)] };
            }
          }
        }
        if ((!insert$483(seen, keyTy$482(t)))) {
          return { $tag: "None" };
        }
        for (const $13 of $rt.items(argTypes$494(args))) {
          const a = $13;
          const $14 = containerIn$299(self, a, seen);
          m$15: {
            if (($14.$tag === "Some")) {
              const found = $14.$;
              {
                return { $tag: "Some", $: found };
              }
              break m$15;
            }
            if (true) {
              {
              }
              break m$15;
            }
            $rt.unmatched($14);
          }
        }
        return { $tag: "None" };
      }
      break m$2;
    }
    if (true) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function primName$300(p) {
  const $1 = p;
  m$2: {
    if (($1.$tag === "I8")) {
      return "i8";
      break m$2;
    }
    if (($1.$tag === "I16")) {
      return "i16";
      break m$2;
    }
    if (($1.$tag === "I32")) {
      return "i32";
      break m$2;
    }
    if (($1.$tag === "I64")) {
      return "i64";
      break m$2;
    }
    if (($1.$tag === "I128")) {
      return "i128";
      break m$2;
    }
    if (($1.$tag === "Isize")) {
      return "isize";
      break m$2;
    }
    if (($1.$tag === "U8")) {
      return "u8";
      break m$2;
    }
    if (($1.$tag === "U16")) {
      return "u16";
      break m$2;
    }
    if (($1.$tag === "U32")) {
      return "u32";
      break m$2;
    }
    if (($1.$tag === "U64")) {
      return "u64";
      break m$2;
    }
    if (($1.$tag === "Usize")) {
      return "usize";
      break m$2;
    }
    if (($1.$tag === "F32")) {
      return "f32";
      break m$2;
    }
    if (($1.$tag === "F64")) {
      return "f64";
      break m$2;
    }
    if (($1.$tag === "Bool")) {
      return "bool";
      break m$2;
    }
    if (($1.$tag === "Str")) {
      return "str";
      break m$2;
    }
    if (($1.$tag === "Void")) {
      return "void";
      break m$2;
    }
    if (($1.$tag === "Never")) {
      return "never";
      break m$2;
    }
    if (($1.$tag === "Type")) {
      return "Type";
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eraseTy$301(t, p, tasks) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      return { $tag: "Named", $: [d, eraseArgs$158(args, p, tasks)] };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const r = $1.$;
      return { $tag: "Record", $: eraseRow$495(r, p, tasks) };
      break m$2;
    }
    if (($1.$tag === "Union")) {
      const r = $1.$;
      return { $tag: "Union", $: eraseRow$495(r, p, tasks) };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $3 of $rt.items(ts)) {
          const x = $3;
          $b.Vec_push(out, eraseTy$301(x, p, tasks));
        }
        return { $tag: "Tuple", $: out.v };
      }
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const e = $1.$[0];
      const l = $1.$[1];
      return { $tag: "Array", $: [$b.Box_new(eraseTy$301(e, p, tasks)), clone$198(l)] };
      break m$2;
    }
    if (($1.$tag === "Slice")) {
      const e = $1.$;
      return { $tag: "Slice", $: $b.Box_new(eraseTy$301(e, p, tasks)) };
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const e = $1.$[1];
      return { $tag: "Borrow", $: [m, $b.Box_new(eraseTy$301(e, p, tasks))] };
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      {
        const params = { v: $b.Vec_new() };
        for (const $4 of $rt.items(f.params)) {
          const x = $4;
          $b.Vec_push(params, eraseTy$301(x, p, tasks));
        }
        return { $tag: "Fn", $: $b.Box_new({ mode: f.mode, params: params.v, ret: eraseTy$301(f.ret, p, tasks), effects: eraseEffs$302(f.effects, p, tasks) }) };
      }
      break m$2;
    }
    if (true) {
      return clone$23(t);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eraseEffs$302(r, p, tasks) {
  if (rowSuspends$306(p, r, tasks)) {
    return { effs: [{ def: 0n, regions: $b.Vec_new(), args: $b.Vec_new() }], tail: { $tag: "Closed" } };
  } else {
    {
      return pure$37();
    }
  }
}
function writeKeyArg$303(a, out) {
  const $1 = a;
  m$2: {
    if (($1.$tag === "Ty")) {
      const t = $1.$;
      {
        $b.String_push(out, "T");
        writeKey$496(t, out);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const r = $1.$;
      {
        $b.String_push(out, "R");
        writeKeyRegion$497(r, out);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Row")) {
      const r = $1.$;
      {
        $b.String_push(out, "E");
        writeKeyEffs$498(r, out);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Len")) {
      const l = $1.$;
      const $3 = l;
      m$4: {
        if (($3.$tag === "Known")) {
          const k = $3.$;
          return $b.String_push(out, ("" + "L" + String(k)));
          break m$4;
        }
        if (($3.$tag === "Var")) {
          const v = $3.$;
          return $b.String_push(out, ("" + "Lv" + String(v)));
          break m$4;
        }
        if (($3.$tag === "Param")) {
          const s = $3.$;
          return $b.String_push(out, ("" + "Lp" + String(s.id)));
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function fnEffects$304(self, fid) {
  const $1 = $rt.idx(self.p.fns, fid).scheme.effects;
  m$2: {
    if (($1.$tag === "Some")) {
      const e = $1.$;
      return clone$40(e);
      break m$2;
    }
    if (($1.$tag === "None")) {
      const $3 = $b.HashMap_get(self.p.inferred, fid);
      m$4: {
        if (($3.$tag === "Some" && ($3.$.$tag === "Some"))) {
          const e = $3.$.$;
          return clone$40(e);
          break m$4;
        }
        if (true) {
          return pure$37();
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function substEffs$305(r, map) {
  const effs = { v: $b.Vec_new() };
  for (const $1 of $rt.items(r.effs)) {
    const e = $1;
    const regions = { v: $b.Vec_new() };
    for (const $2 of $rt.items(e.regions)) {
      const x = $2;
      $b.Vec_push(regions, substRegion$499(x, map));
    }
    const args = { v: $b.Vec_new() };
    for (const $3 of $rt.items(e.args)) {
      const t = $3;
      $b.Vec_push(args, subst$308(t, map));
    }
    $b.Vec_push(effs, { def: e.def, regions: regions.v, args: args.v });
  }
  let tail = clone$99(r.tail);
  const $4 = r.tail;
  m$5: {
    if (($4.$tag === "Param")) {
      const s = $4.$;
      {
        const $6 = $b.HashMap_get(map, s.id);
        m$7: {
          if (($6.$tag === "Some" && ($6.$.$tag === "Row"))) {
            const row = $6.$.$;
            {
              for (const $8 of $rt.items(row.effs)) {
                const e = $8;
                $b.Vec_push(effs, clone$106(e));
              }
              tail = clone$99(row.tail);
            }
            break m$7;
          }
          if (true) {
            {
            }
            break m$7;
          }
          $rt.unmatched($6);
        }
      }
      break m$5;
    }
    if (true) {
      {
      }
      break m$5;
    }
    $rt.unmatched($4);
  }
  return { effs: effs.v, tail: tail };
}
function rowSuspends$306(p, r, tasks) {
  return some$500($b.slice_iter(r.effs), ((e) => {
  {
    const name = $b.String_asStr($rt.idx(p.defs, e.def).name);
    const $1 = $rt.idx(p.defs, e.def).kind;
    m$2: {
      if (($1.$tag === "Effect")) {
        return (((name !== "Fail") && (name !== "Region")) && ((name !== "Io") || tasks));
        break m$2;
      }
      if (true) {
        return false;
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  }));
}
function some$307(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function subst$308(t, map) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Param")) {
      const s = $1.$;
      const $3 = $b.HashMap_get(map, s.id);
      m$4: {
        if (($3.$tag === "Some" && ($3.$.$tag === "Ty"))) {
          const x = $3.$.$;
          return clone$23(x);
          break m$4;
        }
        if (true) {
          return clone$23(t);
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        const out = { v: $b.Vec_new() };
        for (const $5 of $rt.items(args)) {
          const a = $5;
          $b.Vec_push(out, substArg$501(a, map));
        }
        return { $tag: "Named", $: [d, out.v] };
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const r = $1.$;
      return { $tag: "Record", $: substRow$502(r, map) };
      break m$2;
    }
    if (($1.$tag === "Union")) {
      const r = $1.$;
      return { $tag: "Union", $: substRow$502(r, map) };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $6 of $rt.items(ts)) {
          const x = $6;
          $b.Vec_push(out, subst$308(x, map));
        }
        if ((($b.slice_len(out.v) === 1n) && eq$234($rt.idx(out.v, 0n), voidTy$112()))) {
          return voidTy$112();
        } else {
          {
            return { $tag: "Tuple", $: out.v };
          }
        }
      }
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const e = $1.$[0];
      const l = $1.$[1];
      return { $tag: "Array", $: [$b.Box_new(subst$308(e, map)), substLen$503(l, map)] };
      break m$2;
    }
    if (($1.$tag === "Slice")) {
      const e = $1.$;
      return { $tag: "Slice", $: $b.Box_new(subst$308(e, map)) };
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const e = $1.$[1];
      return { $tag: "Borrow", $: [m, $b.Box_new(subst$308(e, map))] };
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      {
        const params = { v: $b.Vec_new() };
        for (const $7 of $rt.items(f.params)) {
          const p = $7;
          $b.Vec_push(params, subst$308(p, map));
        }
        return { $tag: "Fn", $: $b.Box_new({ mode: f.mode, params: params.v, ret: subst$308(f.ret, map), effects: substEffs$305(f.effects, map) }) };
      }
      break m$2;
    }
    if (($1.$tag === "Assoc")) {
      const base = $1.$[0];
      const n = $1.$[1];
      return { $tag: "Assoc", $: [$b.Box_new(subst$308(base, map)), $b.String_clone(n)] };
      break m$2;
    }
    if (true) {
      return clone$23(t);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function resolveAssoc$309(self, t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Assoc")) {
      const base = $1.$[0];
      const name = $1.$[1];
      {
        const b = resolveAssoc$309(self, base);
        const $3 = assocType$250(self.p, b, $b.String_asStr(name));
        m$4: {
          if (($3.$tag === "Some")) {
            const r = $3.$;
            return resolveAssoc$309(self, subst$308(r, self.map));
            break m$4;
          }
          if (($3.$tag === "None")) {
            return clone$23(t);
            break m$4;
          }
          $rt.unmatched($3);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const inner = $1.$[1];
      return { $tag: "Borrow", $: [m, $b.Box_new(resolveAssoc$309(self, inner))] };
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        const out = { v: $b.Vec_new() };
        for (const $5 of $rt.items(args)) {
          const a = $5;
          const $6 = out;
          let $7;
          const $8 = a;
          m$9: {
            if (($8.$tag === "Ty")) {
              const x = $8.$;
              $7 = { $tag: "Ty", $: resolveAssoc$309(self, x) };
              break m$9;
            }
            if (true) {
              const other = $8;
              $7 = clone$290(other);
              break m$9;
            }
            $rt.unmatched($8);
          }
          $b.Vec_push($6, $7);
        }
        return { $tag: "Named", $: [d, out.v] };
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $10 of $rt.items(ts)) {
          const x = $10;
          $b.Vec_push(out, resolveAssoc$309(self, x));
        }
        return { $tag: "Tuple", $: out.v };
      }
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const e = $1.$[0];
      const l = $1.$[1];
      return { $tag: "Array", $: [$b.Box_new(resolveAssoc$309(self, e)), clone$198(l)] };
      break m$2;
    }
    if (($1.$tag === "Slice")) {
      const e = $1.$;
      return { $tag: "Slice", $: $b.Box_new(resolveAssoc$309(self, e)) };
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      {
        const params = { v: $b.Vec_new() };
        for (const $11 of $rt.items(f.params)) {
          const x = $11;
          $b.Vec_push(params, resolveAssoc$309(self, x));
        }
        return { $tag: "Fn", $: $b.Box_new({ mode: f.mode, params: params.v, ret: resolveAssoc$309(self, f.ret), effects: clone$40(f.effects) }) };
      }
      break m$2;
    }
    if (true) {
      return clone$23(t);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function cellsBlock$310(self, b, scopes) {
  $b.Vec_push(scopes, $b.HashMap_new());
  for (const $1 of $rt.items(b.stmts)) {
    const s = $1;
    const $2 = s;
    m$3: {
      if (($2.$tag === "Let")) {
        const pat = $2.$.pat;
        const init = $2.$.init;
        {
          cellsExpr$504(self, init, scopes);
          const top = $rt.usize($b.slice_len(scopes.v) - 1n);
          bindIds$505(pat, $rt.indexRef(scopes.v, top));
        }
        break m$3;
      }
      if ((($2.$tag === "Expr") || ($2.$tag === "Defer"))) {
        let x;
        if (($2.$tag === "Expr")) { x = $2.$; }
        else if (($2.$tag === "Defer")) { x = $2.$; }
        cellsExpr$504(self, x, scopes);
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  const $4 = b.tail;
  m$5: {
    if (($4.$tag === "Some")) {
      const t = $4.$;
      {
        cellsExpr$504(self, t, scopes);
      }
      break m$5;
    }
    if (true) {
      {
      }
      break m$5;
    }
    $rt.unmatched($4);
  }
  $b.Vec_pop(scopes);
  return undefined;
}
function local$311(self, name) {
  let i = $b.slice_len(self.scopes);
  while ((i > 0n)) {
    i = $rt.usize(i - 1n);
    const $1 = $b.HashMap_get($rt.idx(self.scopes, i), name);
    m$2: {
      if (($1.$tag === "Some")) {
        const l = $1.$;
        {
          return { $tag: "Some", $: clone$506(l) };
        }
        break m$2;
      }
      if (true) {
        {
        }
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  return { $tag: "None" };
}
function bindingTy$312(self, id) {
  let $1;
  const $2 = $b.HashMap_get(self.p.typed, self.fid);
  m$3: {
    if (($2.$tag === "Some")) {
      const t = $2.$;
      const $4 = $b.HashMap_get(t.bindings, id);
      m$5: {
        if (($4.$tag === "Some")) {
          const x = $4.$;
          $1 = clone$23(x);
          break m$5;
        }
        if (($4.$tag === "None")) {
          $1 = { $tag: "Error" };
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$3;
    }
    if (($2.$tag === "None")) {
      $1 = { $tag: "Error" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const raw = $1;
  return concrete$163(self, raw);
}
function value$313(self, e) {
  const v = ex$507(self, e);
  if (isMutBorrow$508(exprTy$316(self.v, e.id))) {
    return ("" + v + ".v");
  } else {
    {
      return v;
    }
  }
}
function exAs$314(self, e, want) {
  if (isMutBorrow$508(want)) {
    return lend$509(self, e);
  }
  const v = ex$507(self, e);
  return coerce$510(self.v, v, e, want);
}
function isPlace$315(e) {
  const $1 = e.kind;
  m$2: {
    if ((($1.$tag === "Ident") || ($1.$tag === "Field") || ($1.$tag === "Index"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function exprTy$316(self, id) {
  let $1;
  const $2 = $b.HashMap_get(self.p.typed, self.fid);
  m$3: {
    if (($2.$tag === "Some")) {
      const t = $2.$;
      const $4 = $b.HashMap_get(t.exprs, id);
      m$5: {
        if (($4.$tag === "Some")) {
          const x = $4.$;
          $1 = clone$23(x);
          break m$5;
        }
        if (($4.$tag === "None")) {
          $1 = { $tag: "Error" };
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$3;
    }
    if (($2.$tag === "None")) {
      $1 = { $tag: "Error" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const raw = $1;
  return concrete$163(self, raw);
}
function stripBorrow$317(t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Borrow")) {
      const inner = $1.$[1];
      return stripBorrow$317(inner);
      break m$2;
    }
    if (true) {
      return clone$23(t);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function copiedObject$318(self, t) {
  let $1;
  const $2 = t;
  m$3: {
    if ((($2.$tag === "Record") || ($2.$tag === "Tuple") || ($2.$tag === "Array"))) {
      $1 = true;
      break m$3;
    }
    if (($2.$tag === "Named")) {
      const d = $2.$[0];
      const $4 = $rt.idx(self.p.defs, d).kind;
      m$5: {
        if (($4.$tag === "Struct" && ($4.$.fields.$tag === "Some"))) {
          $1 = true;
          break m$5;
        }
        if (true) {
          $1 = false;
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$3;
    }
    if (true) {
      $1 = false;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const object = $1;
  return (object && isCopy$135(self.p, t));
}
function save$319(self, v) {
  const t = fresh$167(self);
  line$168(self, ("" + "const " + t + " = " + v + ";"));
  return t;
}
function cond$320(self, p, subj) {
  const $1 = p.kind;
  m$2: {
    if ((($1.$tag === "Wild") || ($1.$tag === "Bind"))) {
      return $b.str_toString("true");
      break m$2;
    }
    if (($1.$tag === "Lit")) {
      const e = $1.$;
      const $3 = e.kind;
      m$4: {
        if (($3.$tag === "Int")) {
          const n = $3.$;
          if (floatTy$511(exprTy$316(self.v, e.id))) {
            return ("" + subj + " === " + n);
          } else {
            {
              return ("" + subj + " === " + n + "n");
            }
          }
          break m$4;
        }
        if (($3.$tag === "Byte")) {
          const b = $3.$;
          return ("" + subj + " === " + String(b) + "n");
          break m$4;
        }
        if (($3.$tag === "Bool")) {
          const b = $3.$;
          return ("" + subj + " === " + String(b));
          break m$4;
        }
        if (($3.$tag === "Str")) {
          const s = $3.$;
          return ("" + subj + " === " + quote$512(s));
          break m$4;
        }
        if (true) {
          {
            const v = value$313(self, e);
            return ("" + subj + " === " + v);
          }
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const name = $1.$.name;
      const args = $1.$.args;
      {
        const parts = { v: $b.Vec_new() };
        $b.Vec_push(parts, ("" + subj + ".$tag === " + quote$512(name)));
        const $5 = args;
        m$6: {
          if (($5.$tag === "None")) {
            {
            }
            break m$6;
          }
          if (($5.$tag === "Tuple")) {
            const ps = $5.$;
            {
              if (($b.slice_len(ps) === 1n)) {
                const c = cond$320(self, $rt.idx(ps, 0n), $b.String_asStr(("" + subj + ".$")));
                if ((c !== "true")) {
                  $b.Vec_push(parts, c);
                }
              } else {
                {
                  const $7 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(ps)));
                  let $9;
                  for (let $8 = $7.next(); !$8.done; $8 = $7.next($9)) {
                    $9 = undefined;
                    const $10 = $8.value.item;
                    const i = $10[0];
                    const q = $10[1];
                    const c = cond$320(self, q, $b.String_asStr(("" + subj + ".$[" + String(i) + "]")));
                    if ((c !== "true")) {
                      $b.Vec_push(parts, c);
                    }
                  }
                }
              }
            }
            break m$6;
          }
          if (($5.$tag === "Record")) {
            const fs = $5.$;
            fieldConds$513(self, fs, $b.String_asStr(("" + subj + ".$")), parts);
            break m$6;
          }
          $rt.unmatched($5);
        }
        return ("" + "(" + join$53(parts.v, " && ") + ")");
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ps = $1.$;
      {
        const parts = { v: $b.Vec_new() };
        const $11 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(ps)));
        let $13;
        for (let $12 = $11.next(); !$12.done; $12 = $11.next($13)) {
          $13 = undefined;
          const $14 = $12.value.item;
          const i = $14[0];
          const q = $14[1];
          const c = cond$320(self, q, $b.String_asStr(("" + subj + "[" + String(i) + "]")));
          if ((c !== "true")) {
            $b.Vec_push(parts, c);
          }
        }
        if (($b.slice_len(parts.v) === 0n)) {
          return $b.str_toString("true");
        } else {
          {
            return ("" + "(" + join$53(parts.v, " && ") + ")");
          }
        }
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      {
        const parts = { v: $b.Vec_new() };
        fieldConds$513(self, fields, subj, parts);
        if (($b.slice_len(parts.v) === 0n)) {
          return $b.str_toString("true");
        } else {
          {
            return ("" + "(" + join$53(parts.v, " && ") + ")");
          }
        }
      }
      break m$2;
    }
    if (($1.$tag === "Or")) {
      const alts = $1.$;
      {
        const parts = { v: $b.Vec_new() };
        for (const $15 of $rt.items(alts)) {
          const a = $15;
          $b.Vec_push(parts, cond$320(self, a, subj));
        }
        return ("" + "(" + join$53(parts.v, " || ") + ")");
      }
      break m$2;
    }
    if (($1.$tag === "TagAt")) {
      return fail$514(self.v, $rt.copy(p.span), "a tag named by `comptime` code at run time");
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function binds$321(self, p, subj, whole, mutable) {
  const $1 = p.kind;
  m$2: {
    if (($1.$tag === "Or")) {
      const alts = $1.$;
      {
        const first = { v: $b.Vec_new() };
        paths$515($rt.idx(alts, 0n), $b.Vec_new(), first);
        if (($b.slice_len(first.v) === 0n)) {
          return;
        }
        const js = { v: $b.Vec_new() };
        for (const $3 of $rt.items(first.v)) {
          const n = $3[0];
          $b.Vec_push(js, declare$166(self, n, false));
        }
        line$168(self, ("" + "let " + join$53(js.v, ", ") + ";"));
        const $4 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(alts)));
        let $6;
        for (let $5 = $4.next(); !$5.done; $5 = $4.next($6)) {
          $6 = undefined;
          const $7 = $5.value.item;
          const i = $7[0];
          const a = $7[1];
          const c = cond$320(self, a, subj);
          const ps = { v: $b.Vec_new() };
          paths$515(a, $b.Vec_new(), ps);
          const assigns = { v: $b.Vec_new() };
          const $8 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(first.v)));
          let $10;
          for (let $9 = $8.next(); !$9.done; $9 = $8.next($10)) {
            $10 = undefined;
            const $11 = $9.value.item;
            const k = $11[0];
            const n = $11[1][0];
            const $14 = find$516($b.slice_iter(ps.v), (($0$$12) => {
  {
    const $13 = $0$$12;
    const m = $13[0];
    return eq$6(m, n);
  }
            }));
            m$15: {
              if (($14.$tag === "Some")) {
                const id = $14.$[1];
                const segs = $14.$[2];
                {
                  const v = bound$518(self, subj, clone$517(whole), id, segs);
                  $b.Vec_push(assigns, ("" + $rt.idx(js.v, k) + " = " + v + ";"));
                }
                break m$15;
              }
              if (($14.$tag === "None")) {
                fail$514(self.v, $rt.copy(a.span), ("" + "`" + n + "` is not bound by every alternative"));
                break m$15;
              }
              $rt.unmatched($14);
            }
          }
          const $16 = self;
          let $17;
          if ((i === 0n)) {
            $17 = "";
          } else {
            {
              $17 = "else ";
            }
          }
          line$168($16, ("" + $17 + "if (" + c + ") { " + join$53(assigns.v, " ") + " }"));
        }
        return;
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const ps = { v: $b.Vec_new() };
  paths$515(p, $b.Vec_new(), ps);
  for (const $18 of $rt.items(ps.v)) {
    const n = $18[0];
    const id = $18[1];
    const segs = $18[2];
    const v = bound$518(self, subj, clone$517(whole), id, segs);
    const cell = has$19(self.v.cells, id);
    const js = declare$166(self, n, cell);
    let $19;
    if (cell) {
      $19 = ("" + "{ v: " + v + " }");
    } else {
      {
        $19 = v;
      }
    }
    const init = $19;
    const $20 = self;
    let $21;
    if ((mutable && (!cell))) {
      $21 = "let";
    } else {
      {
        $21 = "const";
      }
    }
    line$168($20, ("" + $21 + " " + js + " = " + init + ";"));
  }
  return undefined;
}
function into$322(self, e, dest) {
  const $1 = e.kind;
  m$2: {
    if ((($1.$tag === "Block") || ($1.$tag === "Unsafe"))) {
      let b;
      if (($1.$tag === "Block")) { b = $1.$; }
      else if (($1.$tag === "Unsafe")) { b = $1.$; }
      return blockStmt$519(self, b, dest);
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const body = $1.$.body;
      return blockStmt$519(self, body, dest);
      break m$2;
    }
    if (($1.$tag === "If")) {
      const cond = $1.$.cond;
      const then = $1.$.then;
      const otherwise = $1.$.otherwise;
      {
        const c = value$313(self, cond);
        line$168(self, ("" + "if (" + c + ") {"));
        self.v.indent = $rt.usize(self.v.indent + 1n);
        blockInto$520(self, then, dest);
        self.v.indent = $rt.usize(self.v.indent - 1n);
        const $3 = otherwise;
        m$4: {
          if (($3.$tag === "Some")) {
            const x = $3.$;
            {
              line$168(self, "} else {");
              self.v.indent = $rt.usize(self.v.indent + 1n);
              into$322(self, x, dest);
              self.v.indent = $rt.usize(self.v.indent - 1n);
              line$168(self, "}");
              return undefined;
            }
            break m$4;
          }
          if (($3.$tag === "None")) {
            {
              line$168(self, "}");
              const $5 = dest;
              m$6: {
                if (($5.$tag === "Assign")) {
                  const t = $5.$;
                  {
                    line$168(self, ("" + "else " + t + " = undefined;"));
                    return undefined;
                  }
                  break m$6;
                }
                if (true) {
                  {
                    return undefined;
                  }
                  break m$6;
                }
                $rt.unmatched($5);
              }
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const scrutinee = $1.$.scrutinee;
      const arms = $1.$.arms;
      return matchInto$521(self, scrutinee, arms, dest);
      break m$2;
    }
    if (($1.$tag === "While")) {
      const cond = $1.$.cond;
      const body = $1.$.body;
      {
        if (simple$522(cond)) {
          const c = value$313(self, cond);
          line$168(self, ("" + "while (" + c + ") {"));
          self.v.indent = $rt.usize(self.v.indent + 1n);
        } else {
          {
            line$168(self, "while (true) {");
            self.v.indent = $rt.usize(self.v.indent + 1n);
            const c = value$313(self, cond);
            line$168(self, ("" + "if (!(" + c + ")) break;"));
          }
        }
        blockInto$520(self, body, { $tag: "Discard" });
        self.v.indent = $rt.usize(self.v.indent - 1n);
        line$168(self, "}");
        deliver$323(self, "undefined", dest);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "For")) {
      const mutable = $1.$.mutable;
      const pat = $1.$.pat;
      const iter = $1.$.iter;
      const body = $1.$.body;
      {
        forOf$523(self, mutable, pat, iter, body);
        deliver$323(self, "undefined", dest);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Try")) {
      const body = $1.$.body;
      const pat = $1.$.pat;
      const handler = $1.$.handler;
      {
        line$168(self, "try {");
        self.v.indent = $rt.usize(self.v.indent + 1n);
        blockInto$520(self, body, dest);
        self.v.indent = $rt.usize(self.v.indent - 1n);
        const err = fresh$167(self);
        line$168(self, ("" + "} catch (" + err + ") {"));
        self.v.indent = $rt.usize(self.v.indent + 1n);
        line$168(self, ("" + "if (!(" + err + " instanceof $rt.Fail)) throw " + err + ";"));
        push$165(self);
        const c = cond$320(self, pat, $b.String_asStr(("" + err + ".value")));
        if ((c !== "true")) {
          line$168(self, ("" + "if (!(" + c + ")) throw " + err + ";"));
        }
        binds$321(self, pat, $b.String_asStr(("" + err + ".value")), { $tag: "None" }, false);
        blockInto$520(self, handler, dest);
        pop$170(self);
        self.v.indent = $rt.usize(self.v.indent - 1n);
        line$168(self, "}");
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Return")) {
      const v = $1.$;
      {
        if (self.v.inHandle) {
          const want = clone$23(self.v.fnRet);
          let $7;
          const $8 = v;
          m$9: {
            if (($8.$tag === "Some")) {
              const x = $8.$;
              $7 = exAs$314(self, x, want);
              break m$9;
            }
            if (($8.$tag === "None")) {
              $7 = $b.str_toString("undefined");
              break m$9;
            }
            $rt.unmatched($8);
          }
          const r = $7;
          line$168(self, ("" + "throw new $rt.Return(" + r + ");"));
          return;
        }
        const $10 = v;
        m$11: {
          if (($10.$tag === "Some")) {
            const x = $10.$;
            return into$322(self, x, { $tag: "Return" });
            break m$11;
          }
          if (($10.$tag === "None")) {
            return line$168(self, "return;");
            break m$11;
          }
          $rt.unmatched($10);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Break")) {
      return line$168(self, "break;");
      break m$2;
    }
    if (($1.$tag === "Continue")) {
      return line$168(self, "continue;");
      break m$2;
    }
    if (($1.$tag === "Throw")) {
      const x = $1.$;
      {
        const v = value$313(self, x);
        line$168(self, ("" + "throw new $rt.Fail(" + v + ");"));
        return undefined;
      }
      break m$2;
    }
    if (true) {
      {
        const v = valueFor$524(self, e, dest);
        deliver$323(self, v, dest);
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function deliver$323(self, v, dest) {
  const $1 = dest;
  m$2: {
    if (($1.$tag === "Discard")) {
      {
        if ((v !== "undefined")) {
          line$168(self, ("" + v + ";"));
          return undefined;
        }
      }
      break m$2;
    }
    if (($1.$tag === "Return")) {
      return line$168(self, ("" + "return " + v + ";"));
      break m$2;
    }
    if (($1.$tag === "Assign")) {
      const t = $1.$;
      return line$168(self, ("" + t + " = " + v + ";"));
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function isInt$324(p) {
  const $1 = p;
  m$2: {
    if ((($1.$tag === "I8") || ($1.$tag === "I16") || ($1.$tag === "I32") || ($1.$tag === "I64") || ($1.$tag === "I128") || ($1.$tag === "Isize") || ($1.$tag === "U8") || ($1.$tag === "U16") || ($1.$tag === "U32") || ($1.$tag === "U64") || ($1.$tag === "Usize"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function lex$325(src) {
  return lexRange$525(src, 0n, $b.str_len(src));
}
function atEof$326(self) {
  return eq$526(tok$527(self), { $tag: "Eof" });
}
function item$327(self) {
  const start = span$528(self.v);
  const exported = eatKw$529(self, "export");
  let $1;
  if ((atKw$530(self.v, "import") && (!exported))) {
    $1 = importItem$531(self);
  } else {
    if (at$532(self.v, "@")) {
      const layout = layout$533(self);
      const view = eatWord$534(self, "view");
      $1 = { $tag: "Struct", $: structDecl$535(self, { $tag: "Some", $: layout }, view) };
    } else {
      if ((atWord$536(self.v, "view") && (isKw$538(tokAt$537(self.v, 1n), "struct") || isKw$538(tokAt$537(self.v, 1n), "enum")))) {
        bump$539(self);
        if (atKw$530(self.v, "struct")) {
          $1 = { $tag: "Struct", $: structDecl$535(self, { $tag: "None" }, true) };
        } else {
          {
            let e = enumDecl$540(self);
            e.view = true;
            $1 = { $tag: "Enum", $: e };
          }
        }
      } else {
        if (atKw$530(self.v, "struct")) {
          $1 = { $tag: "Struct", $: structDecl$535(self, { $tag: "None" }, false) };
        } else {
          if (atKw$530(self.v, "enum")) {
            $1 = { $tag: "Enum", $: enumDecl$540(self) };
          } else {
            if (atKw$530(self.v, "const")) {
              bump$539(self);
              const name = ident$541(self);
              let $2;
              if (eat$542(self, ":")) {
                $2 = { $tag: "Some", $: ty$543(self) };
              } else {
                {
                  $2 = { $tag: "None" };
                }
              }
              const ty = $2;
              expect$544(self, "=");
              const value = expr$545(self);
              expect$544(self, ";");
              $1 = { $tag: "Const", $: { name: name, ty: ty, value: value } };
            } else {
              if (atKw$530(self.v, "interface")) {
                $1 = { $tag: "Interface", $: interfaceDecl$546(self) };
              } else {
                if (atKw$530(self.v, "impl")) {
                  $1 = { $tag: "Impl", $: implDecl$547(self) };
                } else {
                  if (atKw$530(self.v, "type")) {
                    $1 = { $tag: "TypeAlias", $: typeAlias$548(self) };
                  } else {
                    if ((atWord$536(self.v, "effect") && isIdent$549(tokAt$537(self.v, 1n)))) {
                      $1 = { $tag: "Effect", $: effectDecl$550(self) };
                    } else {
                      if ((atKw$530(self.v, "function") || atKw$530(self.v, "comptime"))) {
                        $1 = { $tag: "Function", $: fnDecl$551(self) };
                      } else {
                        if (atKw$530(self.v, "extern")) {
                          bump$539(self);
                          const $3 = tok$527(self.v);
                          m$4: {
                            if (($3.$tag === "Str")) {
                              const abi = $3.$;
                              if ((abi === "C")) {
                                {
                                  bump$539(self);
                                }
                                break m$4;
                              }
                            }
                            if (true) {
                              error$552(self.v, "`\"C\"`");
                              break m$4;
                            }
                            $rt.unmatched($3);
                          }
                          const sig = sig$553(self, true);
                          expect$544(self, ";");
                          $1 = { $tag: "Extern", $: sig };
                        } else {
                          {
                            $1 = error$552(self.v, "a declaration");
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  const kind = $1;
  return { exported: exported, kind: kind, span: since$554(self.v, $rt.copy(start)) };
}
function clone$328(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Import")) {
      const x = $1.$;
      return { $tag: "Import", $: clone$555(x) };
      break m$2;
    }
    if (($1.$tag === "Const")) {
      const x = $1.$;
      return { $tag: "Const", $: clone$556(x) };
      break m$2;
    }
    if (($1.$tag === "Struct")) {
      const x = $1.$;
      return { $tag: "Struct", $: clone$557(x) };
      break m$2;
    }
    if (($1.$tag === "Enum")) {
      const x = $1.$;
      return { $tag: "Enum", $: clone$558(x) };
      break m$2;
    }
    if (($1.$tag === "Interface")) {
      const x = $1.$;
      return { $tag: "Interface", $: clone$559(x) };
      break m$2;
    }
    if (($1.$tag === "Impl")) {
      const x = $1.$;
      return { $tag: "Impl", $: clone$560(x) };
      break m$2;
    }
    if (($1.$tag === "TypeAlias")) {
      const x = $1.$;
      return { $tag: "TypeAlias", $: clone$561(x) };
      break m$2;
    }
    if (($1.$tag === "Effect")) {
      const x = $1.$;
      return { $tag: "Effect", $: clone$562(x) };
      break m$2;
    }
    if (($1.$tag === "Function")) {
      const x = $1.$;
      return { $tag: "Function", $: clone$29(x) };
      break m$2;
    }
    if (($1.$tag === "Extern")) {
      const x = $1.$;
      return { $tag: "Extern", $: clone$93(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$329(self) {
  return self;
}
function clone$330(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$563(x));
  }
  return v.v;
}
function clone$331(self) {
  {
    return { args: clone$564(self.args), name: $b.String_clone(self.name) };
  }
}
function clone$332(self) {
  {
    return { args: clone$564(self.args), name: clone$223(self.name) };
  }
}
function clone$333(self) {
  {
    return { fields: clone$565(self.fields), name: clone$566(self.name) };
  }
}
function clone$334(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$60(x));
  }
  return v.v;
}
function clone$335(self) {
  {
    return { name: clone$218(self.name), target: clone$223(self.target) };
  }
}
function clone$336(self) {
  {
    return { name: clone$223(self.name), target: clone$223(self.target) };
  }
}
function clone$337(self) {
  {
    return { index: clone$223(self.index), target: clone$223(self.target) };
  }
}
function clone$338(self) {
  {
    return { args: clone$334(self.args), callee: clone$223(self.callee), typeArgs: clone$567(self.typeArgs) };
  }
}
function clone$339(self) {
  {
    return { op: $b.String_clone(self.op), operand: clone$223(self.operand) };
  }
}
function clone$340(self) {
  {
    return { lhs: clone$223(self.lhs), op: $b.String_clone(self.op), rhs: clone$223(self.rhs) };
  }
}
function clone$341(self) {
  {
    return { op: $b.String_clone(self.op), target: clone$223(self.target), value: clone$223(self.value) };
  }
}
function clone$342(self) {
  {
    return { expr: clone$223(self.expr), ty: clone$193(self.ty) };
  }
}
function clone$343(self) {
  {
    return { hi: clone$96(self.hi), lo: clone$96(self.lo) };
  }
}
function clone$344(self) {
  {
    return { body: clone$223(self.body), params: clone$219(self.params) };
  }
}
function clone$345(self) {
  {
    return { cond: clone$223(self.cond), otherwise: clone$96(self.otherwise), then: clone$30(self.then) };
  }
}
function clone$346(self) {
  {
    return { body: clone$30(self.body), cond: clone$223(self.cond) };
  }
}
function clone$347(self) {
  {
    return { body: clone$30(self.body), iter: clone$223(self.iter), mutable: clone$199(self.mutable), pat: clone$274(self.pat) };
  }
}
function clone$348(self) {
  {
    return { arms: clone$568(self.arms), scrutinee: clone$223(self.scrutinee) };
  }
}
function clone$349(self) {
  {
    return { body: clone$30(self.body), handler: clone$30(self.handler), pat: clone$274(self.pat) };
  }
}
function clone$350(self) {
  {
    return { body: clone$30(self.body), name: clone$218(self.name) };
  }
}
function clone$351(self) {
  {
    return { arms: clone$569(self.arms), body: clone$30(self.body), effect: clone$193(self.effect) };
  }
}
function eq$352(self, other) {
  {
    {
      {
        if ((!eq$6(self.message, other.message))) {
          return false;
        }
      }
      {
        if ((!eq$570(self.span, other.span))) {
          return false;
        }
      }
    }
    return true;
  }
}
function clone$353(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Region")) {
      const x = $1.$;
      return { $tag: "Region", $: clone$571(x) };
      break m$2;
    }
    if (($1.$tag === "Row")) {
      const x = $1.$;
      return { $tag: "Row", $: clone$572(x) };
      break m$2;
    }
    if (($1.$tag === "Comptime")) {
      const x = $1.$;
      return { $tag: "Comptime", $: clone$573(x) };
      break m$2;
    }
    if (($1.$tag === "Type")) {
      const x = $1.$;
      return { $tag: "Type", $: clone$572(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function elabRowType$354(self, t, scope) {
  const $1 = t.kind;
  m$2: {
    if (($1.$tag === "EmptyRow")) {
      return pure$37();
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const items = $1.$;
      {
        const row = { v: $b.Vec_new() };
        for (const $3 of $rt.items(items)) {
          const i = $3;
          $b.Vec_push(row, { $tag: "Effect", $: clone$193(i) });
        }
        return elabEffects$195(self, row.v, scope);
      }
      break m$2;
    }
    if (($1.$tag === "Path")) {
      const segments = $1.$.segments;
      const args = $1.$.args;
      if ((($b.slice_len(segments) === 1n) && ($b.slice_len(args) === 0n))) {
        {
          const $4 = $b.HashMap_get(scope.params, $b.String_asStr($rt.idx(segments, 0n).name));
          m$5: {
            if (($4.$tag === "Some" && (($4.$[1].$tag === "Row")))) {
              const sym = $4.$[0];
              return { effs: $b.Vec_new(), tail: { $tag: "Param", $: clone$34(sym) } };
              break m$5;
            }
            if (true) {
              return elabEffects$195(self, [{ $tag: "Effect", $: clone$193(t) }], scope);
              break m$5;
            }
            $rt.unmatched($4);
          }
        }
        break m$2;
      }
    }
    if (true) {
      {
        error$62(self, scope.module, $rt.copy(t.span), "expected a row");
        return pure$37();
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function elabRegion$355(self, t, scope) {
  const $1 = t.kind;
  m$2: {
    if (($1.$tag === "Path")) {
      const segments = $1.$.segments;
      const args = $1.$.args;
      {
        if ((($b.slice_len(segments) === 1n) && ($b.slice_len(args) === 0n))) {
          const name = $b.String_clone($rt.idx(segments, 0n).name);
          if ((name === "Heap")) {
            return { $tag: "Heap" };
          }
          const $3 = $b.HashMap_get(scope.params, $b.String_asStr(name));
          m$4: {
            if (($3.$tag === "Some" && (($3.$[1].$tag === "Region")))) {
              const sym = $3.$[0];
              {
                return { $tag: "Param", $: clone$34(sym) };
              }
              break m$4;
            }
            if (true) {
              {
              }
              break m$4;
            }
            $rt.unmatched($3);
          }
        }
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  error$62(self, scope.module, $rt.copy(t.span), "expected a region");
  return { $tag: "Heap" };
}
function clone$356(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$574(x));
  }
  return v.v;
}
function eq$357(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Equal") && ($1[1].$tag === "Equal"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Greater") && ($1[1].$tag === "Greater"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Less") && ($1[1].$tag === "Less"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function cmp$358(self, other) {
  if ((self < other)) {
    return { $tag: "Less" };
  } else {
    if ((self === other)) {
      return { $tag: "Equal" };
    } else {
      {
        return { $tag: "Greater" };
      }
    }
  }
}
function classIn$359(self, t, seen) {
  const $1 = t;
  m$2: {
    if ((($1.$tag === "Borrow") || ($1.$tag === "Slice") || ($1.$tag === "Prim" && ($1.$.$tag === "Str")))) {
      return 2n;
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        let c = 1n;
        for (const $3 of $rt.items(ts)) {
          const x = $3;
          c = max$575(c, classIn$359(self, x, seen));
        }
        return c;
      }
      break m$2;
    }
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      {
        let c = 1n;
        for (const $4 of $rt.items(r.labels)) {
          const x = $4[1];
          c = max$575(c, classIn$359(self, x, seen));
        }
        return c;
      }
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const e = $1.$[0];
      return classIn$359(self, e, seen);
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      if (isKnown$479(self, d, "Ref")) {
        return 1n;
        break m$2;
      }
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        if ((!insert$483(seen, keyTy$482(t)))) {
          return 1n;
        }
        let c = 1n;
        for (const $5 of $rt.items(argTypes$494(args))) {
          const a = $5;
          c = max$575(c, classIn$359(self, a, seen));
        }
        if ((c < 2n)) {
          const $6 = components$484(self, d, args);
          m$7: {
            if (($6.$tag === "Some")) {
              const cs = $6.$;
              {
                for (const $8 of $rt.items(cs)) {
                  const x = $8;
                  c = max$575(c, classIn$359(self, x, seen));
                }
              }
              break m$7;
            }
            if (true) {
              {
              }
              break m$7;
            }
            $rt.unmatched($6);
          }
        }
        return c;
      }
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      return 1n;
      break m$2;
    }
    if (($1.$tag === "Assoc")) {
      return 2n;
      break m$2;
    }
    if (true) {
      return 1n;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$360(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Var")) {
      const x = $1.$;
      return { $tag: "Var", $: clone$77(x) };
      break m$2;
    }
    if (($1.$tag === "Param")) {
      const x = $1.$;
      return { $tag: "Param", $: clone$34(x) };
      break m$2;
    }
    if (($1.$tag === "Heap")) {
      return { $tag: "Heap" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$361(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Path")) {
      const x = $1.$;
      return { $tag: "Path", $: clone$576(x) };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const x = $1.$;
      return { $tag: "Record", $: clone$577(x) };
      break m$2;
    }
    if (($1.$tag === "Union")) {
      const x = $1.$;
      return { $tag: "Union", $: clone$578(x) };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const x = $1.$;
      return { $tag: "Tuple", $: clone$567(x) };
      break m$2;
    }
    if (($1.$tag === "EmptyRow")) {
      return { $tag: "EmptyRow" };
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const x = $1.$;
      return { $tag: "Fn", $: clone$579(x) };
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const x = $1.$;
      return { $tag: "Array", $: clone$580(x) };
      break m$2;
    }
    if (($1.$tag === "Mut")) {
      const x = $1.$;
      return { $tag: "Mut", $: clone$581(x) };
      break m$2;
    }
    if (($1.$tag === "Readonly")) {
      const x = $1.$;
      return { $tag: "Readonly", $: clone$581(x) };
      break m$2;
    }
    if (($1.$tag === "Ptr")) {
      const x = $1.$;
      return { $tag: "Ptr", $: clone$581(x) };
      break m$2;
    }
    if (($1.$tag === "Dyn")) {
      const x = $1.$;
      return { $tag: "Dyn", $: clone$400(x) };
      break m$2;
    }
    if (($1.$tag === "Expr")) {
      const x = $1.$;
      return { $tag: "Expr", $: clone$223(x) };
      break m$2;
    }
    if (($1.$tag === "Spliced")) {
      const x = $1.$;
      return { $tag: "Spliced", $: clone$174(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$362(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Type")) {
      return { $tag: "Type" };
      break m$2;
    }
    if (($1.$tag === "Region")) {
      return { $tag: "Region" };
      break m$2;
    }
    if (($1.$tag === "Row")) {
      return { $tag: "Row" };
      break m$2;
    }
    if (($1.$tag === "Len")) {
      return { $tag: "Len" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$363(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$290(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$364(self) {
  return self;
}
function clone$365(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Shared")) {
      return { $tag: "Shared" };
      break m$2;
    }
    if (($1.$tag === "Mut")) {
      return { $tag: "Mut" };
      break m$2;
    }
    if (($1.$tag === "Once")) {
      return { $tag: "Once" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function some$366(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function clone$367(self) {
  {
    const v = [$b.String_clone($rt.idx(self, 0n)), clone$90($rt.idx(self, 1n))];
    return v;
  }
}
function clone$368(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$582(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$369(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$583(x));
  }
  return v.v;
}
function ctValue$370(self, name) {
  const $1 = lookup$390(self, name);
  m$2: {
    if (($1.$tag === "Some" && ($1.$.$tag === "Some"))) {
      const v = $1.$.$;
      return { $tag: "Some", $: v };
      break m$2;
    }
    if (true) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function splice$371(self, v, at) {
  const span = sp$214(self, $rt.copy(at));
  let $1;
  const $2 = v;
  m$3: {
    if (($2.$tag === "Unit")) {
      return unit$584(self, $rt.copy(at));
      break m$3;
    }
    if (($2.$tag === "Bool")) {
      const b = $2.$;
      $1 = { $tag: "Bool", $: b };
      break m$3;
    }
    if (($2.$tag === "Int")) {
      const i = $2.$;
      if ((i < 0n)) {
        $1 = { $tag: "Unary", $: { op: $b.str_toString("-"), operand: $b.Box_new(mk$380(self, { $tag: "Int", $: ("" + String($rt.i128(-i))) }, $rt.copy(span))) } };
        break m$3;
      }
    }
    if (($2.$tag === "Int")) {
      const i = $2.$;
      $1 = { $tag: "Int", $: ("" + String(i)) };
      break m$3;
    }
    if (($2.$tag === "Str")) {
      const s = $2.$;
      $1 = { $tag: "Str", $: $b.String_clone(s) };
      break m$3;
    }
    if (($2.$tag === "Type")) {
      const t = $2.$;
      $1 = { $tag: "TypeRef", $: spliceTy$379(self, clone$23(t)) };
      break m$3;
    }
    if (($2.$tag === "List")) {
      const xs = $2.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $4 of $rt.items(xs)) {
          const x = $4;
          $b.Vec_push(out, splice$371(self, x, $rt.copy(at)));
        }
        $1 = { $tag: "List", $: out.v };
      }
      break m$3;
    }
    if (($2.$tag === "Record")) {
      const fs = $2.$;
      {
        const fields = { v: $b.Vec_new() };
        for (const $5 of $rt.items(fs)) {
          const k = $5[0];
          const x = $5[1];
          const name = { name: $b.String_clone(k), span: sp$214(self, $rt.copy(at)) };
          $b.Vec_push(fields, { name: name, value: { $tag: "Some", $: splice$371(self, x, $rt.copy(at)) }, computed: { $tag: "None" }, generate: { $tag: "None" } });
        }
        $1 = { $tag: "Record", $: { name: { $tag: "None" }, fields: fields.v } };
      }
      break m$3;
    }
    if (($2.$tag === "Tag" && ($2.$[1].$tag === "None"))) {
      const n = $2.$[0];
      $1 = { $tag: "Tag", $: { name: $b.String_clone(n), args: { $tag: "None" } } };
      break m$3;
    }
    if (($2.$tag === "Tag" && ($2.$[1].$tag === "Some"))) {
      const n = $2.$[0];
      const x = $2.$[1].$;
      $1 = { $tag: "Tag", $: { name: $b.String_clone(n), args: { $tag: "Tuple", $: [splice$371(self, x, $rt.copy(at))] } } };
      break m$3;
    }
    if ((($2.$tag === "Fn") || ($2.$tag === "Closure"))) {
      $1 = fail$391($rt.copy(at), "a `comptime` function cannot be used at run time");
      break m$3;
    }
    $rt.unmatched($2);
  }
  const kind = $1;
  return mk$380(self, kind, $rt.copy(span));
}
function tagArgs$372(self, a) {
  const $1 = a;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const es = $1.$;
      return { $tag: "Tuple", $: exprs$383(self, es) };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fs = $1.$;
      return { $tag: "Record", $: inits$375(self, fs) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function ctName$373(self, e) {
  const $1 = eval$$378(self, e);
  m$2: {
    if (($1.$tag === "Str")) {
      const s = $1.$;
      return s;
      break m$2;
    }
    if (true) {
      const v = $1;
      return fail$391($rt.copy(e.span), $b.String_asStr(("" + "a computed name must be a string, not " + cvKind$392(v))));
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function ident$374(self, i) {
  return { name: $b.String_clone(i.name), span: sp$214(self, $rt.copy(i.span)) };
}
function inits$375(self, fs) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(fs)) {
    const f = $1;
    const $2 = f.generate;
    m$3: {
      if (($2.$tag === "Some")) {
        const g = $2.$;
        {
          genItems$585(self, g, out);
          continue;
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
    let $4;
    const $5 = f.computed;
    m$6: {
      if (($5.$tag === "Some")) {
        const e = $5.$;
        {
          const n = ctName$373(self, e);
          $4 = { name: n, span: sp$214(self, $rt.copy(f.name.span)) };
        }
        break m$6;
      }
      if (($5.$tag === "None")) {
        $4 = ident$374(self, f.name);
        break m$6;
      }
      $rt.unmatched($5);
    }
    const name = $4;
    let $7;
    const $8 = f.value;
    m$9: {
      if (($8.$tag === "Some")) {
        const v = $8.$;
        $7 = { $tag: "Some", $: expr$215(self, v) };
        break m$9;
      }
      if (($8.$tag === "None")) {
        const $10 = ctValue$370(self.v, $b.String_asStr(f.name.name));
        m$11: {
          if (($10.$tag === "Some")) {
            const v = $10.$;
            $7 = { $tag: "Some", $: splice$371(self, v, $rt.copy(f.name.span)) };
            break m$11;
          }
          if (($10.$tag === "None")) {
            $7 = { $tag: "None" };
            break m$11;
          }
          $rt.unmatched($10);
        }
        break m$9;
      }
      $rt.unmatched($8);
    }
    const value = $7;
    $b.Vec_push(out, { name: name, value: value, computed: { $tag: "None" }, generate: { $tag: "None" } });
  }
  return out.v;
}
function list$376(self, items) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(items)) {
    const it = $1;
    let $2;
    const $3 = it.kind;
    m$4: {
      if (($3.$tag === "Comptime")) {
        const x = $3.$;
        $2 = x;
        break m$4;
      }
      if (true) {
        {
          $b.Vec_push(out, expr$215(self, it));
          continue;
          $2 = undefined;
        }
        break m$4;
      }
      $rt.unmatched($3);
    }
    const inner = $2;
    const $5 = inner.kind;
    m$6: {
      if (($5.$tag === "For")) {
        const pat = $5.$.pat;
        const iter = $5.$.iter;
        const body = $5.$.body;
        {
          for (const $7 of $rt.items(evalList$586(self, iter))) {
            const v = $7;
            const depth = $b.slice_len(self.v.env);
            const binds = { v: $b.Vec_new() };
            if ((!ctMatch$587(self, pat, v, binds))) {
              fail$391($rt.copy(pat.span), $b.String_asStr(("" + "`" + cvShow$588(self.v.p.v, v) + "` does not match this pattern")));
            }
            bind$589(self, binds.v);
            const b = block$91(self, body);
            $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
            const span = $rt.copy(b.span);
            $b.Vec_push(out, mk$380(self, { $tag: "Block", $: b }, $rt.copy(span)));
          }
        }
        break m$6;
      }
      if (($5.$tag === "If")) {
        const cond = $5.$.cond;
        const then = $5.$.then;
        const otherwise = $5.$.otherwise;
        {
          if (evalBool$590(self, cond)) {
            const b = scopedBlock$386(self, then);
            const span = $rt.copy(b.span);
            $b.Vec_push(out, mk$380(self, { $tag: "Block", $: b }, $rt.copy(span)));
          } else {
            const $8 = otherwise;
            m$9: {
              if (($8.$tag === "Some")) {
                const o = $8.$;
                {
                  $b.Vec_push(out, expr$215(self, o));
                }
                break m$9;
              }
              if (true) {
                {
                }
                break m$9;
              }
              $rt.unmatched($8);
            }
          }
        }
        break m$6;
      }
      if (true) {
        $b.Vec_push(out, expr$215(self, it));
        break m$6;
      }
      $rt.unmatched($5);
    }
  }
  return out.v;
}
function isCt$377(self, e) {
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "Ident")) {
      const n = $1.$;
      return ($b.Option_isSome(ctValue$370(self, $b.String_asStr(n))) || ((n === "Type") && isNone$591(lookup$390(self, $b.String_asStr(n)))));
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      return isCt$377(self, target);
      break m$2;
    }
    if (($1.$tag === "Call")) {
      const callee = $1.$.callee;
      const args = $1.$.args;
      const $3 = callee.kind;
      m$4: {
        if (($3.$tag === "Field")) {
          const target = $3.$.target;
          return isCt$377(self, target);
          break m$4;
        }
        if (($3.$tag === "Ident")) {
          const n = $3.$;
          {
            let $5 = isNone$591(lookup$390(self, $b.String_asStr(n)));
            if ($5) {
              let $6;
              const $7 = lookup$47(self.p.v, self.module, $b.String_asStr(n));
              m$8: {
                if (($7.$tag === "Some" && ($7.$.$tag === "Fn"))) {
                  const f = $7.$.$;
                  const $9 = fnDecl$24(self.p.v, f);
                  m$10: {
                    if (($9.$tag === "Some")) {
                      const d = $9.$;
                      $6 = d.sig.isComptime;
                      break m$10;
                    }
                    if (($9.$tag === "None")) {
                      $6 = false;
                      break m$10;
                    }
                    $rt.unmatched($9);
                  }
                  break m$8;
                }
                if (true) {
                  $6 = false;
                  break m$8;
                }
                $rt.unmatched($7);
              }
              $5 = $6;
            }
            return ($5 && every$592($b.slice_iter(args), ((a) => {
  return isCt$377(self, a);
            })));
          }
          break m$4;
        }
        if (true) {
          return false;
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eval$$378(self, e) {
  tick$593(self, $rt.copy(e.span));
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "Int")) {
      const s = $1.$;
      const $3 = parseDecimal$594($b.String_asStr($b.str_replaceAll(s, "_", "")));
      m$4: {
        if (($3.$tag === "Some")) {
          const n = $3.$;
          return { $tag: "Int", $: n };
          break m$4;
        }
        if (($3.$tag === "None")) {
          return fail$391($rt.copy(e.span), "bad integer");
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (($1.$tag === "Str")) {
      const s = $1.$;
      return { $tag: "Str", $: $b.String_clone(s) };
      break m$2;
    }
    if (($1.$tag === "Bool")) {
      const b = $1.$;
      return { $tag: "Bool", $: b };
      break m$2;
    }
    if (($1.$tag === "Template")) {
      const pieces = $1.$;
      {
        const s = { v: $b.String_new() };
        for (const $5 of $rt.items(pieces)) {
          const p = $5;
          const $6 = p;
          m$7: {
            if (($6.$tag === "Lit")) {
              const l = $6.$;
              $b.String_push(s, $b.String_asStr(l));
              break m$7;
            }
            if (($6.$tag === "Expr")) {
              const x = $6.$;
              {
                const v = eval$$378(self, x);
                $b.String_push(s, $b.String_asStr(cvShow$588(self.v.p.v, v)));
              }
              break m$7;
            }
            $rt.unmatched($6);
          }
        }
        return { $tag: "Str", $: s.v };
      }
      break m$2;
    }
    if (($1.$tag === "Ident")) {
      const n = $1.$;
      return identValue$595(self, $b.String_asStr(n), $rt.copy(e.span));
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const name = $1.$.name;
      const args = $1.$.args;
      const $8 = args;
      m$9: {
        if (($8.$tag === "None")) {
          return { $tag: "Tag", $: [$b.String_clone(name), { $tag: "None" }] };
          break m$9;
        }
        if (($8.$tag === "Tuple")) {
          const xs = $8.$;
          if (($b.slice_len(xs) === 1n)) {
            return { $tag: "Tag", $: [$b.String_clone(name), { $tag: "Some", $: $b.Box_new(eval$$378(self, $rt.idx(xs, 0n))) }] };
            break m$9;
          }
        }
        if (($8.$tag === "Tuple")) {
          const xs = $8.$;
          {
            const vs = { v: $b.Vec_new() };
            for (const $10 of $rt.items(xs)) {
              const x = $10;
              $b.Vec_push(vs, eval$$378(self, x));
            }
            return { $tag: "Tag", $: [$b.String_clone(name), { $tag: "Some", $: $b.Box_new({ $tag: "List", $: vs.v }) }] };
          }
          break m$9;
        }
        if (($8.$tag === "Record")) {
          const fs = $8.$;
          return { $tag: "Tag", $: [$b.String_clone(name), { $tag: "Some", $: $b.Box_new(evalRecord$596(self, fs)) }] };
          break m$9;
        }
        $rt.unmatched($8);
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      return evalRecord$596(self, fields);
      break m$2;
    }
    if (($1.$tag === "List")) {
      const xs = $1.$;
      {
        const vs = { v: $b.Vec_new() };
        for (const $11 of $rt.items(xs)) {
          const x = $11;
          $b.Vec_push(vs, eval$$378(self, x));
        }
        return { $tag: "List", $: vs.v };
      }
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      const name = $1.$.name;
      {
        const v = eval$$378(self, target);
        return fieldOf$381(self, v, $b.String_asStr(name.name), $rt.copy(name.span));
      }
      break m$2;
    }
    if (($1.$tag === "Index")) {
      const target = $1.$.target;
      const index = $1.$.index;
      {
        const v = eval$$378(self, target);
        const i = eval$$378(self, index);
        const $12 = [v, i];
        m$13: {
          if ((($12[0].$tag === "List") && ($12[1].$tag === "Int"))) {
            const xs = $12[0].$;
            const k = $12[1].$;
            if (((k >= 0n) && ($rt.wrap_usize(k) < $b.slice_len(xs)))) {
              return clone$90($rt.idx(xs, $rt.wrap_usize(k)));
              break m$13;
            }
          }
          if ((($12[0].$tag === "List") && ($12[1].$tag === "Int"))) {
            return fail$391($rt.copy(e.span), "index out of range");
            break m$13;
          }
          if (true) {
            return fail$391($rt.copy(e.span), "cannot index this `comptime` value");
            break m$13;
          }
          $rt.unmatched($12);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Call")) {
      const callee = $1.$.callee;
      const args = $1.$.args;
      return evalCall$597(self, callee, args, $rt.copy(e.span));
      break m$2;
    }
    if (($1.$tag === "Unary")) {
      const op = $1.$.op;
      const operand = $1.$.operand;
      {
        const v = eval$$378(self, operand);
        const $14 = v;
        m$15: {
          if (($14.$tag === "Bool")) {
            const b = $14.$;
            if ((op === "!")) {
              return { $tag: "Bool", $: (!b) };
              break m$15;
            }
          }
          if (($14.$tag === "Int")) {
            const i = $14.$;
            if ((op === "-")) {
              return { $tag: "Int", $: $rt.i128(-i) };
              break m$15;
            }
          }
          if (true) {
            const other = $14;
            return fail$391($rt.copy(e.span), $b.String_asStr(("" + "cannot apply `" + op + "` to " + cvKind$392(other))));
            break m$15;
          }
          $rt.unmatched($14);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Binary")) {
      const op = $1.$.op;
      const lhs = $1.$.lhs;
      const rhs = $1.$.rhs;
      {
        if (((op === "&&") || (op === "||"))) {
          const l = evalBool$590(self, lhs);
          if (((op === "&&") !== l)) {
            return { $tag: "Bool", $: l };
          }
          return { $tag: "Bool", $: evalBool$590(self, rhs) };
        }
        const l = eval$$378(self, lhs);
        const r = eval$$378(self, rhs);
        const $16 = binary$598($b.String_asStr(op), l, r);
        m$17: {
          if (($16.$tag === "Some")) {
            const v = $16.$;
            return v;
            break m$17;
          }
          if (($16.$tag === "None")) {
            return fail$391($rt.copy(e.span), $b.String_asStr(("" + "cannot apply `" + op + "` to these `comptime` values")));
            break m$17;
          }
          $rt.unmatched($16);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Lambda")) {
      const params = $1.$.params;
      const body = $1.$.body;
      {
        const names = { v: $b.Vec_new() };
        for (const $18 of $rt.items(params)) {
          const p = $18;
          $b.Vec_push(names, $b.String_clone(p.name.name));
        }
        return { $tag: "Closure", $: [names.v, $b.Box_new(clone$60($b.Box_get(body))), clone$369(self.v.env)] };
      }
      break m$2;
    }
    if (($1.$tag === "Block")) {
      const b = $1.$;
      {
        const depth = $b.slice_len(self.v.env);
        let $19;
        try {
          $19 = evalBlock$599(self, b);
        } catch ($20) {
          if (!($20 instanceof $rt.Fail)) throw $20;
          const s = $20.value;
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
          throw new $rt.Fail(s);
        }
        const r = $19;
        $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
        return r;
      }
      break m$2;
    }
    if (($1.$tag === "If")) {
      const cond = $1.$.cond;
      const then = $1.$.then;
      const otherwise = $1.$.otherwise;
      {
        if (evalBool$590(self, cond)) {
          const depth = $b.slice_len(self.v.env);
          let $21;
          try {
            $21 = evalBlock$599(self, then);
          } catch ($22) {
            if (!($22 instanceof $rt.Fail)) throw $22;
            const s = $22.value;
            $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
            throw new $rt.Fail(s);
          }
          const r = $21;
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
          return r;
        } else {
          {
            const $23 = otherwise;
            m$24: {
              if (($23.$tag === "Some")) {
                const o = $23.$;
                return eval$$378(self, o);
                break m$24;
              }
              if (($23.$tag === "None")) {
                return { $tag: "Unit" };
                break m$24;
              }
              $rt.unmatched($23);
            }
          }
        }
      }
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const scrutinee = $1.$.scrutinee;
      const arms = $1.$.arms;
      {
        const v = eval$$378(self, scrutinee);
        for (const $25 of $rt.items(arms)) {
          const arm = $25;
          const depth = $b.slice_len(self.v.env);
          const binds = { v: $b.Vec_new() };
          if (ctMatch$587(self, arm.pat, v, binds)) {
            bind$589(self, binds.v);
            let $26;
            const $27 = arm.guard;
            m$28: {
              if (($27.$tag === "Some")) {
                const g = $27.$;
                $26 = evalBool$590(self, g);
                break m$28;
              }
              if (($27.$tag === "None")) {
                $26 = true;
                break m$28;
              }
              $rt.unmatched($27);
            }
            const ok = $26;
            if (ok) {
              let $29;
              try {
                $29 = eval$$378(self, arm.body);
              } catch ($30) {
                if (!($30 instanceof $rt.Fail)) throw $30;
                const s = $30.value;
                $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
                throw new $rt.Fail(s);
              }
              const r = $29;
              $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
              return r;
            }
          }
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
        }
        return fail$391($rt.copy(scrutinee.span), $b.String_asStr(("" + "no arm matches `" + cvShow$588(self.v.p.v, v) + "`")));
      }
      break m$2;
    }
    if (($1.$tag === "Return")) {
      const v = $1.$;
      {
        let $31;
        const $32 = v;
        m$33: {
          if (($32.$tag === "Some")) {
            const x = $32.$;
            $31 = eval$$378(self, x);
            break m$33;
          }
          if (($32.$tag === "None")) {
            $31 = { $tag: "Unit" };
            break m$33;
          }
          $rt.unmatched($32);
        }
        const r = $31;
        throw new $rt.Fail({ $tag: "CtReturn", $: r });
      }
      break m$2;
    }
    if (($1.$tag === "Comptime")) {
      const x = $1.$;
      return eval$$378(self, x);
      break m$2;
    }
    if (($1.$tag === "TypeRef")) {
      const i = $1.$;
      return { $tag: "Type", $: clone$23($rt.idx(self.v.p.v.spliced, i)) };
      break m$2;
    }
    if (true) {
      return fail$391($rt.copy(e.span), "this cannot be computed at compile time");
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function spliceTy$379(self, t) {
  $b.Vec_push(new $rt.FieldRef(self.v.p.v, "spliced"), t);
  return $rt.usize($b.slice_len(self.v.p.v.spliced) - 1n);
}
function mk$380(self, kind, span) {
  return { kind: kind, span: span, id: id$398(self) };
}
function fieldOf$381(self, v, name, span) {
  const $1 = v;
  m$2: {
    if (($1.$tag === "Record")) {
      const fs = $1.$;
      const $3 = recordGet$600(fs, name);
      m$4: {
        if (($3.$tag === "Some")) {
          const x = $3.$;
          return x;
          break m$4;
        }
        if (($3.$tag === "None")) {
          return fail$391($rt.copy(span), $b.String_asStr(("" + "no field `" + name + "` in `" + cvShow$588(self.v.p.v, v) + "`")));
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (true) {
      const other = $1;
      return fail$391($rt.copy(span), $b.String_asStr(("" + cvKind$392(other) + " has no field `" + name + "`")));
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function includes$382(self, x) {
  for (const $1 of $rt.items(self)) {
    const y = $1;
    if ((y === x)) {
      return true;
    }
  }
  return false;
}
function exprs$383(self, es) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(es)) {
    const e = $1;
    $b.Vec_push(out, expr$215(self, e));
  }
  return out.v;
}
function optExpr$384(self, e) {
  const $1 = e;
  m$2: {
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: $b.Box_new(expr$215(self, x)) };
      break m$2;
    }
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function params$385(self, ps) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(ps)) {
    const p = $1;
    let $2;
    const $3 = p.ty;
    m$4: {
      if (($3.$tag === "Some")) {
        const t = $3.$;
        $2 = { $tag: "Some", $: ty$216(self, t) };
        break m$4;
      }
      if (($3.$tag === "None")) {
        $2 = { $tag: "None" };
        break m$4;
      }
      $rt.unmatched($3);
    }
    const ty = $2;
    shadow$388(self, $b.String_asStr(p.name.name));
    $b.Vec_push(out, { isComptime: p.isComptime, name: ident$374(self, p.name), ty: ty });
  }
  return out.v;
}
function scopedBlock$386(self, b) {
  const depth = $b.slice_len(self.v.env);
  const r = block$91(self, b);
  $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
  return r;
}
function arms$387(self, arms) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(arms)) {
    const a = $1;
    const $2 = a.generate;
    m$3: {
      if (($2.$tag === "Some")) {
        const g = $2.$;
        {
          genArms$601(self, g, out);
          continue;
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
    const depth = $b.slice_len(self.v.env);
    const pat = pattern$217(self, a.pat);
    let $4;
    const $5 = a.guard;
    m$6: {
      if (($5.$tag === "Some")) {
        const g = $5.$;
        $4 = { $tag: "Some", $: expr$215(self, g) };
        break m$6;
      }
      if (($5.$tag === "None")) {
        $4 = { $tag: "None" };
        break m$6;
      }
      $rt.unmatched($5);
    }
    const guard = $4;
    const body = expr$215(self, a.body);
    $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
    $b.Vec_push(out, { pat: pat, guard: guard, body: body, generate: { $tag: "None" } });
  }
  return out.v;
}
function shadow$388(self, name) {
  if ($b.Option_isSome(lookup$390(self.v, name))) {
    $b.Vec_push(new $rt.FieldRef(self.v, "env"), [$b.str_toString(name), { $tag: "None" }]);
    return undefined;
  }
}
function comptime$389(self, inner, at) {
  const $1 = inner.kind;
  m$2: {
    if (($1.$tag === "If")) {
      const cond = $1.$.cond;
      const then = $1.$.then;
      const otherwise = $1.$.otherwise;
      {
        if (evalBool$590(self, cond)) {
          const b = scopedBlock$386(self, then);
          const span = $rt.copy(b.span);
          return mk$380(self, { $tag: "Block", $: b }, $rt.copy(span));
        } else {
          {
            const $3 = otherwise;
            m$4: {
              if (($3.$tag === "Some")) {
                const o = $3.$;
                let $5;
                const $6 = o.kind;
                m$7: {
                  if (($6.$tag === "If")) {
                    $5 = true;
                    break m$7;
                  }
                  if (true) {
                    $5 = false;
                    break m$7;
                  }
                  $rt.unmatched($6);
                }
                if ($5) {
                  return comptime$389(self, o, $rt.copy(at));
                  break m$4;
                }
              }
              if (($3.$tag === "Some")) {
                const o = $3.$;
                return expr$215(self, o);
                break m$4;
              }
              if (($3.$tag === "None")) {
                return unit$584(self, $rt.copy(at));
                break m$4;
              }
              $rt.unmatched($3);
            }
          }
        }
      }
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const scrutinee = $1.$.scrutinee;
      const arms = $1.$.arms;
      {
        const v = eval$$378(self, scrutinee);
        for (const $8 of $rt.items(arms)) {
          const arm = $8;
          const depth = $b.slice_len(self.v.env);
          const binds = { v: $b.Vec_new() };
          if (ctMatch$587(self, arm.pat, v, binds)) {
            bind$589(self, binds.v);
            let $9;
            const $10 = arm.guard;
            m$11: {
              if (($10.$tag === "Some")) {
                const g = $10.$;
                $9 = evalBool$590(self, g);
                break m$11;
              }
              if (($10.$tag === "None")) {
                $9 = true;
                break m$11;
              }
              $rt.unmatched($10);
            }
            const guard = $9;
            if (guard) {
              const r = expr$215(self, arm.body);
              $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
              return r;
            }
          }
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
        }
        return fail$391($rt.copy(scrutinee.span), $b.String_asStr(("" + "no arm matches `" + cvShow$588(self.v.p.v, v) + "`")));
      }
      break m$2;
    }
    if (($1.$tag === "For")) {
      const pat = $1.$.pat;
      const iter = $1.$.iter;
      const body = $1.$.body;
      {
        const items = evalList$586(self, iter);
        const span = sp$214(self, $rt.copy(at));
        const stmts = { v: $b.Vec_new() };
        for (const $12 of $rt.items(items)) {
          const item = $12;
          const depth = $b.slice_len(self.v.env);
          const binds = { v: $b.Vec_new() };
          if ((!ctMatch$587(self, pat, item, binds))) {
            fail$391($rt.copy(pat.span), $b.String_asStr(("" + "`" + cvShow$588(self.v.p.v, item) + "` does not match this pattern")));
          }
          bind$589(self, binds.v);
          const b = block$91(self, body);
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
          const bspan = $rt.copy(b.span);
          $b.Vec_push(stmts, { $tag: "Expr", $: mk$380(self, { $tag: "Block", $: b }, $rt.copy(bspan)) });
        }
        return mk$380(self, { $tag: "Block", $: { stmts: stmts.v, tail: { $tag: "None" }, span: span } }, $rt.copy(span));
      }
      break m$2;
    }
    if (true) {
      {
        const v = eval$$378(self, inner);
        return splice$371(self, v, $rt.copy(at));
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function lookup$390(self, name) {
  let i = $b.slice_len(self.env);
  while ((i > 0n)) {
    i = $rt.usize(i - 1n);
    if (($rt.idx($rt.idx(self.env, i), 0n) === name)) {
      return { $tag: "Some", $: clone$602($rt.idx($rt.idx(self.env, i), 1n)) };
    }
  }
  return { $tag: "None" };
}
function fail$391(span, msg) {
  throw new $rt.Fail({ $tag: "CtError", $: [span, $b.str_toString(msg)] });
}
function cvKind$392(v) {
  const $1 = v;
  m$2: {
    if (($1.$tag === "Unit")) {
      return "void";
      break m$2;
    }
    if (($1.$tag === "Bool")) {
      return "a `bool`";
      break m$2;
    }
    if (($1.$tag === "Int")) {
      return "an integer";
      break m$2;
    }
    if (($1.$tag === "Str")) {
      return "a string";
      break m$2;
    }
    if (($1.$tag === "List")) {
      return "a list";
      break m$2;
    }
    if (($1.$tag === "Record")) {
      return "a record";
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      return "a tag";
      break m$2;
    }
    if (($1.$tag === "Type")) {
      return "a type";
      break m$2;
    }
    if ((($1.$tag === "Fn") || ($1.$tag === "Closure"))) {
      return "a function";
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function fields$393(self, fs) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(fs)) {
    const f = $1;
    const $2 = f.generate;
    m$3: {
      if (($2.$tag === "Some")) {
        const g = $2.$;
        {
          genFields$603(self, g, out);
          continue;
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
    let $4;
    const $5 = f.computed;
    m$6: {
      if (($5.$tag === "Some")) {
        const e = $5.$;
        {
          const n = ctName$373(self, e);
          $4 = { name: n, span: sp$214(self, $rt.copy(f.name.span)) };
        }
        break m$6;
      }
      if (($5.$tag === "None")) {
        $4 = ident$374(self, f.name);
        break m$6;
      }
      $rt.unmatched($5);
    }
    const name = $4;
    $b.Vec_push(out, { name: name, ty: ty$216(self, f.ty), private: f.private, computed: { $tag: "None" }, generate: { $tag: "None" } });
  }
  return out.v;
}
function clone$394(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Shared")) {
      return { $tag: "Shared" };
      break m$2;
    }
    if (($1.$tag === "Mut")) {
      return { $tag: "Mut" };
      break m$2;
    }
    if (($1.$tag === "Once")) {
      return { $tag: "Once" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function uses$395(self, u) {
  const $1 = u;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const items = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $3 of $rt.items(items)) {
          const it = $3;
          const $4 = out;
          let $5;
          const $6 = it;
          m$7: {
            if (($6.$tag === "Effect")) {
              const t = $6.$;
              $5 = { $tag: "Effect", $: ty$216(self, t) };
              break m$7;
            }
            if (($6.$tag === "Spread")) {
              const i = $6.$;
              $5 = { $tag: "Spread", $: ident$374(self, i) };
              break m$7;
            }
            $rt.unmatched($6);
          }
          $b.Vec_push($4, $5);
        }
        return { $tag: "Some", $: out.v };
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function tagPats$396(self, a) {
  const $1 = a;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ps = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $3 of $rt.items(ps)) {
          const x = $3;
          $b.Vec_push(out, pattern$217(self, x));
        }
        return { $tag: "Tuple", $: out.v };
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fs = $1.$;
      return { $tag: "Record", $: fieldPats$397(self, fs) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function fieldPats$397(self, fs) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(fs)) {
    const n = $1[0];
    const p = $1[1];
    let $2;
    const $3 = p;
    m$4: {
      if (($3.$tag === "Some")) {
        const x = $3.$;
        $2 = { $tag: "Some", $: pattern$217(self, x) };
        break m$4;
      }
      if (($3.$tag === "None")) {
        {
          shadow$388(self, $b.String_asStr(n.name));
          $2 = { $tag: "None" };
        }
        break m$4;
      }
      $rt.unmatched($3);
    }
    const q = $2;
    $b.Vec_push(out, [ident$374(self, n), q]);
  }
  return out.v;
}
function id$398(self) {
  self.v.p.v.nextId = $rt.usize(self.v.p.v.nextId + 1n);
  return self.v.p.v.nextId;
}
function clone$399(self) {
  {
    return { isComptime: clone$199(self.isComptime), name: clone$218(self.name), ty: clone$188(self.ty) };
  }
}
function clone$400(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$218(x));
  }
  return v.v;
}
function clone$401(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$604(x));
  }
  return v.v;
}
function clone$402(self) {
  {
    return { init: clone$60(self.init), mutable: clone$199(self.mutable), pat: clone$274(self.pat), span: clone$94(self.span), ty: clone$188(self.ty) };
  }
}
function clone$403(self) {
  {
    const v = [clone$34($rt.idx(self, 0n)), clone$362($rt.idx(self, 1n))];
    return v;
  }
}
function indexOf$404(self, x) {
  let i = 0n;
  for (const $1 of $rt.items(self)) {
    const y = $1;
    if ((y === x)) {
      return { $tag: "Some", $: i };
    }
    i = $rt.usize(i + 1n);
  }
  return { $tag: "None" };
}
function primAt$405(i) {
  const $1 = i;
  m$2: {
    if ($1 === 0n) {
      return { $tag: "I8" };
      break m$2;
    }
    if ($1 === 1n) {
      return { $tag: "I16" };
      break m$2;
    }
    if ($1 === 2n) {
      return { $tag: "I32" };
      break m$2;
    }
    if ($1 === 3n) {
      return { $tag: "I64" };
      break m$2;
    }
    if ($1 === 4n) {
      return { $tag: "I128" };
      break m$2;
    }
    if ($1 === 5n) {
      return { $tag: "Isize" };
      break m$2;
    }
    if ($1 === 6n) {
      return { $tag: "U8" };
      break m$2;
    }
    if ($1 === 7n) {
      return { $tag: "U16" };
      break m$2;
    }
    if ($1 === 8n) {
      return { $tag: "U32" };
      break m$2;
    }
    if ($1 === 9n) {
      return { $tag: "U64" };
      break m$2;
    }
    if ($1 === 10n) {
      return { $tag: "Usize" };
      break m$2;
    }
    if ($1 === 11n) {
      return { $tag: "F32" };
      break m$2;
    }
    if ($1 === 12n) {
      return { $tag: "F64" };
      break m$2;
    }
    if ($1 === 13n) {
      return { $tag: "Bool" };
      break m$2;
    }
    if ($1 === 14n) {
      return { $tag: "Str" };
      break m$2;
    }
    if ($1 === 15n) {
      return { $tag: "Void" };
      break m$2;
    }
    if ($1 === 16n) {
      return { $tag: "Never" };
      break m$2;
    }
    if (true) {
      return { $tag: "Type" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function concreteArg$406(a) {
  const $1 = a;
  m$2: {
    if (($1.$tag === "Ty")) {
      const t = $1.$;
      return (!containsParams$148(t));
      break m$2;
    }
    if (($1.$tag === "Len")) {
      const l = $1.$;
      const $3 = l;
      m$4: {
        if (($3.$tag === "Known")) {
          return true;
          break m$4;
        }
        if (true) {
          return false;
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (true) {
      return true;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function structFields$407(self, fields) {
  try {
    return { $tag: "Some", $: fields$393(self, fields) };
  } catch ($1) {
    if (!($1 instanceof $rt.Fail)) throw $1;
    const s = $1.value;
    report$92(self, s);
    return { $tag: "None" };
  }
}
function find$408(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function eq$409(self, other) {
  {
    {
      {
        if ((!eq$605($rt.idx(self, 0n), $rt.idx(other, 0n)))) {
          return false;
        }
      }
      {
        if ((!eq$606($rt.idx(self, 1n), $rt.idx(other, 1n)))) {
          return false;
        }
      }
    }
    return true;
  }
}
function eq$410(self, other) {
  {
    {
      {
        if ((!eq$607(self.labels, other.labels))) {
          return false;
        }
      }
      {
        if ((!eq$120(self.tail, other.tail))) {
          return false;
        }
      }
    }
    return true;
  }
}
function eq$411(self, other) {
  if (($b.slice_len(self) !== $b.slice_len(other))) {
    return false;
  }
  let i = 0n;
  while ((i < $b.slice_len(self))) {
    if ((!eq$234($rt.idx(self, i), $rt.idx(other, i)))) {
      return false;
    }
    i = $rt.usize(i + 1n);
  }
  return true;
}
function eq$412(self, other) {
  {
    {
      {
        if ((!eq$413($rt.idx(self, 0n), $rt.idx(other, 0n)))) {
          return false;
        }
      }
      {
        if ((!eq$608($rt.idx(self, 1n), $rt.idx(other, 1n)))) {
          return false;
        }
      }
    }
    return true;
  }
}
function eq$413(self, other) {
  return eq$234($b.Box_get(self), $b.Box_get(other));
}
function eq$414(self, other) {
  {
    {
      {
        if ((!eq$609($rt.idx(self, 0n), $rt.idx(other, 0n)))) {
          return false;
        }
      }
      {
        if ((!eq$413($rt.idx(self, 1n), $rt.idx(other, 1n)))) {
          return false;
        }
      }
    }
    return true;
  }
}
function eq$415(self, other) {
  return eq$610($b.Box_get(self), $b.Box_get(other));
}
function eq$416(self, other) {
  {
    {
      {
        if ((!eq$413($rt.idx(self, 0n), $rt.idx(other, 0n)))) {
          return false;
        }
      }
      {
        if ((!eq$6($rt.idx(self, 1n), $rt.idx(other, 1n)))) {
          return false;
        }
      }
    }
    return true;
  }
}
function isFloat$417(p) {
  const $1 = p;
  m$2: {
    if ((($1.$tag === "F32") || ($1.$tag === "F64"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function freshKind$418(self, kind) {
  $b.Vec_push(new $rt.FieldRef(self.v, "tys"), [{ $tag: "None" }, kind]);
  return { $tag: "Var", $: $rt.wrap_u32($rt.usize($b.slice_len(self.v.tys) - 1n)) };
}
function stringTy$419(self) {
  return named$611(self, "String", $b.Vec_new());
}
function ident$420(self, name, span, at) {
  const $1 = local$612(self.v, name);
  m$2: {
    if (($1.$tag === "Some")) {
      const t = $1.$;
      {
        return t;
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const $3 = lookup$47(self.v.p.v, self.v.module, name);
  m$4: {
    if (($3.$tag === "Some" && ($3.$.$tag === "Const"))) {
      const c = $3.$.$;
      return clone$23($rt.idx(self.v.p.v.consts, c).ty);
      break m$4;
    }
    if (($3.$tag === "Some" && ($3.$.$tag === "Fn"))) {
      const fid = $3.$.$;
      {
        let scheme = clone$22($rt.idx(self.v.p.v.fns, fid).scheme);
        const module = self.v.module;
        scheme.effects = { $tag: "Some", $: fnEffects$613(self.v.p, fid, module, $rt.copy(span)) };
        const inst = instantiate$614(self, scheme, $b.Vec_new(), true);
        const $5 = at;
        m$6: {
          if (($5.$tag === "Some")) {
            const id = $5.$;
            {
              $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "calls"), id, fid);
              $b.Vec_push(new $rt.FieldRef(self.v, "pendingTargs"), { id: id, span: span, args: clone$197(inst.args), bounds: $b.Vec_new() });
              if (isTemplate$21(self.v.p.v, fid)) {
                $b.Vec_push(new $rt.FieldRef(self.v, "pendingSpecs"), [id, $rt.copy(span), fid, clone$197(inst.args)]);
              }
            }
            break m$6;
          }
          if (true) {
            {
            }
            break m$6;
          }
          $rt.unmatched($5);
        }
        const params = { v: $b.Vec_new() };
        for (const $7 of $rt.items(inst.params)) {
          const t = $7[1];
          $b.Vec_push(params, clone$23(t));
        }
        const $8 = { $tag: "Shared" };
        const $9 = params.v;
        const $10 = inst.ret;
        let $11;
        const $12 = inst.effects;
        m$13: {
          if (($12.$tag === "Some")) {
            const x = $12.$;
            $11 = x;
            break m$13;
          }
          if (($12.$tag === "None")) {
            $11 = pure$37();
            break m$13;
          }
          $rt.unmatched($12);
        }
        return { $tag: "Fn", $: $b.Box_new({ mode: $8, params: $9, ret: $10, effects: $11 }) };
      }
      break m$4;
    }
    if (true) {
      {
        const msg = unknown$192(self.v.p.v, "name", name);
        err$108(self, $rt.copy(span), $b.String_asStr(msg));
        return { $tag: "Error" };
      }
      break m$4;
    }
    $rt.unmatched($3);
  }
}
function tag$421(self, name, args, expected, span, id) {
  let known = { $tag: "None" };
  const $1 = expected;
  m$2: {
    if (($1.$tag === "Some")) {
      const x = $1.$;
      {
        const $3 = tagPayloads$242(self, x);
        m$4: {
          if (($3.$tag === "Some")) {
            const tags = $3.$[0];
            const tail = $3.$[1];
            {
              const $5 = labelGet$233(tags, name);
              m$6: {
                if (($5.$tag === "Some")) {
                  const t = $5.$;
                  {
                    known = { $tag: "Some", $: { $tag: "Some", $: t } };
                  }
                  break m$6;
                }
                if (($5.$tag === "None")) {
                  {
                    if (eq$120(tail, { $tag: "Closed" })) {
                      known = { $tag: "Some", $: { $tag: "None" } };
                    }
                  }
                  break m$6;
                }
                $rt.unmatched($5);
              }
            }
            break m$4;
          }
          if (true) {
            {
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const $7 = known;
  m$8: {
    if (($7.$tag === "Some" && ($7.$.$tag === "None"))) {
      {
        let $9;
        const $10 = expected;
        m$11: {
          if (($10.$tag === "Some")) {
            const t = $10.$;
            $9 = show$123(self.v, t);
            break m$11;
          }
          if (($10.$tag === "None")) {
            $9 = $b.String_new();
            break m$11;
          }
          $rt.unmatched($10);
        }
        const x = $9;
        err$108(self, $rt.copy(span), $b.String_asStr(("" + "`#" + name + "` is not a tag of `" + x + "`")));
      }
      break m$8;
    }
    if (true) {
      {
      }
      break m$8;
    }
    $rt.unmatched($7);
  }
  let $12;
  const $13 = known;
  m$14: {
    if (($13.$tag === "Some" && ($13.$.$tag === "Some"))) {
      const t = $13.$.$;
      $12 = { $tag: "Some", $: t };
      break m$14;
    }
    if (true) {
      $12 = { $tag: "None" };
      break m$14;
    }
    $rt.unmatched($13);
  }
  const payloadExpected = $12;
  let $15;
  const $16 = payloadExpected;
  m$17: {
    if (($16.$tag === "Some")) {
      const t = $16.$;
      $15 = { $tag: "Some", $: resolve$109(self.v.s, t) };
      break m$17;
    }
    if (($16.$tag === "None")) {
      $15 = { $tag: "None" };
      break m$17;
    }
    $rt.unmatched($16);
  }
  const resolved = $15;
  let $18;
  const $19 = [args, resolved];
  m$20: {
    if ((($19[0].$tag === "Tuple") && ($19[1].$tag === "Some" && ($19[1].$.$tag === "Tuple")))) {
      const items = $19[0].$;
      const ts = $19[1].$.$;
      $18 = (($b.slice_len(items) === 1n) && ($b.slice_len(ts) !== 1n));
      break m$20;
    }
    if ((($19[0].$tag === "Tuple") && ($19[1].$tag === "Some" && ($19[1].$.$tag === "Record")))) {
      const items = $19[0].$;
      $18 = ($b.slice_len(items) === 1n);
      break m$20;
    }
    if (true) {
      $18 = false;
      break m$20;
    }
    $rt.unmatched($19);
  }
  const whole = $18;
  let $21;
  const $22 = args;
  m$23: {
    if (($22.$tag === "None")) {
      $21 = voidTy$112();
      break m$23;
    }
    if (($22.$tag === "Tuple")) {
      const items = $22.$;
      if (whole) {
        {
          let $24;
          const $25 = payloadExpected;
          m$26: {
            if (($25.$tag === "Some")) {
              const t = $25.$;
              $24 = clone$23(t);
              break m$26;
            }
            if (($25.$tag === "None")) {
              $24 = { $tag: "Error" };
              break m$26;
            }
            $rt.unmatched($25);
          }
          const p = $24;
          slot$615(self, $rt.idx(items, 0n), p);
          insert$20(new $rt.FieldRef(self.v.typed, "whole"), id);
          $21 = p;
        }
        break m$23;
      }
    }
    if (($22.$tag === "Tuple")) {
      const items = $22.$;
      {
        const want = { v: $b.Vec_new() };
        let $27;
        const $28 = payloadExpected;
        m$29: {
          if (($28.$tag === "Some")) {
            const t = $28.$;
            $27 = { $tag: "Some", $: resolve$109(self.v.s, t) };
            break m$29;
          }
          if (($28.$tag === "None")) {
            $27 = { $tag: "None" };
            break m$29;
          }
          $rt.unmatched($28);
        }
        const $30 = $27;
        m$31: {
          if (($30.$tag === "Some" && ($30.$.$tag === "Tuple"))) {
            const ts = $30.$.$;
            if (($b.slice_len(ts) === $b.slice_len(items))) {
              {
                for (const $32 of $rt.items(ts)) {
                  const t = $32;
                  $b.Vec_push(want, { $tag: "Some", $: clone$23(t) });
                }
              }
              break m$31;
            }
          }
          if (true) {
            {
              const $33 = $b.slice_len(items);
              for (let $34$$35 = 0n; $34$$35 < $33; $34$$35++) {
                $b.Vec_push(want, { $tag: "None" });
              }
            }
            break m$31;
          }
          $rt.unmatched($30);
        }
        const out = { v: $b.Vec_new() };
        const $36 = $b.slice_len(items);
        for (let i = 0n; i < $36; i++) {
          const $37 = $rt.idx(want.v, i);
          m$38: {
            if (($37.$tag === "Some")) {
              const w = $37.$;
              {
                slot$615(self, $rt.idx(items, i), w);
                $b.Vec_push(out, clone$23(w));
              }
              break m$38;
            }
            if (($37.$tag === "None")) {
              $b.Vec_push(out, expr$102(self, $rt.idx(items, i), { $tag: "None" }));
              break m$38;
            }
            $rt.unmatched($37);
          }
        }
        $21 = { $tag: "Tuple", $: out.v };
      }
      break m$23;
    }
    if (($22.$tag === "Record")) {
      const fields = $22.$;
      $21 = record$422(self, { $tag: "None" }, fields, clone$225(payloadExpected), $rt.copy(span));
      break m$23;
    }
    $rt.unmatched($22);
  }
  const payload = $21;
  const $39 = payloadExpected;
  m$40: {
    if (($39.$tag === "Some")) {
      const p = $39.$;
      {
        if ((!lends$116(self, payload, p))) {
          const a = show$123(self.v, p);
          const b = show$123(self.v, payload);
          err$108(self, $rt.copy(span), $b.String_asStr(("" + "`#" + name + "` carries `" + a + "`, found `" + b + "`")));
        }
        const $41 = expected;
        m$42: {
          if (($41.$tag === "Some")) {
            const x = $41.$;
            {
              const $43 = strip$124(self.v, x);
              m$44: {
                if (($43.$tag === "Named")) {
                  {
                    return strip$124(self.v, x);
                  }
                  break m$44;
                }
                if (true) {
                  {
                  }
                  break m$44;
                }
                $rt.unmatched($43);
              }
            }
            break m$42;
          }
          if (true) {
            {
            }
            break m$42;
          }
          $rt.unmatched($41);
        }
      }
      break m$40;
    }
    if (true) {
      {
      }
      break m$40;
    }
    $rt.unmatched($39);
  }
  const labels = { v: $b.Vec_new() };
  labelSet$184(labels, name, payload);
  return { $tag: "Union", $: { labels: labels.v, tail: freshRowTail$243(new $rt.FieldRef(self.v, "s")) } };
}
function record$422(self, name, fields, expected, span) {
  let $1;
  const $2 = name;
  m$3: {
    if (($2.$tag === "Some")) {
      const path = $2.$;
      {
        const scope = clone$97(self.v.scope);
        const t = { kind: { $tag: "Path", $: { segments: clone$400(path), args: $b.Vec_new() } }, span: span };
        $1 = { $tag: "Some", $: instantiateNamed$616(self, t, scope) };
      }
      break m$3;
    }
    if (($2.$tag === "None")) {
      const $4 = expected;
      m$5: {
        if (($4.$tag === "Some")) {
          const x = $4.$;
          const $6 = strip$124(self.v, x);
          m$7: {
            if (($6.$tag === "Named")) {
              const d = $6.$[0];
              const args = $6.$[1];
              $1 = { $tag: "Some", $: { $tag: "Named", $: [d, args] } };
              break m$7;
            }
            if (($6.$tag === "Record")) {
              const r = $6.$;
              $1 = { $tag: "Some", $: { $tag: "Record", $: r } };
              break m$7;
            }
            if (true) {
              $1 = { $tag: "None" };
              break m$7;
            }
            $rt.unmatched($6);
          }
          break m$5;
        }
        if (($4.$tag === "None")) {
          $1 = { $tag: "None" };
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$3;
    }
    $rt.unmatched($2);
  }
  const target = $1;
  let wanted = { $tag: "None" };
  let named = false;
  const $8 = target;
  m$9: {
    if (($8.$tag === "Some" && ($8.$.$tag === "Named"))) {
      const d = $8.$.$[0];
      const args = $8.$.$[1];
      {
        named = true;
        const zonked = { v: $b.Vec_new() };
        for (const $10 of $rt.items(args)) {
          const a = $10;
          $b.Vec_push(zonked, zonkArg$145(self.v.s, a));
        }
        ensureInstance$231(self.v.p, d, zonked.v);
        if (failedInstance$448(self.v.p.v, d, zonked.v)) {
          for (const $11 of $rt.items(fields)) {
            const f = $11;
            const $12 = f.value;
            m$13: {
              if (($12.$tag === "Some")) {
                const v = $12.$;
                {
                  expr$102(self, v, { $tag: "None" });
                }
                break m$13;
              }
              if (true) {
                {
                }
                break m$13;
              }
              $rt.unmatched($12);
            }
          }
          return { $tag: "Error" };
        }
        wanted = structFields$449(self.v.p.v, d, zonked.v);
        unsealed$240(self, d, "built", $rt.copy(span));
      }
      break m$9;
    }
    if (($8.$tag === "Some" && ($8.$.$tag === "Record"))) {
      const r = $8.$.$;
      {
        wanted = { $tag: "Some", $: expandRow$125(self.v.s, r).labels };
      }
      break m$9;
    }
    if (true) {
      {
      }
      break m$9;
    }
    $rt.unmatched($8);
  }
  const labels = { v: $b.Vec_new() };
  for (const $14 of $rt.items(fields)) {
    const f = $14;
    let $15;
    const $16 = wanted;
    m$17: {
      if (($16.$tag === "Some")) {
        const w = $16.$;
        const $20 = find$408($b.slice_iter(w), (($0$$18) => {
  {
    const $19 = $0$$18;
    const k = $19[0];
    return eq$6(k, f.name.name);
  }
        }));
        m$21: {
          if (($20.$tag === "Some")) {
            const t = $20.$[1];
            $15 = { $tag: "Some", $: clone$23(t) };
            break m$21;
          }
          if (($20.$tag === "None")) {
            $15 = { $tag: "None" };
            break m$21;
          }
          $rt.unmatched($20);
        }
        break m$17;
      }
      if (($16.$tag === "None")) {
        $15 = { $tag: "None" };
        break m$17;
      }
      $rt.unmatched($16);
    }
    const want = $15;
    if ((($b.Option_isSome(wanted) && isNone$269(want)) && named)) {
      let $22;
      const $23 = target;
      m$24: {
        if (($23.$tag === "Some")) {
          const t = $23.$;
          $22 = show$123(self.v, t);
          break m$24;
        }
        if (($23.$tag === "None")) {
          $22 = $b.String_new();
          break m$24;
        }
        $rt.unmatched($23);
      }
      const shown = $22;
      err$108(self, $rt.copy(f.name.span), $b.String_asStr(("" + "no field `" + f.name.name + "` in `" + shown + "`")));
    }
    let $25;
    const $26 = f.value;
    m$27: {
      if (($26.$tag === "Some")) {
        const v = $26.$;
        const $28 = want;
        m$29: {
          if (($28.$tag === "Some")) {
            const w = $28.$;
            {
              slot$615(self, v, w);
              $25 = clone$23(w);
            }
            break m$29;
          }
          if (($28.$tag === "None")) {
            $25 = expr$102(self, v, { $tag: "None" });
            break m$29;
          }
          $rt.unmatched($28);
        }
        break m$27;
      }
      if (($26.$tag === "None")) {
        {
          const t = ident$420(self, $b.String_asStr(f.name.name), $rt.copy(f.name.span), { $tag: "None" });
          const $30 = want;
          m$31: {
            if (($30.$tag === "Some")) {
              const w = $30.$;
              {
                coerce$44(self, t, w, $rt.copy(f.name.span));
                $25 = clone$23(w);
              }
              break m$31;
            }
            if (($30.$tag === "None")) {
              $25 = t;
              break m$31;
            }
            $rt.unmatched($30);
          }
        }
        break m$27;
      }
      $rt.unmatched($26);
    }
    const t = $25;
    labelSet$184(labels, $b.String_asStr(f.name.name), t);
  }
  const $32 = target;
  m$33: {
    if (($32.$tag === "Some" && ($32.$.$tag === "Named"))) {
      const d = $32.$.$[0];
      const args = $32.$.$[1];
      {
        const $34 = wanted;
        m$35: {
          if (($34.$tag === "Some")) {
            const w = $34.$;
            {
              const missing = { v: $b.Vec_new() };
              for (const $36 of $rt.items(w)) {
                const k = $36[0];
                if ((!labelHas$126(labels.v, $b.String_asStr(k)))) {
                  $b.Vec_push(missing, ("" + "`" + k + "`"));
                }
              }
              if (($b.slice_len(missing.v) > 0n)) {
                err$108(self, $rt.copy(span), $b.String_asStr(("" + "missing fields " + join$53(missing.v, ", "))));
              }
            }
            break m$35;
          }
          if (true) {
            {
            }
            break m$35;
          }
          $rt.unmatched($34);
        }
        return { $tag: "Named", $: [d, clone$197(args)] };
      }
      break m$33;
    }
    if (true) {
      return { $tag: "Record", $: { labels: labels.v, tail: { $tag: "Closed" } } };
      break m$33;
    }
    $rt.unmatched($32);
  }
}
function list$423(self, items, expected) {
  let $1;
  const $2 = expected;
  m$3: {
    if (($2.$tag === "Some")) {
      const x = $2.$;
      $1 = { $tag: "Some", $: strip$124(self.v, x) };
      break m$3;
    }
    if (($2.$tag === "None")) {
      $1 = { $tag: "None" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const want = $1;
  const $4 = want;
  m$5: {
    if (($4.$tag === "Some" && ($4.$.$tag === "Tuple"))) {
      const ts = $4.$.$;
      if (($b.slice_len(ts) === $b.slice_len(items))) {
        {
          const $6 = $b.slice_len(items);
          for (let i = 0n; i < $6; i++) {
            slot$615(self, $rt.idx(items, i), $rt.idx(ts, i));
          }
          return { $tag: "Tuple", $: ts };
        }
        break m$5;
      }
    }
    if (($4.$tag === "Some" && ($4.$.$tag === "Array"))) {
      const elem = $4.$.$[0];
      const len = $4.$.$[1];
      {
        for (const $7 of $rt.items(items)) {
          const it = $7;
          slot$615(self, it, elem);
        }
        try {
          unifyLen$445(new $rt.FieldRef(self.v, "s"), len, { $tag: "Known", $: $rt.wrap_u64($b.slice_len(items)) });
        } catch ($8) {
          if (!($8 instanceof $rt.Fail)) throw $8;
        }
        return { $tag: "Array", $: [elem, len] };
      }
      break m$5;
    }
    if (($4.$tag === "Some" && ($4.$.$tag === "Slice"))) {
      const elem = $4.$.$;
      {
        for (const $9 of $rt.items(items)) {
          const it = $9;
          slot$615(self, it, elem);
        }
        return { $tag: "Array", $: [elem, { $tag: "Known", $: $rt.wrap_u64($b.slice_len(items)) }] };
      }
      break m$5;
    }
    if (($4.$tag === "Some" && ($4.$.$tag === "Named"))) {
      const d = $4.$.$[0];
      const args = $4.$.$[1];
      if ((d === known$104(self.v, "Vec"))) {
        {
          const $10 = first$258(args);
          m$11: {
            if (($10.$tag === "Some" && ($10.$.$tag === "Ty"))) {
              const elem = $10.$.$;
              {
                for (const $12 of $rt.items(items)) {
                  const it = $12;
                  slot$615(self, it, elem);
                }
              }
              break m$11;
            }
            if (true) {
              {
              }
              break m$11;
            }
            $rt.unmatched($10);
          }
          return { $tag: "Named", $: [d, args] };
        }
        break m$5;
      }
    }
    if (true) {
      {
        const ts = { v: $b.Vec_new() };
        for (const $13 of $rt.items(items)) {
          const it = $13;
          $b.Vec_push(ts, expr$102(self, it, { $tag: "None" }));
        }
        if (($b.slice_len(ts.v) === 0n)) {
          return { $tag: "Tuple", $: ts.v };
        }
        let agree = true;
        const $14 = $b.slice_len(ts.v);
        for (let i = 1n; i < $14; i++) {
          if ((!tryUnify$237(self, $rt.idx(ts.v, 0n), $rt.idx(ts.v, i)))) {
            agree = false;
            break;
          }
        }
        if (agree) {
          return { $tag: "Array", $: [$b.Box_new(clone$23($rt.idx(ts.v, 0n))), { $tag: "Known", $: $rt.wrap_u64($b.slice_len(ts.v)) }] };
        } else {
          {
            return { $tag: "Tuple", $: ts.v };
          }
        }
      }
      break m$5;
    }
    $rt.unmatched($4);
  }
}
function index$424(self, target, index, span) {
  const t = expr$102(self, target, { $tag: "None" });
  const base = strip$124(self.v, t);
  const $1 = base;
  m$2: {
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        const $3 = index.kind;
        m$4: {
          if (($3.$tag === "Int")) {
            const i = $3.$;
            const $5 = $b.parseInt($b.String_asStr(i));
            m$6: {
              if (($5.$tag === "Some")) {
                const k = $5.$;
                if (((k >= 0n) && ($rt.wrap_usize(k) < $b.slice_len(ts)))) {
                  return clone$23($rt.idx(ts, $rt.wrap_usize(k)));
                  break m$6;
                }
              }
              if (true) {
                {
                  err$108(self, $rt.copy(index.span), $b.String_asStr(("" + "a tuple of " + String($b.slice_len(ts)) + " has no element " + i)));
                  return { $tag: "Error" };
                }
                break m$6;
              }
              $rt.unmatched($5);
            }
            break m$4;
          }
          if (true) {
            {
              err$108(self, $rt.copy(index.span), "a tuple is indexed by a constant: `t[0]`");
              return { $tag: "Error" };
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  let $7;
  const $8 = base;
  m$9: {
    if ((($8.$tag === "Array") || ($8.$tag === "Slice"))) {
      let e;
      if (($8.$tag === "Array")) { e = $8.$[0]; }
      else if (($8.$tag === "Slice")) { e = $8.$; }
      $7 = clone$23($b.Box_get(e));
      break m$9;
    }
    if (($8.$tag === "Prim" && ($8.$.$tag === "Str"))) {
      $7 = { $tag: "Prim", $: { $tag: "U8" } };
      break m$9;
    }
    if (($8.$tag === "Named")) {
      const d = $8.$[0];
      const args = $8.$[1];
      if ((d === known$104(self.v, "Vec"))) {
        const $10 = first$258(args);
        m$11: {
          if (($10.$tag === "Some" && ($10.$.$tag === "Ty"))) {
            const e = $10.$.$;
            $7 = clone$23(e);
            break m$11;
          }
          if (true) {
            $7 = { $tag: "Error" };
            break m$11;
          }
          $rt.unmatched($10);
        }
        break m$9;
      }
    }
    if (($8.$tag === "Error")) {
      return { $tag: "Error" };
      break m$9;
    }
    if (true) {
      {
        const shown = show$123(self.v, base);
        err$108(self, $rt.copy(span), $b.String_asStr(("" + "cannot index `" + shown + "`")));
        return { $tag: "Error" };
        $7 = undefined;
      }
      break m$9;
    }
    $rt.unmatched($8);
  }
  const elem = $7;
  const usizeTy = { $tag: "Prim", $: { $tag: "Usize" } };
  const $12 = index.kind;
  m$13: {
    if (($12.$tag === "Range")) {
      const lo = $12.$.lo;
      const hi = $12.$.hi;
      {
        const $14 = lo;
        m$15: {
          if (($14.$tag === "Some")) {
            const x = $14.$;
            {
              check$428(self, x, usizeTy);
            }
            break m$15;
          }
          if (true) {
            {
            }
            break m$15;
          }
          $rt.unmatched($14);
        }
        const $16 = hi;
        m$17: {
          if (($16.$tag === "Some")) {
            const x = $16.$;
            {
              check$428(self, x, usizeTy);
            }
            break m$17;
          }
          if (true) {
            {
            }
            break m$17;
          }
          $rt.unmatched($16);
        }
        if (eq$234(base, { $tag: "Prim", $: { $tag: "Str" } })) {
          return { $tag: "Prim", $: { $tag: "Str" } };
        } else {
          {
            return { $tag: "Slice", $: $b.Box_new(elem) };
          }
        }
      }
      break m$13;
    }
    if (true) {
      {
      }
      break m$13;
    }
    $rt.unmatched($12);
  }
  const it0 = expr$102(self, index, { $tag: "Some", $: clone$23(usizeTy) });
  const it = strip$124(self.v, it0);
  coerce$44(self, it, usizeTy, $rt.copy(index.span));
  return elem;
}
function call$425(self, callee, typeArgs, args, expected, e) {
  const span = $rt.copy(e.span);
  const scope = clone$97(self.v.scope);
  const explicit = { v: $b.Vec_new() };
  for (const $1 of $rt.items(typeArgs)) {
    const t = $1;
    $b.Vec_push(explicit, elabTy$101(self.v.p, t, scope));
  }
  const $2 = callee.kind;
  m$3: {
    if (($2.$tag === "Ident")) {
      const name = $2.$;
      if (isNone$269(local$612(self.v, $b.String_asStr(name)))) {
        {
          const $4 = lookup$47(self.v.p.v, self.v.module, $b.String_asStr(name));
          m$5: {
            if (($4.$tag === "Some" && ($4.$.$tag === "Fn"))) {
              const fid = $4.$.$;
              {
                let $6;
                const $7 = fnDecl$24(self.v.p.v, fid);
                m$8: {
                  if (($7.$tag === "Some")) {
                    const d = $7.$;
                    $6 = d.sig.isComptime;
                    break m$8;
                  }
                  if (($7.$tag === "None")) {
                    $6 = false;
                    break m$8;
                  }
                  $rt.unmatched($7);
                }
                if ($6) {
                  err$108(self, $rt.copy(span), $b.String_asStr(("" + "`" + name + "` is a `comptime function`: call it from `comptime` code")));
                  return { $tag: "Error" };
                }
                return callFn$617(self, fid, $b.Vec_new(), { $tag: "None" }, explicit.v, args, expected, e);
              }
              break m$5;
            }
            if (true) {
              {
              }
              break m$5;
            }
            $rt.unmatched($4);
          }
        }
        break m$3;
      }
    }
    if (($2.$tag === "Field")) {
      const target = $2.$.target;
      const name = $2.$.name;
      {
        const $9 = target.kind;
        m$10: {
          if (($9.$tag === "TypeRef")) {
            const i = $9.$;
            {
              const ty = clone$23($rt.idx(self.v.p.v.spliced, i));
              return callOnType$618(self, ty, $b.String_asStr(name.name), explicit.v, args, expected, e);
            }
            break m$10;
          }
          if (true) {
            {
            }
            break m$10;
          }
          $rt.unmatched($9);
        }
        const $11 = target.kind;
        m$12: {
          if (($11.$tag === "Ident")) {
            const tname = $11.$;
            {
              if (isNone$269(local$612(self.v, $b.String_asStr(tname)))) {
                let $13;
                const $14 = $b.HashMap_get(self.v.scope.params, $b.String_asStr(tname));
                m$15: {
                  if (($14.$tag === "Some")) {
                    const sym = $14.$[0];
                    $13 = { $tag: "Some", $: clone$34(sym) };
                    break m$15;
                  }
                  if (($14.$tag === "None")) {
                    $13 = { $tag: "None" };
                    break m$15;
                  }
                  $rt.unmatched($14);
                }
                const param = $13;
                const $16 = param;
                m$17: {
                  if (($16.$tag === "Some")) {
                    const sym = $16.$;
                    {
                      return callOnType$618(self, { $tag: "Param", $: sym }, $b.String_asStr(name.name), explicit.v, args, expected, e);
                    }
                    break m$17;
                  }
                  if (true) {
                    {
                    }
                    break m$17;
                  }
                  $rt.unmatched($16);
                }
                const $18 = lookup$47(self.v.p.v, self.v.module, $b.String_asStr(tname));
                m$19: {
                  if (($18.$tag === "Some" && ($18.$.$tag === "Def"))) {
                    const d = $18.$.$;
                    {
                      return callStatic$619(self, d, $b.String_asStr(name.name), explicit.v, args, expected, e);
                    }
                    break m$19;
                  }
                  if (true) {
                    {
                    }
                    break m$19;
                  }
                  $rt.unmatched($18);
                }
              }
            }
            break m$12;
          }
          if (true) {
            {
            }
            break m$12;
          }
          $rt.unmatched($11);
        }
        const recv = expr$102(self, target, { $tag: "None" });
        return callMethod$620(self, recv, $rt.copy(target.span), $b.String_asStr(name.name), explicit.v, args, expected, e);
      }
      break m$3;
    }
    if (true) {
      {
      }
      break m$3;
    }
    $rt.unmatched($2);
  }
  const t = expr$102(self, callee, { $tag: "None" });
  let $20;
  const $21 = resolve$109(self.v.s, t);
  m$22: {
    if (($21.$tag === "Borrow")) {
      const m = $21.$[0];
      $20 = { $tag: "Some", $: m };
      break m$22;
    }
    if (true) {
      $20 = { $tag: "None" };
      break m$22;
    }
    $rt.unmatched($21);
  }
  const through = $20;
  const $23 = strip$124(self.v, t);
  m$24: {
    if (($23.$tag === "Named")) {
      const d = $23.$[0];
      const cargs = $23.$[1];
      {
        if ((d === known$104(self.v, "Cont"))) {
          let $25;
          const $26 = first$258(cargs);
          m$27: {
            if (($26.$tag === "Some" && ($26.$.$tag === "Ty"))) {
              const x = $26.$.$;
              $25 = clone$23(x);
              break m$27;
            }
            if (true) {
              return { $tag: "Error" };
              break m$27;
            }
            $rt.unmatched($26);
          }
          const a = $25;
          let $28;
          const $29 = get$137(cargs, 1n);
          m$30: {
            if (($29.$tag === "Some" && ($29.$.$tag === "Ty"))) {
              const x = $29.$.$;
              $28 = clone$23(x);
              break m$30;
            }
            if (true) {
              return { $tag: "Error" };
              break m$30;
            }
            $rt.unmatched($29);
          }
          const b = $28;
          if ($b.Option_isSome(through)) {
            err$108(self, $rt.copy(callee.span), "a continuation is called only by moving it");
          }
          let $31;
          if (eq$234(a, voidTy$112())) {
            $31 = $b.Vec_new();
          } else {
            {
              $31 = [clone$23(a)];
            }
          }
          const params = $31;
          checkArgs$621(self, params, args, $rt.copy(span));
          const $32 = get$137(cargs, 2n);
          m$33: {
            if (($32.$tag === "Some" && ($32.$.$tag === "Row"))) {
              const row = $32.$.$;
              {
                perform$437(self, clone$40(row), $rt.copy(span), e.id);
              }
              break m$33;
            }
            if (true) {
              {
              }
              break m$33;
            }
            $rt.unmatched($32);
          }
          return b;
        }
      }
      break m$24;
    }
    if (true) {
      {
      }
      break m$24;
    }
    $rt.unmatched($23);
  }
  const $34 = strip$124(self.v, t);
  m$35: {
    if (($34.$tag === "Fn")) {
      const f = $34.$;
      if (($b.Option_isSome(through) && (eq$622(f.mode, { $tag: "Once" }) || (eq$622(f.mode, { $tag: "Mut" }) && eq$623(through, { $tag: "Some", $: false }))))) {
        {
          let $36;
          if (eq$622(f.mode, { $tag: "Once" })) {
            $36 = ["once", "only by moving it"];
          } else {
            {
              $36 = ["mut", "only through a `mut` borrow"];
            }
          }
          const $37 = $36;
          const mode = $37[0];
          const how = $37[1];
          err$108(self, $rt.copy(callee.span), $b.String_asStr(("" + "a `" + mode + "` function is called " + how)));
          return clone$23(f.ret);
        }
        break m$35;
      }
    }
    if (($34.$tag === "Fn")) {
      const f = $34.$;
      {
        checkArgs$621(self, f.params, args, $rt.copy(span));
        perform$437(self, f.effects, $rt.copy(span), e.id);
        return clone$23(f.ret);
      }
      break m$35;
    }
    if (($34.$tag === "Error")) {
      return { $tag: "Error" };
      break m$35;
    }
    if (true) {
      const other = $34;
      {
        const shown = show$123(self.v, other);
        err$108(self, $rt.copy(callee.span), $b.String_asStr(("" + "`" + shown + "` is not a function")));
        return { $tag: "Error" };
      }
      break m$35;
    }
    $rt.unmatched($34);
  }
}
function binary$426(self, op, lhs, rhs, e) {
  const span = $rt.copy(e.span);
  if (((op === "&&") || (op === "||"))) {
    check$428(self, lhs, boolTy$189());
    check$428(self, rhs, boolTy$189());
    return boolTy$189();
  }
  const lit = ((x) => {
  const $1 = x.kind;
  m$2: {
    if ((($1.$tag === "Tag") || ($1.$tag === "Record" && ($1.$.name.$tag === "None")) || ($1.$tag === "List"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
  });
  let l = { $tag: "Error" };
  let r = { $tag: "Error" };
  if ((lit(lhs) && (!lit(rhs)))) {
    const r0 = expr$102(self, rhs, { $tag: "None" });
    r = strip$124(self.v, r0);
    const l0 = expr$102(self, lhs, { $tag: "Some", $: clone$23(r) });
    l = strip$124(self.v, l0);
  } else {
    {
      const l0 = expr$102(self, lhs, { $tag: "None" });
      l = strip$124(self.v, l0);
      const r0 = expr$102(self, rhs, { $tag: "Some", $: clone$23(l) });
      r = strip$124(self.v, r0);
    }
  }
  const comparison = ((((((op === "==") || (op === "!=")) || (op === "<")) || (op === ">")) || (op === "<=")) || (op === ">="));
  let operand = clone$23(l);
  if (tryUnify$237(self, l, r)) {
  } else {
    if ((comparison && lends$116(self, l, { $tag: "Borrow", $: [false, $b.Box_new(clone$23(r))] }))) {
      operand = clone$23(r);
    } else {
      if ((comparison && lends$116(self, r, { $tag: "Borrow", $: [false, $b.Box_new(clone$23(l))] }))) {
      } else {
        {
          const a = show$123(self.v, l);
          const b = show$123(self.v, r);
          err$108(self, $rt.copy(span), $b.String_asStr(("" + "`" + op + "` needs operands of the same type, found `" + a + "` and `" + b + "`")));
        }
      }
    }
  }
  if (((op === "==") || (op === "!="))) {
    $b.Vec_push(new $rt.FieldRef(self.v, "pendingOps"), [e.id, $rt.copy(span), operand, $b.str_toString("Eq"), $b.str_toString("eq")]);
    return boolTy$189();
  }
  if (((((op === "<") || (op === ">")) || (op === "<=")) || (op === ">="))) {
    $b.Vec_push(new $rt.FieldRef(self.v, "pendingOps"), [e.id, $rt.copy(span), operand, $b.str_toString("Ord"), $b.str_toString("cmp")]);
    return boolTy$189();
  }
  return operand;
}
function lambda$427(self, params, body, expected) {
  let $1;
  const $2 = expected;
  m$3: {
    if (($2.$tag === "Some")) {
      const x = $2.$;
      $1 = { $tag: "Some", $: normalize$113(self.v, resolve$109(self.v.s, x)) };
      break m$3;
    }
    if (($2.$tag === "None")) {
      $1 = { $tag: "None" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const want = $1;
  let wantParams = { $tag: "None" };
  let wantRet = { $tag: "None" };
  let mode = { $tag: "Shared" };
  const $4 = want;
  m$5: {
    if (($4.$tag === "Some" && ($4.$.$tag === "Fn"))) {
      const f = $4.$.$;
      {
        if (($b.slice_len(f.params) === $b.slice_len(params))) {
          wantParams = { $tag: "Some", $: clone$35(f.params) };
          wantRet = { $tag: "Some", $: clone$23(f.ret) };
          mode = f.mode;
        }
      }
      break m$5;
    }
    if (true) {
      {
      }
      break m$5;
    }
    $rt.unmatched($4);
  }
  $b.Vec_push(new $rt.FieldRef(self.v, "scopes"), $b.HashMap_new());
  const ptys = { v: $b.Vec_new() };
  const $6 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(params)));
  let $8;
  for (let $7 = $6.next(); !$7.done; $7 = $6.next($8)) {
    $8 = undefined;
    const $9 = $7.value.item;
    const i = $9[0];
    const p = $9[1];
    let $10;
    const $11 = p.ty;
    m$12: {
      if (($11.$tag === "Some")) {
        const ty = $11.$;
        {
          const scope = clone$97(self.v.scope);
          $10 = elabTy$101(self.v.p, ty, scope);
        }
        break m$12;
      }
      if (($11.$tag === "None")) {
        const $13 = wantParams;
        m$14: {
          if (($13.$tag === "Some")) {
            const w = $13.$;
            $10 = normalize$113(self.v, $rt.idx(w, i));
            break m$14;
          }
          if (($13.$tag === "None")) {
            $10 = fresh$238(new $rt.FieldRef(self.v, "s"));
            break m$14;
          }
          $rt.unmatched($13);
        }
        break m$12;
      }
      $rt.unmatched($11);
    }
    const t = $10;
    if ((p.name.name !== "_")) {
      declare$42(self, $b.String_asStr(p.name.name), clone$23(t));
    }
    $b.Vec_push(ptys, t);
  }
  let $15;
  const $16 = wantRet;
  m$17: {
    if (($16.$tag === "Some")) {
      const x = $16.$;
      $15 = clone$23(x);
      break m$17;
    }
    if (($16.$tag === "None")) {
      $15 = fresh$238(new $rt.FieldRef(self.v, "s"));
      break m$17;
    }
    $rt.unmatched($16);
  }
  const r = $15;
  const savedRet = $b.replace(new $rt.FieldRef(self.v, "ret"), clone$23(r));
  const innerAllowed = freshEffs$41(new $rt.FieldRef(self.v, "s"));
  const savedAllowed = $b.replace(new $rt.FieldRef(self.v, "allowed"), clone$40(innerAllowed));
  $b.Vec_push(new $rt.FieldRef(self.v, "performed"), $b.Vec_new());
  const t = expr$102(self, body, { $tag: "Some", $: clone$23(r) });
  $b.Vec_pop(new $rt.FieldRef(self.v, "performed"));
  if ($b.Option_isSome(wantRet)) {
    coerce$44(self, t, r, $rt.copy(body.span));
  } else {
    {
      try {
        unify$239(new $rt.FieldRef(self.v, "s"), r, t);
      } catch ($18) {
        if (!($18 instanceof $rt.Fail)) throw $18;
      }
    }
  }
  self.v.allowed = savedAllowed;
  self.v.ret = savedRet;
  $b.Vec_pop(new $rt.FieldRef(self.v, "scopes"));
  return { $tag: "Fn", $: $b.Box_new({ mode: mode, params: ptys.v, ret: r, effects: innerAllowed }) };
}
function check$428(self, e, expected) {
  const t = expr$102(self, e, { $tag: "Some", $: clone$23(expected) });
  coerce$44(self, t, expected, $rt.copy(e.span));
  return t;
}
function unknown$429(self, expected) {
  const $1 = expected;
  m$2: {
    if (($1.$tag === "None")) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      const $3 = resolve$109(self.s, x);
      m$4: {
        if (($3.$tag === "Var")) {
          return true;
          break m$4;
        }
        if (true) {
          return false;
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function tagBuiltBlock$430(b) {
  const $1 = b.tail;
  m$2: {
    if (($1.$tag === "Some")) {
      const t = $1.$;
      return tagBuilt$431(t);
      break m$2;
    }
    if (($1.$tag === "None")) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function tagBuilt$431(e) {
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "Tag")) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Block")) {
      const b = $1.$;
      return tagBuiltBlock$430(b);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function join$432(self, types, expected) {
  const $1 = expected;
  m$2: {
    if (($1.$tag === "Some")) {
      const x = $1.$;
      {
        for (const $3 of $rt.items(types)) {
          const t = $3[0];
          const span = $3[1];
          coerce$44(self, t, x, $rt.copy(span));
        }
        return x;
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  let result = { $tag: "None" };
  for (const $4 of $rt.items(types)) {
    const t = $4[0];
    const span = $4[1];
    if (isNever$110(resolve$109(self.v.s, t))) {
      continue;
    }
    const $5 = result;
    m$6: {
      if (($5.$tag === "None")) {
        {
          result = { $tag: "Some", $: clone$23(t) };
        }
        break m$6;
      }
      if (($5.$tag === "Some")) {
        const r0 = $5.$;
        {
          const r = clone$23(r0);
          if (((!lends$116(self, t, r)) && (!lends$116(self, r, t)))) {
            const a = show$123(self.v, r);
            const b = show$123(self.v, t);
            let $7;
            const $8 = enumHint$128(self.v, r, t);
            m$9: {
              if (($8.$tag === "Some")) {
                const h = $8.$;
                $7 = h;
                break m$9;
              }
              if (($8.$tag === "None")) {
                const $10 = enumHint$128(self.v, t, r);
                m$11: {
                  if (($10.$tag === "Some")) {
                    const h = $10.$;
                    $7 = h;
                    break m$11;
                  }
                  if (($10.$tag === "None")) {
                    $7 = $b.String_new();
                    break m$11;
                  }
                  $rt.unmatched($10);
                }
                break m$9;
              }
              $rt.unmatched($8);
            }
            const hint = $7;
            err$108(self, $rt.copy(span), $b.String_asStr(("" + "branches have different types: `" + a + "` and `" + b + "`" + hint)));
          }
        }
        break m$6;
      }
      $rt.unmatched($5);
    }
  }
  const $12 = result;
  m$13: {
    if (($12.$tag === "Some")) {
      const r = $12.$;
      return r;
      break m$13;
    }
    if (($12.$tag === "None")) {
      return neverTy$111();
      break m$13;
    }
    $rt.unmatched($12);
  }
}
function forOf$433(self, pat, iter, body) {
  const $1 = iter.kind;
  m$2: {
    if (($1.$tag === "Range")) {
      const lo = $1.$.lo;
      const hi = $1.$.hi;
      {
        const t = freshKind$418(new $rt.FieldRef(self.v, "s"), { $tag: "Int" });
        const $3 = [lo, hi];
        m$4: {
          if ((($3[0].$tag === "Some") && ($3[1].$tag === "Some"))) {
            const l = $3[0].$;
            const h = $3[1].$;
            {
              check$428(self, l, t);
              check$428(self, h, t);
            }
            break m$4;
          }
          if (true) {
            err$108(self, $rt.copy(iter.span), "a range iterated needs both bounds: `0..n`");
            break m$4;
          }
          $rt.unmatched($3);
        }
        $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "exprs"), iter.id, clone$23(t));
        $b.HashMap_insert(new $rt.FieldRef(self.v, "spans"), iter.id, $rt.copy(iter.span));
        $b.Vec_push(new $rt.FieldRef(self.v, "scopes"), $b.HashMap_new());
        bind$103(self, pat, t);
        block$43(self, body, { $tag: "None" });
        $b.Vec_pop(new $rt.FieldRef(self.v, "scopes"));
        return voidTy$112();
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const isolated = freshEffs$41(new $rt.FieldRef(self.v, "s"));
  const outer = $b.replace(new $rt.FieldRef(self.v, "allowed"), clone$40(isolated));
  $b.Vec_push(new $rt.FieldRef(self.v, "performed"), $b.Vec_new());
  let $5;
  const $6 = iter.kind;
  m$7: {
    if (($6.$tag === "List")) {
      {
        const elem = fresh$238(new $rt.FieldRef(self.v, "s"));
        $5 = expr$102(self, iter, { $tag: "Some", $: { $tag: "Slice", $: $b.Box_new(elem) } });
      }
      break m$7;
    }
    if (true) {
      $5 = expr$102(self, iter, { $tag: "None" });
      break m$7;
    }
    $rt.unmatched($6);
  }
  const t = $5;
  $b.Vec_pop(new $rt.FieldRef(self.v, "performed"));
  self.v.allowed = outer;
  const yieldDef = known$104(self.v, "Yield");
  let row = expandEffs$105(self.v.s, isolated);
  let item = { $tag: "Error" };
  const $8 = findIndex$624($b.slice_iter(row.effs), ((x) => {
  return (x.def === yieldDef);
  }));
  m$9: {
    if (($8.$tag === "Some")) {
      const i = $8.$;
      {
        item = clone$23($rt.idx($b.Vec_remove(new $rt.FieldRef(row, "effs"), i).args, 0n));
      }
      break m$9;
    }
    if (($8.$tag === "None")) {
      {
        if (isNone$86(findMethod$625(self, t, "each"))) {
          if (!eq$234(resolve$109(self.v.s, t), { $tag: "Error" })) {
            const shown = show$123(self.v, t);
            err$108(self, $rt.copy(iter.span), $b.String_asStr(("" + "`" + shown + "` is neither a generator nor `Iterable`")));
          }
        } else {
          {
            const isolated2 = freshEffs$41(new $rt.FieldRef(self.v, "s"));
            const outer2 = $b.replace(new $rt.FieldRef(self.v, "allowed"), clone$40(isolated2));
            self.v.p.v.nextId = $rt.usize(self.v.p.v.nextId + 1n);
            const implicit = { kind: { $tag: "Break" }, span: { start: iter.span.end, end: iter.span.end }, id: self.v.p.v.nextId };
            $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "eaches"), iter.id, implicit.id);
            callMethod$620(self, t, $rt.copy(iter.span), "each", $b.Vec_new(), $b.Vec_new(), { $tag: "None" }, implicit);
            self.v.allowed = outer2;
            row = expandEffs$105(self.v.s, isolated2);
            const $10 = findIndex$624($b.slice_iter(row.effs), ((x) => {
  return (x.def === yieldDef);
            }));
            m$11: {
              if (($10.$tag === "Some")) {
                const i = $10.$;
                {
                  item = clone$23($rt.idx($b.Vec_remove(new $rt.FieldRef(row, "effs"), i).args, 0n));
                }
                break m$11;
              }
              if (($10.$tag === "None")) {
                {
                }
                break m$11;
              }
              $rt.unmatched($10);
            }
          }
        }
      }
      break m$9;
    }
    $rt.unmatched($8);
  }
  perform$437(self, row, $rt.copy(iter.span), iter.id);
  $b.Vec_push(new $rt.FieldRef(self.v, "scopes"), $b.HashMap_new());
  bind$103(self, pat, item);
  block$43(self, body, { $tag: "None" });
  $b.Vec_pop(new $rt.FieldRef(self.v, "scopes"));
  return voidTy$112();
}
function matchExpr$434(self, scrutinee, arms, expected, span) {
  const st0 = expr$102(self, scrutinee, { $tag: "None" });
  let $1;
  const $2 = resolve$109(self.v.s, st0);
  m$3: {
    if (($2.$tag === "Borrow")) {
      $1 = false;
      break m$3;
    }
    if (true) {
      $1 = true;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const owned = $1;
  const st1 = unbox$626(self.v, st0);
  let $4 = owned;
  if ($4) {
    let $5;
    const $6 = st1;
    m$7: {
      if (($6.$tag === "Borrow")) {
        $5 = true;
        break m$7;
      }
      if (true) {
        $5 = false;
        break m$7;
      }
      $rt.unmatched($6);
    }
    $4 = $5;
  }
  if ($4) {
    $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "lentScrutinees"), scrutinee.id, false);
  }
  let st = clone$23(st1);
  const $8 = unmovablePlace$627(self.v, scrutinee);
  m$9: {
    if (($8.$tag === "Some")) {
      const m = $8.$;
      {
        let $10;
        const $11 = resolve$109(self.v.s, st1);
        m$12: {
          if (($11.$tag === "Borrow")) {
            $10 = true;
            break m$12;
          }
          if (true) {
            $10 = false;
            break m$12;
          }
          $rt.unmatched($11);
        }
        if ((!$10)) {
          $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "lentScrutinees"), scrutinee.id, m);
          st = { $tag: "Borrow", $: [m, $b.Box_new(st1)] };
        }
      }
      break m$9;
    }
    if (true) {
      {
      }
      break m$9;
    }
    $rt.unmatched($8);
  }
  const handled = { v: $b.Vec_new() };
  const before = { v: $b.Vec_new() };
  for (const $13 of $rt.items(arms)) {
    const arm = $13;
    $b.Vec_push(before, clone$76(handled.v));
    if (isNone$273(arm.guard)) {
      wholeTags$628(arm.pat, handled);
    }
  }
  const open = unknown$429(self.v, expected);
  const order = { v: $b.Vec_new() };
  const $14 = $b.slice_len(arms);
  for (let i = 0n; i < $14; i++) {
    if (((!open) || (!tagBuilt$431($rt.idx(arms, i).body)))) {
      $b.Vec_push(order, i);
    }
  }
  if (open) {
    const $15 = $b.slice_len(arms);
    for (let i = 0n; i < $15; i++) {
      if (tagBuilt$431($rt.idx(arms, i).body)) {
        $b.Vec_push(order, i);
      }
    }
  }
  const types = { v: $b.Vec_new() };
  const $16 = $b.slice_len(arms);
  for (let $17$$18 = 0n; $17$$18 < $16; $17$$18++) {
    $b.Vec_push(types, { $tag: "None" });
  }
  let first = { $tag: "None" };
  for (const $19 of $rt.items(order.v)) {
    const i = $19;
    $b.Vec_push(new $rt.FieldRef(self.v, "scopes"), $b.HashMap_new());
    let $20;
    const $21 = $rt.idx(arms, i).pat.kind;
    m$22: {
      if (($21.$tag === "Bind")) {
        if (($b.slice_len($rt.idx(before.v, i)) > 0n)) {
          $20 = withoutTags$629(self.v, st, $rt.idx(before.v, i));
          break m$22;
        }
      }
      if (true) {
        $20 = { $tag: "None" };
        break m$22;
      }
      $rt.unmatched($21);
    }
    const narrowed = $20;
    const $23 = self;
    const $24 = $rt.idx(arms, i).pat;
    let $25;
    const $26 = narrowed;
    m$27: {
      if (($26.$tag === "Some")) {
        const n = $26.$;
        $25 = n;
        break m$27;
      }
      if (($26.$tag === "None")) {
        $25 = clone$23(st);
        break m$27;
      }
      $rt.unmatched($26);
    }
    bind$103($23, $24, $25);
    const $28 = $rt.idx(arms, i).guard;
    m$29: {
      if (($28.$tag === "Some")) {
        const g = $28.$;
        {
          check$428(self, g, boolTy$189());
        }
        break m$29;
      }
      if (true) {
        {
        }
        break m$29;
      }
      $rt.unmatched($28);
    }
    let $30;
    if (open) {
      const $31 = first;
      m$32: {
        if (($31.$tag === "Some")) {
          const f = $31.$;
          $30 = { $tag: "Some", $: clone$23(f) };
          break m$32;
        }
        if (($31.$tag === "None")) {
          $30 = clone$225(expected);
          break m$32;
        }
        $rt.unmatched($31);
      }
    } else {
      {
        $30 = clone$225(expected);
      }
    }
    const want = $30;
    const t = expr$102(self, $rt.idx(arms, i).body, want);
    if ((isNone$269(first) && (!isNever$110(resolve$109(self.v.s, t))))) {
      first = { $tag: "Some", $: clone$23(t) };
    }
    const $33 = types.v;
    $33[$rt.at($33, i)] = { $tag: "Some", $: [t, $rt.copy($rt.idx(arms, i).body.span)] };
    $b.Vec_pop(new $rt.FieldRef(self.v, "scopes"));
  }
  const out = { v: $b.Vec_new() };
  for (const $34 of $rt.items(types.v)) {
    const t = $34;
    const $35 = t;
    m$36: {
      if (($35.$tag === "Some")) {
        const x = $35.$;
        {
          $b.Vec_push(out, clone$630(x));
        }
        break m$36;
      }
      if (true) {
        {
        }
        break m$36;
      }
      $rt.unmatched($35);
    }
  }
  $b.Vec_push(new $rt.FieldRef(self.v, "pendingMatches"), [st, clone$568(arms), $rt.copy(span)]);
  return join$432(self, out.v, expected);
}
function tryCatch$435(self, body, pat, handler, expected) {
  const payload = { $tag: "Union", $: { labels: $b.Vec_new(), tail: freshRowTail$243(new $rt.FieldRef(self.v, "s")) } };
  const fail = eff$436(self.v, "Fail", $b.Vec_new(), [clone$23(payload)]);
  const outer = enterHandler$631(self, fail);
  const a = block$43(self, body, clone$225(expected));
  leaveHandler$632(self, fail, outer);
  closeUnion$272(new $rt.FieldRef(self.v, "s"), payload);
  $b.Vec_push(new $rt.FieldRef(self.v, "scopes"), $b.HashMap_new());
  bind$103(self, pat, payload);
  const b = block$43(self, handler, clone$225(expected));
  $b.Vec_pop(new $rt.FieldRef(self.v, "scopes"));
  return join$432(self, [[a, $rt.copy(body.span)], [b, $rt.copy(handler.span)]], expected);
}
function eff$436(self, name, regions, args) {
  return { def: known$104(self, name), regions: regions, args: args };
}
function perform$437(self, effects, span, id) {
  const row0 = expandEffs$105(self.v.s, effects);
  const defs = { v: $b.Vec_new() };
  for (const $1 of $rt.items(row0.effs)) {
    const e = $1;
    $b.Vec_push(defs, { $tag: "Some", $: e.def });
  }
  if (!eq$120(row0.tail, { $tag: "Closed" })) {
    $b.Vec_push(defs, { $tag: "None" });
  }
  let $2;
  const $3 = $b.HashMap_get(self.v.typed.performs, id);
  m$4: {
    if (($3.$tag === "Some")) {
      const v = $3.$;
      $2 = clone$633(v);
      break m$4;
    }
    if (($3.$tag === "None")) {
      $2 = $b.Vec_new();
      break m$4;
    }
    $rt.unmatched($3);
  }
  const recorded = { v: $2 };
  for (const $5 of $rt.items(defs.v)) {
    const d = $5;
    $b.Vec_push(recorded, d);
  }
  $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "performs"), id, recorded.v);
  const allowed = clone$40(self.v.allowed);
  if (($b.slice_len(row0.effs) === 0n)) {
    const $6 = row0.tail;
    m$7: {
      if (($6.$tag === "Var")) {
        const v = $6.$;
        {
          const $8 = $b.slice_len(self.v.pendingConts);
          for (let i = 0n; i < $8; i++) {
            if (($rt.idx($rt.idx(self.v.pendingConts, i), 0n) === v)) {
              $b.Vec_push($rt.indexRef($rt.idx(self.v.pendingConts, i), 1n), [$rt.copy(span), allowed]);
              return;
            }
          }
        }
        break m$7;
      }
      if (true) {
        {
        }
        break m$7;
      }
      $rt.unmatched($6);
    }
  }
  const regionDef = known$104(self.v, "Region");
  const handled = { v: $b.Vec_new() };
  for (const $9 of $rt.items(expandEffs$105(self.v.s, allowed).effs)) {
    const e = $9;
    if ((e.def === regionDef)) {
      const $10 = first$634(e.regions);
      m$11: {
        if (($10.$tag === "Some")) {
          const r = $10.$;
          {
            const $12 = resolveRegion$130(self.v.s, r);
            m$13: {
              if (($12.$tag === "Param")) {
                const s = $12.$;
                {
                  $b.Vec_push(handled, s);
                }
                break m$13;
              }
              if (true) {
                {
                }
                break m$13;
              }
              $rt.unmatched($12);
            }
          }
          break m$11;
        }
        if (true) {
          {
          }
          break m$11;
        }
        $rt.unmatched($10);
      }
    }
  }
  let effs = expandEffs$105(self.v.s, effects);
  const failDef = known$104(self.v, "Fail");
  const allowsFail = some$500($b.slice_iter(expandEffs$105(self.v.s, allowed).effs), ((e) => {
  return (e.def === failDef);
  }));
  const kept = { v: $b.Vec_new() };
  for (const $14 of $rt.items(effs.effs)) {
    const e = $14;
    if ((e.def !== failDef)) {
      $b.Vec_push(kept, clone$106(e));
      continue;
    }
    let $15;
    const $16 = first$263(e.args);
    m$17: {
      if (($16.$tag === "Some")) {
        const t = $16.$;
        $15 = { $tag: "Some", $: resolve$109(self.v.s, t) };
        break m$17;
      }
      if (($16.$tag === "None")) {
        $15 = { $tag: "None" };
        break m$17;
      }
      $rt.unmatched($16);
    }
    const $18 = $15;
    m$19: {
      if (($18.$tag === "Some" && ($18.$.$tag === "Var"))) {
        if ((!allowsFail)) {
          {
            const empty = { $tag: "Union", $: { labels: $b.Vec_new(), tail: { $tag: "Closed" } } };
            try {
              unify$239(new $rt.FieldRef(self.v, "s"), $rt.idx(e.args, 0n), empty);
            } catch ($20) {
              if (!($20 instanceof $rt.Fail)) throw $20;
            }
          }
          break m$19;
        }
      }
      if (($18.$tag === "Some" && ($18.$.$tag === "Union"))) {
        const r = $18.$.$;
        {
          const x = expandRow$125(self.v.s, r);
          if ((!(($b.slice_len(x.labels) === 0n) && eq$120(x.tail, { $tag: "Closed" })))) {
            $b.Vec_push(kept, clone$106(e));
          }
        }
        break m$19;
      }
      if (true) {
        $b.Vec_push(kept, clone$106(e));
        break m$19;
      }
      $rt.unmatched($18);
    }
  }
  effs.effs = kept.v;
  if (($b.slice_len(self.v.performed) > 0n)) {
    const last = $rt.usize($b.slice_len(self.v.performed) - 1n);
    for (const $21 of $rt.items(effs.effs)) {
      const e = $21;
      $b.Vec_push($rt.indexRef(self.v.performed, last), clone$106(e));
    }
  }
  if (($b.slice_len(handled.v) > 0n)) {
    const rest = { v: $b.Vec_new() };
    for (const $22 of $rt.items(effs.effs)) {
      const e = $22;
      if ((e.def !== regionDef)) {
        $b.Vec_push(rest, clone$106(e));
        continue;
      }
      let $23;
      const $24 = first$634(e.regions);
      m$25: {
        if (($24.$tag === "Some")) {
          const r = $24.$;
          $23 = { $tag: "Some", $: resolveRegion$130(self.v.s, r) };
          break m$25;
        }
        if (($24.$tag === "None")) {
          $23 = { $tag: "None" };
          break m$25;
        }
        $rt.unmatched($24);
      }
      const $26 = $23;
      m$27: {
        if (($26.$tag === "Some" && ($26.$.$tag === "Var"))) {
          const v = $26.$.$;
          $b.Vec_push(new $rt.FieldRef(self.v, "pendingRegions"), [v, clone$635(handled.v)]);
          break m$27;
        }
        if (true) {
          $b.Vec_push(rest, clone$106(e));
          break m$27;
        }
        $rt.unmatched($26);
      }
    }
    effs.effs = rest.v;
  }
  let $28;
  try {
    effSub$117(new $rt.FieldRef(self.v, "s"), effs, allowed);
    $28 = { $tag: "None" };
  } catch ($29) {
    if (!($29 instanceof $rt.Fail)) throw $29;
    if (!(($29.value.$tag === "Misfit"))) throw $29;
    const e = $29.value.$;
    $28 = { $tag: "Some", $: e };
  }
  const misfit = $28;
  const $30 = misfit;
  m$31: {
    if (($30.$tag === "Some")) {
      const e = $30.$;
      {
        const what = showEff$118(self.v, e);
        const isFail = (e.def === failDef);
        const cleanup = (self.v.inDefer && (isFail || (e.def === known$104(self.v, "Yield"))));
        let $32;
        if (cleanup) {
          $32 = ("" + "a `defer` cannot perform " + what + ": it runs while its block is being left, perhaps by a failure");
        } else {
          if (isFail) {
            const $33 = find$438($b.slice_iter(expandEffs$105(self.v.s, allowed).effs), ((x) => {
  return (x.def === e.def);
            }));
            m$34: {
              if (($33.$tag === "Some")) {
                const d = $33.$;
                $32 = ("" + "this can fail with `" + show$123(self.v, $rt.idx(e.args, 0n)) + "`, which is not in the declared failures `" + show$123(self.v, $rt.idx(d.args, 0n)) + "`");
                break m$34;
              }
              if (($33.$tag === "None")) {
                $32 = ("" + "this can fail with `" + show$123(self.v, $rt.idx(e.args, 0n)) + "`, but the enclosing function does not declare `Fail`");
                break m$34;
              }
              $rt.unmatched($33);
            }
          } else {
            if ((e.def === regionDef)) {
              let $35;
              const $36 = first$634(e.regions);
              m$37: {
                if (($36.$tag === "Some")) {
                  const r = $36.$;
                  $35 = { $tag: "Some", $: resolveRegion$130(self.v.s, r) };
                  break m$37;
                }
                if (($36.$tag === "None")) {
                  $35 = { $tag: "None" };
                  break m$37;
                }
                $rt.unmatched($36);
              }
              const $38 = $35;
              m$39: {
                if (($38.$tag === "Some" && ($38.$.$tag === "Heap"))) {
                  $32 = $b.str_toString("this allocates in a region, but its result is expected in the heap; region allocation needs an enclosing `region` block");
                  break m$39;
                }
                if (true) {
                  $32 = ("" + "this allocates in " + what + ", but no enclosing `region` block or declared effect allows it");
                  break m$39;
                }
                $rt.unmatched($38);
              }
            } else {
              {
                $32 = ("" + "effect " + what + " is not declared by the enclosing function");
              }
            }
          }
        }
        const msg = $32;
        err$108(self, $rt.copy(span), $b.String_asStr(msg));
        return undefined;
      }
      break m$31;
    }
    if (true) {
      {
        return undefined;
      }
      break m$31;
    }
    $rt.unmatched($30);
  }
}
function find$438(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function region$439(self, name, body, expected, span) {
  const sym = freshSym$59(self.v.p, $b.String_asStr(name.name));
  const saved = clone$97(self.v.scope);
  $b.HashMap_insert(new $rt.FieldRef(self.v.scope, "params"), $b.String_clone(name.name), [clone$34(sym), { $tag: "Region" }]);
  self.v.scope.elidedRegion = { $tag: "Some", $: { $tag: "Param", $: clone$34(sym) } };
  const eff = eff$436(self.v, "Region", [{ $tag: "Param", $: clone$34(sym) }], $b.Vec_new());
  const outer = enterHandler$631(self, eff);
  const t = block$43(self, body, expected);
  leaveHandler$632(self, eff, outer);
  self.v.scope = saved;
  settleRegions$636(self, sym, t);
  const z = zonk$134(self.v.s, t);
  if (mentionsRegion$637(z, sym)) {
    const shown = show$123(self.v, z);
    err$108(self, $rt.copy(span), $b.String_asStr(("" + "a value of type `" + shown + "` would outlive region `" + name.name + "`")));
  }
  const outerVars = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self.v.scopes)) {
    const sc = $1;
    const $2 = $b.Gen_each($b.HashMap_entries(sc));
    let $4;
    for (let $3 = $2.next(); !$3.done; $3 = $2.next($4)) {
      $4 = undefined;
      const $5 = $3.value.item;
      const k = $5[0];
      const v = $5[1];
      $b.Vec_push(outerVars, [$b.String_clone(k), clone$23(v)]);
    }
  }
  for (const $6 of $rt.items(outerVars.v)) {
    const v = $6[0];
    const ty = $6[1];
    if (mentionsRegion$637(zonk$134(self.v.s, ty), sym)) {
      err$108(self, $rt.copy(span), $b.String_asStr(("" + "`" + v + "` would hold data from region `" + name.name + "` after the region ends")));
    }
  }
  return t;
}
function handle$440(self, body, effect, arms, expected, e) {
  const scope = clone$97(self.v.scope);
  const row = elabEffects$195(self.v.p, [{ $tag: "Effect", $: clone$193(effect) }], scope);
  let $1;
  const $2 = first$638(row.effs);
  m$3: {
    if (($2.$tag === "Some")) {
      const x = $2.$;
      $1 = clone$106(x);
      break m$3;
    }
    if (($2.$tag === "None")) {
      return { $tag: "Error" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const eff = $1;
  $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "handled"), e.id, eff.def);
  let $4;
  const $5 = expected;
  m$6: {
    if (($5.$tag === "Some")) {
      const x = $5.$;
      $4 = x;
      break m$6;
    }
    if (($5.$tag === "None")) {
      $4 = fresh$238(new $rt.FieldRef(self.v, "s"));
      break m$6;
    }
    $rt.unmatched($5);
  }
  const result = $4;
  const contRow = freshEffs$41(new $rt.FieldRef(self.v, "s"));
  let $7;
  const $8 = contRow.tail;
  m$9: {
    if (($8.$tag === "Var")) {
      const v = $8.$;
      $7 = v;
      break m$9;
    }
    if (true) {
      return { $tag: "Error" };
      break m$9;
    }
    $rt.unmatched($8);
  }
  const contVar = $7;
  $b.Vec_push(new $rt.FieldRef(self.v, "pendingConts"), [contVar, $b.Vec_new()]);
  const around = clone$40(self.v.allowed);
  $b.Vec_push(new $rt.FieldRef(self.v, "performed"), $b.Vec_new());
  handleParts$639(self, body, eff, arms, result, contRow);
  let $10;
  const $11 = $b.Vec_pop(new $rt.FieldRef(self.v, "performed"));
  m$12: {
    if (($11.$tag === "Some")) {
      const v = $11.$;
      $10 = v;
      break m$12;
    }
    if (($11.$tag === "None")) {
      $10 = $b.Vec_new();
      break m$12;
    }
    $rt.unmatched($11);
  }
  const inside = $10;
  let $13;
  const $14 = $b.Vec_pop(new $rt.FieldRef(self.v, "pendingConts"));
  m$15: {
    if (($14.$tag === "Some")) {
      const c = $14.$[1];
      $13 = c;
      break m$15;
    }
    if (($14.$tag === "None")) {
      $13 = $b.Vec_new();
      break m$15;
    }
    $rt.unmatched($14);
  }
  const calls = $13;
  const own = ownRow$640(self, inside, around);
  const expanded = expandEffs$105(self.v.s, contRow);
  let $16;
  const $17 = expanded.tail;
  m$18: {
    if (($17.$tag === "Var")) {
      const v = $17.$;
      $16 = ((v === contVar) && ($b.slice_len(expanded.effs) === 0n));
      break m$18;
    }
    if (true) {
      $16 = false;
      break m$18;
    }
    $rt.unmatched($17);
  }
  const unbound = $16;
  if (unbound) {
    bindEffs$641(new $rt.FieldRef(self.v, "s"), contVar, clone$40(own));
  } else {
    {
      let $19;
      try {
        effSub$117(new $rt.FieldRef(self.v, "s"), own, contRow);
        $19 = { $tag: "None" };
      } catch ($20) {
        if (!($20 instanceof $rt.Fail)) throw $20;
        if (!(($20.value.$tag === "Misfit"))) throw $20;
        const x = $20.value.$;
        $19 = { $tag: "Some", $: x };
      }
      const misfit = $19;
      const $21 = misfit;
      m$22: {
        if (($21.$tag === "Some")) {
          const x = $21.$;
          {
            const what = showEff$118(self.v, x);
            err$108(self, $rt.copy(body.span), $b.String_asStr(("" + "resuming this `handle`'s continuation performs " + what + ", which its declared type does not allow")));
          }
          break m$22;
        }
        if (true) {
          {
          }
          break m$22;
        }
        $rt.unmatched($21);
      }
    }
  }
  if (($b.slice_len(self.v.performed) > 0n)) {
    const last = $rt.usize($b.slice_len(self.v.performed) - 1n);
    for (const $23 of $rt.items(own.effs)) {
      const x = $23;
      $b.Vec_push($rt.indexRef(self.v.performed, last), clone$106(x));
    }
  }
  for (const $24 of $rt.items(calls)) {
    const span = $24[0];
    const allowed = $24[1];
    const saved = $b.replace(new $rt.FieldRef(self.v, "allowed"), clone$40(allowed));
    $b.Vec_push(new $rt.FieldRef(self.v, "performed"), $b.Vec_new());
    perform$437(self, contRow, $rt.copy(span), e.id);
    $b.Vec_pop(new $rt.FieldRef(self.v, "performed"));
    self.v.allowed = saved;
  }
  return result;
}
function tryUnify$441(self, a, b) {
  const snap = clone$114(self.v);
  try {
    unify$239(self, a, b);
    return true;
  } catch ($1) {
    if (!($1 instanceof $rt.Fail)) throw $1;
    restore$122(self, snap);
    return false;
  }
}
function bindTy$442(self, v, t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Var")) {
      const w = $1.$;
      {
        if ((w === v)) {
          return;
        }
        const $3 = [kind$642(self.v, v), kind$642(self.v, w)];
        const a = $3[0];
        const b = $3[1];
        let $4;
        const $5 = [a, b];
        m$6: {
          if (((($5[0].$tag === "Any")) || (($5[1].$tag === "Any")))) {
            let k;
            if ((($5[0].$tag === "Any"))) { k = $5[1]; }
            else if ((($5[1].$tag === "Any"))) { k = $5[0]; }
            $4 = k;
            break m$6;
          }
          if (true) {
            const x = $5[0];
            const y = $5[1];
            if (eq$643(x, y)) {
              $4 = x;
              break m$6;
            }
          }
          if (true) {
            throw new $rt.Fail({ $tag: "Mismatch" });
            break m$6;
          }
          $rt.unmatched($5);
        }
        const merged = $4;
        const $7 = $rt.idx(self.v.tys, $rt.wrap_usize(w));
        $7[$rt.at($7, 1n)] = merged;
        const $8 = $rt.idx(self.v.tys, $rt.wrap_usize(v));
        $8[$rt.at($8, 0n)] = { $tag: "Some", $: { $tag: "Var", $: w } };
        return;
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  let $9;
  const $10 = kind$642(self.v, v);
  m$11: {
    if (($10.$tag === "Any")) {
      $9 = true;
      break m$11;
    }
    if (($10.$tag === "Int")) {
      const $12 = t;
      m$13: {
        if (($12.$tag === "Prim")) {
          const p = $12.$;
          $9 = isInt$324(p);
          break m$13;
        }
        if (($12.$tag === "Error")) {
          $9 = true;
          break m$13;
        }
        if (true) {
          $9 = false;
          break m$13;
        }
        $rt.unmatched($12);
      }
      break m$11;
    }
    if (($10.$tag === "Float")) {
      const $14 = t;
      m$15: {
        if (($14.$tag === "Prim")) {
          const p = $14.$;
          $9 = isFloat$417(p);
          break m$15;
        }
        if (($14.$tag === "Error")) {
          $9 = true;
          break m$15;
        }
        if (true) {
          $9 = false;
          break m$15;
        }
        $rt.unmatched($14);
      }
      break m$11;
    }
    $rt.unmatched($10);
  }
  const fits = $9;
  if (((!fits) || occurs$644(self.v, v, t))) {
    throw new $rt.Fail({ $tag: "Mismatch" });
  }
  const $16 = $rt.idx(self.v.tys, $rt.wrap_usize(v));
  $16[$rt.at($16, 0n)] = { $tag: "Some", $: t };
  return undefined;
}
function unifyArg$443(self, a, b) {
  const $1 = [a, b];
  m$2: {
    if ((($1[0].$tag === "Ty") && ($1[1].$tag === "Ty"))) {
      const x = $1[0].$;
      const y = $1[1].$;
      return unify$239(self, x, y);
      break m$2;
    }
    if ((($1[0].$tag === "Region") && ($1[1].$tag === "Region"))) {
      const x = $1[0].$;
      const y = $1[1].$;
      return unifyRegion$132(self, x, y);
      break m$2;
    }
    if ((($1[0].$tag === "Row") && ($1[1].$tag === "Row"))) {
      const x = $1[0].$;
      const y = $1[1].$;
      {
        const ex = expandEffs$105(self.v, x);
        const ey = expandEffs$105(self.v, y);
        if (($b.slice_len(ex.effs) === 0n)) {
          const $3 = ex.tail;
          m$4: {
            if (($3.$tag === "Var")) {
              const v = $3.$;
              {
                if (!eq$120(ey.tail, ex.tail)) {
                  const $5 = self.v.effs;
                  $5[$rt.at($5, $rt.wrap_usize(v))] = { $tag: "Some", $: ey };
                }
                return;
              }
              break m$4;
            }
            if (true) {
              {
              }
              break m$4;
            }
            $rt.unmatched($3);
          }
        }
        if (($b.slice_len(ey.effs) === 0n)) {
          const $6 = ey.tail;
          m$7: {
            if (($6.$tag === "Var")) {
              const v = $6.$;
              {
                if (!eq$120(ex.tail, ey.tail)) {
                  const $8 = self.v.effs;
                  $8[$rt.at($8, $rt.wrap_usize(v))] = { $tag: "Some", $: ex };
                }
                return;
              }
              break m$7;
            }
            if (true) {
              {
              }
              break m$7;
            }
            $rt.unmatched($6);
          }
        }
        effSubOrMismatch$446(self, x, y);
        effSubOrMismatch$446(self, y, x);
        return undefined;
      }
      break m$2;
    }
    if ((($1[0].$tag === "Len") && ($1[1].$tag === "Len"))) {
      const x = $1[0].$;
      const y = $1[1].$;
      return unifyLen$445(self, x, y);
      break m$2;
    }
    if (true) {
      throw new $rt.Fail({ $tag: "Mismatch" });
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function unifyRows$444(self, a, b) {
  const ra = expandRow$125(self.v, a);
  const rb = expandRow$125(self.v, b);
  for (const $1 of $rt.items(ra.labels)) {
    const k = $1[0];
    const ta = $1[1];
    const $2 = labelGet$233(rb.labels, $b.String_asStr(k));
    m$3: {
      if (($2.$tag === "Some")) {
        const tb = $2.$;
        {
          unify$239(self, ta, tb);
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  const onlyA = { v: $b.Vec_new() };
  for (const $4 of $rt.items(ra.labels)) {
    const k = $4[0];
    const t = $4[1];
    if ((!labelHas$126(rb.labels, $b.String_asStr(k)))) {
      $b.Vec_push(onlyA, [$b.String_clone(k), clone$23(t)]);
    }
  }
  const onlyB = { v: $b.Vec_new() };
  for (const $5 of $rt.items(rb.labels)) {
    const k = $5[0];
    const t = $5[1];
    if ((!labelHas$126(ra.labels, $b.String_asStr(k)))) {
      $b.Vec_push(onlyB, [$b.String_clone(k), clone$23(t)]);
    }
  }
  const $6 = [clone$99(ra.tail), clone$99(rb.tail)];
  m$7: {
    if ((($6[0].$tag === "Var") && ($6[1].$tag === "Var"))) {
      const x = $6[0].$;
      const y = $6[1].$;
      if ((x === y)) {
        {
          if ((($b.slice_len(onlyA.v) > 0n) || ($b.slice_len(onlyB.v) > 0n))) {
            throw new $rt.Fail({ $tag: "Mismatch" });
            return undefined;
          }
        }
        break m$7;
      }
    }
    if ((($6[0].$tag === "Var") && ($6[1].$tag === "Var"))) {
      {
        const fresh = freshRowTail$243(self);
        bindRowTail$284(self, ra.tail, onlyB.v, clone$99(fresh));
        bindRowTail$284(self, rb.tail, onlyA.v, fresh);
        return undefined;
      }
      break m$7;
    }
    if ((($6[0].$tag === "Var"))) {
      const other = $6[1];
      {
        if (($b.slice_len(onlyA.v) > 0n)) {
          throw new $rt.Fail({ $tag: "Mismatch" });
        }
        bindRowTail$284(self, ra.tail, onlyB.v, clone$99(other));
        return undefined;
      }
      break m$7;
    }
    if ((($6[1].$tag === "Var"))) {
      const other = $6[0];
      {
        if (($b.slice_len(onlyB.v) > 0n)) {
          throw new $rt.Fail({ $tag: "Mismatch" });
        }
        bindRowTail$284(self, rb.tail, onlyA.v, clone$99(other));
        return undefined;
      }
      break m$7;
    }
    if (true) {
      const x = $6[0];
      const y = $6[1];
      {
        if ((!((eq$120(x, y) && ($b.slice_len(onlyA.v) === 0n)) && ($b.slice_len(onlyB.v) === 0n)))) {
          throw new $rt.Fail({ $tag: "Mismatch" });
          return undefined;
        }
      }
      break m$7;
    }
    $rt.unmatched($6);
  }
}
function unifyLen$445(self, a, b) {
  const x = resolveLen$280(self.v, a);
  const y = resolveLen$280(self.v, b);
  if (eq$608(x, y)) {
    return;
  }
  const $1 = x;
  m$2: {
    if (($1.$tag === "Var")) {
      const v = $1.$;
      {
        const $3 = self.v.lens;
        $3[$rt.at($3, $rt.wrap_usize(v))] = { $tag: "Some", $: y };
        return;
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const $4 = y;
  m$5: {
    if (($4.$tag === "Var")) {
      const v = $4.$;
      {
        const $6 = self.v.lens;
        $6[$rt.at($6, $rt.wrap_usize(v))] = { $tag: "Some", $: x };
        return undefined;
      }
      break m$5;
    }
    if (true) {
      throw new $rt.Fail({ $tag: "Mismatch" });
      break m$5;
    }
    $rt.unmatched($4);
  }
}
function effSubOrMismatch$446(self, a, b) {
  try {
    effSub$117(self, a, b);
    return undefined;
  } catch ($1) {
    if (!($1 instanceof $rt.Fail)) throw $1;
    throw new $rt.Fail({ $tag: "Mismatch" });
    return undefined;
  }
}
function eq$447(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "None") && ($1[1].$tag === "None"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Some") && ($1[1].$tag === "Some"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$605(a, b);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function failedInstance$448(self, d, args) {
  return (($b.Option_isSome($rt.idx(self.defs, d).templateFields) && every$298($b.slice_iter(args), ((a) => {
  return concreteArg$406(a);
  }))) && (!$b.HashMap_has(self.instances, $b.String_asStr(("" + String(d) + "|" + keyArgs$159(args))))));
}
function structFields$449(self, d, args) {
  if ($b.Option_isSome($rt.idx(self.defs, d).templateFields)) {
    const $1 = $b.HashMap_get(self.instances, $b.String_asStr(("" + String(d) + "|" + keyArgs$159(args))));
    m$2: {
      if (($1.$tag === "Some")) {
        const fs = $1.$;
        return { $tag: "Some", $: clone$74(fs) };
        break m$2;
      }
      if (($1.$tag === "None")) {
        return { $tag: "None" };
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  const $3 = $rt.idx(self.defs, d).kind;
  m$4: {
    if (($3.$tag === "Struct" && ($3.$.fields.$tag === "Some"))) {
      const fs = $3.$.fields.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $5 of $rt.items(fs)) {
          const k = $5[0];
          const t = $5[1];
          $b.Vec_push(out, [$b.String_clone(k), substParams$230(t, $rt.idx(self.defs, d).params, args)]);
        }
        return { $tag: "Some", $: out.v };
      }
      break m$4;
    }
    if (true) {
      return { $tag: "None" };
      break m$4;
    }
    $rt.unmatched($3);
  }
}
function some$450(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function assocImpl$451(self, base, name) {
  const $1 = $b.slice_len(self.defs);
  for (let d = 0n; d < $1; d++) {
    const $2 = $rt.idx(self.defs, d).kind;
    m$3: {
      if (($2.$tag === "Interface")) {
        const assoc = $2.$.assoc;
        {
          if (some$450($b.slice_iter(assoc), ((a) => {
  return (a === name);
          }))) {
            const $4 = resolveImpl$287(self, d, base);
            m$5: {
              if (($4.$tag === "Some")) {
                const r = $4.$;
                {
                  return { $tag: "Some", $: r };
                }
                break m$5;
              }
              if (true) {
                {
                }
                break m$5;
              }
              $rt.unmatched($4);
            }
          }
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return { $tag: "None" };
}
function bindsKey$452(b) {
  const parts = { v: $b.Vec_new() };
  const $1 = $b.Gen_each($b.HashMap_entries(b));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const k = $4[0];
    const v = $4[1];
    $b.Vec_push(parts, [k, keyArgs$159([clone$290(v)])]);
  }
  $b.slice_sortBy(parts, ((x, y) => {
  return cmp$645($rt.idx(x, 0n), $rt.idx(y, 0n));
  }));
  const out = { v: $b.String_new() };
  for (const $5 of $rt.items(parts.v)) {
    const k = $5[0];
    const v = $5[1];
    $b.String_push(out, ("" + String(k) + "=" + v));
  }
  return out.v;
}
function bindsMap$453(b) {
  const m = { v: $b.HashMap_new() };
  const $1 = $b.Gen_each($b.HashMap_entries(b));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const k = $4[0];
    const v = $4[1];
    $b.HashMap_insert(m, k, clone$290(v));
  }
  return m.v;
}
function clone$454(self) {
  {
    const v = [clone$225($rt.idx(self, 0n)), clone$646($rt.idx(self, 1n))];
    return v;
  }
}
function clone$455(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$80(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$456(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$198(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eq$457(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Var") && ($1[1].$tag === "Var"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$266(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Param") && ($1[1].$tag === "Param"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$262(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Heap") && ($1[1].$tag === "Heap"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function defName$458(names, d) {
  if ((d < $b.slice_len(names))) {
    return $b.String_asStr($rt.idx(names, d));
  } else {
    {
      return "?";
    }
  }
}
function writeRegion$459(r, out) {
  const $1 = r;
  m$2: {
    if (($1.$tag === "Var")) {
      const v = $1.$;
      return $b.String_push(out, ("" + "'?" + String(v)));
      break m$2;
    }
    if (($1.$tag === "Param")) {
      const s = $1.$;
      return $b.String_push(out, s.name);
      break m$2;
    }
    if (($1.$tag === "Heap")) {
      return $b.String_push(out, "Heap");
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function writeList$460(ts, names, out) {
  const $1 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(ts)));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const i = $4[0];
    const t = $4[1];
    if ((i > 0n)) {
      $b.String_push(out, ", ");
    }
    writeTy$485(t, names, out);
  }
  return undefined;
}
function writeTail$461(tail, prefix, kind, out) {
  const $1 = tail;
  m$2: {
    if (($1.$tag === "Closed")) {
      {
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Var")) {
      const v = $1.$;
      return $b.String_push(out, ("" + prefix + "?" + kind + String(v)));
      break m$2;
    }
    if (($1.$tag === "Param")) {
      const s = $1.$;
      return $b.String_push(out, ("" + prefix + s.name));
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function findIndex$462(self, test) {
  let i = 0n;
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: i };
    }
    i = $rt.usize(i + 1n);
  }
  return { $tag: "None" };
}
function clone$463(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Wild")) {
      return { $tag: "Wild" };
      break m$2;
    }
    if (($1.$tag === "Bind")) {
      const x = $1.$;
      return { $tag: "Bind", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Lit")) {
      const x = $1.$;
      return { $tag: "Lit", $: clone$223(x) };
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const x = $1.$;
      return { $tag: "Tag", $: clone$647(x) };
      break m$2;
    }
    if (($1.$tag === "TagAt")) {
      const x = $1.$;
      return { $tag: "TagAt", $: clone$648(x) };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const x = $1.$;
      return { $tag: "Tuple", $: clone$649(x) };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const x = $1.$;
      return { $tag: "Record", $: clone$650(x) };
      break m$2;
    }
    if (($1.$tag === "Or")) {
      const x = $1.$;
      return { $tag: "Or", $: clone$649(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function ctors$464(self, t0) {
  const t = strip$124(self.v, t0);
  if (eq$234(t, boolTy$189())) {
    return { $tag: "Some", $: [[{ $tag: "Bool", $: false }, $b.Vec_new()], [{ $tag: "Bool", $: true }, $b.Vec_new()]] };
  }
  const $1 = tagPayloads$242(self, t);
  m$2: {
    if (($1.$tag === "Some")) {
      const tags = $1.$[0];
      const tail0 = $1.$[1];
      {
        let tail = tail0;
        const $3 = tail;
        m$4: {
          if (($3.$tag === "Var")) {
            {
              closeUnion$272(new $rt.FieldRef(self.v, "s"), t);
              tail = { $tag: "Closed" };
            }
            break m$4;
          }
          if (true) {
            {
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
        if (!eq$120(tail, { $tag: "Closed" })) {
          return { $tag: "None" };
        }
        const out = { v: $b.Vec_new() };
        for (const $5 of $rt.items(tags)) {
          const k = $5[0];
          const p = $5[1];
          $b.Vec_push(out, [{ $tag: "Tag", $: $b.String_clone(k) }, payloadFields$468(resolve$109(self.v.s, p))]);
        }
        return { $tag: "Some", $: out.v };
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const $6 = t;
  m$7: {
    if (($6.$tag === "Tuple")) {
      const ts = $6.$;
      return { $tag: "Some", $: [[{ $tag: "Tuple" }, clone$35(ts)]] };
      break m$7;
    }
    if (($6.$tag === "Array" && ($6.$[1].$tag === "Known"))) {
      const e = $6.$[0];
      const n = $6.$[1].$;
      {
        const fs = { v: $b.Vec_new() };
        const $8 = $rt.wrap_usize(n);
        for (let $9$$10 = 0n; $9$$10 < $8; $9$$10++) {
          $b.Vec_push(fs, clone$23($b.Box_get(e)));
        }
        return { $tag: "Some", $: [[{ $tag: "Tuple" }, fs.v]] };
      }
      break m$7;
    }
    if (($6.$tag === "Record")) {
      const r = $6.$;
      {
        const fs = { v: $b.Vec_new() };
        for (const $11 of $rt.items(expandRow$125(self.v.s, r).labels)) {
          const x = $11[1];
          $b.Vec_push(fs, clone$23(x));
        }
        return { $tag: "Some", $: [[{ $tag: "Record" }, fs.v]] };
      }
      break m$7;
    }
    if (($6.$tag === "Named")) {
      const d = $6.$[0];
      const args = $6.$[1];
      const $12 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, d), "kind");
      const $13 = $12.v;
      m$14: {
        if (($13.$tag === "Struct" && ($13.$.fields.$tag === "Some"))) {
          {
            ensureInstance$231(self.v.p, d, args);
            let $15;
            const $16 = structFields$449(self.v.p.v, d, args);
            m$17: {
              if (($16.$tag === "Some")) {
                const x = $16.$;
                $15 = x;
                break m$17;
              }
              if (($16.$tag === "None")) {
                $15 = $b.Vec_new();
                break m$17;
              }
              $rt.unmatched($16);
            }
            const fs = { v: $15 };
            $b.slice_sortBy(fs, ((a, b) => {
  return cmp$651($rt.idx(a, 0n), $rt.idx(b, 0n));
            }));
            const out = { v: $b.Vec_new() };
            for (const $18 of $rt.items(fs.v)) {
              const x = $18[1];
              $b.Vec_push(out, clone$23(x));
            }
            return { $tag: "Some", $: [[{ $tag: "Record" }, out.v]] };
          }
          break m$14;
        }
        if (true) {
          return { $tag: "None" };
          break m$14;
        }
        $rt.unmatched($13);
      }
      break m$7;
    }
    if (true) {
      return { $tag: "None" };
      break m$7;
    }
    $rt.unmatched($6);
  }
}
function first$465(self) {
  if (($b.slice_len(self) === 0n)) {
    return { $tag: "None" };
  } else {
    {
      return { $tag: "Some", $: $rt.idx(self, 0n) };
    }
  }
}
function recordLabels$466(self, t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Record")) {
      const r = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $3 of $rt.items(expandRow$125(self.v.s, r).labels)) {
          const k = $3[0];
          $b.Vec_push(out, $b.String_clone(k));
        }
        return out.v;
      }
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      const $4 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, d), "kind");
      const $5 = $4.v;
      m$6: {
        if (($5.$tag === "Struct" && ($5.$.fields.$tag === "Some"))) {
          {
            const ls = { v: $b.Vec_new() };
            const $7 = structFields$449(self.v.p.v, d, args);
            m$8: {
              if (($7.$tag === "Some")) {
                const fs = $7.$;
                {
                  for (const $9 of $rt.items(fs)) {
                    const k = $9[0];
                    $b.Vec_push(ls, $b.String_clone(k));
                  }
                }
                break m$8;
              }
              if (true) {
                {
                }
                break m$8;
              }
              $rt.unmatched($7);
            }
            sort$652(ls);
            return ls.v;
          }
          break m$6;
        }
        if (true) {
          return $b.Vec_new();
          break m$6;
        }
        $rt.unmatched($5);
      }
      break m$2;
    }
    if (true) {
      return $b.Vec_new();
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function find$467(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function payloadFields$468(p) {
  const $1 = p;
  m$2: {
    if (($1.$tag === "Prim" && ($1.$.$tag === "Void"))) {
      return $b.Vec_new();
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      return clone$35(ts);
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const r = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $3 of $rt.items(r.labels)) {
          const x = $3[1];
          $b.Vec_push(out, clone$23(x));
        }
        return out.v;
      }
      break m$2;
    }
    if (true) {
      const t = $1;
      return [clone$23(t)];
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$469(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Wild")) {
      return { $tag: "Wild" };
      break m$2;
    }
    if (($1.$tag === "Never")) {
      return { $tag: "Never" };
      break m$2;
    }
    if (($1.$tag === "Ctor")) {
      const x = $1.$;
      return { $tag: "Ctor", $: clone$653(x) };
      break m$2;
    }
    if (($1.$tag === "Or")) {
      const x = $1.$;
      return { $tag: "Or", $: clone$470(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$470(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$469(x));
  }
  return v.v;
}
function clone$471(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Tag")) {
      const x = $1.$;
      return { $tag: "Tag", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Bool")) {
      const x = $1.$;
      return { $tag: "Bool", $: clone$199(x) };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      return { $tag: "Tuple" };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      return { $tag: "Record" };
      break m$2;
    }
    if (($1.$tag === "Lit")) {
      return { $tag: "Lit" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function includes$472(self, x) {
  for (const $1 of $rt.items(self)) {
    const y = $1;
    if (eq$474(y, x)) {
      return true;
    }
  }
  return false;
}
function every$473(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if ((!test(x))) {
      return false;
    }
  }
  return true;
}
function eq$474(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Tag") && ($1[1].$tag === "Tag"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$6(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Bool") && ($1[1].$tag === "Bool"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$609(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Tuple") && ($1[1].$tag === "Tuple"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Record") && ($1[1].$tag === "Record"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Lit") && ($1[1].$tag === "Lit"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$475(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Wild")) {
      return { $tag: "Wild" };
      break m$2;
    }
    if (($1.$tag === "Ctor")) {
      const x = $1.$;
      return { $tag: "Ctor", $: clone$654(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function find$476(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function clone$477(self) {
  {
    const v = [clone$471($rt.idx(self, 0n)), clone$35($rt.idx(self, 1n))];
    return v;
  }
}
function every$478(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if ((!test(x))) {
      return false;
    }
  }
  return true;
}
function isKnown$479(self, d, name) {
  return eq$447(knownDef$139(self, name), { $tag: "Some", $: d });
}
function defNamed$480(self, d, names) {
  return (includes$382(names, $b.String_asStr($rt.idx(self.defs, d).name)) && $rt.idx(self.modules, $rt.idx(self.defs, d).module).isStd);
}
function hasDrop$481(self, d) {
  return some$286($b.slice_iter(self.impls), ((imp) => {
  const $1 = imp.target;
  m$2: {
    if (($1.$tag === "Named")) {
      const t = $1.$[0];
      let $3 = (t === d);
      if ($3) {
        let $4;
        const $5 = imp.iface;
        m$6: {
          if (($5.$tag === "Some")) {
            const i = $5.$[0];
            $4 = ($rt.idx(self.defs, i).name === "Drop");
            break m$6;
          }
          if (($5.$tag === "None")) {
            $4 = false;
            break m$6;
          }
          $rt.unmatched($5);
        }
        $3 = $4;
      }
      return $3;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
  }));
}
function keyTy$482(t) {
  const out = { v: $b.String_new() };
  writeKey$496(t, out);
  return out.v;
}
function insert$483(self, v) {
  if ($b.HashMap_has(self.v.map, v)) {
    return false;
  }
  $b.HashMap_insert(new $rt.FieldRef(self.v, "map"), v, true);
  return true;
}
function components$484(self, d, args) {
  const $1 = $rt.idx(self.defs, d).kind;
  m$2: {
    if (($1.$tag === "Struct" && ($1.$.fields.$tag === "Some"))) {
      const $3 = structFields$449(self, d, args);
      m$4: {
        if (($3.$tag === "Some")) {
          const fs = $3.$;
          {
            const out = { v: $b.Vec_new() };
            for (const $5 of $rt.items(fs)) {
              const t = $5[1];
              $b.Vec_push(out, clone$23(t));
            }
            return { $tag: "Some", $: out.v };
          }
          break m$4;
        }
        if (($3.$tag === "None")) {
          return { $tag: "None" };
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (($1.$tag === "Enum")) {
      const tags = $1.$.tags;
      {
        const out = { v: $b.Vec_new() };
        for (const $6 of $rt.items(tags)) {
          const t = $6[1];
          $b.Vec_push(out, substParamsOf$655(self, d, t, args));
        }
        return { $tag: "Some", $: out.v };
      }
      break m$2;
    }
    if (true) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function writeTy$485(t, names, out) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Var")) {
      const v = $1.$;
      return $b.String_push(out, ("" + "?" + String(v)));
      break m$2;
    }
    if (($1.$tag === "Param")) {
      const s = $1.$;
      return $b.String_push(out, s.name);
      break m$2;
    }
    if (($1.$tag === "Prim")) {
      const p = $1.$;
      return $b.String_push(out, primName$300(p));
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        $b.String_push(out, defName$458(names, d));
        if (($b.slice_len(args) > 0n)) {
          $b.String_push(out, "<");
          const $3 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(args)));
          let $5;
          for (let $4 = $3.next(); !$4.done; $4 = $3.next($5)) {
            $5 = undefined;
            const $6 = $4.value.item;
            const i = $6[0];
            const a = $6[1];
            if ((i > 0n)) {
              $b.String_push(out, ", ");
            }
            writeArg$656(a, names, out);
          }
          $b.String_push(out, ">");
          return undefined;
        }
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const r = $1.$;
      {
        $b.String_push(out, "{ ");
        for (const $7 of $rt.items(r.labels)) {
          const k = $7[0];
          const v = $7[1];
          $b.String_push(out, k);
          $b.String_push(out, ": ");
          writeTy$485(v, names, out);
          $b.String_push(out, "; ");
        }
        writeTail$461(r.tail, "...", "r", out);
        $b.String_push(out, "}");
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Union")) {
      const r = $1.$;
      {
        const $8 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(r.labels)));
        let $10;
        for (let $9 = $8.next(); !$9.done; $9 = $8.next($10)) {
          $10 = undefined;
          const $11 = $9.value.item;
          const i = $11[0];
          const k = $11[1][0];
          const v = $11[1][1];
          if ((i > 0n)) {
            $b.String_push(out, " | ");
          }
          $b.String_push(out, "#");
          $b.String_push(out, k);
          const $12 = v;
          m$13: {
            if (($12.$tag === "Prim" && ($12.$.$tag === "Void"))) {
              {
              }
              break m$13;
            }
            if (($12.$tag === "Tuple")) {
              const ts = $12.$;
              {
                $b.String_push(out, "(");
                writeList$460(ts, names, out);
                $b.String_push(out, ")");
              }
              break m$13;
            }
            if (true) {
              const other = $12;
              {
                $b.String_push(out, " ");
                writeTy$485(other, names, out);
              }
              break m$13;
            }
            $rt.unmatched($12);
          }
        }
        if (!eq$120(r.tail, { $tag: "Closed" })) {
          $b.String_push(out, " | ");
          writeTail$461(r.tail, "...", "r", out);
          return undefined;
        }
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        $b.String_push(out, "[");
        writeList$460(ts, names, out);
        $b.String_push(out, "]");
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const e = $1.$[0];
      const len = $1.$[1];
      {
        writeTy$485(e, names, out);
        $b.String_push(out, "[");
        const $14 = len;
        m$15: {
          if (($14.$tag === "Known")) {
            const k = $14.$;
            $b.String_push(out, ("" + String(k)));
            break m$15;
          }
          if (($14.$tag === "Var")) {
            const v = $14.$;
            $b.String_push(out, ("" + "?" + String(v)));
            break m$15;
          }
          if (($14.$tag === "Param")) {
            const s = $14.$;
            $b.String_push(out, s.name);
            break m$15;
          }
          $rt.unmatched($14);
        }
        $b.String_push(out, "]");
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Slice")) {
      const e = $1.$;
      {
        writeTy$485(e, names, out);
        $b.String_push(out, "[]");
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const e = $1.$[1];
      {
        const $16 = out;
        let $17;
        if (m) {
          $17 = "mut ";
        } else {
          {
            $17 = "readonly ";
          }
        }
        $b.String_push($16, $17);
        writeTy$485(e, names, out);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      {
        const $18 = out;
        let $19;
        const $20 = f.mode;
        m$21: {
          if (($20.$tag === "Shared")) {
            $19 = "";
            break m$21;
          }
          if (($20.$tag === "Mut")) {
            $19 = "mut ";
            break m$21;
          }
          if (($20.$tag === "Once")) {
            $19 = "once ";
            break m$21;
          }
          $rt.unmatched($20);
        }
        $b.String_push($18, $19);
        $b.String_push(out, "(");
        writeList$460(f.params, names, out);
        $b.String_push(out, ") => ");
        writeTy$485(f.ret, names, out);
        if ((($b.slice_len(f.effects.effs) > 0n) || !eq$120(f.effects.tail, { $tag: "Closed" }))) {
          $b.String_push(out, " uses ");
          writeEffs$267(f.effects, names, out);
          return undefined;
        }
      }
      break m$2;
    }
    if (($1.$tag === "Assoc")) {
      const base = $1.$[0];
      const n = $1.$[1];
      {
        writeTy$485(base, names, out);
        $b.String_push(out, ".");
        $b.String_push(out, n);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Error")) {
      return $b.String_push(out, "{error}");
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function assumedOf$486(assumed, id) {
  const $1 = $b.HashMap_get(assumed, id);
  m$2: {
    if (($1.$tag === "Some")) {
      const b = $1.$;
      return clone$35(b);
      break m$2;
    }
    if (($1.$tag === "None")) {
      return $b.Vec_new();
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function some$487(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function isStdDef$488(self, d) {
  return $rt.idx(self.modules, $rt.idx(self.defs, d).module).isStd;
}
function isSendGiven$489(self, t, sendParams) {
  const seen = { v: new$$281() };
  return ((class$$187(self, t) === 1n) && sendIn$657(self, t, sendParams, seen));
}
function lentBy$490(self, q, k) {
  let $1 = eq$234(q, k);
  if (!$1) {
    let $2;
    const $3 = q;
    m$4: {
      if ((($3.$tag === "Var") || ($3.$tag === "Param") || ($3.$tag === "Error"))) {
        $2 = true;
        break m$4;
      }
      if (true) {
        $2 = false;
        break m$4;
      }
      $rt.unmatched($3);
    }
    $1 = $2;
  }
  let $5 = $1;
  if (!$5) {
    let $6;
    const $7 = k;
    m$8: {
      if ((($7.$tag === "Var") || ($7.$tag === "Param"))) {
        $6 = true;
        break m$8;
      }
      if (true) {
        $6 = false;
        break m$8;
      }
      $rt.unmatched($7);
    }
    $5 = $6;
  }
  if ($5) {
    return true;
  }
  const $9 = [q, k];
  m$10: {
    if ((($9[1].$tag === "Named"))) {
      const d = $9[1].$[0];
      const args = $9[1].$[1];
      if (((isKnown$479(self, d, "Ref") || isKnown$479(self, d, "Box")) || isKnown$479(self, d, "Arc"))) {
        {
          const $11 = last$256(args);
          m$12: {
            if (($11.$tag === "Some" && ($11.$.$tag === "Ty"))) {
              const t = $11.$.$;
              return lentBy$490(self, q, t);
              break m$12;
            }
            if (true) {
              return false;
              break m$12;
            }
            $rt.unmatched($11);
          }
        }
        break m$10;
      }
    }
    if ((($9[0].$tag === "Prim" && ($9[0].$.$tag === "Str")) && ($9[1].$tag === "Named"))) {
      const d = $9[1].$[0];
      return isKnown$479(self, d, "String");
      break m$10;
    }
    if ((($9[0].$tag === "Slice") && ($9[1].$tag === "Named"))) {
      const e = $9[0].$;
      const d = $9[1].$[0];
      const args = $9[1].$[1];
      let $13 = isKnown$479(self, d, "Vec");
      if ($13) {
        let $14;
        const $15 = first$258(args);
        m$16: {
          if (($15.$tag === "Some" && ($15.$.$tag === "Ty"))) {
            const t = $15.$.$;
            $14 = eq$234(t, $b.Box_get(e));
            break m$16;
          }
          if (true) {
            $14 = false;
            break m$16;
          }
          $rt.unmatched($15);
        }
        $13 = $14;
      }
      return $13;
      break m$10;
    }
    if (true) {
      return false;
      break m$10;
    }
    $rt.unmatched($9);
  }
}
function resolveDepth$491(self, iface, ty0, depth) {
  if ((depth > 16n)) {
    return { $tag: "None" };
  }
  const ty = stripBorrows$295(ty0);
  const candidates = { v: $b.Vec_new() };
  const $1 = $b.slice_len(self.impls);
  for (let i = 0n; i < $1; i++) {
    if ((!isBlanket$658(self, i))) {
      $b.Vec_push(candidates, i);
    }
  }
  const $2 = $b.slice_len(self.impls);
  for (let i = 0n; i < $2; i++) {
    if (isBlanket$658(self, i)) {
      $b.Vec_push(candidates, i);
    }
  }
  for (const $3 of $rt.items(candidates.v)) {
    const i = $3;
    let $4;
    const $5 = $rt.idx(self.impls, i).iface;
    m$6: {
      if (($5.$tag === "Some")) {
        const d = $5.$[0];
        $4 = (d === iface);
        break m$6;
      }
      if (($5.$tag === "None")) {
        $4 = false;
        break m$6;
      }
      $rt.unmatched($5);
    }
    const forIface = $4;
    if (($rt.idx(self.impls, i).derived || (!forIface))) {
      continue;
    }
    if ((isBlanket$658(self, i) && (!derives$659(self, iface, ty)))) {
      continue;
    }
    const vars = { v: $b.Vec_new() };
    for (const $7 of $rt.items($rt.idx(self.impls, i).params)) {
      const g = $7;
      $b.Vec_push(vars, g.sym.id);
    }
    const binds = { v: $b.HashMap_new() };
    if ((!matchTy$660($rt.idx(self.impls, i).target, ty, vars.v, binds))) {
      continue;
    }
    const args = { v: $b.Vec_new() };
    for (const $8 of $rt.items($rt.idx(self.impls, i).params)) {
      const g = $8;
      const $9 = args;
      let $10;
      const $11 = $b.HashMap_get(binds.v, g.sym.id);
      m$12: {
        if (($11.$tag === "Some")) {
          const a = $11.$;
          $10 = clone$290(a);
          break m$12;
        }
        if (($11.$tag === "None")) {
          $10 = paramArg$291(g);
          break m$12;
        }
        $rt.unmatched($11);
      }
      $b.Vec_push($9, $10);
    }
    let ok = true;
    const $13 = $b.slice_len($rt.idx(self.impls, i).params);
    for (let k = 0n; k < $13; k++) {
      const $14 = $rt.idx(args.v, k);
      m$15: {
        if (($14.$tag === "Ty")) {
          const t = $14.$;
          {
            for (const $16 of $rt.items($rt.idx($rt.idx(self.impls, i).params, k).bounds)) {
              const b = $16;
              const bound = substParams$230(b, $rt.idx(self.impls, i).params, args.v);
              if ((!satisfiesDepth$285(self, t, bound, $b.HashMap_new(), $rt.usize(depth + 1n)))) {
                ok = false;
              }
            }
          }
          break m$15;
        }
        if (true) {
          {
          }
          break m$15;
        }
        $rt.unmatched($14);
      }
    }
    const supers = ifaceClosure$142(self, iface);
    let supersOk = true;
    const $17 = $b.slice_len(supers);
    for (let k = 1n; k < $17; k++) {
      if ((!satisfiesDepth$285(self, ty, { $tag: "Named", $: [$rt.idx(supers, k), $b.Vec_new()] }, $b.HashMap_new(), $rt.usize(depth + 1n)))) {
        supersOk = false;
      }
    }
    if ((ok && supersOk)) {
      return { $tag: "Some", $: [i, binds.v] };
    } else {
      {
        return { $tag: "None" };
      }
    }
  }
  return { $tag: "None" };
}
function implMethod$492(self, imp, name) {
  for (const $1 of $rt.items($rt.idx(self.impls, imp).methods)) {
    const f = $1;
    if (($rt.idx(self.fns, f).name === name)) {
      return { $tag: "Some", $: f };
    }
  }
  return { $tag: "None" };
}
function specKey$493(ct) {
  const out = { v: $b.String_new() };
  for (const $1 of $rt.items(ct)) {
    const t = $1[1];
    $b.String_push(out, keyTy$482(eraseRegions$661(t)));
    $b.String_push(out, ";");
  }
  return out.v;
}
function argTypes$494(args) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(args)) {
    const a = $1;
    const $2 = a;
    m$3: {
      if (($2.$tag === "Ty")) {
        const t = $2.$;
        {
          $b.Vec_push(out, clone$23(t));
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return out.v;
}
function eraseRow$495(r, p, tasks) {
  const labels = { v: $b.Vec_new() };
  for (const $1 of $rt.items(r.labels)) {
    const k = $1[0];
    const x = $1[1];
    $b.Vec_push(labels, [$b.String_clone(k), eraseTy$301(x, p, tasks)]);
  }
  return { labels: labels.v, tail: clone$99(r.tail) };
}
function writeKey$496(t, out) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Var")) {
      const v = $1.$;
      return $b.String_push(out, ("" + "?" + String(v)));
      break m$2;
    }
    if (($1.$tag === "Param")) {
      const s = $1.$;
      return $b.String_push(out, ("" + "'" + String(s.id)));
      break m$2;
    }
    if (($1.$tag === "Prim")) {
      const p = $1.$;
      return $b.String_push(out, primName$300(p));
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        $b.String_push(out, ("" + "N" + String(d) + "<"));
        for (const $3 of $rt.items(args)) {
          const a = $3;
          writeKeyArg$303(a, out);
          $b.String_push(out, ",");
        }
        $b.String_push(out, ">");
        return undefined;
      }
      break m$2;
    }
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      {
        const $4 = out;
        let $5;
        let $6;
        const $7 = t;
        m$8: {
          if (($7.$tag === "Record")) {
            $6 = true;
            break m$8;
          }
          if (true) {
            $6 = false;
            break m$8;
          }
          $rt.unmatched($7);
        }
        if ($6) {
          $5 = "R(";
        } else {
          {
            $5 = "U(";
          }
        }
        $b.String_push($4, $5);
        for (const $9 of $rt.items(r.labels)) {
          const k = $9[0];
          const v = $9[1];
          $b.String_push(out, k);
          $b.String_push(out, ":");
          writeKey$496(v, out);
          $b.String_push(out, ",");
        }
        writeKeyTail$662(r.tail, out);
        $b.String_push(out, ")");
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        $b.String_push(out, "[");
        for (const $10 of $rt.items(ts)) {
          const x = $10;
          writeKey$496(x, out);
          $b.String_push(out, ",");
        }
        $b.String_push(out, "]");
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const e = $1.$[0];
      const len = $1.$[1];
      {
        writeKey$496(e, out);
        const $11 = len;
        m$12: {
          if (($11.$tag === "Known")) {
            const k = $11.$;
            return $b.String_push(out, ("" + "[" + String(k) + "]"));
            break m$12;
          }
          if (($11.$tag === "Var")) {
            const v = $11.$;
            return $b.String_push(out, ("" + "[?" + String(v) + "]"));
            break m$12;
          }
          if (($11.$tag === "Param")) {
            const s = $11.$;
            return $b.String_push(out, ("" + "['" + String(s.id) + "]"));
            break m$12;
          }
          $rt.unmatched($11);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Slice")) {
      const e = $1.$;
      {
        writeKey$496(e, out);
        $b.String_push(out, "[]");
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const e = $1.$[1];
      {
        const $13 = out;
        let $14;
        if (m) {
          $14 = "&mut ";
        } else {
          {
            $14 = "&";
          }
        }
        $b.String_push($13, $14);
        writeKey$496(e, out);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      {
        $b.String_push(out, "fn(");
        for (const $15 of $rt.items(f.params)) {
          const p = $15;
          writeKey$496(p, out);
          $b.String_push(out, ",");
        }
        $b.String_push(out, ")");
        writeKey$496(f.ret, out);
        writeKeyEffs$498(f.effects, out);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Assoc")) {
      const base = $1.$[0];
      const n = $1.$[1];
      {
        writeKey$496(base, out);
        $b.String_push(out, ".");
        $b.String_push(out, n);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Error")) {
      return $b.String_push(out, "!");
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function writeKeyRegion$497(r, out) {
  const $1 = r;
  m$2: {
    if (($1.$tag === "Var")) {
      const v = $1.$;
      return $b.String_push(out, ("" + "v" + String(v)));
      break m$2;
    }
    if (($1.$tag === "Param")) {
      const s = $1.$;
      return $b.String_push(out, ("" + "p" + String(s.id)));
      break m$2;
    }
    if (($1.$tag === "Heap")) {
      return $b.String_push(out, "H");
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function writeKeyEffs$498(r, out) {
  $b.String_push(out, "{");
  for (const $1 of $rt.items(r.effs)) {
    const e = $1;
    $b.String_push(out, ("" + String(e.def) + "<"));
    for (const $2 of $rt.items(e.regions)) {
      const g = $2;
      writeKeyRegion$497(g, out);
      $b.String_push(out, ",");
    }
    for (const $3 of $rt.items(e.args)) {
      const t = $3;
      writeKey$496(t, out);
      $b.String_push(out, ",");
    }
    $b.String_push(out, ">");
  }
  writeKeyTail$662(r.tail, out);
  $b.String_push(out, "}");
  return undefined;
}
function substRegion$499(r, map) {
  const $1 = r;
  m$2: {
    if (($1.$tag === "Param")) {
      const s = $1.$;
      const $3 = $b.HashMap_get(map, s.id);
      m$4: {
        if (($3.$tag === "Some" && ($3.$.$tag === "Region"))) {
          const x = $3.$.$;
          return clone$360(x);
          break m$4;
        }
        if (true) {
          return clone$360(r);
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (true) {
      return clone$360(r);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function some$500(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return true;
    }
  }
  return false;
}
function substArg$501(a, map) {
  const $1 = a;
  m$2: {
    if (($1.$tag === "Ty")) {
      const t = $1.$;
      return { $tag: "Ty", $: subst$308(t, map) };
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const r = $1.$;
      return { $tag: "Region", $: substRegion$499(r, map) };
      break m$2;
    }
    if (($1.$tag === "Row")) {
      const r = $1.$;
      return { $tag: "Row", $: substEffs$305(r, map) };
      break m$2;
    }
    if (($1.$tag === "Len")) {
      const l = $1.$;
      return { $tag: "Len", $: substLen$503(l, map) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function substRow$502(r, map) {
  const labels = { v: $b.Vec_new() };
  for (const $1 of $rt.items(r.labels)) {
    const k = $1[0];
    const t = $1[1];
    $b.Vec_push(labels, [$b.String_clone(k), subst$308(t, map)]);
  }
  return { labels: labels.v, tail: clone$99(r.tail) };
}
function substLen$503(l, map) {
  const $1 = l;
  m$2: {
    if (($1.$tag === "Param")) {
      const s = $1.$;
      const $3 = $b.HashMap_get(map, s.id);
      m$4: {
        if (($3.$tag === "Some" && ($3.$.$tag === "Len"))) {
          const x = $3.$.$;
          return clone$198(x);
          break m$4;
        }
        if (true) {
          return clone$198(l);
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (true) {
      return clone$198(l);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function cellsExpr$504(self, e, scopes) {
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "BorrowMut")) {
      const x = $1.$;
      {
        lentExpr$663(self, x, scopes.v);
        cellsExpr$504(self, x, scopes);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Call")) {
      const callee = $1.$.callee;
      const args = $1.$.args;
      {
        let $3;
        const $4 = $b.HashMap_get(self.v.p.typed, self.v.fid);
        m$5: {
          if (($4.$tag === "Some")) {
            const t = $4.$;
            const $6 = $b.HashMap_get(t.calls, e.id);
            m$7: {
              if (($6.$tag === "Some")) {
                const f = $6.$;
                $3 = { $tag: "Some", $: f };
                break m$7;
              }
              if (($6.$tag === "None")) {
                $3 = { $tag: "None" };
                break m$7;
              }
              $rt.unmatched($6);
            }
            break m$5;
          }
          if (($4.$tag === "None")) {
            $3 = { $tag: "None" };
            break m$5;
          }
          $rt.unmatched($4);
        }
        const fid = $3;
        const $8 = fid;
        m$9: {
          if (($8.$tag === "Some")) {
            const f = $8.$;
            {
              let $10;
              const $11 = first$664($rt.idx(self.v.p.fns, f).scheme.params);
              m$12: {
                if (($11.$tag === "Some")) {
                  const n = $11.$[0];
                  const t = $11.$[1];
                  $10 = ((n === "self") && isMutBorrow$508(t));
                  break m$12;
                }
                if (($11.$tag === "None")) {
                  $10 = false;
                  break m$12;
                }
                $rt.unmatched($11);
              }
              const recvMut = $10;
              if (recvMut) {
                const $13 = callee.kind;
                m$14: {
                  if (($13.$tag === "Field")) {
                    const target = $13.$.target;
                    {
                      lentExpr$663(self, target, scopes.v);
                    }
                    break m$14;
                  }
                  if (true) {
                    {
                    }
                    break m$14;
                  }
                  $rt.unmatched($13);
                }
              }
            }
            break m$9;
          }
          if (true) {
            {
            }
            break m$9;
          }
          $rt.unmatched($8);
        }
        cellsExpr$504(self, callee, scopes);
        for (const $15 of $rt.items(args)) {
          const a = $15;
          cellsExpr$504(self, a, scopes);
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const scrutinee = $1.$.scrutinee;
      const arms = $1.$.arms;
      {
        let $16;
        const $17 = $b.HashMap_get(self.v.p.typed, self.v.fid);
        m$18: {
          if (($17.$tag === "Some")) {
            const t = $17.$;
            $16 = eq$665($b.HashMap_get(t.lentScrutinees, scrutinee.id), { $tag: "Some", $: true });
            break m$18;
          }
          if (($17.$tag === "None")) {
            $16 = false;
            break m$18;
          }
          $rt.unmatched($17);
        }
        const lentMut = $16;
        if (lentMut) {
          lentExpr$663(self, scrutinee, scopes.v);
        }
        cellsExpr$504(self, scrutinee, scopes);
        for (const $19 of $rt.items(arms)) {
          const arm = $19;
          const sc = { v: $b.HashMap_new() };
          bindIds$505(arm.pat, sc);
          $b.Vec_push(scopes, sc.v);
          const $20 = arm.guard;
          m$21: {
            if (($20.$tag === "Some")) {
              const g = $20.$;
              {
                cellsExpr$504(self, g, scopes);
              }
              break m$21;
            }
            if (true) {
              {
              }
              break m$21;
            }
            $rt.unmatched($20);
          }
          cellsExpr$504(self, arm.body, scopes);
          $b.Vec_pop(scopes);
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "For")) {
      const pat = $1.$.pat;
      const iter = $1.$.iter;
      const body = $1.$.body;
      {
        cellsExpr$504(self, iter, scopes);
        const sc = { v: $b.HashMap_new() };
        bindIds$505(pat, sc);
        $b.Vec_push(scopes, sc.v);
        cellsBlock$310(self, body, scopes);
        $b.Vec_pop(scopes);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Try")) {
      const body = $1.$.body;
      const pat = $1.$.pat;
      const handler = $1.$.handler;
      {
        cellsBlock$310(self, body, scopes);
        const sc = { v: $b.HashMap_new() };
        bindIds$505(pat, sc);
        $b.Vec_push(scopes, sc.v);
        cellsBlock$310(self, handler, scopes);
        $b.Vec_pop(scopes);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Lambda")) {
      const params = $1.$.params;
      const body = $1.$.body;
      {
        const sc = { v: $b.HashMap_new() };
        for (const $22 of $rt.items(params)) {
          const p = $22;
          $b.HashMap_insert(sc, $b.String_clone(p.name.name), [true, p.name.span.start]);
        }
        $b.Vec_push(scopes, sc.v);
        cellsExpr$504(self, body, scopes);
        $b.Vec_pop(scopes);
        return undefined;
      }
      break m$2;
    }
    if ((($1.$tag === "Block") || ($1.$tag === "Unsafe"))) {
      let b;
      if (($1.$tag === "Block")) { b = $1.$; }
      else if (($1.$tag === "Unsafe")) { b = $1.$; }
      return cellsBlock$310(self, b, scopes);
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const body = $1.$.body;
      return cellsBlock$310(self, body, scopes);
      break m$2;
    }
    if (($1.$tag === "If")) {
      const cond = $1.$.cond;
      const then = $1.$.then;
      const otherwise = $1.$.otherwise;
      {
        cellsExpr$504(self, cond, scopes);
        cellsBlock$310(self, then, scopes);
        const $23 = otherwise;
        m$24: {
          if (($23.$tag === "Some")) {
            const o = $23.$;
            {
              cellsExpr$504(self, o, scopes);
              return undefined;
            }
            break m$24;
          }
          if (true) {
            {
              return undefined;
            }
            break m$24;
          }
          $rt.unmatched($23);
        }
      }
      break m$2;
    }
    if (($1.$tag === "While")) {
      const cond = $1.$.cond;
      const body = $1.$.body;
      {
        cellsExpr$504(self, cond, scopes);
        cellsBlock$310(self, body, scopes);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Handle")) {
      const body = $1.$.body;
      const arms = $1.$.arms;
      {
        cellsBlock$310(self, body, scopes);
        for (const $25 of $rt.items(arms)) {
          const a = $25;
          const sc = { v: $b.HashMap_new() };
          for (const $26 of $rt.items(a.params)) {
            const p = $26;
            $b.HashMap_insert(sc, $b.String_clone(p.name), [true, p.span.start]);
          }
          $b.Vec_push(scopes, sc.v);
          cellsBlock$310(self, a.body, scopes);
          $b.Vec_pop(scopes);
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Template")) {
      const parts = $1.$;
      {
        for (const $27 of $rt.items(parts)) {
          const p = $27;
          const $28 = p;
          m$29: {
            if (($28.$tag === "Expr")) {
              const x = $28.$;
              {
                cellsExpr$504(self, x, scopes);
              }
              break m$29;
            }
            if (true) {
              {
              }
              break m$29;
            }
            $rt.unmatched($28);
          }
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      return cellsExpr$504(self, target, scopes);
      break m$2;
    }
    if (($1.$tag === "Index")) {
      const target = $1.$.target;
      const index = $1.$.index;
      {
        cellsExpr$504(self, target, scopes);
        cellsExpr$504(self, index, scopes);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Unary")) {
      const operand = $1.$.operand;
      return cellsExpr$504(self, operand, scopes);
      break m$2;
    }
    if (($1.$tag === "Binary")) {
      const lhs = $1.$.lhs;
      const rhs = $1.$.rhs;
      {
        cellsExpr$504(self, lhs, scopes);
        cellsExpr$504(self, rhs, scopes);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Assign")) {
      const target = $1.$.target;
      const value = $1.$.value;
      {
        cellsExpr$504(self, target, scopes);
        cellsExpr$504(self, value, scopes);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Cast")) {
      const expr = $1.$.expr;
      return cellsExpr$504(self, expr, scopes);
      break m$2;
    }
    if (($1.$tag === "Range")) {
      const lo = $1.$.lo;
      const hi = $1.$.hi;
      {
        const $30 = lo;
        m$31: {
          if (($30.$tag === "Some")) {
            const x = $30.$;
            {
              cellsExpr$504(self, x, scopes);
            }
            break m$31;
          }
          if (true) {
            {
            }
            break m$31;
          }
          $rt.unmatched($30);
        }
        const $32 = hi;
        m$33: {
          if (($32.$tag === "Some")) {
            const x = $32.$;
            {
              cellsExpr$504(self, x, scopes);
              return undefined;
            }
            break m$33;
          }
          if (true) {
            {
              return undefined;
            }
            break m$33;
          }
          $rt.unmatched($32);
        }
      }
      break m$2;
    }
    if (($1.$tag === "List")) {
      const items = $1.$;
      {
        for (const $34 of $rt.items(items)) {
          const x = $34;
          cellsExpr$504(self, x, scopes);
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const args = $1.$.args;
      const $35 = args;
      m$36: {
        if (($35.$tag === "None")) {
          {
            return undefined;
          }
          break m$36;
        }
        if (($35.$tag === "Tuple")) {
          const es = $35.$;
          {
            for (const $37 of $rt.items(es)) {
              const x = $37;
              cellsExpr$504(self, x, scopes);
            }
            return undefined;
          }
          break m$36;
        }
        if (($35.$tag === "Record")) {
          const fs = $35.$;
          {
            for (const $38 of $rt.items(fs)) {
              const f = $38;
              const $39 = f.value;
              m$40: {
                if (($39.$tag === "Some")) {
                  const v = $39.$;
                  {
                    cellsExpr$504(self, v, scopes);
                  }
                  break m$40;
                }
                if (true) {
                  {
                  }
                  break m$40;
                }
                $rt.unmatched($39);
              }
            }
            return undefined;
          }
          break m$36;
        }
        $rt.unmatched($35);
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      {
        for (const $41 of $rt.items(fields)) {
          const f = $41;
          const $42 = f.value;
          m$43: {
            if (($42.$tag === "Some")) {
              const v = $42.$;
              {
                cellsExpr$504(self, v, scopes);
              }
              break m$43;
            }
            if (true) {
              {
              }
              break m$43;
            }
            $rt.unmatched($42);
          }
        }
        return undefined;
      }
      break m$2;
    }
    if ((($1.$tag === "Throw") || ($1.$tag === "Yield") || ($1.$tag === "Comptime"))) {
      let x;
      if (($1.$tag === "Throw")) { x = $1.$; }
      else if (($1.$tag === "Yield")) { x = $1.$; }
      else if (($1.$tag === "Comptime")) { x = $1.$; }
      return cellsExpr$504(self, x, scopes);
      break m$2;
    }
    if (($1.$tag === "Return")) {
      const v = $1.$;
      {
        const $44 = v;
        m$45: {
          if (($44.$tag === "Some")) {
            const x = $44.$;
            {
              cellsExpr$504(self, x, scopes);
              return undefined;
            }
            break m$45;
          }
          if (true) {
            {
              return undefined;
            }
            break m$45;
          }
          $rt.unmatched($44);
        }
      }
      break m$2;
    }
    if (true) {
      {
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function bindIds$505(p, scope) {
  const ps = { v: $b.Vec_new() };
  paths$515(p, $b.Vec_new(), ps);
  for (const $1 of $rt.items(ps.v)) {
    const n = $1[0];
    const id = $1[1];
    $b.HashMap_insert(scope, $b.String_clone(n), [false, id]);
  }
  return undefined;
}
function clone$506(self) {
  {
    return { cell: clone$199(self.cell), js: $b.String_clone(self.js) };
  }
}
function ex$507(self, e) {
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "Int")) {
      const n = $1.$;
      if (floatTy$511(exprTy$316(self.v, e.id))) {
        return $b.String_clone(n);
      } else {
        {
          return ("" + n + "n");
        }
      }
      break m$2;
    }
    if (($1.$tag === "Float")) {
      const n = $1.$;
      return $b.String_clone(n);
      break m$2;
    }
    if (($1.$tag === "Str")) {
      const s = $1.$;
      return quote$512(s);
      break m$2;
    }
    if (($1.$tag === "Byte")) {
      const b = $1.$;
      return ("" + String(b) + "n");
      break m$2;
    }
    if (($1.$tag === "Bool")) {
      const b = $1.$;
      if (b) {
        return $b.str_toString("true");
      } else {
        {
          return $b.str_toString("false");
        }
      }
      break m$2;
    }
    if (($1.$tag === "Template")) {
      const parts = $1.$;
      {
        const out = { v: $b.str_toString("(\"\"") };
        for (const $3 of $rt.items(parts)) {
          const p = $3;
          const $4 = p;
          m$5: {
            if (($4.$tag === "Lit")) {
              const s = $4.$;
              {
                if (($b.String_len(s) > 0n)) {
                  $b.String_push(out, " + ");
                  $b.String_push(out, $b.String_asStr(quote$512(s)));
                }
              }
              break m$5;
            }
            if (($4.$tag === "Expr")) {
              const x = $4.$;
              {
                const v = shown$666(self, x);
                $b.String_push(out, ("" + " + " + v));
              }
              break m$5;
            }
            $rt.unmatched($4);
          }
        }
        $b.String_push(out, ")");
        return out.v;
      }
      break m$2;
    }
    if (($1.$tag === "Ident")) {
      const n = $1.$;
      return ident$667(self, n, e);
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      const name = $1.$.name;
      {
        const t = obj$668(self, target);
        return ("" + t + "." + mangleField$669($b.String_asStr(name.name)));
      }
      break m$2;
    }
    if (($1.$tag === "Index")) {
      const target = $1.$.target;
      const index = $1.$.index;
      const $6 = index.kind;
      m$7: {
        if (($6.$tag === "Range")) {
          const lo = $6.$.lo;
          const hi = $6.$.hi;
          {
            const t = obj$668(self, target);
            let $8;
            if ((simpleOpt$670(lo) && simpleOpt$670(hi))) {
              $8 = t;
            } else {
              {
                $8 = save$319(self, t);
              }
            }
            const st = $8;
            let $9;
            const $10 = lo;
            m$11: {
              if (($10.$tag === "Some")) {
                const x = $10.$;
                $9 = value$313(self, x);
                break m$11;
              }
              if (($10.$tag === "None")) {
                $9 = $b.str_toString("0n");
                break m$11;
              }
              $rt.unmatched($10);
            }
            const l = $9;
            let $12;
            const $13 = hi;
            m$14: {
              if (($13.$tag === "Some")) {
                const x = $13.$;
                $12 = value$313(self, x);
                break m$14;
              }
              if (($13.$tag === "None")) {
                $12 = $b.str_toString("undefined");
                break m$14;
              }
              $rt.unmatched($13);
            }
            const h = $12;
            return ("" + "$rt.slice(" + st + ", " + l + ", " + h + ")");
          }
          break m$7;
        }
        if (true) {
          {
            const a = obj$668(self, target);
            let $15;
            if (simple$522(index)) {
              $15 = a;
            } else {
              {
                $15 = save$319(self, a);
              }
            }
            const sa = $15;
            const i = value$313(self, index);
            return ("" + "$rt.idx(" + sa + ", " + i + ")");
          }
          break m$7;
        }
        $rt.unmatched($6);
      }
      break m$2;
    }
    if (($1.$tag === "Call")) {
      const callee = $1.$.callee;
      const args = $1.$.args;
      return call$671(self, e, callee, args, false);
      break m$2;
    }
    if (($1.$tag === "Unary")) {
      const op = $1.$.op;
      const operand = $1.$.operand;
      {
        const v = value$313(self, operand);
        if ((op === "-")) {
          const $16 = intPrim$171(exprTy$316(self.v, e.id));
          m$17: {
            if (($16.$tag === "Some")) {
              const p = $16.$;
              return ("" + "$rt." + primName$300(p) + "(-" + v + ")");
              break m$17;
            }
            if (($16.$tag === "None")) {
              return ("" + "(-" + v + ")");
              break m$17;
            }
            $rt.unmatched($16);
          }
        } else {
          {
            return ("" + "(" + op + v + ")");
          }
        }
      }
      break m$2;
    }
    if (($1.$tag === "Binary")) {
      const op = $1.$.op;
      const lhs = $1.$.lhs;
      const rhs = $1.$.rhs;
      return binary$672(self, e, op, lhs, rhs);
      break m$2;
    }
    if (($1.$tag === "Assign")) {
      const op = $1.$.op;
      const target = $1.$.target;
      const value = $1.$.value;
      {
        assign$673(self, op, target, value);
        return $b.str_toString("undefined");
      }
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const name = $1.$.name;
      const args = $1.$.args;
      return tag$674(self, e, name, args);
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      return record$675(self, e, fields);
      break m$2;
    }
    if (($1.$tag === "List")) {
      const items = $1.$;
      {
        const vs = items$676(self, items);
        return ("" + "[" + join$53(vs, ", ") + "]");
      }
      break m$2;
    }
    if (($1.$tag === "Lambda")) {
      const params = $1.$.params;
      const body = $1.$.body;
      return lambda$677(self, e, params, body);
      break m$2;
    }
    if (($1.$tag === "Range")) {
      return fail$514(self.v, $rt.copy(e.span), "a range can only index or be iterated");
      break m$2;
    }
    if (($1.$tag === "Yield")) {
      const x = $1.$;
      {
        const v = value$313(self, x);
        return ("" + "(yield $rt.yielded(" + v + "))");
      }
      break m$2;
    }
    if (($1.$tag === "Cast")) {
      const expr = $1.$.expr;
      {
        const v = value$313(self, expr);
        const to = exprTy$316(self.v, e.id);
        const from = exprTy$316(self.v, expr.id);
        return cast$678(self.v, v, from, to);
      }
      break m$2;
    }
    if (($1.$tag === "Comptime")) {
      const x = $1.$;
      return ex$507(self, x);
      break m$2;
    }
    if (($1.$tag === "BorrowMut")) {
      const x = $1.$;
      return lend$509(self, x);
      break m$2;
    }
    if ((($1.$tag === "Return") || ($1.$tag === "Break") || ($1.$tag === "Continue") || ($1.$tag === "Throw"))) {
      {
        into$322(self, e, { $tag: "Discard" });
        return $b.str_toString("undefined");
      }
      break m$2;
    }
    if (($1.$tag === "Block")) {
      const b = $1.$;
      if ((($b.slice_len(b.stmts) === 0n) && simpleOpt$670(b.tail))) {
        const $18 = b.tail;
        m$19: {
          if (($18.$tag === "Some")) {
            const t = $18.$;
            return ex$507(self, t);
            break m$19;
          }
          if (($18.$tag === "None")) {
            return $b.str_toString("undefined");
            break m$19;
          }
          $rt.unmatched($18);
        }
        break m$2;
      }
    }
    if (($1.$tag === "Handle")) {
      const body = $1.$.body;
      const arms = $1.$.arms;
      return handle$679(self, e, body, arms);
      break m$2;
    }
    if (($1.$tag === "TagAt")) {
      return fail$514(self.v, $rt.copy(e.span), "a tag named by `comptime` code at run time");
      break m$2;
    }
    if (($1.$tag === "TypeRef")) {
      return fail$514(self.v, $rt.copy(e.span), "a type used as a value");
      break m$2;
    }
    if (($1.$tag === "FieldAt")) {
      return fail$514(self.v, $rt.copy(e.span), "a field named by `comptime` code at run time");
      break m$2;
    }
    if (true) {
      {
        const t = fresh$167(self);
        line$168(self, ("" + "let " + t + ";"));
        into$322(self, e, { $tag: "Assign", $: $b.String_clone(t) });
        return t;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function isMutBorrow$508(t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Borrow" && $1.$[0] === true)) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function lend$509(self, e) {
  let $1;
  const $2 = e.kind;
  m$3: {
    if ((($2.$tag === "Field") || ($2.$tag === "Index"))) {
      $1 = isMutBorrow$508(exprTy$316(self.v, e.id));
      break m$3;
    }
    if (true) {
      $1 = false;
      break m$3;
    }
    $rt.unmatched($2);
  }
  if ($1) {
    return ex$507(self, e);
  }
  const $4 = e.kind;
  m$5: {
    if (($4.$tag === "BorrowMut")) {
      const inner = $4.$;
      return lend$509(self, inner);
      break m$5;
    }
    if (($4.$tag === "Ident")) {
      const n = $4.$;
      {
        const $6 = local$311(self.v, $b.String_asStr(n));
        m$7: {
          if (($6.$tag === "Some")) {
            const l = $6.$;
            {
              if ((l.cell || isMutBorrow$508(exprTy$316(self.v, e.id)))) {
                return l.js;
              }
              return ("" + "{ v: " + l.js + " }");
            }
            break m$7;
          }
          if (true) {
            {
            }
            break m$7;
          }
          $rt.unmatched($6);
        }
        const v = ex$507(self, e);
        return ("" + "{ v: " + v + " }");
      }
      break m$5;
    }
    if (($4.$tag === "Field")) {
      const target = $4.$.target;
      const name = $4.$.name;
      {
        const o = obj$668(self, target);
        return ("" + "new $rt.FieldRef(" + o + ", " + quote$512(name.name) + ")");
      }
      break m$5;
    }
    if (($4.$tag === "Index")) {
      const target = $4.$.target;
      const index = $4.$.index;
      {
        const $8 = index.kind;
        m$9: {
          if (($8.$tag === "Range")) {
            const lo = $8.$.lo;
            const hi = $8.$.hi;
            {
              const a = obj$668(self, target);
              let $10;
              if ((simpleOpt$670(lo) && simpleOpt$670(hi))) {
                $10 = a;
              } else {
                {
                  $10 = save$319(self, a);
                }
              }
              const sa = $10;
              let $11;
              const $12 = lo;
              m$13: {
                if (($12.$tag === "Some")) {
                  const x = $12.$;
                  $11 = value$313(self, x);
                  break m$13;
                }
                if (($12.$tag === "None")) {
                  $11 = $b.str_toString("0n");
                  break m$13;
                }
                $rt.unmatched($12);
              }
              const l = $11;
              let $14;
              const $15 = hi;
              m$16: {
                if (($15.$tag === "Some")) {
                  const x = $15.$;
                  $14 = value$313(self, x);
                  break m$16;
                }
                if (($15.$tag === "None")) {
                  $14 = $b.str_toString("undefined");
                  break m$16;
                }
                $rt.unmatched($15);
              }
              const h = $14;
              return ("" + "$rt.rangeRef(" + sa + ", " + l + ", " + h + ")");
            }
            break m$9;
          }
          if (true) {
            {
            }
            break m$9;
          }
          $rt.unmatched($8);
        }
        const a = obj$668(self, target);
        let $17;
        if (simple$522(index)) {
          $17 = a;
        } else {
          {
            $17 = save$319(self, a);
          }
        }
        const sa = $17;
        const i = value$313(self, index);
        return ("" + "$rt.indexRef(" + sa + ", " + i + ")");
      }
      break m$5;
    }
    if (true) {
      {
        const v = ex$507(self, e);
        if (isMutBorrow$508(exprTy$316(self.v, e.id))) {
          return v;
        } else {
          {
            return ("" + "{ v: " + v + " }");
          }
        }
      }
      break m$5;
    }
    $rt.unmatched($4);
  }
}
function coerce$510(self, v, e, want) {
  const have = exprTy$316(self, e.id);
  if ((isMutBorrow$508(have) && (!isMutBorrow$508(want)))) {
    const inner = stripBorrow$317(have);
    let $1;
    const $2 = want;
    m$3: {
      if (($2.$tag === "Borrow" && $2.$[0] === false)) {
        $1 = false;
        break m$3;
      }
      if (true) {
        $1 = true;
        break m$3;
      }
      $rt.unmatched($2);
    }
    if (($1 && copiedObject$318(self, inner))) {
      return ("" + "$rt.copy(" + v + ".v)");
    } else {
      {
        return ("" + v + ".v");
      }
    }
  }
  const $4 = want;
  m$5: {
    if (($4.$tag === "Borrow")) {
      return v;
      break m$5;
    }
    if (true) {
      if ((isPlace$315(e) && copiedObject$318(self, want))) {
        return ("" + "$rt.copy(" + v + ")");
      } else {
        {
          return v;
        }
      }
      break m$5;
    }
    $rt.unmatched($4);
  }
}
function floatTy$511(t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Prim")) {
      const p = $1.$;
      return isFloat$417(p);
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const inner = $1.$[1];
      return floatTy$511(inner);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function quote$512(s) {
  const bytes = $b.str_asBytes(s);
  const out = { v: $b.str_toString("\"") };
  let run = 0n;
  let i = 0n;
  while ((i < $b.slice_len(bytes))) {
    const b = $rt.idx(bytes, i);
    const plain = ((((b >= 0x20n) && (b < 0x7fn)) && (b !== 34n)) && (b !== 92n));
    if ((!plain)) {
      if ((run < i)) {
        $b.String_push(out, $b.str_slice(s, run, i));
      }
      if ((b === 34n)) {
        $b.String_push(out, "\\\"");
      } else {
        if ((b === 92n)) {
          $b.String_push(out, "\\\\");
        } else {
          if ((b === 10n)) {
            $b.String_push(out, "\\n");
          } else {
            {
              const h = $rt.wrap_usize((b >> 4n));
              const l = $rt.wrap_usize((b & 15n));
              $b.String_push(out, "\\x");
              $b.String_push(out, $b.str_slice($c2$HEX, h, $rt.usize(h + 1n)));
              $b.String_push(out, $b.str_slice($c2$HEX, l, $rt.usize(l + 1n)));
            }
          }
        }
      }
      run = $rt.usize(i + 1n);
    }
    i = $rt.usize(i + 1n);
  }
  $b.String_push(out, $b.str_slice(s, run, $b.slice_len(bytes)));
  $b.String_push(out, "\"");
  return out.v;
}
function fieldConds$513(self, fs, subj, parts) {
  for (const $1 of $rt.items(fs)) {
    const f = $1[0];
    const q = $1[1];
    const $2 = q;
    m$3: {
      if (($2.$tag === "Some")) {
        const q$$4 = $2.$;
        {
          const c = cond$320(self, q$$4, $b.String_asStr(("" + subj + "." + mangleField$669($b.String_asStr(f.name)))));
          if ((c !== "true")) {
            $b.Vec_push(parts, c);
          }
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return undefined;
}
function fail$514(self, span, message) {
  throw new $rt.Fail({ $tag: "Diagnostic", $: { span: sourceSpan$176(self.p, $rt.copy(span)), message: $b.str_toString(message) } });
}
function paths$515(p, segs, out) {
  const $1 = p.kind;
  m$2: {
    if (($1.$tag === "Bind")) {
      const n = $1.$;
      return $b.Vec_push(out, [$b.String_clone(n), p.id, segs]);
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const args = $1.$.args;
      {
        const inner = { v: clone$680(segs) };
        $b.Vec_push(inner, { $tag: "Payload" });
        const $3 = args;
        m$4: {
          if (($3.$tag === "None")) {
            {
              return undefined;
            }
            break m$4;
          }
          if (($3.$tag === "Tuple")) {
            const ps = $3.$;
            {
              if (($b.slice_len(ps) === 1n)) {
                paths$515($rt.idx(ps, 0n), inner.v, out);
                return undefined;
              } else {
                {
                  const $5 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(ps)));
                  let $7;
                  for (let $6 = $5.next(); !$6.done; $6 = $5.next($7)) {
                    $7 = undefined;
                    const $8 = $6.value.item;
                    const i = $8[0];
                    const q = $8[1];
                    const s = { v: clone$680(inner.v) };
                    $b.Vec_push(s, { $tag: "Index", $: i });
                    paths$515(q, s.v, out);
                  }
                  return undefined;
                }
              }
            }
            break m$4;
          }
          if (($3.$tag === "Record")) {
            const fs = $3.$;
            return fieldPaths$681(fs, inner.v, out);
            break m$4;
          }
          $rt.unmatched($3);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ps = $1.$;
      {
        const $9 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(ps)));
        let $11;
        for (let $10 = $9.next(); !$10.done; $10 = $9.next($11)) {
          $11 = undefined;
          const $12 = $10.value.item;
          const i = $12[0];
          const q = $12[1];
          const s = { v: clone$680(segs) };
          $b.Vec_push(s, { $tag: "Index", $: i });
          paths$515(q, s.v, out);
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      return fieldPaths$681(fields, segs, out);
      break m$2;
    }
    if (($1.$tag === "Or")) {
      const alts = $1.$;
      {
        if (($b.slice_len(alts) > 0n)) {
          paths$515($rt.idx(alts, 0n), segs, out);
          return undefined;
        }
      }
      break m$2;
    }
    if (true) {
      {
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function find$516(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function clone$517(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: $b.String_clone(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function bound$518(self, subj, whole, id, segs) {
  if ((isNone$682(whole) || (!isMutBorrow$508(bindingTy$312(self.v, id))))) {
    return at$683(subj, segs);
  }
  if (($b.slice_len(segs) === 0n)) {
    const $1 = whole;
    m$2: {
      if (($1.$tag === "Some")) {
        const r = $1.$;
        return r;
        break m$2;
      }
      if (($1.$tag === "None")) {
        return $b.str_toString(subj);
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  const parent = { v: clone$680(segs) };
  let $3;
  const $4 = $b.Vec_pop(parent);
  m$5: {
    if (($4.$tag === "Some")) {
      const s = $4.$;
      $3 = s;
      break m$5;
    }
    if (($4.$tag === "None")) {
      $3 = { $tag: "Payload" };
      break m$5;
    }
    $rt.unmatched($4);
  }
  const last = $3;
  const o = at$683(subj, parent.v);
  const $6 = last;
  m$7: {
    if (($6.$tag === "Field")) {
      const f = $6.$;
      return ("" + "new $rt.FieldRef(" + o + ", " + quote$512($b.String_asStr(mangleField$669($b.String_asStr(f)))) + ")");
      break m$7;
    }
    if (($6.$tag === "Index")) {
      const i = $6.$;
      return ("" + "new $rt.FieldRef(" + o + ", " + String(i) + ")");
      break m$7;
    }
    if (($6.$tag === "Payload")) {
      return ("" + "new $rt.FieldRef(" + o + ", \"$\")");
      break m$7;
    }
    $rt.unmatched($6);
  }
}
function blockStmt$519(self, b, dest) {
  line$168(self, "{");
  self.v.indent = $rt.usize(self.v.indent + 1n);
  blockInto$520(self, b, dest);
  self.v.indent = $rt.usize(self.v.indent - 1n);
  line$168(self, "}");
  return undefined;
}
function blockInto$520(self, b, dest) {
  push$165(self);
  stmtsFrom$169(self, b, 0n, dest);
  pop$170(self);
  return undefined;
}
function matchInto$521(self, scrutinee, arms, dest) {
  let $1;
  const $2 = $b.HashMap_get(self.v.p.typed, self.v.fid);
  m$3: {
    if (($2.$tag === "Some")) {
      const t = $2.$;
      const $4 = $b.HashMap_get(t.lentScrutinees, scrutinee.id);
      m$5: {
        if (($4.$tag === "Some")) {
          const m = $4.$;
          $1 = { $tag: "Some", $: m };
          break m$5;
        }
        if (($4.$tag === "None")) {
          $1 = { $tag: "None" };
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$3;
    }
    if (($2.$tag === "None")) {
      $1 = { $tag: "None" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const lent = $1;
  const lentMut = (eq$623(lent, { $tag: "Some", $: true }) || isMutBorrow$508(exprTy$316(self.v, scrutinee.id)));
  let whole = { $tag: "None" };
  let s = $b.String_new();
  if (lentMut) {
    const r = lend$509(self, scrutinee);
    const rs = save$319(self, r);
    s = save$319(self, ("" + rs + ".v"));
    whole = { $tag: "Some", $: rs };
  } else {
    {
      const v = value$313(self, scrutinee);
      s = save$319(self, v);
    }
  }
  const label = ("" + "m" + fresh$167(self));
  line$168(self, ("" + label + ": {"));
  self.v.indent = $rt.usize(self.v.indent + 1n);
  for (const $6 of $rt.items(arms)) {
    const arm = $6;
    if ($b.Option_isSome(arm.generate)) {
      fail$514(self.v, $rt.copy(arm.pat.span), "arms generated by `comptime` code at run time");
    }
    const c = cond$320(self, arm.pat, s);
    line$168(self, ("" + "if (" + c + ") {"));
    self.v.indent = $rt.usize(self.v.indent + 1n);
    push$165(self);
    binds$321(self, arm.pat, s, clone$517(whole), false);
    const $7 = arm.guard;
    m$8: {
      if (($7.$tag === "Some")) {
        const g = $7.$;
        {
          const gv = value$313(self, g);
          line$168(self, ("" + "if (" + gv + ") {"));
          self.v.indent = $rt.usize(self.v.indent + 1n);
          into$322(self, arm.body, dest);
          line$168(self, ("" + "break " + label + ";"));
          self.v.indent = $rt.usize(self.v.indent - 1n);
          line$168(self, "}");
        }
        break m$8;
      }
      if (($7.$tag === "None")) {
        {
          into$322(self, arm.body, dest);
          line$168(self, ("" + "break " + label + ";"));
        }
        break m$8;
      }
      $rt.unmatched($7);
    }
    pop$170(self);
    self.v.indent = $rt.usize(self.v.indent - 1n);
    line$168(self, "}");
  }
  line$168(self, ("" + "$rt.unmatched(" + s + ");"));
  self.v.indent = $rt.usize(self.v.indent - 1n);
  line$168(self, "}");
  return undefined;
}
function simple$522(e) {
  const $1 = e.kind;
  m$2: {
    if ((($1.$tag === "Int") || ($1.$tag === "Float") || ($1.$tag === "Str") || ($1.$tag === "Byte") || ($1.$tag === "Bool") || ($1.$tag === "Ident") || ($1.$tag === "Lambda") || ($1.$tag === "TypeRef"))) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Template")) {
      const parts = $1.$;
      return every$684($b.slice_iter(parts), ((p) => {
  const $3 = p;
  m$4: {
    if (($3.$tag === "Lit")) {
      return true;
      break m$4;
    }
    if (($3.$tag === "Expr")) {
      const x = $3.$;
      return simple$522(x);
      break m$4;
    }
    $rt.unmatched($3);
  }
      }));
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      return simple$522(target);
      break m$2;
    }
    if (($1.$tag === "Unary")) {
      const operand = $1.$.operand;
      return simple$522(operand);
      break m$2;
    }
    if (($1.$tag === "Cast")) {
      const expr = $1.$.expr;
      return simple$522(expr);
      break m$2;
    }
    if ((($1.$tag === "BorrowMut") || ($1.$tag === "Comptime"))) {
      let x;
      if (($1.$tag === "BorrowMut")) { x = $1.$; }
      else if (($1.$tag === "Comptime")) { x = $1.$; }
      return simple$522(x);
      break m$2;
    }
    if (($1.$tag === "Index")) {
      const target = $1.$.target;
      const index = $1.$.index;
      return (simple$522(target) && simple$522(index));
      break m$2;
    }
    if (($1.$tag === "Binary")) {
      const lhs = $1.$.lhs;
      const rhs = $1.$.rhs;
      return (simple$522(lhs) && simple$522(rhs));
      break m$2;
    }
    if (($1.$tag === "Call")) {
      const callee = $1.$.callee;
      const args = $1.$.args;
      return (simple$522(callee) && every$592($b.slice_iter(args), ((a) => {
  return simple$522(a);
      })));
      break m$2;
    }
    if (($1.$tag === "List")) {
      const items = $1.$;
      return every$592($b.slice_iter(items), ((a) => {
  return simple$522(a);
      }));
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const args = $1.$.args;
      const $5 = args;
      m$6: {
        if (($5.$tag === "None")) {
          return true;
          break m$6;
        }
        if (($5.$tag === "Tuple")) {
          const es = $5.$;
          return every$592($b.slice_iter(es), ((a) => {
  return simple$522(a);
          }));
          break m$6;
        }
        if (($5.$tag === "Record")) {
          const fs = $5.$;
          return simpleInits$685(fs);
          break m$6;
        }
        $rt.unmatched($5);
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      return simpleInits$685(fields);
      break m$2;
    }
    if (($1.$tag === "Block")) {
      const b = $1.$;
      return (($b.slice_len(b.stmts) === 0n) && simpleOpt$670(b.tail));
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function forOf$523(self, mutable, pat, iter, body) {
  push$165(self);
  const $1 = iter.kind;
  m$2: {
    if (($1.$tag === "Range" && ($1.$.lo.$tag === "Some") && ($1.$.hi.$tag === "Some"))) {
      const lo = $1.$.lo.$;
      const hi = $1.$.hi.$;
      {
        let $3;
        const $4 = pat.kind;
        m$5: {
          if (($4.$tag === "Bind")) {
            const n = $4.$;
            $3 = { $tag: "Some", $: $b.String_clone(n) };
            break m$5;
          }
          if (($4.$tag === "Wild")) {
            $3 = { $tag: "Some", $: $b.str_toString("_") };
            break m$5;
          }
          if (true) {
            $3 = { $tag: "None" };
            break m$5;
          }
          $rt.unmatched($4);
        }
        const counted = $3;
        const $6 = counted;
        m$7: {
          if (($6.$tag === "Some")) {
            const n = $6.$;
            {
              const a0 = value$313(self, lo);
              let $8;
              if (simple$522(hi)) {
                $8 = a0;
              } else {
                {
                  $8 = save$319(self, a0);
                }
              }
              const a = $8;
              const b = value$313(self, hi);
              const end = save$319(self, b);
              const cell = has$19(self.v.cells, pat.id);
              let $9;
              if (cell) {
                $9 = fresh$167(self);
              } else {
                {
                  $9 = declare$166(self, $b.String_asStr(n), false);
                }
              }
              const counter = $9;
              line$168(self, ("" + "for (let " + counter + " = " + a + "; " + counter + " < " + end + "; " + counter + "++) {"));
              self.v.indent = $rt.usize(self.v.indent + 1n);
              if (cell) {
                const js = declare$166(self, $b.String_asStr(n), true);
                line$168(self, ("" + "const " + js + " = { v: " + counter + " };"));
              }
              blockInto$520(self, body, { $tag: "Discard" });
              self.v.indent = $rt.usize(self.v.indent - 1n);
              line$168(self, "}");
              pop$170(self);
              return;
            }
            break m$7;
          }
          if (true) {
            {
            }
            break m$7;
          }
          $rt.unmatched($6);
        }
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const it = stripBorrow$317(exprTy$316(self.v, iter.id));
  let $10;
  const $11 = it;
  m$12: {
    if (($11.$tag === "Prim" && ($11.$.$tag === "Void"))) {
      $10 = true;
      break m$12;
    }
    if (true) {
      $10 = false;
      break m$12;
    }
    $rt.unmatched($11);
  }
  if ($10) {
    let $13;
    const $14 = iter.kind;
    m$15: {
      if (($14.$tag === "Call")) {
        const callee = $14.$.callee;
        const args = $14.$.args;
        $13 = call$671(self, iter, callee, args, true);
        break m$15;
      }
      if (true) {
        $13 = fail$514(self.v, $rt.copy(iter.span), "a generator is iterated where it is called");
        break m$15;
      }
      $rt.unmatched($14);
    }
    const g = $13;
    drive$686(self, g, mutable, pat, body);
    pop$170(self);
    return;
  }
  let $16;
  const $17 = $b.HashMap_get(self.v.p.typed, self.v.fid);
  m$18: {
    if (($17.$tag === "Some")) {
      const t = $17.$;
      const $19 = $b.HashMap_get(t.eaches, iter.id);
      m$20: {
        if (($19.$tag === "Some")) {
          const id = $19.$;
          $16 = { $tag: "Some", $: id };
          break m$20;
        }
        if (($19.$tag === "None")) {
          $16 = { $tag: "None" };
          break m$20;
        }
        $rt.unmatched($19);
      }
      break m$18;
    }
    if (($17.$tag === "None")) {
      $16 = { $tag: "None" };
      break m$18;
    }
    $rt.unmatched($17);
  }
  const each = $16;
  const v = value$313(self, iter);
  let list = true;
  const $21 = each;
  m$22: {
    if (($21.$tag === "Some")) {
      const id = $21.$;
      {
        let $23;
        const $24 = $b.HashMap_get(self.v.p.typed, self.v.fid);
        m$25: {
          if (($24.$tag === "Some")) {
            const t = $24.$;
            const $26 = $b.HashMap_get(t.calls, id);
            m$27: {
              if (($26.$tag === "Some")) {
                const f = $26.$;
                $23 = { $tag: "Some", $: f };
                break m$27;
              }
              if (($26.$tag === "None")) {
                $23 = { $tag: "None" };
                break m$27;
              }
              $rt.unmatched($26);
            }
            break m$25;
          }
          if (($24.$tag === "None")) {
            $23 = { $tag: "None" };
            break m$25;
          }
          $rt.unmatched($24);
        }
        const efid = $23;
        const $28 = efid;
        m$29: {
          if (($28.$tag === "Some")) {
            const efid$$30 = $28.$;
            {
              const c = callee$688(self, efid$$30, callArgs$687(self.v, id), $rt.copy(iter.span));
              const $31 = c;
              m$32: {
                if (($31.$tag === "Inst")) {
                  const i = $31.$;
                  {
                    const js = $b.String_clone($rt.idx(self.v.insts, i).js);
                    drive$686(self, ("" + js + "(" + v + ")"), mutable, pat, body);
                    pop$170(self);
                    return;
                  }
                  break m$32;
                }
                if (($31.$tag === "Builtin")) {
                  const k = $31.$;
                  {
                    if (((((k !== "Vec_each") && (k !== "slice_each")) && (k !== "array_each")) && (k !== "RegionList_each"))) {
                      drive$686(self, ("" + "$b." + k + "(" + v + ")"), mutable, pat, body);
                      pop$170(self);
                      return;
                    }
                  }
                  break m$32;
                }
                $rt.unmatched($31);
              }
            }
            break m$29;
          }
          if (true) {
            {
            }
            break m$29;
          }
          $rt.unmatched($28);
        }
      }
      break m$22;
    }
    if (true) {
      {
      }
      break m$22;
    }
    $rt.unmatched($21);
  }
  if (list) {
    const x = fresh$167(self);
    line$168(self, ("" + "for (const " + x + " of $rt.items(" + v + ")) {"));
    self.v.indent = $rt.usize(self.v.indent + 1n);
    loopBinds$689(self, pat, x, mutable);
    blockInto$520(self, body, { $tag: "Discard" });
    self.v.indent = $rt.usize(self.v.indent - 1n);
    line$168(self, "}");
  }
  pop$170(self);
  return undefined;
}
function valueFor$524(self, e, dest) {
  const $1 = dest;
  m$2: {
    if (($1.$tag === "Return")) {
      {
        const r = clone$23(self.v.ret);
        return exAs$314(self, e, r);
      }
      break m$2;
    }
    if (true) {
      {
        const v = value$313(self, e);
        if ((isPlace$315(e) && copiedObject$318(self.v, stripBorrow$317(exprTy$316(self.v, e.id))))) {
          return ("" + "$rt.copy(" + v + ")");
        } else {
          {
            return v;
          }
        }
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function lexRange$525(src, start, end) {
  const lx = { v: { src: src, bytes: $b.str_asBytes(src), pos: start, end: end, out: $b.Vec_new() } };
  run$690(lx);
  return $b.replace(new $rt.FieldRef(lx.v, "out"), $b.Vec_new());
}
function eq$526(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Ident") && ($1[1].$tag === "Ident"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$6(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Kw") && ($1[1].$tag === "Kw"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$6(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Int") && ($1[1].$tag === "Int"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$6(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Float") && ($1[1].$tag === "Float"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$6(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Byte") && ($1[1].$tag === "Byte"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$691(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Str") && ($1[1].$tag === "Str"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$6(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Template") && ($1[1].$tag === "Template"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$692(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Tag") && ($1[1].$tag === "Tag"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$6(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Punct") && ($1[1].$tag === "Punct"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$6(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Eof") && ($1[1].$tag === "Eof"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function tok$527(self) {
  return $rt.idx(self.toks, self.pos).tok;
}
function span$528(self) {
  return $rt.copy($rt.idx(self.toks, self.pos).span);
}
function eatKw$529(self, k) {
  if (atKw$530(self.v, k)) {
    bump$539(self);
    return true;
  } else {
    {
      return false;
    }
  }
}
function atKw$530(self, k) {
  return isKw$538(tok$527(self), k);
}
function importItem$531(self) {
  expectKw$693(self, "import");
  expect$544(self, "{");
  const names = { v: $b.Vec_new() };
  while ((!at$532(self.v, "}"))) {
    const name = ident$541(self);
    let $1;
    if (eatKw$529(self, "as")) {
      $1 = ident$541(self);
    } else {
      {
        $1 = clone$218(name);
      }
    }
    const local = $1;
    $b.Vec_push(names, [name, local]);
    if ((!eat$542(self, ","))) {
      break;
    }
  }
  expect$544(self, "}");
  expectWord$694(self, "from");
  let $2;
  const $3 = tok$527(self.v);
  m$4: {
    if (($3.$tag === "Str")) {
      const s = $3.$;
      $2 = $b.String_clone(s);
      break m$4;
    }
    if (true) {
      $2 = error$552(self.v, "a module path string");
      break m$4;
    }
    $rt.unmatched($3);
  }
  const from = $2;
  bump$539(self);
  expect$544(self, ";");
  return { $tag: "Import", $: { names: names.v, from: from } };
}
function at$532(self, p) {
  return isPunct$695(tok$527(self), p);
}
function layout$533(self) {
  expect$544(self, "@");
  expectWord$694(self, "layout");
  expect$544(self, "(");
  const kind = ident$541(self);
  expect$544(self, ")");
  return kind;
}
function eatWord$534(self, w) {
  if (atWord$536(self.v, w)) {
    bump$539(self);
    return true;
  } else {
    {
      return false;
    }
  }
}
function structDecl$535(self, layout, view) {
  expectKw$693(self, "struct");
  const name = ident$541(self);
  const params = typeParams$696(self);
  let $1;
  if ((self.v.declarations && eat$542(self, ";"))) {
    $1 = { $tag: "None" };
  } else {
    {
      $1 = { $tag: "Some", $: fieldList$697(self) };
    }
  }
  const fields = $1;
  return { layout: layout, view: view, name: name, params: params, fields: fields };
}
function atWord$536(self, w) {
  return isWord$698(tok$527(self), w);
}
function tokAt$537(self, n) {
  return $rt.idx(self.toks, min$146($rt.usize(self.pos + n), $rt.usize($b.slice_len(self.toks) - 1n))).tok;
}
function isKw$538(t, k) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Kw")) {
      const q = $1.$;
      return (q === k);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function bump$539(self) {
  const s = span$528(self.v);
  if ((self.v.pos < $rt.usize($b.slice_len(self.v.toks) - 1n))) {
    self.v.pos = $rt.usize(self.v.pos + 1n);
  }
  return $rt.copy(s);
}
function enumDecl$540(self) {
  expectKw$693(self, "enum");
  const name = ident$541(self);
  const params = typeParams$696(self);
  expect$544(self, "{");
  const tags = { v: $b.Vec_new() };
  while ((!at$532(self.v, "}"))) {
    $b.Vec_push(tags, tagDecl$699(self));
    if ((!eat$542(self, ","))) {
      break;
    }
  }
  expect$544(self, "}");
  return { view: false, name: name, params: params, tags: tags.v };
}
function ident$541(self) {
  let $1;
  const $2 = tok$527(self.v);
  m$3: {
    if (($2.$tag === "Ident")) {
      const n = $2.$;
      $1 = $b.String_clone(n);
      break m$3;
    }
    if (true) {
      $1 = error$552(self.v, "an identifier");
      break m$3;
    }
    $rt.unmatched($2);
  }
  const name = $1;
  const span = bump$539(self);
  return { name: name, span: span };
}
function eat$542(self, p) {
  if (at$532(self.v, p)) {
    bump$539(self);
    return true;
  } else {
    {
      return false;
    }
  }
}
function ty$543(self) {
  const start = span$528(self.v);
  let $1 = at$532(self.v, "|");
  if (!$1) {
    let $2;
    const $3 = tok$527(self.v);
    m$4: {
      if (($3.$tag === "Tag")) {
        $2 = true;
        break m$4;
      }
      if (true) {
        $2 = false;
        break m$4;
      }
      $rt.unmatched($3);
    }
    $1 = $2;
  }
  if ($1) {
    return unionTy$700(self);
  }
  if (isIdent$549(tok$527(self.v))) {
    const save = self.v.pos;
    const first = tyPostfix$701(self);
    if ((!at$532(self.v, "|"))) {
      return first;
    }
    self.v.pos = save;
    return unionTy$700(self);
  }
  if ((atKw$530(self.v, "mut") && atN$702(self.v, 1n, "("))) {
    bump$539(self);
    return fnTy$703(self, { $tag: "Mut" }, $rt.copy(start));
  }
  if (eatKw$529(self, "once")) {
    return fnTy$703(self, { $tag: "Once" }, $rt.copy(start));
  }
  if (eatKw$529(self, "mut")) {
    const inner = ty$543(self);
    return { kind: { $tag: "Mut", $: $b.Box_new(inner) }, span: since$554(self.v, $rt.copy(start)) };
  }
  if (eatKw$529(self, "readonly")) {
    const inner = ty$543(self);
    return { kind: { $tag: "Readonly", $: $b.Box_new(inner) }, span: since$554(self.v, $rt.copy(start)) };
  }
  if (at$532(self.v, "(")) {
    return fnTy$703(self, { $tag: "Shared" }, $rt.copy(start));
  }
  return tyPostfix$701(self);
}
function expect$544(self, p) {
  if (at$532(self.v, p)) {
    return bump$539(self);
  } else {
    {
      return error$552(self.v, ("" + "`" + p + "`"));
    }
  }
}
function expr$545(self) {
  const start = span$528(self.v);
  const lhs = range$704(self);
  const $1 = find$705($b.slice_iter($c9$ASSIGN), ((op) => {
  return at$532(self.v, op);
  }));
  m$2: {
    if (($1.$tag === "Some")) {
      const op = $1.$;
      {
        bump$539(self);
        const value = expr$545(self);
        return expr_$706(self, { $tag: "Assign", $: { op: $b.str_toString(op), target: $b.Box_new(lhs), value: $b.Box_new(value) } }, since$554(self.v, $rt.copy(start)));
      }
      break m$2;
    }
    if (($1.$tag === "None")) {
      return lhs;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function interfaceDecl$546(self) {
  expectKw$693(self, "interface");
  const name = ident$541(self);
  const params = typeParams$696(self);
  let $1;
  if (eatKw$529(self, "extends")) {
    $1 = bounds$707(self);
  } else {
    {
      $1 = $b.Vec_new();
    }
  }
  const ext = $1;
  expect$544(self, "{");
  const members = { v: $b.Vec_new() };
  while ((!at$532(self.v, "}"))) {
    if (eatKw$529(self, "type")) {
      const aname = ident$541(self);
      let $2;
      if (eatKw$529(self, "extends")) {
        $2 = bounds$707(self);
      } else {
        {
          $2 = $b.Vec_new();
        }
      }
      const bounds = $2;
      $b.Vec_push(members, { $tag: "AssocType", $: { name: aname, bounds: bounds } });
    } else {
      {
        $b.Vec_push(members, { $tag: "Method", $: memberSig$708(self) });
      }
    }
    expect$544(self, ";");
  }
  expect$544(self, "}");
  return { name: name, params: params, extends: ext, members: members.v };
}
function implDecl$547(self) {
  expectKw$693(self, "impl");
  const params = typeParams$696(self);
  const first = ty$543(self);
  let iface = { $tag: "None" };
  const target = { v: first };
  if (eatKw$529(self, "for")) {
    iface = { $tag: "Some", $: $b.replace(target, ty$543(self)) };
  }
  const methods = { v: $b.Vec_new() };
  const assoc = { v: $b.Vec_new() };
  if (($b.Option_isSome(iface) && eat$542(self, ";"))) {
    return { params: params, iface: iface, target: target.v, methods: methods.v, assoc: assoc.v, derived: true };
  }
  expect$544(self, "{");
  while ((!at$532(self.v, "}"))) {
    if (eatKw$529(self, "type")) {
      const aname = ident$541(self);
      expect$544(self, "=");
      $b.Vec_push(assoc, [aname, ty$543(self)]);
      expect$544(self, ";");
      continue;
    }
    const exported = eatKw$529(self, "export");
    const sig = memberSig$708(self);
    let $1;
    if ((self.v.declarations && eat$542(self, ";"))) {
      $1 = { $tag: "None" };
    } else {
      {
        $1 = { $tag: "Some", $: block$709(self) };
      }
    }
    const body = $1;
    $b.Vec_push(methods, { exported: exported, decl: { sig: sig, body: body } });
  }
  expect$544(self, "}");
  return { params: params, iface: iface, target: target.v, methods: methods.v, assoc: assoc.v, derived: false };
}
function typeAlias$548(self) {
  expectKw$693(self, "type");
  const name = ident$541(self);
  const params = typeParams$696(self);
  expect$544(self, "=");
  const ty = ty$543(self);
  expect$544(self, ";");
  return { name: name, params: params, ty: ty };
}
function isIdent$549(t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Ident")) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function effectDecl$550(self) {
  expectWord$694(self, "effect");
  const name = ident$541(self);
  const params = typeParams$696(self);
  expect$544(self, "{");
  const ops = { v: $b.Vec_new() };
  while ((!at$532(self.v, "}"))) {
    const withKw = atKw$530(self.v, "function");
    $b.Vec_push(ops, sig$553(self, withKw));
    expect$544(self, ";");
  }
  expect$544(self, "}");
  return { name: name, params: params, ops: ops.v };
}
function fnDecl$551(self) {
  const sig = sig$553(self, true);
  let $1;
  if ((self.v.declarations && eat$542(self, ";"))) {
    $1 = { $tag: "None" };
  } else {
    {
      $1 = { $tag: "Some", $: block$709(self) };
    }
  }
  const body = $1;
  return { sig: sig, body: body };
}
function error$552(self, expected) {
  throw new $rt.Fail({ $tag: "Diagnostic", $: { span: span$528(self), message: ("" + "expected " + expected + ", found " + describe$710(self)) } });
}
function sig$553(self, functionKw) {
  return sigNamed$711(self, functionKw, (!functionKw));
}
function since$554(self, start) {
  return { start: start.start, end: max$156(prevEnd$712(self), start.start) };
}
function clone$555(self) {
  {
    return { from: $b.String_clone(self.from), names: clone$713(self.names) };
  }
}
function clone$556(self) {
  {
    return { name: clone$218(self.name), ty: clone$188(self.ty), value: clone$60(self.value) };
  }
}
function clone$557(self) {
  {
    return { fields: clone$182(self.fields), layout: clone$714(self.layout), name: clone$218(self.name), params: clone$179(self.params), view: clone$199(self.view) };
  }
}
function clone$558(self) {
  {
    return { name: clone$218(self.name), params: clone$179(self.params), tags: clone$715(self.tags), view: clone$199(self.view) };
  }
}
function clone$559(self) {
  {
    return { extends: clone$567(self.extends), members: clone$716(self.members), name: clone$218(self.name), params: clone$179(self.params) };
  }
}
function clone$560(self) {
  {
    return { assoc: clone$717(self.assoc), derived: clone$199(self.derived), iface: clone$188(self.iface), methods: clone$718(self.methods), params: clone$179(self.params), target: clone$193(self.target) };
  }
}
function clone$561(self) {
  {
    return { name: clone$218(self.name), params: clone$179(self.params), ty: clone$193(self.ty) };
  }
}
function clone$562(self) {
  {
    return { name: clone$218(self.name), ops: clone$719(self.ops), params: clone$179(self.params) };
  }
}
function clone$563(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Lit")) {
      const x = $1.$;
      return { $tag: "Lit", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Expr")) {
      const x = $1.$;
      return { $tag: "Expr", $: clone$60(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$564(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const x = $1.$;
      return { $tag: "Tuple", $: clone$334(x) };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const x = $1.$;
      return { $tag: "Record", $: clone$565(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$565(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$720(x));
  }
  return v.v;
}
function clone$566(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$400(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$567(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$193(x));
  }
  return v.v;
}
function clone$568(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$721(x));
  }
  return v.v;
}
function clone$569(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$722(x));
  }
  return v.v;
}
function eq$570(self, other) {
  {
    {
      {
        if ((!eq$605(self.end, other.end))) {
          return false;
        }
      }
      {
        if ((!eq$605(self.start, other.start))) {
          return false;
        }
      }
    }
    return true;
  }
}
function clone$571(self) {
  {
    return { default: clone$188(self.default), name: clone$218(self.name) };
  }
}
function clone$572(self) {
  {
    return { bounds: clone$567(self.bounds), default: clone$188(self.default), name: clone$218(self.name) };
  }
}
function clone$573(self) {
  {
    return { name: clone$218(self.name), ty: clone$193(self.ty) };
  }
}
function clone$574(self) {
  {
    return { name: clone$218(self.name), ty: clone$193(self.ty), private: clone$199(self.private), computed: clone$96(self.computed), generate: clone$723(self.generate) };
  }
}
function max$575(a, b) {
  if ((b > a)) {
    return b;
  } else {
    {
      return a;
    }
  }
}
function clone$576(self) {
  {
    return { args: clone$567(self.args), segments: clone$400(self.segments) };
  }
}
function clone$577(self) {
  {
    return { fields: clone$356(self.fields), rest: clone$714(self.rest) };
  }
}
function clone$578(self) {
  {
    return { includes: clone$567(self.includes), rest: clone$714(self.rest), tags: clone$715(self.tags) };
  }
}
function clone$579(self) {
  {
    return { mode: clone$394(self.mode), params: clone$219(self.params), ret: clone$724(self.ret), uses: clone$221(self.uses) };
  }
}
function clone$580(self) {
  {
    return { elem: clone$581(self.elem), len: clone$96(self.len) };
  }
}
function clone$581(self) {
  return $b.Box_new(clone$193($b.Box_get(self)));
}
function clone$582(self) {
  return $b.Box_new(clone$90($b.Box_get(self)));
}
function clone$583(self) {
  {
    const v = [$b.String_clone($rt.idx(self, 0n)), clone$602($rt.idx(self, 1n))];
    return v;
  }
}
function unit$584(self, at) {
  const span = sp$214(self, $rt.copy(at));
  return mk$380(self, { $tag: "Block", $: { stmts: $b.Vec_new(), tail: { $tag: "None" }, span: span } }, $rt.copy(span));
}
function genItems$585(self, g, out) {
  const $1 = g;
  m$2: {
    if (($1.$tag === "If")) {
      const cond = $1.$.cond;
      const then = $1.$.then;
      const otherwise = $1.$.otherwise;
      {
        let $3;
        if (evalBool$590(self, cond)) {
          $3 = then;
        } else {
          {
            $3 = otherwise;
          }
        }
        const chosen = $3;
        for (const $4 of $rt.items(inits$375(self, chosen))) {
          const x = $4;
          $b.Vec_push(out, clone$720(x));
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Do")) {
      const e = $1.$;
      {
        eval$$378(self, e);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const scrutinee = $1.$.scrutinee;
      const arms = $1.$.arms;
      {
        const v = eval$$378(self, scrutinee);
        for (const $5 of $rt.items(arms)) {
          const pat = $5[0];
          const items = $5[1];
          const depth = $b.slice_len(self.v.env);
          const binds = { v: $b.Vec_new() };
          if (ctMatch$587(self, pat, v, binds)) {
            bind$589(self, binds.v);
            const r = inits$375(self, items);
            $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
            for (const $6 of $rt.items(r)) {
              const x = $6;
              $b.Vec_push(out, clone$720(x));
            }
            return;
          }
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
        }
        fail$391($rt.copy(scrutinee.span), $b.String_asStr(("" + "no arm matches `" + cvShow$588(self.v.p.v, v) + "`")));
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "For")) {
      const pat = $1.$.pat;
      const iter = $1.$.iter;
      const body = $1.$.body;
      {
        for (const $7 of $rt.items(evalList$586(self, iter))) {
          const v = $7;
          const depth = $b.slice_len(self.v.env);
          const binds = { v: $b.Vec_new() };
          if ((!ctMatch$587(self, pat, v, binds))) {
            fail$391($rt.copy(pat.span), $b.String_asStr(("" + "`" + cvShow$588(self.v.p.v, v) + "` does not match this pattern")));
          }
          bind$589(self, binds.v);
          const r = inits$375(self, body);
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
          for (const $8 of $rt.items(r)) {
            const x = $8;
            $b.Vec_push(out, clone$720(x));
          }
        }
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function evalList$586(self, e) {
  const $1 = eval$$378(self, e);
  m$2: {
    if (($1.$tag === "List")) {
      const xs = $1.$;
      return xs;
      break m$2;
    }
    if (true) {
      const v = $1;
      return fail$391($rt.copy(e.span), $b.String_asStr(("" + "`comptime for` needs a list, found " + cvKind$392(v))));
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function ctMatch$587(self, p, v, out) {
  const $1 = p.kind;
  m$2: {
    if (($1.$tag === "Wild")) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Bind")) {
      const n = $1.$;
      {
        $b.Vec_push(out, [$b.String_clone(n), clone$90(v)]);
        return true;
      }
      break m$2;
    }
    if (($1.$tag === "Lit")) {
      const e = $1.$;
      {
        const lit = eval$$378(self, e);
        return cvEq$725(lit, v);
      }
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const name = $1.$.name;
      const args = $1.$.args;
      const $3 = v;
      m$4: {
        if (($3.$tag === "Tag")) {
          const n = $3.$[0];
          const payload = $3.$[1];
          {
            if (!eq$6(name, n)) {
              return false;
            }
            const $5 = args;
            m$6: {
              if (($5.$tag === "None")) {
                return true;
                break m$6;
              }
              if (($5.$tag === "Tuple")) {
                const ps = $5.$;
                const $7 = payload;
                m$8: {
                  if (($7.$tag === "Some")) {
                    const x = $7.$;
                    {
                      if (($b.slice_len(ps) === 1n)) {
                        return ctMatch$587(self, $rt.idx(ps, 0n), x, out);
                      }
                      const $9 = $b.Box_get(x);
                      m$10: {
                        if (($9.$tag === "List")) {
                          const xs = $9.$;
                          if (($b.slice_len(xs) === $b.slice_len(ps))) {
                            {
                              const $11 = $b.slice_len(ps);
                              for (let i = 0n; i < $11; i++) {
                                if ((!ctMatch$587(self, $rt.idx(ps, i), $rt.idx(xs, i), out))) {
                                  return false;
                                }
                              }
                              return true;
                            }
                            break m$10;
                          }
                        }
                        if (true) {
                          return false;
                          break m$10;
                        }
                        $rt.unmatched($9);
                      }
                    }
                    break m$8;
                  }
                  if (($7.$tag === "None")) {
                    return false;
                    break m$8;
                  }
                  $rt.unmatched($7);
                }
                break m$6;
              }
              if (($5.$tag === "Record")) {
                const fs = $5.$;
                const $12 = payload;
                m$13: {
                  if (($12.$tag === "Some")) {
                    const x = $12.$;
                    return ctRecord$726(self, fs, x, out);
                    break m$13;
                  }
                  if (($12.$tag === "None")) {
                    return false;
                    break m$13;
                  }
                  $rt.unmatched($12);
                }
                break m$6;
              }
              $rt.unmatched($5);
            }
          }
          break m$4;
        }
        if (true) {
          return false;
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ps = $1.$;
      const $14 = v;
      m$15: {
        if (($14.$tag === "List")) {
          const xs = $14.$;
          if (($b.slice_len(ps) === $b.slice_len(xs))) {
            {
              const $16 = $b.slice_len(ps);
              for (let i = 0n; i < $16; i++) {
                if ((!ctMatch$587(self, $rt.idx(ps, i), $rt.idx(xs, i), out))) {
                  return false;
                }
              }
              return true;
            }
            break m$15;
          }
        }
        if (true) {
          return false;
          break m$15;
        }
        $rt.unmatched($14);
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      return ctRecord$726(self, fields, v, out);
      break m$2;
    }
    if (($1.$tag === "Or")) {
      const ps = $1.$;
      {
        for (const $17 of $rt.items(ps)) {
          const q = $17;
          const binds = { v: $b.Vec_new() };
          if (ctMatch$587(self, q, v, binds)) {
            for (const $18 of $rt.items(binds.v)) {
              const b = $18;
              $b.Vec_push(out, clone$367(b));
            }
            return true;
          }
        }
        return false;
      }
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function cvShow$588(p, v) {
  const $1 = v;
  m$2: {
    if (($1.$tag === "Unit")) {
      return $b.str_toString("void");
      break m$2;
    }
    if (($1.$tag === "Bool")) {
      const b = $1.$;
      return ("" + String(b));
      break m$2;
    }
    if (($1.$tag === "Int")) {
      const i = $1.$;
      return ("" + String(i));
      break m$2;
    }
    if (($1.$tag === "Str")) {
      const s = $1.$;
      return $b.String_clone(s);
      break m$2;
    }
    if (($1.$tag === "Type")) {
      const t = $1.$;
      return show$136(p, t);
      break m$2;
    }
    if (($1.$tag === "List")) {
      const xs = $1.$;
      {
        const parts = { v: $b.Vec_new() };
        for (const $3 of $rt.items(xs)) {
          const x = $3;
          $b.Vec_push(parts, cvShow$588(p, x));
        }
        return ("" + "[" + join$53(parts.v, ", ") + "]");
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fs = $1.$;
      {
        const parts = { v: $b.Vec_new() };
        for (const $4 of $rt.items(fs)) {
          const k = $4[0];
          const x = $4[1];
          $b.Vec_push(parts, ("" + k + ": " + cvShow$588(p, x)));
        }
        return ("" + "{ " + join$53(parts.v, ", ") + " }");
      }
      break m$2;
    }
    if (($1.$tag === "Tag" && ($1.$[1].$tag === "None"))) {
      const n = $1.$[0];
      return ("" + "#" + n);
      break m$2;
    }
    if (($1.$tag === "Tag" && ($1.$[1].$tag === "Some"))) {
      const n = $1.$[0];
      const x = $1.$[1].$;
      return ("" + "#" + n + "(" + cvShow$588(p, x) + ")");
      break m$2;
    }
    if ((($1.$tag === "Fn") || ($1.$tag === "Closure"))) {
      return $b.str_toString("function");
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function bind$589(self, binds) {
  for (const $1 of $rt.items(binds)) {
    const k = $1[0];
    const v = $1[1];
    $b.Vec_push(new $rt.FieldRef(self.v, "env"), [$b.String_clone(k), { $tag: "Some", $: clone$90(v) }]);
  }
  return undefined;
}
function evalBool$590(self, e) {
  const $1 = eval$$378(self, e);
  m$2: {
    if (($1.$tag === "Bool")) {
      const b = $1.$;
      return b;
      break m$2;
    }
    if (true) {
      const v = $1;
      return fail$391($rt.copy(e.span), $b.String_asStr(("" + "expected a `bool`, found " + cvKind$392(v))));
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function isNone$591(self) {
  return (!$b.Option_isSome(self));
}
function every$592(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if ((!test(x))) {
      return false;
    }
  }
  return true;
}
function tick$593(self, span) {
  self.v.steps = $rt.u64(self.v.steps + 1n);
  if ((self.v.steps > $c4$STEP_BUDGET)) {
    fail$391($rt.copy(span), "`comptime` evaluation ran out of steps");
    return undefined;
  }
}
function parseDecimal$594(s) {
  const bytes = $b.str_asBytes(s);
  if (($b.slice_len(bytes) === 0n)) {
    return { $tag: "None" };
  }
  let n = 0n;
  for (const $1 of $rt.items(bytes)) {
    const b = $1;
    if (((b < 48n) || (b > 57n))) {
      return { $tag: "None" };
    }
    n = $rt.i128($rt.i128(n * 10n) + $rt.wrap_i128($rt.u8(b - 48n)));
  }
  return { $tag: "Some", $: n };
}
function identValue$595(self, n, span) {
  const $1 = lookup$390(self.v, n);
  m$2: {
    if (($1.$tag === "Some" && ($1.$.$tag === "Some"))) {
      const v = $1.$.$;
      return v;
      break m$2;
    }
    if (($1.$tag === "Some" && ($1.$.$tag === "None"))) {
      fail$391($rt.copy(span), $b.String_asStr(("" + "`" + n + "` is a run-time value; `comptime` code cannot use it")));
      break m$2;
    }
    if (($1.$tag === "None")) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const $3 = primFromName$227(n);
  m$4: {
    if (($3.$tag === "Some")) {
      const p = $3.$;
      {
        if ((!eq$228(p, { $tag: "Type" }) || isNone$191(lookup$47(self.v.p.v, self.v.module, n)))) {
          return { $tag: "Type", $: { $tag: "Prim", $: p } };
        }
      }
      break m$4;
    }
    if (true) {
      {
      }
      break m$4;
    }
    $rt.unmatched($3);
  }
  const $5 = lookup$47(self.v.p.v, self.v.module, n);
  m$6: {
    if (($5.$tag === "Some" && ($5.$.$tag === "Const"))) {
      const c = $5.$.$;
      {
        const value = clone$60($rt.idx(self.v.p.v.consts, c).value);
        const m = $rt.idx(self.v.p.v.consts, c).module;
        const saved = $b.replace(new $rt.FieldRef(self.v, "module"), m);
        let $7;
        try {
          $7 = eval$$378(self, value);
        } catch ($8) {
          if (!($8 instanceof $rt.Fail)) throw $8;
          const s = $8.value;
          self.v.module = saved;
          throw new $rt.Fail(s);
        }
        const r = $7;
        self.v.module = saved;
        return r;
      }
      break m$6;
    }
    if (($5.$tag === "Some" && ($5.$.$tag === "Fn"))) {
      const f = $5.$.$;
      return { $tag: "Fn", $: f };
      break m$6;
    }
    if (($5.$tag === "Some" && ($5.$.$tag === "Def"))) {
      {
        const scope = moduleScope$31(self.v.module);
        const t = { kind: { $tag: "Path", $: { segments: [{ name: $b.str_toString(n), span: span }], args: $b.Vec_new() } }, span: span };
        return { $tag: "Type", $: elabTy$101(self.v.p, t, scope) };
      }
      break m$6;
    }
    if (($5.$tag === "None")) {
      return fail$391($rt.copy(span), $b.String_asStr(("" + "unknown name `" + n + "` in `comptime` code")));
      break m$6;
    }
    $rt.unmatched($5);
  }
}
function evalRecord$596(self, fs) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(fs)) {
    const f = $1;
    let $2;
    const $3 = f.value;
    m$4: {
      if (($3.$tag === "Some")) {
        const x = $3.$;
        $2 = eval$$378(self, x);
        break m$4;
      }
      if (($3.$tag === "None")) {
        $2 = identValue$595(self, $b.String_asStr(f.name.name), $rt.copy(f.name.span));
        break m$4;
      }
      $rt.unmatched($3);
    }
    const v = $2;
    recordSet$727(out, $b.String_asStr(f.name.name), v);
  }
  return { $tag: "Record", $: out.v };
}
function evalCall$597(self, callee, args, span) {
  const $1 = callee.kind;
  m$2: {
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      const name = $1.$.name;
      {
        let $3;
        const $4 = target.kind;
        m$5: {
          if (($4.$tag === "Ident")) {
            const t = $4.$;
            $3 = ((t === "Type") && isNone$591(lookup$390(self.v, $b.String_asStr(t))));
            break m$5;
          }
          if (true) {
            $3 = false;
            break m$5;
          }
          $rt.unmatched($4);
        }
        const isType = $3;
        if (isType) {
          const vals = evalArgs$728(self, args);
          return reflect$729(self, $b.String_asStr(name.name), vals, $rt.copy(span));
        }
        const recv = eval$$378(self, target);
        const vals = evalArgs$728(self, args);
        return method$730(self, recv, $b.String_asStr(name.name), vals, $rt.copy(span));
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const $6 = callee.kind;
  m$7: {
    if (($6.$tag === "Ident")) {
      const n = $6.$;
      {
        if (isNone$591(lookup$390(self.v, $b.String_asStr(n)))) {
          if ((n === "panic")) {
            let $8;
            const $9 = $b.slice_len(args);
            m$10: {
              if ($9 === 0n) {
                $8 = $b.str_toString("panic");
                break m$10;
              }
              if (true) {
                {
                  const v = eval$$378(self, $rt.idx(args, 0n));
                  $8 = cvShow$588(self.v.p.v, v);
                }
                break m$10;
              }
              $rt.unmatched($9);
            }
            const msg = $8;
            fail$391($rt.copy(span), $b.String_asStr(msg));
          }
          if ((n === "assert")) {
            if ((!evalBool$590(self, $rt.idx(args, 0n)))) {
              let $11;
              if (($b.slice_len(args) > 1n)) {
                const v = eval$$378(self, $rt.idx(args, 1n));
                $11 = cvShow$588(self.v.p.v, v);
              } else {
                {
                  $11 = $b.str_toString("assertion failed");
                }
              }
              const msg = $11;
              fail$391($rt.copy(span), $b.String_asStr(msg));
            }
            return { $tag: "Unit" };
          }
        }
      }
      break m$7;
    }
    if (true) {
      {
      }
      break m$7;
    }
    $rt.unmatched($6);
  }
  const f = eval$$378(self, callee);
  const vals = evalArgs$728(self, args);
  return apply$731(self, f, vals, $rt.copy(span));
}
function binary$598(op, l, r) {
  if ((op === "==")) {
    return { $tag: "Some", $: { $tag: "Bool", $: cvEq$725(l, r) } };
  }
  if ((op === "!=")) {
    return { $tag: "Some", $: { $tag: "Bool", $: (!cvEq$725(l, r)) } };
  }
  const $1 = [l, r];
  m$2: {
    if ((($1[0].$tag === "Int") && ($1[1].$tag === "Int"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      {
        if ((op === "+")) {
          return { $tag: "Some", $: { $tag: "Int", $: $rt.i128(a + b) } };
        }
        if ((op === "-")) {
          return { $tag: "Some", $: { $tag: "Int", $: $rt.i128(a - b) } };
        }
        if ((op === "*")) {
          return { $tag: "Some", $: { $tag: "Int", $: $rt.i128(a * b) } };
        }
        if (((op === "/") && (b !== 0n))) {
          return { $tag: "Some", $: { $tag: "Int", $: $rt.div(a, b, $rt.i128) } };
        }
        if (((op === "%") && (b !== 0n))) {
          return { $tag: "Some", $: { $tag: "Int", $: $rt.rem(a, b) } };
        }
        if ((op === "&")) {
          return { $tag: "Some", $: { $tag: "Int", $: (a & b) } };
        }
        if ((op === "|")) {
          return { $tag: "Some", $: { $tag: "Int", $: (a | b) } };
        }
        if ((((op === "<<") && (b >= 0n)) && (b < 127n))) {
          return { $tag: "Some", $: { $tag: "Int", $: $rt.i128(a << b) } };
        }
        if ((((op === ">>") && (b >= 0n)) && (b < 127n))) {
          return { $tag: "Some", $: { $tag: "Int", $: (a >> b) } };
        }
        if ((op === "<")) {
          return { $tag: "Some", $: { $tag: "Bool", $: (a < b) } };
        }
        if ((op === "<=")) {
          return { $tag: "Some", $: { $tag: "Bool", $: (a <= b) } };
        }
        if ((op === ">")) {
          return { $tag: "Some", $: { $tag: "Bool", $: (a > b) } };
        }
        if ((op === ">=")) {
          return { $tag: "Some", $: { $tag: "Bool", $: (a >= b) } };
        }
        return { $tag: "None" };
      }
      break m$2;
    }
    if ((($1[0].$tag === "Str") && ($1[1].$tag === "Str"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      if ((op === "+")) {
        return { $tag: "Some", $: { $tag: "Str", $: ("" + a + b) } };
        break m$2;
      }
    }
    if ((($1[0].$tag === "List") && ($1[1].$tag === "List"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      if ((op === "+")) {
        {
          const out = { v: a };
          for (const $3 of $rt.items(b)) {
            const x = $3;
            $b.Vec_push(out, clone$90(x));
          }
          return { $tag: "Some", $: { $tag: "List", $: out.v } };
        }
        break m$2;
      }
    }
    if (true) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function evalBlock$599(self, b) {
  for (const $1 of $rt.items(b.stmts)) {
    const st = $1;
    const $2 = st;
    m$3: {
      if (($2.$tag === "Let")) {
        const pat = $2.$.pat;
        const init = $2.$.init;
        {
          const v = eval$$378(self, init);
          const binds = { v: $b.Vec_new() };
          if ((!ctMatch$587(self, pat, v, binds))) {
            fail$391($rt.copy(pat.span), "pattern does not match");
          }
          bind$589(self, binds.v);
        }
        break m$3;
      }
      if ((($2.$tag === "Expr") || ($2.$tag === "Defer"))) {
        let e;
        if (($2.$tag === "Expr")) { e = $2.$; }
        else if (($2.$tag === "Defer")) { e = $2.$; }
        {
          eval$$378(self, e);
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  const $4 = b.tail;
  m$5: {
    if (($4.$tag === "Some")) {
      const t = $4.$;
      return eval$$378(self, t);
      break m$5;
    }
    if (($4.$tag === "None")) {
      return { $tag: "Unit" };
      break m$5;
    }
    $rt.unmatched($4);
  }
}
function recordGet$600(fs, k) {
  const $3 = find$732($b.slice_iter(fs), (($0$$1) => {
  {
    const $2 = $0$$1;
    const n = $2[0];
    return (n === k);
  }
  }));
  m$4: {
    if (($3.$tag === "Some")) {
      const v = $3.$[1];
      return { $tag: "Some", $: clone$90(v) };
      break m$4;
    }
    if (($3.$tag === "None")) {
      return { $tag: "None" };
      break m$4;
    }
    $rt.unmatched($3);
  }
}
function genArms$601(self, g, out) {
  const $1 = g;
  m$2: {
    if (($1.$tag === "If")) {
      const cond = $1.$.cond;
      const then = $1.$.then;
      const otherwise = $1.$.otherwise;
      {
        let $3;
        if (evalBool$590(self, cond)) {
          $3 = then;
        } else {
          {
            $3 = otherwise;
          }
        }
        const chosen = $3;
        for (const $4 of $rt.items(arms$387(self, chosen))) {
          const x = $4;
          $b.Vec_push(out, clone$721(x));
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Do")) {
      const e = $1.$;
      {
        eval$$378(self, e);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const scrutinee = $1.$.scrutinee;
      const arms = $1.$.arms;
      {
        const v = eval$$378(self, scrutinee);
        for (const $5 of $rt.items(arms)) {
          const pat = $5[0];
          const items = $5[1];
          const depth = $b.slice_len(self.v.env);
          const binds = { v: $b.Vec_new() };
          if (ctMatch$587(self, pat, v, binds)) {
            bind$589(self, binds.v);
            const r = arms$387(self, items);
            $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
            for (const $6 of $rt.items(r)) {
              const x = $6;
              $b.Vec_push(out, clone$721(x));
            }
            return;
          }
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
        }
        fail$391($rt.copy(scrutinee.span), $b.String_asStr(("" + "no arm matches `" + cvShow$588(self.v.p.v, v) + "`")));
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "For")) {
      const pat = $1.$.pat;
      const iter = $1.$.iter;
      const body = $1.$.body;
      {
        for (const $7 of $rt.items(evalList$586(self, iter))) {
          const v = $7;
          const depth = $b.slice_len(self.v.env);
          const binds = { v: $b.Vec_new() };
          if ((!ctMatch$587(self, pat, v, binds))) {
            fail$391($rt.copy(pat.span), $b.String_asStr(("" + "`" + cvShow$588(self.v.p.v, v) + "` does not match this pattern")));
          }
          bind$589(self, binds.v);
          const r = arms$387(self, body);
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
          for (const $8 of $rt.items(r)) {
            const x = $8;
            $b.Vec_push(out, clone$721(x));
          }
        }
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$602(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$90(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function genFields$603(self, g, out) {
  const $1 = g;
  m$2: {
    if (($1.$tag === "If")) {
      const cond = $1.$.cond;
      const then = $1.$.then;
      const otherwise = $1.$.otherwise;
      {
        let $3;
        if (evalBool$590(self, cond)) {
          $3 = then;
        } else {
          {
            $3 = otherwise;
          }
        }
        const chosen = $3;
        for (const $4 of $rt.items(fields$393(self, chosen))) {
          const x = $4;
          $b.Vec_push(out, clone$574(x));
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Do")) {
      const e = $1.$;
      {
        eval$$378(self, e);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const scrutinee = $1.$.scrutinee;
      const arms = $1.$.arms;
      {
        const v = eval$$378(self, scrutinee);
        for (const $5 of $rt.items(arms)) {
          const pat = $5[0];
          const items = $5[1];
          const depth = $b.slice_len(self.v.env);
          const binds = { v: $b.Vec_new() };
          if (ctMatch$587(self, pat, v, binds)) {
            bind$589(self, binds.v);
            const r = fields$393(self, items);
            $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
            for (const $6 of $rt.items(r)) {
              const x = $6;
              $b.Vec_push(out, clone$574(x));
            }
            return;
          }
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
        }
        fail$391($rt.copy(scrutinee.span), $b.String_asStr(("" + "no arm matches `" + cvShow$588(self.v.p.v, v) + "`")));
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "For")) {
      const pat = $1.$.pat;
      const iter = $1.$.iter;
      const body = $1.$.body;
      {
        for (const $7 of $rt.items(evalList$586(self, iter))) {
          const v = $7;
          const depth = $b.slice_len(self.v.env);
          const binds = { v: $b.Vec_new() };
          if ((!ctMatch$587(self, pat, v, binds))) {
            fail$391($rt.copy(pat.span), $b.String_asStr(("" + "`" + cvShow$588(self.v.p.v, v) + "` does not match this pattern")));
          }
          bind$589(self, binds.v);
          const r = fields$393(self, body);
          $b.Vec_truncate(new $rt.FieldRef(self.v, "env"), depth);
          for (const $8 of $rt.items(r)) {
            const x = $8;
            $b.Vec_push(out, clone$574(x));
          }
        }
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$604(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Effect")) {
      const x = $1.$;
      return { $tag: "Effect", $: clone$193(x) };
      break m$2;
    }
    if (($1.$tag === "Spread")) {
      const x = $1.$;
      return { $tag: "Spread", $: clone$218(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eq$605(self, other) {
  return (self === other);
}
function eq$606(self, other) {
  if (($b.slice_len(self) !== $b.slice_len(other))) {
    return false;
  }
  let i = 0n;
  while ((i < $b.slice_len(self))) {
    if ((!eq$733($rt.idx(self, i), $rt.idx(other, i)))) {
      return false;
    }
    i = $rt.usize(i + 1n);
  }
  return true;
}
function eq$607(self, other) {
  if (($b.slice_len(self) !== $b.slice_len(other))) {
    return false;
  }
  let i = 0n;
  while ((i < $b.slice_len(self))) {
    if ((!eq$734($rt.idx(self, i), $rt.idx(other, i)))) {
      return false;
    }
    i = $rt.usize(i + 1n);
  }
  return true;
}
function eq$608(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Known") && ($1[1].$tag === "Known"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$735(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Var") && ($1[1].$tag === "Var"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$266(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Param") && ($1[1].$tag === "Param"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$262(a, b);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eq$609(self, other) {
  return (self === other);
}
function eq$610(self, other) {
  {
    {
      {
        if ((!eq$622(self.mode, other.mode))) {
          return false;
        }
      }
      {
        if ((!eq$411(self.params, other.params))) {
          return false;
        }
      }
      {
        if ((!eq$234(self.ret, other.ret))) {
          return false;
        }
      }
      {
        if ((!eq$736(self.effects, other.effects))) {
          return false;
        }
      }
    }
    return true;
  }
}
function named$611(self, name, args) {
  return { $tag: "Named", $: [known$104(self, name), args] };
}
function local$612(self, name) {
  let i = $b.slice_len(self.scopes);
  while ((i > 0n)) {
    i = $rt.usize(i - 1n);
    const $1 = $b.HashMap_get($rt.idx(self.scopes, i), name);
    m$2: {
      if (($1.$tag === "Some")) {
        const t = $1.$;
        {
          return { $tag: "Some", $: clone$23(t) };
        }
        break m$2;
      }
      if (true) {
        {
        }
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  return { $tag: "None" };
}
function fnEffects$613(p, fid, module, span) {
  const $1 = new $rt.FieldRef($rt.idx(p.v.fns, fid).scheme, "effects");
  const $2 = $1.v;
  m$3: {
    if (($2.$tag === "Some")) {
      const e = new $rt.FieldRef($2, "$");
      {
        return clone$40(e.v);
      }
      break m$3;
    }
    if (true) {
      {
      }
      break m$3;
    }
    $rt.unmatched($2);
  }
  const $4 = $b.HashMap_get(p.v.inferred, fid);
  m$5: {
    if (($4.$tag === "Some" && ($4.$.$tag === "Some"))) {
      const e = $4.$.$;
      return clone$40(e);
      break m$5;
    }
    if (($4.$tag === "Some" && ($4.$.$tag === "None"))) {
      {
        $b.HashMap_insert(new $rt.FieldRef(p.v, "assumedPure"), fid, [module, $rt.copy(span)]);
        return pure$37();
      }
      break m$5;
    }
    if (($4.$tag === "None")) {
      {
      }
      break m$5;
    }
    $rt.unmatched($4);
  }
  $b.HashMap_insert(new $rt.FieldRef(p.v, "inferred"), fid, { $tag: "None" });
  checkFn$3(p, fid);
  const $6 = $b.HashMap_get(p.v.inferred, fid);
  m$7: {
    if (($6.$tag === "Some" && ($6.$.$tag === "Some"))) {
      const e = $6.$.$;
      return clone$40(e);
      break m$7;
    }
    if (true) {
      return pure$37();
      break m$7;
    }
    $rt.unmatched($6);
  }
}
function instantiate$614(self, scheme, explicit, calleeOpenFail) {
  const map = { v: $b.HashMap_new() };
  const recordTails = { v: $b.HashMap_new() };
  let k = 0n;
  const args = { v: $b.Vec_new() };
  for (const $1 of $rt.items(scheme.tparams)) {
    const g = $1;
    let $2;
    const $3 = g.kind;
    m$4: {
      if (($3.$tag === "Type")) {
        {
          let $5;
          if ((k < $b.slice_len(explicit))) {
            $5 = clone$23($rt.idx(explicit, k));
          } else {
            {
              $5 = fresh$238(new $rt.FieldRef(self.v, "s"));
            }
          }
          const t = $5;
          k = $rt.usize(k + 1n);
          $2 = { $tag: "Ty", $: t };
        }
        break m$4;
      }
      if (($3.$tag === "Region")) {
        $2 = { $tag: "Region", $: freshRegion$737(new $rt.FieldRef(self.v, "s")) };
        break m$4;
      }
      if (($3.$tag === "Row")) {
        {
          $b.HashMap_insert(recordTails, g.sym.id, freshRowTail$243(new $rt.FieldRef(self.v, "s")));
          $2 = { $tag: "Row", $: freshEffs$41(new $rt.FieldRef(self.v, "s")) };
        }
        break m$4;
      }
      if (($3.$tag === "Len")) {
        $2 = { $tag: "Len", $: freshLen$738(new $rt.FieldRef(self.v, "s")) };
        break m$4;
      }
      $rt.unmatched($3);
    }
    const a = $2;
    $b.Vec_push(args, clone$290(a));
    $b.HashMap_insert(map, g.sym.id, a);
  }
  const params = { v: $b.Vec_new() };
  for (const $6 of $rt.items(scheme.params)) {
    const n = $6[0];
    const t = $6[1];
    $b.Vec_push(params, [$b.String_clone(n), instRecordTails$739(subst$308(t, map.v), recordTails.v)]);
  }
  const ret = instRecordTails$739(subst$308(scheme.ret, map.v), recordTails.v);
  let $7;
  const $8 = scheme.effects;
  m$9: {
    if (($8.$tag === "Some")) {
      const e = $8.$;
      {
        const row = { v: substEffs$305(e, map.v) };
        const $10 = $b.slice_len(row.v.effs);
        for (let i = 0n; i < $10; i++) {
          const targs = { v: $b.Vec_new() };
          for (const $11 of $rt.items($rt.idx(row.v.effs, i).args)) {
            const t = $11;
            $b.Vec_push(targs, instRecordTails$739(t, recordTails.v));
          }
          $rt.idx(row.v.effs, i).args = targs.v;
        }
        if (calleeOpenFail) {
          openFail$740(self, row);
        }
        $7 = { $tag: "Some", $: row.v };
      }
      break m$9;
    }
    if (($8.$tag === "None")) {
      $7 = { $tag: "None" };
      break m$9;
    }
    $rt.unmatched($8);
  }
  const effects = $7;
  return { params: params.v, ret: ret, effects: effects, args: args.v };
}
function slot$615(self, e, t) {
  check$428(self, e, t);
  $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "slots"), e.id, clone$23(t));
  return undefined;
}
function instantiateNamed$616(self, t, scope) {
  let $1;
  const $2 = t.kind;
  m$3: {
    if (($2.$tag === "Path")) {
      const segments = $2.$.segments;
      $1 = segments;
      break m$3;
    }
    if (true) {
      return { $tag: "Error" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const segments = $1;
  const $4 = lookup$47(self.v.p.v, self.v.module, $b.String_asStr($rt.idx(segments, 0n).name));
  m$5: {
    if (($4.$tag === "Some" && ($4.$.$tag === "Def"))) {
      const d = $4.$.$;
      {
        const params = clone$73($rt.idx(self.v.p.v.defs, d).params);
        const args = { v: $b.Vec_new() };
        for (const $6 of $rt.items(params)) {
          const g = $6;
          const $7 = args;
          let $8;
          const $9 = g.kind;
          m$10: {
            if (($9.$tag === "Type")) {
              $8 = { $tag: "Ty", $: fresh$238(new $rt.FieldRef(self.v, "s")) };
              break m$10;
            }
            if (($9.$tag === "Region")) {
              const $11 = scope.elidedRegion;
              m$12: {
                if (($11.$tag === "Some")) {
                  const r = $11.$;
                  $8 = { $tag: "Region", $: clone$360(r) };
                  break m$12;
                }
                if (($11.$tag === "None")) {
                  $8 = { $tag: "Region", $: freshRegion$737(new $rt.FieldRef(self.v, "s")) };
                  break m$12;
                }
                $rt.unmatched($11);
              }
              break m$10;
            }
            if (($9.$tag === "Row")) {
              $8 = { $tag: "Row", $: freshEffs$41(new $rt.FieldRef(self.v, "s")) };
              break m$10;
            }
            if (($9.$tag === "Len")) {
              $8 = { $tag: "Len", $: freshLen$738(new $rt.FieldRef(self.v, "s")) };
              break m$10;
            }
            $rt.unmatched($9);
          }
          $b.Vec_push($7, $8);
        }
        return { $tag: "Named", $: [d, args.v] };
      }
      break m$5;
    }
    if (true) {
      {
        const msg = unknown$192(self.v.p.v, "type", $b.String_asStr($rt.idx(segments, 0n).name));
        err$108(self, $rt.copy(t.span), $b.String_asStr(msg));
        return { $tag: "Error" };
      }
      break m$5;
    }
    $rt.unmatched($4);
  }
}
function callFn$617(self, fid, fixed, recv, explicit, args, expected, e) {
  const span = $rt.copy(e.span);
  $b.HashMap_insert(new $rt.FieldRef(self.v.typed, "calls"), e.id, fid);
  let scheme = clone$22($rt.idx(self.v.p.v.fns, fid).scheme);
  const module = self.v.module;
  scheme.effects = { $tag: "Some", $: fnEffects$613(self.v.p, fid, module, $rt.copy(span)) };
  const inst = instantiate$614(self, scheme, $b.Vec_new(), true);
  const $1 = min$146($b.slice_len(inst.args), $b.slice_len(fixed));
  for (let i = 0n; i < $1; i++) {
    const $2 = [clone$290($rt.idx(inst.args, i)), clone$290($rt.idx(fixed, i))];
    m$3: {
      if ((($2[0].$tag === "Ty") && ($2[1].$tag === "Ty"))) {
        const a = $2[0].$;
        const f = $2[1].$;
        {
          try {
            unify$239(new $rt.FieldRef(self.v, "s"), a, f);
          } catch ($4) {
            if (!($4 instanceof $rt.Fail)) throw $4;
          }
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  const bounds = { v: $b.Vec_new() };
  const $5 = min$146($b.slice_len(scheme.tparams), $b.slice_len(inst.args));
  for (let i = $b.slice_len(fixed); i < $5; i++) {
    const $6 = $rt.idx(inst.args, i);
    m$7: {
      if (($6.$tag === "Ty")) {
        const t = $6.$;
        {
          for (const $8 of $rt.items($rt.idx(scheme.tparams, i).bounds)) {
            const b = $8;
            $b.Vec_push(bounds, [clone$23(t), substParams$230(b, scheme.tparams, inst.args)]);
          }
        }
        break m$7;
      }
      if (true) {
        {
        }
        break m$7;
      }
      $rt.unmatched($6);
    }
  }
  $b.Vec_push(new $rt.FieldRef(self.v, "pendingTargs"), { id: e.id, span: span, args: clone$197(inst.args), bounds: bounds.v });
  if (isTemplate$21(self.v.p.v, fid)) {
    $b.Vec_push(new $rt.FieldRef(self.v, "pendingSpecs"), [e.id, $rt.copy(span), fid, clone$197(inst.args)]);
  }
  const ownTypes = { v: $b.Vec_new() };
  const $9 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(scheme.tparams)));
  let $11;
  for (let $10 = $9.next(); !$10.done; $10 = $9.next($11)) {
    $11 = undefined;
    const $12 = $10.value.item;
    const i = $12[0];
    const g = $12[1];
    if (eq$33(g.kind, { $tag: "Type" })) {
      $b.Vec_push(ownTypes, i);
    }
  }
  if (($b.slice_len(explicit) > 0n)) {
    let $13;
    const $14 = new $rt.FieldRef($rt.idx(self.v.p.v.fns, fid), "implId");
    const $15 = $14.v;
    m$16: {
      if (($15.$tag === "Some")) {
        const i = new $rt.FieldRef($15, "$");
        $13 = $b.slice_len($rt.idx(self.v.p.v.impls, i.v).params);
        break m$16;
      }
      if (($15.$tag === "None")) {
        $13 = 0n;
        break m$16;
      }
      $rt.unmatched($15);
    }
    const implParams = $13;
    const own = { v: $b.Vec_new() };
    for (const $17 of $rt.items(ownTypes.v)) {
      const i = $17;
      if ((i >= implParams)) {
        $b.Vec_push(own, i);
      }
    }
    let $18;
    if (($b.slice_len(own.v) === 0n)) {
      $18 = clone$741(ownTypes.v);
    } else {
      {
        $18 = own.v;
      }
    }
    const targets = $18;
    const $19 = min$146($b.slice_len(targets), $b.slice_len(explicit));
    for (let k = 0n; k < $19; k++) {
      const $20 = $rt.idx(inst.args, $rt.idx(targets, k));
      m$21: {
        if (($20.$tag === "Ty")) {
          const v = $20.$;
          {
            let $22;
            try {
              unify$239(new $rt.FieldRef(self.v, "s"), clone$23(v), $rt.idx(explicit, k));
              $22 = true;
            } catch ($23) {
              if (!($23 instanceof $rt.Fail)) throw $23;
              $22 = false;
            }
            const ok = $22;
            if ((!ok)) {
              err$108(self, $rt.copy(span), "explicit type argument does not fit");
            }
          }
          break m$21;
        }
        if (true) {
          {
          }
          break m$21;
        }
        $rt.unmatched($20);
      }
    }
  }
  let $24;
  const $25 = resolve$109(self.v.s, inst.ret);
  m$26: {
    if (($25.$tag === "Var")) {
      $24 = true;
      break m$26;
    }
    if (true) {
      $24 = false;
      break m$26;
    }
    $rt.unmatched($25);
  }
  const retVar = $24;
  let $27 = retVar;
  if ($27) {
    let $28;
    const $29 = expected;
    m$30: {
      if (($29.$tag === "Some")) {
        const x = $29.$;
        const $31 = resolve$109(self.v.s, x);
        m$32: {
          if (($31.$tag === "Borrow" && $31.$[0] === false)) {
            $28 = true;
            break m$32;
          }
          if (true) {
            $28 = false;
            break m$32;
          }
          $rt.unmatched($31);
        }
        break m$30;
      }
      if (($29.$tag === "None")) {
        $28 = false;
        break m$30;
      }
      $rt.unmatched($29);
    }
    $27 = $28;
  }
  const lentVar = ($27 || ($b.Option_isSome(recv) && retVar));
  const $33 = expected;
  m$34: {
    if (($33.$tag === "Some")) {
      const x = $33.$;
      {
        if ((!lentVar)) {
          const ret = clone$23(inst.ret);
          if ((!tryUnify$237(self, ret, x))) {
            lends$116(self, ret, x);
          }
        }
      }
      break m$34;
    }
    if (true) {
      {
      }
      break m$34;
    }
    $rt.unmatched($33);
  }
  const params = { v: $b.Vec_new() };
  for (const $35 of $rt.items(inst.params)) {
    const t = $35[1];
    $b.Vec_push(params, clone$23(t));
  }
  const $36 = recv;
  m$37: {
    if (($36.$tag === "Some")) {
      const rt = $36.$[0];
      const rspan = $36.$[1];
      {
        if (($b.slice_len(params.v) === 0n)) {
          err$108(self, $rt.copy(rspan), "this function takes no receiver");
        } else {
          {
            const selfTy = $b.Vec_remove(params, 0n);
            coerce$44(self, rt, selfTy, $rt.copy(rspan));
          }
        }
      }
      break m$37;
    }
    if (true) {
      {
      }
      break m$37;
    }
    $rt.unmatched($36);
  }
  checkArgs$621(self, params.v, args, $rt.copy(span));
  const $38 = inst.effects;
  m$39: {
    if (($38.$tag === "Some")) {
      const eff = $38.$;
      {
        perform$437(self, eff, $rt.copy(span), e.id);
      }
      break m$39;
    }
    if (true) {
      {
      }
      break m$39;
    }
    $rt.unmatched($38);
  }
  return inst.ret;
}
function callOnType$618(self, ty, name, explicit, args, expected, e) {
  const $1 = ty;
  m$2: {
    if (($1.$tag === "Param")) {
      const sym = $1.$;
      {
        const $3 = $b.HashMap_get(self.v.bounds, sym.id);
        m$4: {
          if (($3.$tag === "Some")) {
            const bounds = $3.$;
            {
              const $5 = boundMethod$742(self.v.p.v, clone$35(bounds), name);
              m$6: {
                if (($5.$tag === "Some" && (($5.$[1].$tag === "Named")))) {
                  const fid = $5.$[0];
                  const bargs = $5.$[1].$[1];
                  {
                    const fixed = { v: [{ $tag: "Ty", $: clone$23(ty) }] };
                    for (const $7 of $rt.items(bargs)) {
                      const a = $7;
                      $b.Vec_push(fixed, clone$290(a));
                    }
                    return callFn$617(self, fid, fixed.v, { $tag: "None" }, explicit, args, expected, e);
                  }
                  break m$6;
                }
                if (true) {
                  {
                  }
                  break m$6;
                }
                $rt.unmatched($5);
              }
            }
            break m$4;
          }
          if (true) {
            {
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const ifaces = { v: $b.Vec_new() };
  const $8 = $b.Gen_each($b.HashMap_entries(self.v.p.v.ifaceFns));
  let $10;
  for (let $9 = $8.next(); !$9.done; $9 = $8.next($10)) {
    $10 = undefined;
    const $11 = $9.value.item;
    const key = $11[0];
    const parts = $b.str_split(key, ":");
    if ((($b.slice_len(parts) === 2n) && ($rt.idx(parts, 1n) === name))) {
      const $12 = $b.parseInt($b.String_asStr($rt.idx(parts, 0n)));
      m$13: {
        if (($12.$tag === "Some")) {
          const d = $12.$;
          {
            $b.Vec_push(ifaces, $rt.wrap_usize(d));
          }
          break m$13;
        }
        if (true) {
          {
          }
          break m$13;
        }
        $rt.unmatched($12);
      }
    }
  }
  sort$743(ifaces);
  for (const $14 of $rt.items(ifaces.v)) {
    const d = $14;
    const concrete = zonk$134(self.v.s, ty);
    const $15 = resolveImpl$287(self.v.p.v, d, concrete);
    m$16: {
      if (($15.$tag === "Some")) {
        const imp = $15.$[0];
        const binds = $15.$[1];
        {
          const template = isTemplateImpl$288(self.v.p.v, imp);
          let $17;
          if (template) {
            $17 = implMethod$492(self.v.p.v, imp, name);
          } else {
            {
              $17 = methodFor$744(self.v.p.v, imp, name, binds);
            }
          }
          const fid = $17;
          const $18 = fid;
          m$19: {
            if (($18.$tag === "Some")) {
              const f = $18.$;
              {
                let $20;
                if (template) {
                  $20 = [{ $tag: "Ty", $: clone$23(concrete) }];
                } else {
                  {
                    $20 = $b.Vec_new();
                  }
                }
                const fixed = $20;
                return callFn$617(self, f, fixed, { $tag: "None" }, explicit, args, expected, e);
              }
              break m$19;
            }
            if (true) {
              {
              }
              break m$19;
            }
            $rt.unmatched($18);
          }
        }
        break m$16;
      }
      if (true) {
        {
        }
        break m$16;
      }
      $rt.unmatched($15);
    }
  }
  const shown = show$123(self.v, ty);
  err$108(self, $rt.copy(e.span), $b.String_asStr(("" + "`" + shown + "` has no function `" + name + "`")));
  return { $tag: "Error" };
}
function callStatic$619(self, def, name, explicit, args, expected, e) {
  const $1 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, def), "kind");
  const $2 = $1.v;
  m$3: {
    if (($2.$tag === "Effect")) {
      const ops = new $rt.FieldRef($2.$, "ops");
      {
        const $6 = find$745($b.slice_iter(ops.v), (($0$$4) => {
  {
    const $5 = $0$$4;
    const n = $5[0];
    return (n === name);
  }
        }));
        m$7: {
          if (($6.$tag === "Some")) {
            const op = $6.$[1];
            {
              const o = clone$22(op);
              return callOp$746(self, def, o, args, expected, e);
            }
            break m$7;
          }
          if (true) {
            {
            }
            break m$7;
          }
          $rt.unmatched($6);
        }
      }
      break m$3;
    }
    if (true) {
      {
      }
      break m$3;
    }
    $rt.unmatched($2);
  }
  let candidate = { $tag: "None" };
  for (const $8 of $rt.items(self.v.p.v.impls)) {
    const imp = $8;
    let $9;
    const $10 = imp.target;
    m$11: {
      if (($10.$tag === "Named")) {
        const d = $10.$[0];
        $9 = (d === def);
        break m$11;
      }
      if (true) {
        $9 = false;
        break m$11;
      }
      $rt.unmatched($10);
    }
    const forDef = $9;
    if ((forDef && isNone$747(imp.iface))) {
      for (const $12 of $rt.items(imp.methods)) {
        const f = $12;
        if (((($rt.idx(self.v.p.v.fns, f).name === name) && (!hasSelf$748(self.v, f))) && isNone$86(candidate))) {
          candidate = { $tag: "Some", $: f };
        }
      }
    }
  }
  const $13 = candidate;
  m$14: {
    if (($13.$tag === "Some")) {
      const fid = $13.$;
      return callFn$617(self, fid, $b.Vec_new(), { $tag: "None" }, explicit, args, expected, e);
      break m$14;
    }
    if (($13.$tag === "None")) {
      {
        const gargs = { v: $b.Vec_new() };
        for (const $15 of $rt.items(clone$73($rt.idx(self.v.p.v.defs, def).params))) {
          const g = $15;
          const $16 = gargs;
          let $17;
          const $18 = g.kind;
          m$19: {
            if (($18.$tag === "Type")) {
              $17 = { $tag: "Ty", $: fresh$238(new $rt.FieldRef(self.v, "s")) };
              break m$19;
            }
            if (true) {
              $17 = paramArg$291(g);
              break m$19;
            }
            $rt.unmatched($18);
          }
          $b.Vec_push($16, $17);
        }
        const ty = normalize$113(self.v, { $tag: "Named", $: [def, gargs.v] });
        return callOnType$618(self, ty, name, explicit, args, expected, e);
      }
      break m$14;
    }
    $rt.unmatched($13);
  }
}
function callMethod$620(self, recv, rspan, name, explicit, args, expected, e) {
  const $1 = boundMethodOf$749(self, recv, name);
  m$2: {
    if (($1.$tag === "Some")) {
      const fid = $1.$[0];
      const fixed = $1.$[1];
      {
        return callFn$617(self, fid, fixed, { $tag: "Some", $: [clone$23(recv), $rt.copy(rspan)] }, explicit, args, expected, e);
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const $3 = findMethod$625(self, recv, name);
  m$4: {
    if (($3.$tag === "Some")) {
      const fid = $3.$;
      {
        return callFn$617(self, fid, $b.Vec_new(), { $tag: "Some", $: [clone$23(recv), $rt.copy(rspan)] }, explicit, args, expected, e);
      }
      break m$4;
    }
    if (true) {
      {
      }
      break m$4;
    }
    $rt.unmatched($3);
  }
  const shown = show$123(self.v, recv);
  if (!eq$234(resolve$109(self.v.s, recv), { $tag: "Error" })) {
    const derived = [["clone", "Clone"], ["eq", "Eq"], ["cmp", "Ord"], ["hash", "Hash"], ["show", "Show"]];
    let hint = $b.String_new();
    const $5 = strip$124(self.v, recv);
    m$6: {
      if (($5.$tag === "Named")) {
        const d = $5.$[0];
        {
          const $9 = find$750($b.slice_iter(derived), (($0$$7) => {
  {
    const $8 = $rt.copy($0$$7);
    const m = $8[0];
    return (m === name);
  }
          }));
          m$10: {
            if (($9.$tag === "Some")) {
              const iface = $9.$[1];
              {
                let $11;
                const $12 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, d), "kind");
                const $13 = $12.v;
                m$14: {
                  if ((($13.$tag === "Struct" && ($13.$.fields.$tag === "Some")) || ($13.$tag === "Enum"))) {
                    $11 = true;
                    break m$14;
                  }
                  if (true) {
                    $11 = false;
                    break m$14;
                  }
                  $rt.unmatched($13);
                }
                const nominal = $11;
                if ((nominal && (!$rt.idx(self.v.p.v.modules, $rt.idx(self.v.p.v.defs, d).module).isStd))) {
                  const n = $b.String_clone($rt.idx(self.v.p.v.defs, d).name);
                  hint = ("" + ": `" + n + "` does not implement `" + iface + "`; ask for it with `impl " + iface + " for " + n + ";`");
                }
              }
              break m$10;
            }
            if (true) {
              {
              }
              break m$10;
            }
            $rt.unmatched($9);
          }
        }
        break m$6;
      }
      if (true) {
        {
        }
        break m$6;
      }
      $rt.unmatched($5);
    }
    err$108(self, $rt.copy(e.span), $b.String_asStr(("" + "no method `" + name + "` on `" + shown + "`" + hint)));
  }
  return { $tag: "Error" };
}
function checkArgs$621(self, params, args, span) {
  if (($b.slice_len(params) !== $b.slice_len(args))) {
    err$108(self, $rt.copy(span), $b.String_asStr(("" + "expected " + String($b.slice_len(params)) + " arguments, found " + String($b.slice_len(args)))));
  }
  const $1 = min$146($b.slice_len(params), $b.slice_len(args));
  for (let i = 0n; i < $1; i++) {
    ensureAssocs$751(self, $rt.idx(params, i));
    const p = normalize$113(self.v, $rt.idx(params, i));
    check$428(self, $rt.idx(args, i), p);
  }
  return undefined;
}
function eq$622(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Shared") && ($1[1].$tag === "Shared"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Mut") && ($1[1].$tag === "Mut"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Once") && ($1[1].$tag === "Once"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eq$623(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "None") && ($1[1].$tag === "None"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Some") && ($1[1].$tag === "Some"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$609(a, b);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function findIndex$624(self, test) {
  let i = 0n;
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: i };
    }
    i = $rt.usize(i + 1n);
  }
  return { $tag: "None" };
}
function findMethod$625(self, recv, name) {
  const $1 = $b.slice_len(self.v.p.v.fns);
  for (let f = 0n; f < $1; f++) {
    const implId = $rt.idx(self.v.p.v.fns, f).implId;
    let $2 = ($rt.idx(self.v.p.v.fns, f).name === name);
    if ($2) {
      let $3;
      const $4 = implId;
      m$5: {
        if (($4.$tag === "Some")) {
          const i = $4.$;
          $3 = (!isBlanket$658(self.v.p.v, i));
          break m$5;
        }
        if (($4.$tag === "None")) {
          $3 = false;
          break m$5;
        }
        $rt.unmatched($4);
      }
      $2 = $3;
    }
    const isCandidate = (($2 && hasSelf$748(self.v, f)) && (!$b.HashMap_has(self.v.p.v.specOf, f)));
    if ((!isCandidate)) {
      continue;
    }
    let scheme = clone$22($rt.idx(self.v.p.v.fns, f).scheme);
    scheme.effects = { $tag: "None" };
    const snap = clone$114(self.v.s);
    const inst = instantiate$614(self, scheme, $b.Vec_new(), false);
    const selfTy = clone$23($rt.idx($rt.idx(inst.params, 0n), 1n));
    const fits = lends$116(self, recv, selfTy);
    restore$122(new $rt.FieldRef(self.v, "s"), snap);
    if (fits) {
      return { $tag: "Some", $: f };
    }
  }
  const r = zonk$134(self.v.s, recv);
  const ifaces = { v: $b.Vec_new() };
  const $6 = $b.Gen_each($b.HashMap_entries(self.v.p.v.ifaceFns));
  let $8;
  for (let $7 = $6.next(); !$7.done; $7 = $6.next($8)) {
    $8 = undefined;
    const $9 = $7.value.item;
    const key = $9[0];
    const parts = $b.str_split(key, ":");
    if ((($b.slice_len(parts) === 2n) && ($rt.idx(parts, 1n) === name))) {
      const $10 = $b.parseInt($b.String_asStr($rt.idx(parts, 0n)));
      m$11: {
        if (($10.$tag === "Some")) {
          const d = $10.$;
          {
            $b.Vec_push(ifaces, $rt.wrap_usize(d));
          }
          break m$11;
        }
        if (true) {
          {
          }
          break m$11;
        }
        $rt.unmatched($10);
      }
    }
  }
  sort$743(ifaces);
  for (const $12 of $rt.items(ifaces.v)) {
    const d = $12;
    const $13 = resolveImpl$287(self.v.p.v, d, r);
    m$14: {
      if (($13.$tag === "Some")) {
        const imp = $13.$[0];
        {
          if (isBlanket$658(self.v.p.v, imp)) {
            return implMethod$492(self.v.p.v, imp, name);
          }
        }
        break m$14;
      }
      if (true) {
        {
        }
        break m$14;
      }
      $rt.unmatched($13);
    }
  }
  return { $tag: "None" };
}
function unbox$626(self, t) {
  const $1 = resolve$109(self.s, t);
  m$2: {
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const inner = $1.$[1];
      const $3 = boxed$752(self, inner);
      m$4: {
        if (($3.$tag === "Some")) {
          const x = $3.$;
          return unbox$626(self, { $tag: "Borrow", $: [m, $b.Box_new(x)] });
          break m$4;
        }
        if (($3.$tag === "None")) {
          return { $tag: "Borrow", $: [m, inner] };
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (true) {
      const other = $1;
      const $5 = boxed$752(self, other);
      m$6: {
        if (($5.$tag === "Some")) {
          const x = $5.$;
          return unbox$626(self, { $tag: "Borrow", $: [false, $b.Box_new(x)] });
          break m$6;
        }
        if (($5.$tag === "None")) {
          return other;
          break m$6;
        }
        $rt.unmatched($5);
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function unmovablePlace$627(self, e) {
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "Ident")) {
      const $3 = typeOf$753(self, e);
      m$4: {
        if (($3.$tag === "Some" && ($3.$.$tag === "Borrow"))) {
          const m = $3.$.$[0];
          return { $tag: "Some", $: m };
          break m$4;
        }
        if (true) {
          return { $tag: "None" };
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      const $5 = typeOf$753(self, target);
      m$6: {
        if (($5.$tag === "Some" && ($5.$.$tag === "Borrow"))) {
          const m = $5.$.$[0];
          let $7 = m;
          if ($7) {
            let $8;
            const $9 = unmovablePlace$627(self, target);
            m$10: {
              if (($9.$tag === "Some")) {
                const x = $9.$;
                $8 = x;
                break m$10;
              }
              if (($9.$tag === "None")) {
                $8 = true;
                break m$10;
              }
              $rt.unmatched($9);
            }
            $7 = $8;
          }
          return { $tag: "Some", $: $7 };
          break m$6;
        }
        if (true) {
          return unmovablePlace$627(self, target);
          break m$6;
        }
        $rt.unmatched($5);
      }
      break m$2;
    }
    if (($1.$tag === "Index")) {
      const target = $1.$.target;
      const $11 = typeOf$753(self, target);
      m$12: {
        if (($11.$tag === "Some" && ($11.$.$tag === "Tuple"))) {
          return unmovablePlace$627(self, target);
          break m$12;
        }
        if (($11.$tag === "Some" && ($11.$.$tag === "Borrow"))) {
          const m = $11.$.$[0];
          let $13 = m;
          if ($13) {
            let $14;
            const $15 = unmovablePlace$627(self, target);
            m$16: {
              if (($15.$tag === "Some")) {
                const x = $15.$;
                $14 = x;
                break m$16;
              }
              if (($15.$tag === "None")) {
                $14 = true;
                break m$16;
              }
              $rt.unmatched($15);
            }
            $13 = $14;
          }
          return { $tag: "Some", $: $13 };
          break m$12;
        }
        if (($11.$tag === "Some" && ($11.$.$tag === "Slice"))) {
          return { $tag: "Some", $: false };
          break m$12;
        }
        if (true) {
          let $17;
          const $18 = unmovablePlace$627(self, target);
          m$19: {
            if (($18.$tag === "Some")) {
              const m = $18.$;
              $17 = m;
              break m$19;
            }
            if (($18.$tag === "None")) {
              $17 = false;
              break m$19;
            }
            $rt.unmatched($18);
          }
          return { $tag: "Some", $: $17 };
          break m$12;
        }
        $rt.unmatched($11);
      }
      break m$2;
    }
    if (true) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function wholeTags$628(p, out) {
  const $1 = p.kind;
  m$2: {
    if (($1.$tag === "Tag")) {
      const name = $1.$.name;
      const args = $1.$.args;
      {
        let $3;
        const $4 = args;
        m$5: {
          if (($4.$tag === "None")) {
            $3 = true;
            break m$5;
          }
          if (($4.$tag === "Tuple")) {
            const ps = $4.$;
            $3 = every$755($b.slice_iter(ps), ((q) => {
  return irrefutable$754(q);
            }));
            break m$5;
          }
          if (($4.$tag === "Record")) {
            const fs = $4.$;
            $3 = every$756($b.slice_iter(fs), (($0$$6) => {
  {
    const $7 = $0$$6;
    const q = $7[1];
    const $8 = q;
    m$9: {
      if (($8.$tag === "Some")) {
        const x = $8.$;
        return irrefutable$754(x);
        break m$9;
      }
      if (($8.$tag === "None")) {
        return true;
        break m$9;
      }
      $rt.unmatched($8);
    }
  }
            }));
            break m$5;
          }
          $rt.unmatched($4);
        }
        const whole = $3;
        if (whole) {
          $b.Vec_push(out, $b.String_clone(name));
          return undefined;
        }
      }
      break m$2;
    }
    if (($1.$tag === "Or")) {
      const ps = $1.$;
      {
        for (const $10 of $rt.items(ps)) {
          const q = $10;
          wholeTags$628(q, out);
        }
        return undefined;
      }
      break m$2;
    }
    if (true) {
      {
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function withoutTags$629(self, t, tags) {
  const $1 = resolve$109(self.s, t);
  m$2: {
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const inner = $1.$[1];
      const $3 = withoutTags$629(self, inner, tags);
      m$4: {
        if (($3.$tag === "Some")) {
          const u = $3.$;
          return { $tag: "Some", $: { $tag: "Borrow", $: [m, $b.Box_new(u)] } };
          break m$4;
        }
        if (($3.$tag === "None")) {
          return { $tag: "None" };
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (($1.$tag === "Union")) {
      const r = $1.$;
      {
        const x = expandRow$125(self.s, r);
        if (!eq$120(x.tail, { $tag: "Closed" })) {
          return { $tag: "None" };
        }
        const labels = { v: $b.Vec_new() };
        for (const $5 of $rt.items(x.labels)) {
          const k = $5[0];
          const v = $5[1];
          if ((!some$450($b.slice_iter(tags), ((t$$6) => {
  return eq$6(t$$6, k);
          })))) {
            $b.Vec_push(labels, [$b.String_clone(k), clone$23(v)]);
          }
        }
        return { $tag: "Some", $: { $tag: "Union", $: { labels: labels.v, tail: { $tag: "Closed" } } } };
      }
      break m$2;
    }
    if (true) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$630(self) {
  {
    const v = [clone$23($rt.idx(self, 0n)), clone$94($rt.idx(self, 1n))];
    return v;
  }
}
function enterHandler$631(self, eff) {
  const outer = clone$40(self.v.allowed);
  let row = expandEffs$105(self.v.s, outer);
  $b.Vec_insert(new $rt.FieldRef(row, "effs"), 0n, clone$106(eff));
  self.v.allowed = row;
  $b.Vec_push(new $rt.FieldRef(self.v, "performed"), $b.Vec_new());
  return outer;
}
function leaveHandler$632(self, eff, outer) {
  let $1;
  const $2 = $b.Vec_pop(new $rt.FieldRef(self.v, "performed"));
  m$3: {
    if (($2.$tag === "Some")) {
      const v = $2.$;
      $1 = v;
      break m$3;
    }
    if (($2.$tag === "None")) {
      $1 = $b.Vec_new();
      break m$3;
    }
    $rt.unmatched($2);
  }
  const inside = $1;
  self.v.allowed = outer;
  const regionDef = known$104(self.v, "Region");
  if (($b.slice_len(self.v.performed) > 0n)) {
    const last = $rt.usize($b.slice_len(self.v.performed) - 1n);
    for (const $4 of $rt.items(inside)) {
      const x = $4;
      if (((x.def !== eff.def) || ((x.def === regionDef) && (!regionsEqual$259(self.v.s, x.regions, eff.regions))))) {
        $b.Vec_push($rt.indexRef(self.v.performed, last), clone$106(x));
      }
    }
    return undefined;
  }
}
function clone$633(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$757(x));
  }
  return v.v;
}
function first$634(self) {
  if (($b.slice_len(self) === 0n)) {
    return { $tag: "None" };
  } else {
    {
      return { $tag: "Some", $: $rt.idx(self, 0n) };
    }
  }
}
function clone$635(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$34(x));
  }
  return v.v;
}
function settleRegions$636(self, sym, result) {
  const pending = $b.replace(new $rt.FieldRef(self.v, "pendingRegions"), $b.Vec_new());
  for (const $1 of $rt.items(pending)) {
    const v = $1[0];
    const cs = $1[1];
    const candidates = { v: clone$635(cs) };
    let $2;
    const $3 = resolveRegion$130(self.v.s, { $tag: "Var", $: v });
    m$4: {
      if (($3.$tag === "Var")) {
        $2 = true;
        break m$4;
      }
      if (true) {
        $2 = false;
        break m$4;
      }
      $rt.unmatched($3);
    }
    const undecided = $2;
    if ((!undecided)) {
      continue;
    }
    let $5;
    const $6 = first$131(candidates.v);
    m$7: {
      if (($6.$tag === "Some")) {
        const c = $6.$;
        $5 = !eq$262(c, sym);
        break m$7;
      }
      if (($6.$tag === "None")) {
        $5 = true;
        break m$7;
      }
      $rt.unmatched($6);
    }
    if ($5) {
      $b.Vec_push(new $rt.FieldRef(self.v, "pendingRegions"), [v, candidates.v]);
      continue;
    }
    const snap = clone$114(self.v.s);
    try {
      unifyRegion$132(new $rt.FieldRef(self.v, "s"), { $tag: "Var", $: v }, { $tag: "Param", $: clone$34(sym) });
    } catch ($8) {
      if (!($8 instanceof $rt.Fail)) throw $8;
    }
    if ((escapes$758(self.v, sym, result) && ($b.slice_len(candidates.v) > 1n))) {
      restore$122(new $rt.FieldRef(self.v, "s"), snap);
      $b.Vec_remove(candidates, 0n);
      $b.Vec_push(new $rt.FieldRef(self.v, "pendingRegions"), [v, candidates.v]);
    }
  }
  return undefined;
}
function mentionsRegion$637(t, sym) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Named")) {
      const args = $1.$[1];
      return some$292($b.slice_iter(args), ((a) => {
  const $3 = a;
  m$4: {
    if (($3.$tag === "Ty")) {
      const x = $3.$;
      return mentionsRegion$637(x, sym);
      break m$4;
    }
    if (($3.$tag === "Region" && ($3.$.$tag === "Param"))) {
      const s = $3.$.$;
      return eq$262(s, sym);
      break m$4;
    }
    if (true) {
      return false;
      break m$4;
    }
    $rt.unmatched($3);
  }
      }));
      break m$2;
    }
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      return some$294($b.slice_iter(r.labels), (($0$$5) => {
  {
    const $6 = $0$$5;
    const x = $6[1];
    return mentionsRegion$637(x, sym);
  }
      }));
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      return some$293($b.slice_iter(ts), ((x) => {
  return mentionsRegion$637(x, sym);
      }));
      break m$2;
    }
    if ((($1.$tag === "Array") || ($1.$tag === "Slice") || ($1.$tag === "Borrow"))) {
      let x;
      if (($1.$tag === "Array")) { x = $1.$[0]; }
      else if (($1.$tag === "Slice")) { x = $1.$; }
      else if (($1.$tag === "Borrow")) { x = $1.$[1]; }
      return mentionsRegion$637(x, sym);
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      return (some$293($b.slice_iter(f.params), ((x) => {
  return mentionsRegion$637(x, sym);
      })) || mentionsRegion$637(f.ret, sym));
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function first$638(self) {
  if (($b.slice_len(self) === 0n)) {
    return { $tag: "None" };
  } else {
    {
      return { $tag: "Some", $: $rt.idx(self, 0n) };
    }
  }
}
function handleParts$639(self, body, eff, arms, result, contRow) {
  const outer = enterHandler$631(self, eff);
  const t = block$43(self, body, { $tag: "Some", $: clone$23(result) });
  leaveHandler$632(self, eff, outer);
  coerce$44(self, t, result, $rt.copy(body.span));
  let $1;
  const $2 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, eff.def), "kind");
  const $3 = $2.v;
  m$4: {
    if (($3.$tag === "Effect")) {
      const ops = new $rt.FieldRef($3.$, "ops");
      $1 = clone$759(ops.v);
      break m$4;
    }
    if (true) {
      return;
      break m$4;
    }
    $rt.unmatched($3);
  }
  const ops = $1;
  const effParams = clone$73($rt.idx(self.v.p.v.defs, eff.def).params);
  const effArgs = { v: $b.Vec_new() };
  let ri = 0n;
  let ti = 0n;
  for (const $5 of $rt.items(effParams)) {
    const g = $5;
    if (eq$33(g.kind, { $tag: "Region" })) {
      const $6 = effArgs;
      let $7;
      const $8 = get$760(eff.regions, ri);
      m$9: {
        if (($8.$tag === "Some")) {
          const r = $8.$;
          $7 = clone$360(r);
          break m$9;
        }
        if (($8.$tag === "None")) {
          $7 = { $tag: "Heap" };
          break m$9;
        }
        $rt.unmatched($8);
      }
      $b.Vec_push($6, { $tag: "Region", $: $7 });
      ri = $rt.usize(ri + 1n);
    } else {
      {
        const $10 = effArgs;
        let $11;
        const $12 = get$761(eff.args, ti);
        m$13: {
          if (($12.$tag === "Some")) {
            const t$$14 = $12.$;
            $11 = clone$23(t$$14);
            break m$13;
          }
          if (($12.$tag === "None")) {
            $11 = { $tag: "Error" };
            break m$13;
          }
          $rt.unmatched($12);
        }
        $b.Vec_push($10, { $tag: "Ty", $: $11 });
        ti = $rt.usize(ti + 1n);
      }
    }
  }
  for (const $15 of $rt.items(arms)) {
    const arm = $15;
    let $16;
    const $19 = find$745($b.slice_iter(ops), (($0$$17) => {
  {
    const $18 = $0$$17;
    const n = $18[0];
    return eq$6(n, arm.op.name);
  }
    }));
    m$20: {
      if (($19.$tag === "Some")) {
        const o = $19.$[1];
        $16 = clone$22(o);
        break m$20;
      }
      if (($19.$tag === "None")) {
        {
          const ename = $b.String_clone($rt.idx(self.v.p.v.defs, eff.def).name);
          err$108(self, $rt.copy(arm.op.span), $b.String_asStr(("" + "`" + ename + "` has no operation `" + arm.op.name + "`")));
          continue;
          $16 = undefined;
        }
        break m$20;
      }
      $rt.unmatched($19);
    }
    const op = $16;
    const params = { v: $b.Vec_new() };
    for (const $21 of $rt.items(op.params)) {
      const n = $21[0];
      const t$$22 = $21[1];
      $b.Vec_push(params, [$b.String_clone(n), substParams$230(t$$22, effParams, effArgs.v)]);
    }
    const opRet = substParams$230(op.ret, effParams, effArgs.v);
    $b.Vec_push(new $rt.FieldRef(self.v, "scopes"), $b.HashMap_new());
    const $23 = min$146($b.slice_len(arm.params), $b.slice_len(params.v));
    for (let i = 0n; i < $23; i++) {
      declare$42(self, $b.String_asStr($rt.idx(arm.params, i).name), clone$23($rt.idx($rt.idx(params.v, i), 1n)));
    }
    const $24 = arm.resumes;
    m$25: {
      if (($24.$tag === "Some")) {
        const k = $24.$;
        {
          const cont = { $tag: "Named", $: [known$104(self.v, "Cont"), [{ $tag: "Ty", $: opRet }, { $tag: "Ty", $: clone$23(result) }, { $tag: "Row", $: clone$40(contRow) }]] };
          declare$42(self, $b.String_asStr(k.name), cont);
        }
        break m$25;
      }
      if (true) {
        {
        }
        break m$25;
      }
      $rt.unmatched($24);
    }
    const at = block$43(self, arm.body, { $tag: "Some", $: clone$23(result) });
    coerce$44(self, at, result, $rt.copy(arm.body.span));
    $b.Vec_pop(new $rt.FieldRef(self.v, "scopes"));
  }
  return undefined;
}
function ownRow$640(self, inside, around0) {
  const around = zonkEffs$119(self.v.s, around0);
  const failDef = known$104(self.v, "Fail");
  const effs = { v: $b.Vec_new() };
  const fails = { v: $b.Vec_new() };
  let anyFail = false;
  for (const $1 of $rt.items(inside)) {
    const x = $1;
    const z = zonkEffs$119(self.v.s, { effs: [clone$106(x)], tail: { $tag: "Closed" } });
    let $2;
    const $3 = last$762(z.effs);
    m$4: {
      if (($3.$tag === "Some")) {
        const e = $3.$;
        $2 = clone$106(e);
        break m$4;
      }
      if (($3.$tag === "None")) {
        continue;
        break m$4;
      }
      $rt.unmatched($3);
    }
    const e = $2;
    if ((!some$500($b.slice_iter(around.effs), ((c) => {
  return ((c.def === e.def) && regionsEqual$259(self.v.s, c.regions, e.regions));
    })))) {
      continue;
    }
    if ((e.def === failDef)) {
      anyFail = true;
      const $5 = first$263(e.args);
      m$6: {
        if (($5.$tag === "Some")) {
          const t = $5.$;
          {
            const $7 = zonk$134(self.v.s, t);
            m$8: {
              if (($7.$tag === "Union")) {
                const r = $7.$;
                {
                  for (const $9 of $rt.items(expandRow$125(self.v.s, r).labels)) {
                    const k = $9[0];
                    const v = $9[1];
                    labelSet$184(fails, $b.String_asStr(k), clone$23(v));
                  }
                }
                break m$8;
              }
              if (true) {
                {
                }
                break m$8;
              }
              $rt.unmatched($7);
            }
          }
          break m$6;
        }
        if (true) {
          {
          }
          break m$6;
        }
        $rt.unmatched($5);
      }
    } else {
      if ((!some$500($b.slice_iter(effs.v), ((y) => {
  return eq$763(y, e);
      })))) {
        $b.Vec_push(effs, e);
      }
    }
  }
  if (anyFail) {
    $b.Vec_push(effs, { def: failDef, regions: $b.Vec_new(), args: [{ $tag: "Union", $: { labels: fails.v, tail: { $tag: "Closed" } } }] });
  }
  return { effs: effs.v, tail: { $tag: "Closed" } };
}
function bindEffs$641(self, v, row) {
  const $1 = self.v.effs;
  $1[$rt.at($1, $rt.wrap_usize(v))] = { $tag: "Some", $: row };
  return undefined;
}
function kind$642(self, v) {
  return $rt.idx($rt.idx(self.tys, $rt.wrap_usize(v)), 1n);
}
function eq$643(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Any") && ($1[1].$tag === "Any"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Int") && ($1[1].$tag === "Int"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Float") && ($1[1].$tag === "Float"))) {
      return true;
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function occurs$644(self, v, t) {
  const $1 = resolve$109(self, t);
  m$2: {
    if (($1.$tag === "Var")) {
      const w = $1.$;
      return (w === v);
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const args = $1.$[1];
      return some$292($b.slice_iter(args), ((a) => {
  const $3 = a;
  m$4: {
    if (($3.$tag === "Ty")) {
      const x = $3.$;
      return occurs$644(self, v, x);
      break m$4;
    }
    if (true) {
      return false;
      break m$4;
    }
    $rt.unmatched($3);
  }
      }));
      break m$2;
    }
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      return some$294($b.slice_iter(expandRow$125(self, r).labels), (($0$$5) => {
  {
    const $6 = $0$$5;
    const x = $6[1];
    return occurs$644(self, v, x);
  }
      }));
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      return some$293($b.slice_iter(ts), ((x) => {
  return occurs$644(self, v, x);
      }));
      break m$2;
    }
    if ((($1.$tag === "Array") || ($1.$tag === "Slice") || ($1.$tag === "Borrow") || ($1.$tag === "Assoc"))) {
      let x;
      if (($1.$tag === "Array")) { x = $1.$[0]; }
      else if (($1.$tag === "Slice")) { x = $1.$; }
      else if (($1.$tag === "Borrow")) { x = $1.$[1]; }
      else if (($1.$tag === "Assoc")) { x = $1.$[0]; }
      return occurs$644(self, v, x);
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      return (some$293($b.slice_iter(f.params), ((x) => {
  return occurs$644(self, v, x);
      })) || occurs$644(self, v, f.ret));
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function cmp$645(self, other) {
  if ((self < other)) {
    return { $tag: "Less" };
  } else {
    if ((self === other)) {
      return { $tag: "Equal" };
    } else {
      {
        return { $tag: "Greater" };
      }
    }
  }
}
function clone$646(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Any")) {
      return { $tag: "Any" };
      break m$2;
    }
    if (($1.$tag === "Int")) {
      return { $tag: "Int" };
      break m$2;
    }
    if (($1.$tag === "Float")) {
      return { $tag: "Float" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$647(self) {
  {
    return { args: clone$764(self.args), name: $b.String_clone(self.name) };
  }
}
function clone$648(self) {
  {
    return { args: clone$764(self.args), name: clone$223(self.name) };
  }
}
function clone$649(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$274(x));
  }
  return v.v;
}
function clone$650(self) {
  {
    return { fields: clone$765(self.fields), name: clone$566(self.name) };
  }
}
function cmp$651(self, other) {
  return cmp$358($b.String_asStr(self), $b.String_asStr(other));
}
function sort$652(self) {
  return $b.slice_sortBy(self, ((a, b) => {
  return cmp$651(a, b);
  }));
}
function clone$653(self) {
  {
    const v = [clone$471($rt.idx(self, 0n)), clone$470($rt.idx(self, 1n))];
    return v;
  }
}
function clone$654(self) {
  {
    const v = [clone$471($rt.idx(self, 0n)), clone$766($rt.idx(self, 1n))];
    return v;
  }
}
function substParamsOf$655(p, d, t, args) {
  return substParams$230(t, $rt.idx(p.defs, d).params, args);
}
function writeArg$656(a, names, out) {
  const $1 = a;
  m$2: {
    if (($1.$tag === "Ty")) {
      const t = $1.$;
      return writeTy$485(t, names, out);
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const r = $1.$;
      return writeRegion$459(r, out);
      break m$2;
    }
    if (($1.$tag === "Row")) {
      const r = $1.$;
      {
        $b.String_push(out, "[");
        writeEffs$267(r, names, out);
        $b.String_push(out, "]");
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Len")) {
      const l = $1.$;
      const $3 = l;
      m$4: {
        if (($3.$tag === "Known")) {
          const k = $3.$;
          return $b.String_push(out, ("" + String(k)));
          break m$4;
        }
        if (($3.$tag === "Var")) {
          const v = $3.$;
          return $b.String_push(out, ("" + "?" + String(v)));
          break m$4;
        }
        if (($3.$tag === "Param")) {
          const s = $3.$;
          return $b.String_push(out, s.name);
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function sendIn$657(self, t, sendParams, seen) {
  const $1 = t;
  m$2: {
    if ((($1.$tag === "Prim") || ($1.$tag === "Error"))) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      return every$297($b.slice_iter(ts), ((x) => {
  return sendIn$657(self, x, sendParams, seen);
      }));
      break m$2;
    }
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      return every$127($b.slice_iter(r.labels), (($0$$3) => {
  {
    const $4 = $0$$3;
    const x = $4[1];
    return sendIn$657(self, x, sendParams, seen);
  }
      }));
      break m$2;
    }
    if ((($1.$tag === "Array") || ($1.$tag === "Slice") || ($1.$tag === "Borrow"))) {
      let e;
      if (($1.$tag === "Array")) { e = $1.$[0]; }
      else if (($1.$tag === "Slice")) { e = $1.$; }
      else if (($1.$tag === "Borrow")) { e = $1.$[1]; }
      return sendIn$657(self, e, sendParams, seen);
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        if (defNamed$480(self, d, ["Gen", "Fiber", "Scope", "Cont"])) {
          return false;
        }
        if ((!insert$483(seen, keyTy$482(t)))) {
          return true;
        }
        let $5 = every$297($b.slice_iter(argTypes$494(args)), ((a) => {
  return sendIn$657(self, a, sendParams, seen);
        }));
        if ($5) {
          let $6;
          const $7 = components$484(self, d, args);
          m$8: {
            if (($7.$tag === "Some")) {
              const cs = $7.$;
              $6 = every$297($b.slice_iter(cs), ((c) => {
  return sendIn$657(self, c, sendParams, seen);
              }));
              break m$8;
            }
            if (($7.$tag === "None")) {
              $6 = true;
              break m$8;
            }
            $rt.unmatched($7);
          }
          $5 = $6;
        }
        return $5;
      }
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Param")) {
      const sym = $1.$;
      return includes$767(sendParams, sym.id);
      break m$2;
    }
    if ((($1.$tag === "Var") || ($1.$tag === "Assoc"))) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function isBlanket$658(self, imp) {
  const $1 = $rt.idx(self.impls, imp).target;
  m$2: {
    if (($1.$tag === "Param")) {
      const s = $1.$;
      return some$72($b.slice_iter($rt.idx(self.impls, imp).params), ((g) => {
  return (g.isComptime && (g.sym.id === s.id));
      }));
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function derives$659(self, iface, ty) {
  const $1 = ty;
  m$2: {
    if ((($1.$tag === "Prim") || ($1.$tag === "Record") || ($1.$tag === "Union") || ($1.$tag === "Tuple") || ($1.$tag === "Array") || ($1.$tag === "Slice"))) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      return deriveRequest$143(self, iface, d);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function matchTy$660(pat, ty, vars, binds) {
  const $1 = [pat, ty];
  m$2: {
    if ((($1[0].$tag === "Param"))) {
      const s = $1[0].$;
      if (includes$767(vars, s.id)) {
        const $3 = $b.HashMap_get(binds.v, s.id);
        m$4: {
          if (($3.$tag === "Some" && ($3.$.$tag === "Ty"))) {
            const prev = $3.$.$;
            return eq$234(prev, ty);
            break m$4;
          }
          if (true) {
            {
              $b.HashMap_insert(binds, s.id, { $tag: "Ty", $: clone$23(ty) });
              return true;
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
        break m$2;
      }
    }
    if ((($1[0].$tag === "Named") && ($1[1].$tag === "Named"))) {
      const a = $1[0].$[0];
      const xs = $1[0].$[1];
      const b = $1[1].$[0];
      const ys = $1[1].$[1];
      {
        if (((a !== b) || ($b.slice_len(xs) !== $b.slice_len(ys)))) {
          return false;
        }
        const $5 = $b.slice_len(xs);
        for (let i = 0n; i < $5; i++) {
          if ((!matchArg$768($rt.idx(xs, i), $rt.idx(ys, i), vars, binds))) {
            return false;
          }
        }
        return true;
      }
      break m$2;
    }
    if ((($1[0].$tag === "Tuple") && ($1[1].$tag === "Tuple"))) {
      const xs = $1[0].$;
      const ys = $1[1].$;
      {
        if (($b.slice_len(xs) !== $b.slice_len(ys))) {
          return false;
        }
        const $6 = $b.slice_len(xs);
        for (let i = 0n; i < $6; i++) {
          if ((!matchTy$660($rt.idx(xs, i), $rt.idx(ys, i), vars, binds))) {
            return false;
          }
        }
        return true;
      }
      break m$2;
    }
    if (((($1[0].$tag === "Record") && ($1[1].$tag === "Record")) || (($1[0].$tag === "Union") && ($1[1].$tag === "Union")))) {
      let a, b;
      if ((($1[0].$tag === "Record") && ($1[1].$tag === "Record"))) { a = $1[0].$; b = $1[1].$; }
      else if ((($1[0].$tag === "Union") && ($1[1].$tag === "Union"))) { a = $1[0].$; b = $1[1].$; }
      {
        if (($b.slice_len(a.labels) !== $b.slice_len(b.labels))) {
          return false;
        }
        const $7 = $b.slice_len(a.labels);
        for (let i = 0n; i < $7; i++) {
          if ((!eq$6($rt.idx($rt.idx(a.labels, i), 0n), $rt.idx($rt.idx(b.labels, i), 0n)) || (!matchTy$660($rt.idx($rt.idx(a.labels, i), 1n), $rt.idx($rt.idx(b.labels, i), 1n), vars, binds)))) {
            return false;
          }
        }
        return true;
      }
      break m$2;
    }
    if (((($1[0].$tag === "Array") && ($1[1].$tag === "Array")) || (($1[0].$tag === "Slice") && ($1[1].$tag === "Slice")))) {
      let x, y;
      if ((($1[0].$tag === "Array") && ($1[1].$tag === "Array"))) { x = $1[0].$[0]; y = $1[1].$[0]; }
      else if ((($1[0].$tag === "Slice") && ($1[1].$tag === "Slice"))) { x = $1[0].$; y = $1[1].$; }
      return matchTy$660(x, y, vars, binds);
      break m$2;
    }
    if ((($1[0].$tag === "Borrow") && ($1[1].$tag === "Borrow"))) {
      const m1 = $1[0].$[0];
      const x = $1[0].$[1];
      const m2 = $1[1].$[0];
      const y = $1[1].$[1];
      return ((m1 === m2) && matchTy$660(x, y, vars, binds));
      break m$2;
    }
    if (true) {
      return eq$234(pat, ty);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eraseRegions$661(t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        const out = { v: $b.Vec_new() };
        for (const $3 of $rt.items(args)) {
          const a = $3;
          const $4 = out;
          let $5;
          const $6 = a;
          m$7: {
            if (($6.$tag === "Region")) {
              $5 = { $tag: "Region", $: { $tag: "Heap" } };
              break m$7;
            }
            if (($6.$tag === "Ty")) {
              const x = $6.$;
              $5 = { $tag: "Ty", $: eraseRegions$661(x) };
              break m$7;
            }
            if (true) {
              const other = $6;
              $5 = clone$290(other);
              break m$7;
            }
            $rt.unmatched($6);
          }
          $b.Vec_push($4, $5);
        }
        return { $tag: "Named", $: [d, out.v] };
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $8 of $rt.items(ts)) {
          const x = $8;
          $b.Vec_push(out, eraseRegions$661(x));
        }
        return { $tag: "Tuple", $: out.v };
      }
      break m$2;
    }
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      {
        const labels = { v: $b.Vec_new() };
        for (const $9 of $rt.items(r.labels)) {
          const k = $9[0];
          const v = $9[1];
          $b.Vec_push(labels, [$b.String_clone(k), eraseRegions$661(v)]);
        }
        const row = { labels: labels.v, tail: clone$99(r.tail) };
        const $10 = t;
        m$11: {
          if (($10.$tag === "Record")) {
            return { $tag: "Record", $: row };
            break m$11;
          }
          if (true) {
            return { $tag: "Union", $: row };
            break m$11;
          }
          $rt.unmatched($10);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const e = $1.$[0];
      const l = $1.$[1];
      return { $tag: "Array", $: [$b.Box_new(eraseRegions$661(e)), clone$198(l)] };
      break m$2;
    }
    if (($1.$tag === "Slice")) {
      const e = $1.$;
      return { $tag: "Slice", $: $b.Box_new(eraseRegions$661(e)) };
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const e = $1.$[1];
      return { $tag: "Borrow", $: [m, $b.Box_new(eraseRegions$661(e))] };
      break m$2;
    }
    if (true) {
      const other = $1;
      return clone$23(other);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function writeKeyTail$662(t, out) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Closed")) {
      return $b.String_push(out, ".");
      break m$2;
    }
    if (($1.$tag === "Var")) {
      const v = $1.$;
      return $b.String_push(out, ("" + "v" + String(v)));
      break m$2;
    }
    if (($1.$tag === "Param")) {
      const s = $1.$;
      return $b.String_push(out, ("" + "p" + String(s.id)));
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function lentExpr$663(self, e, scopes) {
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "Ident")) {
      const n = $1.$;
      {
        if ((!isMutBorrow$508(exprTy$316(self.v, e.id)))) {
          lentName$769(self, $b.String_asStr(n), scopes);
          return undefined;
        }
      }
      break m$2;
    }
    if (($1.$tag === "BorrowMut")) {
      const x = $1.$;
      return lentExpr$663(self, x, scopes);
      break m$2;
    }
    if (true) {
      {
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function first$664(self) {
  if (($b.slice_len(self) === 0n)) {
    return { $tag: "None" };
  } else {
    {
      return { $tag: "Some", $: $rt.idx(self, 0n) };
    }
  }
}
function eq$665(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "None") && ($1[1].$tag === "None"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Some") && ($1[1].$tag === "Some"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$609(a, b);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function shown$666(self, x) {
  const v = value$313(self, x);
  const t = stripBorrow$317(exprTy$316(self.v, x.id));
  if (isString$770(self.v, t)) {
    return v;
  }
  const $1 = t;
  m$2: {
    if (($1.$tag === "Prim")) {
      const p = $1.$;
      if (isFloat$417(p)) {
        return ("" + "$rt.showFloat(" + v + ")");
      } else {
        {
          return ("" + "String(" + v + ")");
        }
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  let $3;
  const $4 = $b.HashMap_get(self.v.p.typed, self.v.fid);
  m$5: {
    if (($4.$tag === "Some")) {
      const typed = $4.$;
      const $6 = $b.HashMap_get(typed.shows, x.id);
      m$7: {
        if (($6.$tag === "Some")) {
          const s = $6.$;
          $3 = { $tag: "Some", $: clone$79(s) };
          break m$7;
        }
        if (($6.$tag === "None")) {
          $3 = { $tag: "None" };
          break m$7;
        }
        $rt.unmatched($6);
      }
      break m$5;
    }
    if (($4.$tag === "None")) {
      $3 = { $tag: "None" };
      break m$5;
    }
    $rt.unmatched($4);
  }
  const show = $3;
  const $8 = show;
  m$9: {
    if (($8.$tag === "Some")) {
      const f = $8.$[0];
      const args = $8.$[1];
      {
        const concrete = { v: $b.Vec_new() };
        for (const $10 of $rt.items(args)) {
          const a = $10;
          $b.Vec_push(concrete, substArg$501(a, self.v.map));
        }
        const c = callee$688(self, f, concrete.v, $rt.copy(x.span));
        const fname = calleeJs$771(self.v, c);
        return ("" + "$rt.shown(" + fname + ", " + v + ")");
      }
      break m$9;
    }
    if (($8.$tag === "None")) {
      return ("" + "$rt.show(" + v + ")");
      break m$9;
    }
    $rt.unmatched($8);
  }
}
function ident$667(self, n, e) {
  const $1 = local$311(self.v, n);
  m$2: {
    if (($1.$tag === "Some")) {
      const l = $1.$;
      {
        if (l.cell) {
          return ("" + l.js + ".v");
        } else {
          {
            return l.js;
          }
        }
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const $3 = lookup$47(self.v.p, self.v.module, n);
  m$4: {
    if (($3.$tag === "Some" && ($3.$.$tag === "Fn"))) {
      const fid = $3.$.$;
      {
        const args = callArgs$687(self.v, e.id);
        const c = callee$688(self, fid, args, $rt.copy(e.span));
        return calleeJs$771(self.v, c);
      }
      break m$4;
    }
    if (($3.$tag === "Some" && ($3.$.$tag === "Const"))) {
      const c = $3.$.$;
      return constant$772(self, c);
      break m$4;
    }
    if (true) {
      return fail$514(self.v, $rt.copy(e.span), ("" + "unknown name `" + n + "`"));
      break m$4;
    }
    $rt.unmatched($3);
  }
}
function obj$668(self, e) {
  return value$313(self, e);
}
function mangleField$669(n) {
  if (((n === "__proto__") || (n === "constructor"))) {
    return ("" + n + "$");
  } else {
    {
      return $b.str_toString(n);
    }
  }
}
function simpleOpt$670(e) {
  const $1 = e;
  m$2: {
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return simple$522(x);
      break m$2;
    }
    if (($1.$tag === "None")) {
      return true;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function call$671(self, e, callee, args, driven) {
  let $1;
  const $2 = $b.HashMap_get(self.v.p.typed, self.v.fid);
  m$3: {
    if (($2.$tag === "Some")) {
      const t = $2.$;
      const $4 = $b.HashMap_get(t.calls, e.id);
      m$5: {
        if (($4.$tag === "Some")) {
          const f = $4.$;
          $1 = { $tag: "Some", $: f };
          break m$5;
        }
        if (($4.$tag === "None")) {
          $1 = { $tag: "None" };
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$3;
    }
    if (($2.$tag === "None")) {
      $1 = { $tag: "None" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const fid = $1;
  const $6 = fid;
  m$7: {
    if (($6.$tag === "Some")) {
      const fid$$8 = $6.$;
      {
        const cargs = callArgs$687(self.v, e.id);
        const pmap = substMap$162($rt.idx(self.v.p.fns, fid$$8).scheme.tparams, cargs);
        const ptys = { v: $b.Vec_new() };
        for (const $9 of $rt.items($rt.idx(self.v.p.fns, fid$$8).scheme.params)) {
          const t = $9[1];
          $b.Vec_push(ptys, resolveAssoc$309(self.v, subst$308(t, pmap)));
        }
        let $10;
        const $11 = first$664($rt.idx(self.v.p.fns, fid$$8).scheme.params);
        m$12: {
          if (($11.$tag === "Some")) {
            const n = $11.$[0];
            $10 = (n === "self");
            break m$12;
          }
          if (($11.$tag === "None")) {
            $10 = false;
            break m$12;
          }
          $rt.unmatched($11);
        }
        const hasSelf = $10;
        const all = { v: $b.Vec_new() };
        if (hasSelf) {
          const $13 = callee.kind;
          m$14: {
            if (($13.$tag === "Field")) {
              const target = $13.$.target;
              $b.Vec_push(all, clone$60($b.Box_get(target)));
              break m$14;
            }
            if (true) {
              fail$514(self.v, $rt.copy(callee.span), "a method needs a receiver");
              break m$14;
            }
            $rt.unmatched($13);
          }
        }
        for (const $15 of $rt.items(args)) {
          const a = $15;
          $b.Vec_push(all, clone$60(a));
        }
        const vs = args$773(self, all.v, ptys.v);
        const c = callee$688(self, fid$$8, clone$197(cargs), $rt.copy(e.span));
        const suspends = calleeSuspends$774(self.v, c, fid$$8, cargs);
        let $16;
        const $17 = c;
        m$18: {
          if (($17.$tag === "Inst")) {
            const i = $17.$;
            $16 = $b.String_clone($rt.idx(self.v.insts, i).js);
            break m$18;
          }
          if (($17.$tag === "Builtin")) {
            const k = $17.$;
            {
              const yields = rowYields$775(self.v.p, substEffs$305(fnEffects$304(self.v, fid$$8), substMap$162($rt.idx(self.v.p.fns, fid$$8).scheme.tparams, cargs)));
              let $19;
              if ((suspends && (!yields))) {
                $19 = ("" + k + "$g");
              } else {
                {
                  $19 = k;
                }
              }
              const name = $19;
              return builtin$776(self, $b.String_asStr(name), vs, e, (suspends && (!driven)));
              $16 = undefined;
            }
            break m$18;
          }
          $rt.unmatched($17);
        }
        const f = $16;
        if ((suspends && (!driven))) {
          return ("" + "(yield* " + f + "(" + join$53(vs, ", ") + "))");
        } else {
          {
            return ("" + f + "(" + join$53(vs, ", ") + ")");
          }
        }
      }
      break m$7;
    }
    if (true) {
      {
      }
      break m$7;
    }
    $rt.unmatched($6);
  }
  const $20 = callee.kind;
  m$21: {
    if (($20.$tag === "Field")) {
      const target = $20.$.target;
      const name = $20.$.name;
      {
        const $22 = target.kind;
        m$23: {
          if (($22.$tag === "Ident")) {
            const tname = $22.$;
            {
              if (isNone$777(local$311(self.v, $b.String_asStr(tname)))) {
                const $24 = lookup$47(self.v.p, self.v.module, $b.String_asStr(tname));
                m$25: {
                  if (($24.$tag === "Some" && ($24.$.$tag === "Def"))) {
                    const d = $24.$.$;
                    {
                      const $26 = new $rt.FieldRef($rt.idx(self.v.p.defs, d), "kind");
                      const $27 = $26.v;
                      m$28: {
                        if (($27.$tag === "Effect")) {
                          {
                            const vs = { v: $b.Vec_new() };
                            for (const $29 of $rt.items(args)) {
                              const a = $29;
                              $b.Vec_push(vs, value$313(self, a));
                            }
                            const effect = $b.String_clone($rt.idx(self.v.p.defs, d).name);
                            if ((effect === "Fail")) {
                              return ("" + "$rt.raise(" + join$53(vs.v, ", ") + ")");
                            }
                            if ((effect === "Yield")) {
                              return ("" + "(yield $rt.yielded(" + join$53(vs.v, ", ") + "))");
                            }
                            if ((effect === "Io")) {
                              if (self.v.tasks) {
                                return ("" + "(yield* $b.Io_" + name.name + "$g(" + join$53(vs.v, ", ") + "))");
                              } else {
                                {
                                  return ("" + "$b.Io_" + name.name + "(" + join$53(vs.v, ", ") + ")");
                                }
                              }
                            }
                            return ("" + "(yield $rt.perform(" + String(d) + ", " + quote$512(name.name) + ", [" + join$53(vs.v, ", ") + "]))");
                          }
                          break m$28;
                        }
                        if (true) {
                          {
                          }
                          break m$28;
                        }
                        $rt.unmatched($27);
                      }
                    }
                    break m$25;
                  }
                  if (true) {
                    {
                    }
                    break m$25;
                  }
                  $rt.unmatched($24);
                }
              }
            }
            break m$23;
          }
          if (true) {
            {
            }
            break m$23;
          }
          $rt.unmatched($22);
        }
      }
      break m$21;
    }
    if (true) {
      {
      }
      break m$21;
    }
    $rt.unmatched($20);
  }
  const f0 = value$313(self, callee);
  let $30;
  const $31 = stripBorrow$317(exprTy$316(self.v, callee.id));
  m$32: {
    if (($31.$tag === "Fn")) {
      const f = $31.$;
      $30 = { $tag: "Some", $: clone$200($b.Box_get(f)) };
      break m$32;
    }
    if (true) {
      $30 = { $tag: "None" };
      break m$32;
    }
    $rt.unmatched($31);
  }
  const fty = $30;
  let $33;
  if (every$592($b.slice_iter(args), ((a) => {
  return simple$522(a);
  }))) {
    $33 = f0;
  } else {
    {
      $33 = save$319(self, f0);
    }
  }
  const f = $33;
  const $34 = stripBorrow$317(exprTy$316(self.v, callee.id));
  m$35: {
    if (($34.$tag === "Named")) {
      const d = $34.$[0];
      {
        if (isKnown$479(self.v.p, d, "Cont")) {
          const vs = { v: $b.Vec_new() };
          for (const $36 of $rt.items(args)) {
            const a = $36;
            $b.Vec_push(vs, value$313(self, a));
          }
          if (self.v.suspends) {
            return ("" + "(yield* " + f + "(" + join$53(vs.v, ", ") + "))");
          } else {
            {
              return ("" + "$rt.run(" + f + "(" + join$53(vs.v, ", ") + "))");
            }
          }
        }
      }
      break m$35;
    }
    if (true) {
      {
      }
      break m$35;
    }
    $rt.unmatched($34);
  }
  const $37 = fty;
  m$38: {
    if (($37.$tag === "Some")) {
      const t = $37.$;
      {
        const vs = args$773(self, args, t.params);
        if ((rowSuspends$306(self.v.p, t.effects, self.v.tasks) && (!driven))) {
          return ("" + "(yield* " + f + "(" + join$53(vs, ", ") + "))");
        } else {
          {
            return ("" + f + "(" + join$53(vs, ", ") + ")");
          }
        }
      }
      break m$38;
    }
    if (($37.$tag === "None")) {
      {
        const vs = { v: $b.Vec_new() };
        for (const $39 of $rt.items(args)) {
          const a = $39;
          $b.Vec_push(vs, value$313(self, a));
        }
        return ("" + f + "(" + join$53(vs.v, ", ") + ")");
      }
      break m$38;
    }
    $rt.unmatched($37);
  }
}
function binary$672(self, e, op, a, b) {
  if (((op === "&&") || (op === "||"))) {
    const x = value$313(self, a);
    if (simple$522(b)) {
      const y = value$313(self, b);
      return ("" + "(" + x + " " + op + " " + y + ")");
    }
    const t = fresh$167(self);
    line$168(self, ("" + "let " + t + " = " + x + ";"));
    const $1 = self;
    let $2;
    if ((op === "&&")) {
      $2 = ("" + "if (" + t + ") {");
    } else {
      {
        $2 = ("" + "if (!" + t + ") {");
      }
    }
    line$168($1, $2);
    self.v.indent = $rt.usize(self.v.indent + 1n);
    const y = value$313(self, b);
    line$168(self, ("" + t + " = " + y + ";"));
    self.v.indent = $rt.usize(self.v.indent - 1n);
    line$168(self, "}");
    return t;
  }
  let $3;
  const $4 = $b.HashMap_get(self.v.p.typed, self.v.fid);
  m$5: {
    if (($4.$tag === "Some")) {
      const typed = $4.$;
      const $6 = $b.HashMap_get(typed.ops, e.id);
      m$7: {
        if (($6.$tag === "Some")) {
          const m = $6.$;
          $3 = { $tag: "Some", $: clone$79(m) };
          break m$7;
        }
        if (($6.$tag === "None")) {
          $3 = { $tag: "None" };
          break m$7;
        }
        $rt.unmatched($6);
      }
      break m$5;
    }
    if (($4.$tag === "None")) {
      $3 = { $tag: "None" };
      break m$5;
    }
    $rt.unmatched($4);
  }
  const method = $3;
  const $8 = method;
  m$9: {
    if (($8.$tag === "Some")) {
      const f = $8.$[0];
      const args = $8.$[1];
      {
        const t = stripBorrow$317(exprTy$316(self.v, a.id));
        let $10;
        const $11 = t;
        m$12: {
          if (($11.$tag === "Prim")) {
            $10 = true;
            break m$12;
          }
          if (true) {
            $10 = false;
            break m$12;
          }
          $rt.unmatched($11);
        }
        const primitive = $10;
        if ((!primitive)) {
          const concrete = { v: $b.Vec_new() };
          for (const $13 of $rt.items(args)) {
            const g = $13;
            $b.Vec_push(concrete, substArg$501(g, self.v.map));
          }
          const c = callee$688(self, f, concrete.v, $rt.copy(e.span));
          const fname = calleeJs$771(self.v, c);
          let x = value$313(self, a);
          if ((!simple$522(b))) {
            x = save$319(self, x);
          }
          const y = value$313(self, b);
          const $14 = op;
          m$15: {
            if ($14 === "==") {
              return ("" + fname + "(" + x + ", " + y + ")");
              break m$15;
            }
            if ($14 === "!=") {
              return ("" + "!" + fname + "(" + x + ", " + y + ")");
              break m$15;
            }
            if ($14 === "<") {
              return ("" + "(" + fname + "(" + x + ", " + y + ").$tag === \"Less\")");
              break m$15;
            }
            if ($14 === "<=") {
              return ("" + "(" + fname + "(" + x + ", " + y + ").$tag !== \"Greater\")");
              break m$15;
            }
            if ($14 === ">") {
              return ("" + "(" + fname + "(" + x + ", " + y + ").$tag === \"Greater\")");
              break m$15;
            }
            if (true) {
              return ("" + "(" + fname + "(" + x + ", " + y + ").$tag !== \"Less\")");
              break m$15;
            }
            $rt.unmatched($14);
          }
        }
      }
      break m$9;
    }
    if (true) {
      {
      }
      break m$9;
    }
    $rt.unmatched($8);
  }
  let x = value$313(self, a);
  if ((!simple$522(b))) {
    x = save$319(self, x);
  }
  const y = value$313(self, b);
  const t = exprTy$316(self.v, e.id);
  return arith$778(self.v, op, x, y, t, exprTy$316(self.v, a.id));
}
function assign$673(self, op, target, value) {
  const tt = exprTy$316(self.v, target.id);
  let $1;
  const $2 = tt;
  m$3: {
    if (($2.$tag === "Borrow" && $2.$[0] === true)) {
      const inner = $2.$[1];
      $1 = clone$23($b.Box_get(inner));
      break m$3;
    }
    if (true) {
      const other = $2;
      $1 = clone$23(other);
      break m$3;
    }
    $rt.unmatched($2);
  }
  const want = $1;
  const v0 = exAs$314(self, value, want);
  let $4;
  if (simple$522(target)) {
    $4 = v0;
  } else {
    {
      $4 = save$319(self, v0);
    }
  }
  let v = $4;
  const place = place$779(self, target);
  if ((op !== "=")) {
    const bop = $b.str_slice(op, 0n, $rt.usize($b.str_len(op) - 1n));
    v = arith$778(self.v, bop, $b.String_clone(place), v, want, want);
  }
  line$168(self, ("" + place + " = " + v + ";"));
  return undefined;
}
function tag$674(self, e, name, args) {
  const $1 = args;
  m$2: {
    if (($1.$tag === "None")) {
      return ("" + "{ $tag: " + quote$512(name) + " }");
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const es = $1.$;
      {
        const vs = items$676(self, es);
        if (($b.slice_len(vs) === 1n)) {
          return ("" + "{ $tag: " + quote$512(name) + ", $: " + $rt.idx(vs, 0n) + " }");
        } else {
          {
            return ("" + "{ $tag: " + quote$512(name) + ", $: [" + join$53(vs, ", ") + "] }");
          }
        }
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$;
      {
        const rec = record$675(self, e, fields);
        return ("" + "{ $tag: " + quote$512(name) + ", $: " + rec + " }");
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function record$675(self, e, fields) {
  let last = 0n;
  const $1 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(fields)));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const i = $4[0];
    const f = $4[1];
    if (($b.Option_isSome(f.generate) || $b.Option_isSome(f.computed))) {
      fail$514(self.v, $rt.copy(f.name.span), "a record entry `comptime` code names at run time");
    }
    const $5 = f.value;
    m$6: {
      if (($5.$tag === "Some")) {
        const v = $5.$;
        {
          if ((!simple$522(v))) {
            last = i;
          }
        }
        break m$6;
      }
      if (($5.$tag === "None")) {
        {
        }
        break m$6;
      }
      $rt.unmatched($5);
    }
  }
  const entries = { v: $b.Vec_new() };
  const $7 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(fields)));
  let $9;
  for (let $8 = $7.next(); !$8.done; $8 = $7.next($9)) {
    $9 = undefined;
    const $10 = $8.value.item;
    const i = $10[0];
    const f = $10[1];
    let $11;
    const $12 = f.value;
    m$13: {
      if (($12.$tag === "Some")) {
        const v = $12.$;
        const $14 = slotTy$780(self.v, v.id);
        m$15: {
          if (($14.$tag === "Some")) {
            const t = $14.$;
            $11 = exAs$314(self, v, t);
            break m$15;
          }
          if (($14.$tag === "None")) {
            $11 = value$313(self, v);
            break m$15;
          }
          $rt.unmatched($14);
        }
        break m$13;
      }
      if (($12.$tag === "None")) {
        const $16 = local$311(self.v, $b.String_asStr(f.name.name));
        m$17: {
          if (($16.$tag === "Some")) {
            const l = $16.$;
            if (l.cell) {
              $11 = ("" + l.js + ".v");
            } else {
              {
                $11 = l.js;
              }
            }
            break m$17;
          }
          if (($16.$tag === "None")) {
            $11 = fail$514(self.v, $rt.copy(f.name.span), ("" + "unknown name `" + f.name.name + "`"));
            break m$17;
          }
          $rt.unmatched($16);
        }
        break m$13;
      }
      $rt.unmatched($12);
    }
    const x = $11;
    let $18;
    if ((i < last)) {
      $18 = save$319(self, x);
    } else {
      {
        $18 = x;
      }
    }
    const v = $18;
    $b.Vec_push(entries, ("" + mangleField$669($b.String_asStr(f.name.name)) + ": " + v));
  }
  return ("" + "{ " + join$53(entries.v, ", ") + " }");
}
function items$676(self, es) {
  let last = 0n;
  const $1 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(es)));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const i = $4[0];
    const x = $4[1];
    if ((!simple$522(x))) {
      last = i;
    }
  }
  const out = { v: $b.Vec_new() };
  const $5 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(es)));
  let $7;
  for (let $6 = $5.next(); !$6.done; $6 = $5.next($7)) {
    $7 = undefined;
    const $8 = $6.value.item;
    const i = $8[0];
    const x = $8[1];
    let $9;
    const $10 = slotTy$780(self.v, x.id);
    m$11: {
      if (($10.$tag === "Some")) {
        const t = $10.$;
        $9 = exAs$314(self, x, t);
        break m$11;
      }
      if (($10.$tag === "None")) {
        $9 = value$313(self, x);
        break m$11;
      }
      $rt.unmatched($10);
    }
    const v = $9;
    const $12 = out;
    let $13;
    if ((i < last)) {
      $13 = save$319(self, v);
    } else {
      {
        $13 = v;
      }
    }
    $b.Vec_push($12, $13);
  }
  return out.v;
}
function lambda$677(self, e, params, body) {
  let $1;
  const $2 = stripBorrow$317(exprTy$316(self.v, e.id));
  m$3: {
    if (($2.$tag === "Fn")) {
      const f = $2.$;
      $1 = { $tag: "Some", $: clone$200($b.Box_get(f)) };
      break m$3;
    }
    if (true) {
      $1 = { $tag: "None" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const fty = $1;
  let $4;
  const $5 = fty;
  m$6: {
    if (($5.$tag === "Some")) {
      const f = $5.$;
      $4 = rowSuspends$306(self.v.p, f.effects, self.v.tasks);
      break m$6;
    }
    if (($5.$tag === "None")) {
      $4 = false;
      break m$6;
    }
    $rt.unmatched($5);
  }
  const generator = $4;
  let $7;
  const $8 = fty;
  m$9: {
    if (($8.$tag === "Some")) {
      const f = $8.$;
      $7 = clone$23(f.ret);
      break m$9;
    }
    if (($8.$tag === "None")) {
      $7 = { $tag: "Error" };
      break m$9;
    }
    $rt.unmatched($8);
  }
  const ret = $7;
  const saved = $b.replace(new $rt.FieldRef(self.v, "out"), $b.String_new());
  const savedIndent = $b.replace(new $rt.FieldRef(self.v, "indent"), 1n);
  const savedSuspends = $b.replace(new $rt.FieldRef(self.v, "suspends"), generator);
  const savedRet = $b.replace(new $rt.FieldRef(self.v, "ret"), clone$23(ret));
  const savedFnRet = $b.replace(new $rt.FieldRef(self.v, "fnRet"), ret);
  const savedInHandle = $b.replace(new $rt.FieldRef(self.v, "inHandle"), false);
  push$165(self);
  const names = { v: $b.Vec_new() };
  const celled = { v: $b.Vec_new() };
  for (const $10 of $rt.items(params)) {
    const p = $10;
    const cell = has$19(self.v.cellParams, p.name.span.start);
    const js = declare$166(self, $b.String_asStr(p.name.name), cell);
    if (cell) {
      const raw = fresh$167(self);
      $b.Vec_push(names, $b.String_clone(raw));
      $b.Vec_push(celled, [js, raw]);
    } else {
      {
        $b.Vec_push(names, js);
      }
    }
  }
  for (const $11 of $rt.items(celled.v)) {
    const js = $11[0];
    const raw = $11[1];
    line$168(self, ("" + "const " + js + " = { v: " + raw + " };"));
  }
  into$322(self, body, { $tag: "Return" });
  pop$170(self);
  const inner = $b.replace(new $rt.FieldRef(self.v, "out"), saved);
  self.v.indent = savedIndent;
  self.v.suspends = savedSuspends;
  self.v.ret = savedRet;
  self.v.fnRet = savedFnRet;
  self.v.inHandle = savedInHandle;
  const close = { v: $b.String_new() };
  const $12 = self.v.indent;
  for (let $13$$14 = 0n; $13$$14 < $12; $13$$14++) {
    $b.String_push(close, "  ");
  }
  if (generator) {
    return ("" + "(function* (" + join$53(names.v, ", ") + ") {\n" + inner + close.v + "})");
  } else {
    {
      return ("" + "((" + join$53(names.v, ", ") + ") => {\n" + inner + close.v + "})");
    }
  }
}
function cast$678(self, v, from, to) {
  const fromInt = $b.Option_isSome(intPrim$171(from));
  const $1 = intPrim$171(to);
  m$2: {
    if (($1.$tag === "Some")) {
      const p = $1.$;
      if (fromInt) {
        return ("" + "$rt.wrap_" + primName$300(p) + "(" + v + ")");
      } else {
        if (floatTy$511(from)) {
          return ("" + "$rt.wrap_" + primName$300(p) + "($rt.truncFloat(" + v + "))");
        } else {
          {
            return ("" + "$rt.wrap_" + primName$300(p) + "($rt.toInt(" + v + "))");
          }
        }
      }
      break m$2;
    }
    if (($1.$tag === "None")) {
      if ((floatTy$511(to) && fromInt)) {
        return ("" + "Number(" + v + ")");
      } else {
        {
          return v;
        }
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function handle$679(self, e, body, arms) {
  let $1;
  const $2 = $b.HashMap_get(self.v.p.typed, self.v.fid);
  m$3: {
    if (($2.$tag === "Some")) {
      const t = $2.$;
      const $4 = $b.HashMap_get(t.handled, e.id);
      m$5: {
        if (($4.$tag === "Some")) {
          const d = $4.$;
          $1 = d;
          break m$5;
        }
        if (($4.$tag === "None")) {
          $1 = fail$514(self.v, $rt.copy(e.span), "a `handle` not checked");
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$3;
    }
    if (($2.$tag === "None")) {
      $1 = fail$514(self.v, $rt.copy(e.span), "a `handle` not checked");
      break m$3;
    }
    $rt.unmatched($2);
  }
  const effect = $1;
  let $6;
  if (($rt.idx(self.v.p.defs, effect).name === "Yield")) {
    $6 = $b.str_toString("$rt.YIELD");
  } else {
    {
      $6 = ("" + String(effect));
    }
  }
  const id = $6;
  const result = exprTy$316(self.v, e.id);
  const leaves = (blockReturns$781(body) || some$208($b.slice_iter(arms), ((a) => {
  return blockReturns$781(a.body);
  })));
  const b = handlerPart$782(self, $b.Vec_new(), { $tag: "None" }, body, clone$23(result));
  const parts = { v: $b.Vec_new() };
  for (const $7 of $rt.items(arms)) {
    const a = $7;
    const f = handlerPart$782(self, a.params, a.resumes, a.body, clone$23(result));
    $b.Vec_push(parts, ("" + mangleField$669($b.String_asStr(a.op.name)) + ": " + f));
  }
  const run = ("" + "$rt.handle(" + id + ", " + b + ", { " + join$53(parts.v, ", ") + " })");
  let $8;
  if (self.v.suspends) {
    $8 = ("" + "(yield* " + run + ")");
  } else {
    {
      $8 = ("" + "$rt.run(" + run + ")");
    }
  }
  const call = $8;
  if ((!leaves)) {
    return call;
  }
  const t = fresh$167(self);
  const x = fresh$167(self);
  line$168(self, ("" + "let " + t + ";"));
  line$168(self, ("" + "try { " + t + " = " + call + "; } catch (" + x + ") { if (" + x + " instanceof $rt.Return) return " + x + ".v; throw " + x + "; }"));
  return t;
}
function clone$680(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$783(x));
  }
  return v.v;
}
function fieldPaths$681(fs, segs, out) {
  for (const $1 of $rt.items(fs)) {
    const f = $1[0];
    const q = $1[1];
    const s = { v: clone$680(segs) };
    $b.Vec_push(s, { $tag: "Field", $: $b.String_clone(f.name) });
    const $2 = q;
    m$3: {
      if (($2.$tag === "Some")) {
        const q$$4 = $2.$;
        paths$515(q$$4, s.v, out);
        break m$3;
      }
      if (($2.$tag === "None")) {
        $b.Vec_push(out, [$b.String_clone(f.name), f.span.start, s.v]);
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return undefined;
}
function isNone$682(self) {
  return (!$b.Option_isSome(self));
}
function at$683(subj, segs) {
  const out = { v: $b.str_toString(subj) };
  for (const $1 of $rt.items(segs)) {
    const s = $1;
    const $2 = s;
    m$3: {
      if (($2.$tag === "Field")) {
        const f = $2.$;
        {
          $b.String_push(out, ".");
          $b.String_push(out, $b.String_asStr(mangleField$669($b.String_asStr(f))));
        }
        break m$3;
      }
      if (($2.$tag === "Index")) {
        const i = $2.$;
        {
          $b.String_push(out, ("" + "[" + String(i) + "]"));
        }
        break m$3;
      }
      if (($2.$tag === "Payload")) {
        {
          $b.String_push(out, ".$");
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return out.v;
}
function every$684(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if ((!test(x))) {
      return false;
    }
  }
  return true;
}
function simpleInits$685(fs) {
  return every$784($b.slice_iter(fs), ((f) => {
  const $1 = f.value;
  m$2: {
    if (($1.$tag === "Some")) {
      const v = $1.$;
      return simple$522(v);
      break m$2;
    }
    if (($1.$tag === "None")) {
      return true;
      break m$2;
    }
    $rt.unmatched($1);
  }
  }));
}
function drive$686(self, g, mutable, pat, body) {
  const gen = save$319(self, g);
  const r = fresh$167(self);
  const answer = fresh$167(self);
  line$168(self, ("" + "let " + answer + ";"));
  line$168(self, ("" + "for (let " + r + " = " + gen + ".next(); !" + r + ".done; " + r + " = " + gen + ".next(" + answer + ")) {"));
  self.v.indent = $rt.usize(self.v.indent + 1n);
  line$168(self, ("" + answer + " = undefined;"));
  if (self.v.suspends) {
    line$168(self, ("" + "if (!$rt.isYield(" + r + ".value)) { " + answer + " = yield " + r + ".value; continue; }"));
  }
  const x = save$319(self, ("" + r + ".value.item"));
  loopBinds$689(self, pat, x, mutable);
  blockInto$520(self, body, { $tag: "Discard" });
  self.v.indent = $rt.usize(self.v.indent - 1n);
  line$168(self, "}");
  return undefined;
}
function callArgs$687(self, id) {
  const out = { v: $b.Vec_new() };
  const $1 = $b.HashMap_get(self.p.typed, self.fid);
  m$2: {
    if (($1.$tag === "Some")) {
      const t = $1.$;
      {
        const $3 = $b.HashMap_get(t.targs, id);
        m$4: {
          if (($3.$tag === "Some")) {
            const args = $3.$;
            {
              for (const $5 of $rt.items(args)) {
                const a = $5;
                const $6 = out;
                let $7;
                const $8 = substArg$501(a, self.map);
                m$9: {
                  if (($8.$tag === "Ty")) {
                    const x = $8.$;
                    $7 = { $tag: "Ty", $: resolveAssoc$309(self, x) };
                    break m$9;
                  }
                  if (true) {
                    const other = $8;
                    $7 = other;
                    break m$9;
                  }
                  $rt.unmatched($8);
                }
                $b.Vec_push($6, $7);
              }
            }
            break m$4;
          }
          if (true) {
            {
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  return out.v;
}
function callee$688(self, fid, args, span) {
  const ifaceOf = $rt.idx(self.v.p.fns, fid).iface;
  const $1 = ifaceOf;
  m$2: {
    if (($1.$tag === "Some")) {
      const iface = $1.$;
      {
        const name = $b.String_clone($rt.idx(self.v.p.fns, fid).name);
        let $3;
        const $4 = first$258(args);
        m$5: {
          if (($4.$tag === "Some" && ($4.$.$tag === "Ty"))) {
            const t = $4.$.$;
            $3 = clone$23(t);
            break m$5;
          }
          if (true) {
            $3 = fail$514(self.v, $rt.copy(span), ("" + "no type for `Self` in `" + name + "`"));
            break m$5;
          }
          $rt.unmatched($4);
        }
        const selfTy = $3;
        let $6;
        const $7 = resolveImpl$287(self.v.p, iface, selfTy);
        m$8: {
          if (($7.$tag === "Some")) {
            const r = $7.$;
            $6 = r;
            break m$8;
          }
          if (($7.$tag === "None")) {
            {
              const shown = show$136(self.v.p, selfTy);
              $6 = fail$514(self.v, $rt.copy(span), ("" + "no impl of `" + $rt.idx(self.v.p.defs, iface).name + "` for `" + shown + "`"));
            }
            break m$8;
          }
          $rt.unmatched($7);
        }
        const $9 = $6;
        const imp = $9[0];
        const binds = $9[1];
        let $10;
        const $11 = methodForMut$289(new $rt.FieldRef(self.v, "p"), imp, $b.String_asStr(name), binds);
        m$12: {
          if (($11.$tag === "Some")) {
            const m = $11.$;
            $10 = m;
            break m$12;
          }
          if (($11.$tag === "None")) {
            $10 = fail$514(self.v, $rt.copy(span), ("" + "no method `" + name + "`"));
            break m$12;
          }
          $rt.unmatched($11);
        }
        const m = $10;
        if ((!has$19(self.v.p.checked, m))) {
          checkFn$3(new $rt.FieldRef(self.v, "p"), m);
        }
        const env = { v: clone$785(binds) };
        const skip = $rt.usize(1n + $b.slice_len($rt.idx(self.v.p.defs, iface).params));
        const specialized = $b.HashMap_has(self.v.p.specOf, m);
        let implParams = 0n;
        for (const $13 of $rt.items($rt.idx(self.v.p.impls, imp).params)) {
          const g = $13;
          if (((!g.isComptime) || (!specialized))) {
            implParams = $rt.usize(implParams + 1n);
          }
        }
        const mParams = clone$73($rt.idx(self.v.p.fns, m).scheme.tparams);
        let k = implParams;
        while ((k < $b.slice_len(mParams))) {
          const at = $rt.usize($rt.usize(skip + k) - implParams);
          if ((at < $b.slice_len(args))) {
            $b.HashMap_insert(env, $rt.idx(mParams, k).sym.id, clone$290($rt.idx(args, at)));
          }
          k = $rt.usize(k + 1n);
        }
        const margs = { v: $b.Vec_new() };
        for (const $14 of $rt.items(mParams)) {
          const g = $14;
          const $15 = margs;
          let $16;
          const $17 = $b.HashMap_get(env.v, g.sym.id);
          m$18: {
            if (($17.$tag === "Some")) {
              const a = $17.$;
              $16 = clone$290(a);
              break m$18;
            }
            if (($17.$tag === "None")) {
              $16 = { $tag: "Ty", $: { $tag: "Param", $: clone$34(g.sym) } };
              break m$18;
            }
            $rt.unmatched($17);
          }
          $b.Vec_push($15, $16);
        }
        return callee$688(self, m, margs.v, $rt.copy(span));
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const $19 = fnDecl$24(self.v.p, fid);
  m$20: {
    if (($19.$tag === "Some")) {
      const d = $19.$;
      if ($b.Option_isSome(d.body)) {
        return { $tag: "Inst", $: instance$50(self, fid, args) };
        break m$20;
      }
    }
    if (true) {
      return { $tag: "Builtin", $: builtinKey$157(self.v, fid) };
      break m$20;
    }
    $rt.unmatched($19);
  }
}
function loopBinds$689(self, pat, x, mutable) {
  const c = cond$320(self, pat, x);
  if ((c !== "true")) {
    line$168(self, ("" + "if (!(" + c + ")) $rt.unmatched(" + x + ");"));
  }
  binds$321(self, pat, x, { $tag: "None" }, mutable);
  return undefined;
}
function run$690(self) {
  while (true) {
    skipTrivia$786(self);
    const start = self.v.pos;
    if ((self.v.pos >= self.v.end)) {
      push$787(self, { $tag: "Eof" }, start);
      return;
    }
    const c = peek$788(self.v);
    if (((c === 98n) && (peekAt$789(self.v, 1n) === 39n))) {
      self.v.pos = $rt.usize(self.v.pos + 2n);
      const b = byteChar$790(self, start);
      if ((peek$788(self.v) !== 39n)) {
        throw new $rt.Fail(err$791(self.v, start, "unterminated byte literal"));
      }
      self.v.pos = $rt.usize(self.v.pos + 1n);
      push$787(self, { $tag: "Byte", $: b }, start);
    } else {
      if ((isAlpha$792(c) || (c === 95n))) {
        const word = word$793(self);
        let $1;
        if (includes$382($c10$KEYWORDS, $b.String_asStr(word))) {
          $1 = { $tag: "Kw", $: word };
        } else {
          {
            $1 = { $tag: "Ident", $: word };
          }
        }
        const tok = $1;
        push$787(self, tok, start);
      } else {
        if (((c === 35n) && (peekAt$789(self.v, 1n) === 91n))) {
          self.v.pos = $rt.usize(self.v.pos + 2n);
          push$787(self, { $tag: "Punct", $: $b.str_toString("#[") }, start);
        } else {
          if ((c === 35n)) {
            self.v.pos = $rt.usize(self.v.pos + 1n);
            if ((!(isAlpha$792(peek$788(self.v)) || (peek$788(self.v) === 95n)))) {
              throw new $rt.Fail(err$791(self.v, start, "expected a tag name after `#`"));
            }
            const name = word$793(self);
            push$787(self, { $tag: "Tag", $: name }, start);
          } else {
            if (isDigit$794(c)) {
              const tok = number$795(self);
              push$787(self, tok, start);
            } else {
              if ((c === 34n)) {
                self.v.pos = $rt.usize(self.v.pos + 1n);
                const s = string$796(self, start, 34n);
                push$787(self, { $tag: "Str", $: s }, start);
              } else {
                if ((c === 96n)) {
                  self.v.pos = $rt.usize(self.v.pos + 1n);
                  const parts = template$797(self, start);
                  push$787(self, { $tag: "Template", $: parts }, start);
                } else {
                  {
                    const $2 = find$705($b.slice_iter($c11$PUNCT), ((p) => {
  return startsWith$798(self.v, p);
                    }));
                    m$3: {
                      if (($2.$tag === "Some")) {
                        const p = $2.$;
                        {
                          self.v.pos = $rt.usize(self.v.pos + $b.str_len(p));
                          push$787(self, { $tag: "Punct", $: $b.str_toString(p) }, start);
                        }
                        break m$3;
                      }
                      if (($2.$tag === "None")) {
                        {
                          self.v.pos = $rt.usize(self.v.pos + 1n);
                          throw new $rt.Fail(err$791(self.v, start, ("" + "unexpected character `" + $b.str_slice(self.v.src, start, $rt.usize(start + 1n)) + "`")));
                        }
                        break m$3;
                      }
                      $rt.unmatched($2);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  return undefined;
}
function eq$691(self, other) {
  return (self === other);
}
function eq$692(self, other) {
  if (($b.slice_len(self) !== $b.slice_len(other))) {
    return false;
  }
  let i = 0n;
  while ((i < $b.slice_len(self))) {
    if ((!eq$799($rt.idx(self, i), $rt.idx(other, i)))) {
      return false;
    }
    i = $rt.usize(i + 1n);
  }
  return true;
}
function expectKw$693(self, k) {
  if (atKw$530(self.v, k)) {
    return bump$539(self);
  } else {
    {
      return error$552(self.v, ("" + "`" + k + "`"));
    }
  }
}
function expectWord$694(self, w) {
  if ((!eatWord$534(self, w))) {
    error$552(self.v, ("" + "`" + w + "`"));
    return undefined;
  }
}
function isPunct$695(t, p) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Punct")) {
      const q = $1.$;
      return (q === p);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function typeParams$696(self) {
  const out = { v: $b.Vec_new() };
  if ((!eat$542(self, "<"))) {
    return out.v;
  }
  while ((!at$532(self.v, ">"))) {
    let $1;
    if ((atWord$536(self.v, "region") && isIdent$549(tokAt$537(self.v, 1n)))) {
      bump$539(self);
      const name = ident$541(self);
      let $2;
      if (eat$542(self, "=")) {
        $2 = { $tag: "Some", $: ty$543(self) };
      } else {
        {
          $2 = { $tag: "None" };
        }
      }
      const default$ = $2;
      $1 = { $tag: "Region", $: { name: name, default: default$ } };
    } else {
      if ((atWord$536(self.v, "row") && isIdent$549(tokAt$537(self.v, 1n)))) {
        bump$539(self);
        const name = ident$541(self);
        let $3;
        if (eatKw$529(self, "extends")) {
          $3 = bounds$707(self);
        } else {
          {
            $3 = $b.Vec_new();
          }
        }
        const bounds = $3;
        let $4;
        if (eat$542(self, "=")) {
          $4 = { $tag: "Some", $: ty$543(self) };
        } else {
          {
            $4 = { $tag: "None" };
          }
        }
        const default$ = $4;
        $1 = { $tag: "Row", $: { name: name, bounds: bounds, default: default$ } };
      } else {
        if (eatKw$529(self, "comptime")) {
          const name = ident$541(self);
          expect$544(self, ":");
          $1 = { $tag: "Comptime", $: { name: name, ty: ty$543(self) } };
        } else {
          {
            const name = ident$541(self);
            let $5;
            if (eatKw$529(self, "extends")) {
              $5 = bounds$707(self);
            } else {
              {
                $5 = $b.Vec_new();
              }
            }
            const bounds = $5;
            let $6;
            if (eat$542(self, "=")) {
              $6 = { $tag: "Some", $: ty$543(self) };
            } else {
              {
                $6 = { $tag: "None" };
              }
            }
            const default$ = $6;
            $1 = { $tag: "Type", $: { name: name, bounds: bounds, default: default$ } };
          }
        }
      }
    }
    const param = $1;
    $b.Vec_push(out, param);
    if ((!eat$542(self, ","))) {
      break;
    }
  }
  expect$544(self, ">");
  return out.v;
}
function fieldList$697(self) {
  expect$544(self, "{");
  const fields = fieldItems$800(self);
  expect$544(self, "}");
  return fields;
}
function isWord$698(t, w) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Ident")) {
      const q = $1.$;
      return (q === w);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function tagDecl$699(self) {
  let $1;
  const $2 = tok$527(self.v);
  m$3: {
    if (($2.$tag === "Tag")) {
      const t = $2.$;
      $1 = $b.String_clone(t);
      break m$3;
    }
    if (true) {
      $1 = error$552(self.v, "a tag such as `#Some`");
      break m$3;
    }
    $rt.unmatched($2);
  }
  const n = $1;
  const name = mkIdent$801($b.String_asStr(n), bump$539(self));
  let $4;
  if (at$532(self.v, "(")) {
    bump$539(self);
    const tys = { v: $b.Vec_new() };
    while ((!at$532(self.v, ")"))) {
      $b.Vec_push(tys, ty$543(self));
      if ((!eat$542(self, ","))) {
        break;
      }
    }
    expect$544(self, ")");
    $4 = { $tag: "Tuple", $: tys.v };
  } else {
    if (at$532(self.v, "{")) {
      $4 = { $tag: "Record", $: fieldList$697(self) };
    } else {
      {
        $4 = { $tag: "None" };
      }
    }
  }
  const payload = $4;
  return { name: name, payload: payload };
}
function unionTy$700(self) {
  const start = span$528(self.v);
  eat$542(self, "|");
  const tags = { v: $b.Vec_new() };
  const includes = { v: $b.Vec_new() };
  let rest = { $tag: "None" };
  while (true) {
    if (eat$542(self, "...")) {
      rest = { $tag: "Some", $: ident$541(self) };
      break;
    }
    if (isIdent$549(tok$527(self.v))) {
      $b.Vec_push(includes, tyPostfix$701(self));
    } else {
      {
        $b.Vec_push(tags, tagDecl$699(self));
      }
    }
    if ((!eat$542(self, "|"))) {
      break;
    }
  }
  return { kind: { $tag: "Union", $: { tags: tags.v, includes: includes.v, rest: rest } }, span: since$554(self.v, $rt.copy(start)) };
}
function tyPostfix$701(self) {
  const start = span$528(self.v);
  let ty = tyAtom$802(self);
  while (true) {
    if (at$532(self.v, "[")) {
      bump$539(self);
      let $1;
      if (at$532(self.v, "]")) {
        $1 = { $tag: "None" };
      } else {
        {
          $1 = { $tag: "Some", $: $b.Box_new(expr$545(self)) };
        }
      }
      const len = $1;
      expect$544(self, "]");
      ty = { kind: { $tag: "Array", $: { elem: $b.Box_new(ty), len: len } }, span: since$554(self.v, $rt.copy(start)) };
    } else {
      if (at$532(self.v, "*")) {
        bump$539(self);
        ty = { kind: { $tag: "Ptr", $: $b.Box_new(ty) }, span: since$554(self.v, $rt.copy(start)) };
      } else {
        {
          return ty;
        }
      }
    }
  }
  return ty;
}
function atN$702(self, n, p) {
  return isPunct$695(tokAt$537(self, n), p);
}
function fnTy$703(self, mode, start) {
  const params = params$803(self, false);
  expect$544(self, "=>");
  const ret = $b.Box_new(ret$804(self));
  const row = uses$805(self);
  return { kind: { $tag: "Fn", $: { mode: mode, params: params, ret: ret, uses: row } }, span: since$554(self.v, $rt.copy(start)) };
}
function range$704(self) {
  const start = span$528(self.v);
  let lo = { $tag: "None" };
  if ((!at$532(self.v, ".."))) {
    const l = binary$806(self, 0n);
    if ((!at$532(self.v, ".."))) {
      return l;
    }
    lo = { $tag: "Some", $: $b.Box_new(l) };
  }
  bump$539(self);
  const closes = ((((at$532(self.v, "]") || at$532(self.v, ")")) || at$532(self.v, ",")) || at$532(self.v, ";")) || at$532(self.v, "}"));
  let $1;
  if (closes) {
    $1 = { $tag: "None" };
  } else {
    {
      $1 = { $tag: "Some", $: $b.Box_new(binary$806(self, 0n)) };
    }
  }
  const hi = $1;
  return expr_$706(self, { $tag: "Range", $: { lo: lo, hi: hi } }, since$554(self.v, $rt.copy(start)));
}
function find$705(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function expr_$706(self, kind, span) {
  self.v.nextId = $rt.usize(self.v.nextId + 1n);
  return { kind: kind, span: span, id: self.v.nextId };
}
function bounds$707(self) {
  const out = { v: $b.Vec_new() };
  $b.Vec_push(out, tyPostfix$701(self));
  while (eat$542(self, "&")) {
    $b.Vec_push(out, tyPostfix$701(self));
  }
  return out.v;
}
function memberSig$708(self) {
  return sigNamed$711(self, true, true);
}
function block$709(self) {
  const start = expect$544(self, "{");
  const stmts = { v: $b.Vec_new() };
  let tail = { $tag: "None" };
  while ((!at$532(self.v, "}"))) {
    if ((atKw$530(self.v, "const") || atKw$530(self.v, "let"))) {
      const s = span$528(self.v);
      const mutable = atKw$530(self.v, "let");
      bump$539(self);
      const pat = patternOne$807(self);
      let $1;
      if (eat$542(self, ":")) {
        $1 = { $tag: "Some", $: ty$543(self) };
      } else {
        {
          $1 = { $tag: "None" };
        }
      }
      const ty = $1;
      expect$544(self, "=");
      const init = expr$545(self);
      expect$544(self, ";");
      $b.Vec_push(stmts, { $tag: "Let", $: { mutable: mutable, pat: pat, ty: ty, init: init, span: since$554(self.v, $rt.copy(s)) } });
      continue;
    }
    if (eatKw$529(self, "defer")) {
      let $2;
      if (at$532(self.v, "{")) {
        $2 = blockLike$808(self);
      } else {
        {
          $2 = expr$545(self);
        }
      }
      const e = $2;
      $b.Vec_push(stmts, { $tag: "Defer", $: e });
      expect$544(self, ";");
      continue;
    }
    const blockLike = atBlockLike$809(self.v);
    let $3;
    if (blockLike) {
      $3 = blockLike$808(self);
    } else {
      {
        $3 = expr$545(self);
      }
    }
    const e = $3;
    if (eat$542(self, ";")) {
      $b.Vec_push(stmts, { $tag: "Expr", $: e });
    } else {
      if (at$532(self.v, "}")) {
        tail = { $tag: "Some", $: $b.Box_new(e) };
      } else {
        if (blockLike) {
          $b.Vec_push(stmts, { $tag: "Expr", $: e });
        } else {
          {
            error$552(self.v, "`;` or `}`");
          }
        }
      }
    }
  }
  expect$544(self, "}");
  return { stmts: stmts.v, tail: tail, span: since$554(self.v, $rt.copy(start)) };
}
function describe$710(self) {
  const $1 = tok$527(self);
  m$2: {
    if ((($1.$tag === "Ident") || ($1.$tag === "Kw") || ($1.$tag === "Int") || ($1.$tag === "Float"))) {
      let s;
      if (($1.$tag === "Ident")) { s = $1.$; }
      else if (($1.$tag === "Kw")) { s = $1.$; }
      else if (($1.$tag === "Int")) { s = $1.$; }
      else if (($1.$tag === "Float")) { s = $1.$; }
      return ("" + "`" + s + "`");
      break m$2;
    }
    if (($1.$tag === "Byte")) {
      return $b.str_toString("a byte literal");
      break m$2;
    }
    if (($1.$tag === "Str")) {
      return $b.str_toString("a string");
      break m$2;
    }
    if (($1.$tag === "Template")) {
      return $b.str_toString("a template literal");
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const s = $1.$;
      return ("" + "`#" + s + "`");
      break m$2;
    }
    if (($1.$tag === "Punct")) {
      const p = $1.$;
      return ("" + "`" + p + "`");
      break m$2;
    }
    if (($1.$tag === "Eof")) {
      return $b.str_toString("end of file");
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function sigNamed$711(self, functionKw, member) {
  const start = span$528(self.v);
  const isComptime = eatKw$529(self, "comptime");
  if (functionKw) {
    expectKw$693(self, "function");
  }
  let $1;
  if (member) {
    $1 = memberName$810(self);
  } else {
    {
      $1 = ident$541(self);
    }
  }
  const name = $1;
  const typeParams = typeParams$696(self);
  const params = params$803(self, true);
  expect$544(self, ":");
  const ret = ret$804(self);
  const row = uses$805(self);
  return { isComptime: isComptime, name: name, typeParams: typeParams, params: params, ret: ret, uses: row, span: since$554(self.v, $rt.copy(start)) };
}
function prevEnd$712(self) {
  if ((self.pos === 0n)) {
    return 0n;
  } else {
    {
      return $rt.idx(self.toks, $rt.usize(self.pos - 1n)).span.end;
    }
  }
}
function clone$713(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$811(x));
  }
  return v.v;
}
function clone$714(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$218(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$715(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$812(x));
  }
  return v.v;
}
function clone$716(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$813(x));
  }
  return v.v;
}
function clone$717(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$814(x));
  }
  return v.v;
}
function clone$718(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$815(x));
  }
  return v.v;
}
function clone$719(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$93(x));
  }
  return v.v;
}
function clone$720(self) {
  {
    return { name: clone$218(self.name), value: clone$816(self.value), computed: clone$96(self.computed), generate: clone$817(self.generate) };
  }
}
function clone$721(self) {
  {
    return { pat: clone$274(self.pat), guard: clone$816(self.guard), body: clone$60(self.body), generate: clone$818(self.generate) };
  }
}
function clone$722(self) {
  {
    return { body: clone$30(self.body), op: clone$218(self.op), params: clone$400(self.params), resumes: clone$714(self.resumes) };
  }
}
function clone$723(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$819(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$724(self) {
  return $b.Box_new(clone$220($b.Box_get(self)));
}
function cvEq$725(a, b) {
  const $1 = [a, b];
  m$2: {
    if ((($1[0].$tag === "Unit") && ($1[1].$tag === "Unit"))) {
      return true;
      break m$2;
    }
    if ((($1[0].$tag === "Bool") && ($1[1].$tag === "Bool"))) {
      const x = $1[0].$;
      const y = $1[1].$;
      return (x === y);
      break m$2;
    }
    if ((($1[0].$tag === "Int") && ($1[1].$tag === "Int"))) {
      const x = $1[0].$;
      const y = $1[1].$;
      return (x === y);
      break m$2;
    }
    if ((($1[0].$tag === "Str") && ($1[1].$tag === "Str"))) {
      const x = $1[0].$;
      const y = $1[1].$;
      return eq$6(x, y);
      break m$2;
    }
    if ((($1[0].$tag === "Type") && ($1[1].$tag === "Type"))) {
      const x = $1[0].$;
      const y = $1[1].$;
      return eq$234(x, y);
      break m$2;
    }
    if ((($1[0].$tag === "List") && ($1[1].$tag === "List"))) {
      const xs = $1[0].$;
      const ys = $1[1].$;
      return (($b.slice_len(xs) === $b.slice_len(ys)) && cvsEq$820(xs, ys));
      break m$2;
    }
    if ((($1[0].$tag === "Record") && ($1[1].$tag === "Record"))) {
      const xs = $1[0].$;
      const ys = $1[1].$;
      {
        if (($b.slice_len(xs) !== $b.slice_len(ys))) {
          return false;
        }
        const $3 = $b.slice_len(xs);
        for (let i = 0n; i < $3; i++) {
          if ((!eq$6($rt.idx($rt.idx(xs, i), 0n), $rt.idx($rt.idx(ys, i), 0n)) || (!cvEq$725($rt.idx($rt.idx(xs, i), 1n), $rt.idx($rt.idx(ys, i), 1n))))) {
            return false;
          }
        }
        return true;
      }
      break m$2;
    }
    if ((($1[0].$tag === "Tag") && ($1[1].$tag === "Tag"))) {
      const n = $1[0].$[0];
      const p = $1[0].$[1];
      const m = $1[1].$[0];
      const q = $1[1].$[1];
      let $4 = eq$6(n, m);
      if ($4) {
        let $5;
        const $6 = [p, q];
        m$7: {
          if ((($6[0].$tag === "None") && ($6[1].$tag === "None"))) {
            $5 = true;
            break m$7;
          }
          if ((($6[0].$tag === "Some") && ($6[1].$tag === "Some"))) {
            const x = $6[0].$;
            const y = $6[1].$;
            $5 = cvEq$725(x, y);
            break m$7;
          }
          if (true) {
            $5 = false;
            break m$7;
          }
          $rt.unmatched($6);
        }
        $4 = $5;
      }
      return $4;
      break m$2;
    }
    if ((($1[0].$tag === "Fn") && ($1[1].$tag === "Fn"))) {
      const f = $1[0].$;
      const g = $1[1].$;
      return (f === g);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function ctRecord$726(self, fs, v, out) {
  let $1;
  const $2 = v;
  m$3: {
    if (($2.$tag === "Record")) {
      const r = $2.$;
      $1 = r;
      break m$3;
    }
    if (true) {
      return false;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const r = $1;
  for (const $4 of $rt.items(fs)) {
    const n = $4[0];
    const p = $4[1];
    let $5;
    const $6 = recordGet$600(r, $b.String_asStr(n.name));
    m$7: {
      if (($6.$tag === "Some")) {
        const x = $6.$;
        $5 = x;
        break m$7;
      }
      if (($6.$tag === "None")) {
        return false;
        break m$7;
      }
      $rt.unmatched($6);
    }
    const x = $5;
    const $8 = p;
    m$9: {
      if (($8.$tag === "Some")) {
        const q = $8.$;
        {
          if ((!ctMatch$587(self, q, x, out))) {
            return false;
          }
        }
        break m$9;
      }
      if (($8.$tag === "None")) {
        $b.Vec_push(out, [$b.String_clone(n.name), x]);
        break m$9;
      }
      $rt.unmatched($8);
    }
  }
  return true;
}
function recordSet$727(fs, k, v) {
  let i = 0n;
  while ((i < $b.slice_len(fs.v))) {
    if (($rt.idx($rt.idx(fs.v, i), 0n) === k)) {
      const $1 = fs.v;
      $1[$rt.at($1, i)] = [$b.str_toString(k), v];
      return;
    }
    if (eq$357(cmp$358($b.String_asStr($rt.idx($rt.idx(fs.v, i), 0n)), k), { $tag: "Greater" })) {
      break;
    }
    i = $rt.usize(i + 1n);
  }
  $b.Vec_insert(fs, i, [$b.str_toString(k), v]);
  return undefined;
}
function evalArgs$728(self, args) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(args)) {
    const a = $1;
    $b.Vec_push(out, eval$$378(self, a));
  }
  return out.v;
}
function reflect$729(self, name, args, span) {
  let $1;
  const $2 = $b.slice_len(args);
  m$3: {
    if ($2 === 0n) {
      $1 = fail$391($rt.copy(span), $b.String_asStr(("" + "`Type." + name + "` takes a type")));
      break m$3;
    }
    if (true) {
      const $4 = $rt.idx(args, 0n);
      m$5: {
        if (($4.$tag === "Type")) {
          const t = $4.$;
          $1 = clone$23(t);
          break m$5;
        }
        if (true) {
          $1 = fail$391($rt.copy(span), $b.String_asStr(("" + "`Type." + name + "` takes a type")));
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$3;
    }
    $rt.unmatched($2);
  }
  const t = $1;
  if ((name === "info")) {
    return info$821(self, t, $rt.copy(span));
  }
  if ((name === "name")) {
    return { $tag: "Str", $: show$136(self.v.p.v, t) };
  }
  return fail$391($rt.copy(span), $b.String_asStr(("" + "`Type` has no function `" + name + "`")));
}
function method$730(self, recv, name, args, span) {
  const $1 = recv;
  m$2: {
    if (($1.$tag === "List")) {
      const xs = $1.$;
      {
        if ((name === "len")) {
          return { $tag: "Int", $: $rt.wrap_i128($b.slice_len(xs)) };
        }
        if ((name === "isEmpty")) {
          return { $tag: "Bool", $: ($b.slice_len(xs) === 0n) };
        }
        if ((name === "enumerate")) {
          const out = { v: $b.Vec_new() };
          const $3 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(xs)));
          let $5;
          for (let $4 = $3.next(); !$4.done; $4 = $3.next($5)) {
            $5 = undefined;
            const $6 = $4.value.item;
            const i = $6[0];
            const x = $6[1];
            $b.Vec_push(out, { $tag: "List", $: [{ $tag: "Int", $: $rt.wrap_i128(i) }, clone$90(x)] });
          }
          return { $tag: "List", $: out.v };
        }
        let $7;
        if (($b.slice_len(args) > 0n)) {
          $7 = clone$90($rt.idx(args, 0n));
        } else {
          {
            $7 = { $tag: "Unit" };
          }
        }
        const f = $7;
        if ((name === "map")) {
          const out = { v: $b.Vec_new() };
          for (const $8 of $rt.items(xs)) {
            const x = $8;
            $b.Vec_push(out, apply$731(self, clone$90(f), [clone$90(x)], $rt.copy(span)));
          }
          return { $tag: "List", $: out.v };
        }
        if ((name === "filter")) {
          const out = { v: $b.Vec_new() };
          for (const $9 of $rt.items(xs)) {
            const x = $9;
            if (cvEq$725(apply$731(self, clone$90(f), [clone$90(x)], $rt.copy(span)), { $tag: "Bool", $: true })) {
              $b.Vec_push(out, clone$90(x));
            }
          }
          return { $tag: "List", $: out.v };
        }
        if ((name === "any")) {
          for (const $10 of $rt.items(xs)) {
            const x = $10;
            if (cvEq$725(apply$731(self, clone$90(f), [clone$90(x)], $rt.copy(span)), { $tag: "Bool", $: true })) {
              return { $tag: "Bool", $: true };
            }
          }
          return { $tag: "Bool", $: false };
        }
        return fail$391($rt.copy(span), $b.String_asStr(("" + "a list has no `comptime` method `" + name + "`")));
      }
      break m$2;
    }
    if (($1.$tag === "Str")) {
      const s = $1.$;
      if ((name === "len")) {
        return { $tag: "Int", $: $rt.wrap_i128($b.String_len(s)) };
        break m$2;
      }
    }
    if (true) {
      const v = $1;
      return fail$391($rt.copy(span), $b.String_asStr(("" + cvKind$392(v) + " has no `comptime` method `" + name + "`")));
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function apply$731(self, f, args, span) {
  const $1 = f;
  m$2: {
    if (($1.$tag === "Closure")) {
      const params = $1.$[0];
      const body = $1.$[1];
      const env = $1.$[2];
      {
        const e = { v: clone$369(env) };
        const $3 = min$146($b.slice_len(params), $b.slice_len(args));
        for (let i = 0n; i < $3; i++) {
          $b.Vec_push(e, [$b.String_clone($rt.idx(params, i)), { $tag: "Some", $: clone$90($rt.idx(args, i)) }]);
        }
        const saved = $b.replace(new $rt.FieldRef(self.v, "env"), e.v);
        let $4;
        try {
          $4 = { $tag: "Ok", $: eval$$378(self, body) };
        } catch ($5) {
          if (!($5 instanceof $rt.Fail)) throw $5;
          const s = $5.value;
          $4 = { $tag: "Err", $: s };
        }
        const r = $4;
        self.v.env = saved;
        const $6 = r;
        m$7: {
          if ((($6.$tag === "Ok") || ($6.$tag === "Err" && ($6.$.$tag === "CtReturn")))) {
            let v;
            if (($6.$tag === "Ok")) { v = $6.$; }
            else if (($6.$tag === "Err" && ($6.$.$tag === "CtReturn"))) { v = $6.$.$; }
            return v;
            break m$7;
          }
          if (($6.$tag === "Err")) {
            const other = $6.$;
            throw new $rt.Fail(other);
            break m$7;
          }
          $rt.unmatched($6);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const fid = $1.$;
      {
        const decl = $rt.copy($rt.idx(self.v.p.v.fns, fid).decl);
        const module = $rt.idx(self.v.p.v.fns, fid).module;
        let $8;
        const $9 = new $rt.FieldRef($rt.idx($rt.idx(self.v.p.v.modules, decl.module).ast.items, decl.item), "kind");
        const $10 = $9.v;
        m$11: {
          if (($10.$tag === "Function")) {
            const fd = new $rt.FieldRef($10, "$");
            $8 = clone$29(fd.v);
            break m$11;
          }
          if (true) {
            $8 = fail$391($rt.copy(span), "not a `comptime` function");
            break m$11;
          }
          $rt.unmatched($10);
        }
        const fd = $8;
        if ((!fd.sig.isComptime)) {
          fail$391($rt.copy(span), $b.String_asStr(("" + "`" + fd.sig.name.name + "` is not a `comptime function`")));
        }
        let $12;
        const $13 = fd.body;
        m$14: {
          if (($13.$tag === "Some")) {
            const b = $13.$;
            $12 = b;
            break m$14;
          }
          if (($13.$tag === "None")) {
            $12 = fail$391($rt.copy(span), "this function has no body");
            break m$14;
          }
          $rt.unmatched($13);
        }
        const body = $12;
        const e = { v: $b.Vec_new() };
        const $15 = min$146($b.slice_len(fd.sig.params), $b.slice_len(args));
        for (let i = 0n; i < $15; i++) {
          $b.Vec_push(e, [$b.String_clone($rt.idx(fd.sig.params, i).name.name), { $tag: "Some", $: clone$90($rt.idx(args, i)) }]);
        }
        const savedEnv = $b.replace(new $rt.FieldRef(self.v, "env"), e.v);
        const savedModule = $b.replace(new $rt.FieldRef(self.v, "module"), module);
        let $16;
        try {
          $16 = { $tag: "Ok", $: evalBlock$599(self, body) };
        } catch ($17) {
          if (!($17 instanceof $rt.Fail)) throw $17;
          const s = $17.value;
          $16 = { $tag: "Err", $: s };
        }
        const r = $16;
        self.v.env = savedEnv;
        self.v.module = savedModule;
        const $18 = r;
        m$19: {
          if ((($18.$tag === "Ok") || ($18.$tag === "Err" && ($18.$.$tag === "CtReturn")))) {
            let v;
            if (($18.$tag === "Ok")) { v = $18.$; }
            else if (($18.$tag === "Err" && ($18.$.$tag === "CtReturn"))) { v = $18.$.$; }
            return v;
            break m$19;
          }
          if (($18.$tag === "Err")) {
            const other = $18.$;
            throw new $rt.Fail(other);
            break m$19;
          }
          $rt.unmatched($18);
        }
      }
      break m$2;
    }
    if (true) {
      const v = $1;
      return fail$391($rt.copy(span), $b.String_asStr(("" + cvKind$392(v) + " is not a function")));
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function find$732(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function eq$733(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Ty") && ($1[1].$tag === "Ty"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$234(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Region") && ($1[1].$tag === "Region"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$457(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Row") && ($1[1].$tag === "Row"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$736(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Len") && ($1[1].$tag === "Len"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$608(a, b);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eq$734(self, other) {
  {
    {
      {
        if ((!eq$6($rt.idx(self, 0n), $rt.idx(other, 0n)))) {
          return false;
        }
      }
      {
        if ((!eq$234($rt.idx(self, 1n), $rt.idx(other, 1n)))) {
          return false;
        }
      }
    }
    return true;
  }
}
function eq$735(self, other) {
  return (self === other);
}
function eq$736(self, other) {
  {
    {
      {
        if ((!eq$822(self.effs, other.effs))) {
          return false;
        }
      }
      {
        if ((!eq$120(self.tail, other.tail))) {
          return false;
        }
      }
    }
    return true;
  }
}
function freshRegion$737(self) {
  $b.Vec_push(new $rt.FieldRef(self.v, "regions"), { $tag: "None" });
  return { $tag: "Var", $: $rt.wrap_u32($rt.usize($b.slice_len(self.v.regions) - 1n)) };
}
function freshLen$738(self) {
  $b.Vec_push(new $rt.FieldRef(self.v, "lens"), { $tag: "None" });
  return { $tag: "Var", $: $rt.wrap_u32($rt.usize($b.slice_len(self.v.lens) - 1n)) };
}
function instRecordTails$739(t, tails) {
  const $1 = t;
  m$2: {
    if ((($1.$tag === "Record") || ($1.$tag === "Union"))) {
      let r;
      if (($1.$tag === "Record")) { r = $1.$; }
      else if (($1.$tag === "Union")) { r = $1.$; }
      {
        const labels = { v: $b.Vec_new() };
        for (const $3 of $rt.items(r.labels)) {
          const k = $3[0];
          const x = $3[1];
          $b.Vec_push(labels, [$b.String_clone(k), instRecordTails$739(x, tails)]);
        }
        let $4;
        const $5 = r.tail;
        m$6: {
          if (($5.$tag === "Param")) {
            const s = $5.$;
            const $7 = $b.HashMap_get(tails, s.id);
            m$8: {
              if (($7.$tag === "Some")) {
                const x = $7.$;
                $4 = clone$99(x);
                break m$8;
              }
              if (($7.$tag === "None")) {
                $4 = clone$99(r.tail);
                break m$8;
              }
              $rt.unmatched($7);
            }
            break m$6;
          }
          if (true) {
            const other = $5;
            $4 = clone$99(other);
            break m$6;
          }
          $rt.unmatched($5);
        }
        const tail = $4;
        const row = { labels: labels.v, tail: tail };
        const $9 = t;
        m$10: {
          if (($9.$tag === "Record")) {
            return { $tag: "Record", $: row };
            break m$10;
          }
          if (true) {
            return { $tag: "Union", $: row };
            break m$10;
          }
          $rt.unmatched($9);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        const out = { v: $b.Vec_new() };
        for (const $11 of $rt.items(args)) {
          const a = $11;
          const $12 = out;
          let $13;
          const $14 = a;
          m$15: {
            if (($14.$tag === "Ty")) {
              const x = $14.$;
              $13 = { $tag: "Ty", $: instRecordTails$739(x, tails) };
              break m$15;
            }
            if (true) {
              const other = $14;
              $13 = clone$290(other);
              break m$15;
            }
            $rt.unmatched($14);
          }
          $b.Vec_push($12, $13);
        }
        return { $tag: "Named", $: [d, out.v] };
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $16 of $rt.items(ts)) {
          const x = $16;
          $b.Vec_push(out, instRecordTails$739(x, tails));
        }
        return { $tag: "Tuple", $: out.v };
      }
      break m$2;
    }
    if (($1.$tag === "Array")) {
      const x = $1.$[0];
      const l = $1.$[1];
      return { $tag: "Array", $: [$b.Box_new(instRecordTails$739(x, tails)), clone$198(l)] };
      break m$2;
    }
    if (($1.$tag === "Slice")) {
      const x = $1.$;
      return { $tag: "Slice", $: $b.Box_new(instRecordTails$739(x, tails)) };
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const x = $1.$[1];
      return { $tag: "Borrow", $: [m, $b.Box_new(instRecordTails$739(x, tails))] };
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      {
        const params = { v: $b.Vec_new() };
        for (const $17 of $rt.items(f.params)) {
          const x = $17;
          $b.Vec_push(params, instRecordTails$739(x, tails));
        }
        return { $tag: "Fn", $: $b.Box_new({ mode: f.mode, params: params.v, ret: instRecordTails$739(f.ret, tails), effects: clone$40(f.effects) }) };
      }
      break m$2;
    }
    if (true) {
      const other = $1;
      return clone$23(other);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function openFail$740(self, row) {
  const fail = known$104(self.v, "Fail");
  const $1 = $b.slice_len(row.v.effs);
  for (let i = 0n; i < $1; i++) {
    if (($rt.idx(row.v.effs, i).def === fail)) {
      const $2 = first$263($rt.idx(row.v.effs, i).args);
      m$3: {
        if (($2.$tag === "Some")) {
          const t = $2.$;
          {
            const $4 = resolve$109(self.v.s, t);
            m$5: {
              if (($4.$tag === "Union")) {
                const r = $4.$;
                {
                  if (eq$120(r.tail, { $tag: "Closed" })) {
                    const tail = freshRowTail$243(new $rt.FieldRef(self.v, "s"));
                    const $6 = $rt.idx(row.v.effs, i).args;
                    $6[$rt.at($6, 0n)] = { $tag: "Union", $: { labels: clone$74(r.labels), tail: tail } };
                  }
                }
                break m$5;
              }
              if (true) {
                {
                }
                break m$5;
              }
              $rt.unmatched($4);
            }
          }
          break m$3;
        }
        if (true) {
          {
          }
          break m$3;
        }
        $rt.unmatched($2);
      }
    }
  }
  return undefined;
}
function clone$741(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$174(x));
  }
  return v.v;
}
function boundMethod$742(self, bounds, name) {
  for (const $1 of $rt.items(bounds)) {
    const b = $1;
    const $2 = b;
    m$3: {
      if (($2.$tag === "Named")) {
        const d = $2.$[0];
        {
          for (const $4 of $rt.items(ifaceClosure$142(self, d))) {
            const i = $4;
            const $5 = $b.HashMap_get(self.ifaceFns, $b.String_asStr(("" + String(i) + ":" + name)));
            m$6: {
              if (($5.$tag === "Some")) {
                const f = $5.$;
                {
                  let $7;
                  if ((i === d)) {
                    $7 = clone$23(b);
                  } else {
                    {
                      const args = { v: $b.Vec_new() };
                      for (const $8 of $rt.items($rt.idx(self.defs, i).params)) {
                        const g = $8;
                        $b.Vec_push(args, paramArg$291(g));
                      }
                      $7 = { $tag: "Named", $: [i, args.v] };
                    }
                  }
                  const via = $7;
                  return { $tag: "Some", $: [f, via] };
                }
                break m$6;
              }
              if (true) {
                {
                }
                break m$6;
              }
              $rt.unmatched($5);
            }
          }
        }
        break m$3;
      }
      if (true) {
        {
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return { $tag: "None" };
}
function sort$743(self) {
  return $b.slice_sortBy(self, ((a, b) => {
  return cmp$152(a, b);
  }));
}
function methodFor$744(self, imp, name, binds) {
  let $1;
  const $2 = implMethod$492(self, imp, name);
  m$3: {
    if (($2.$tag === "Some")) {
      const m = $2.$;
      $1 = m;
      break m$3;
    }
    if (($2.$tag === "None")) {
      return { $tag: "None" };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const m = $1;
  if ((!isTemplate$21(self, m))) {
    return { $tag: "Some", $: m };
  }
  let $4;
  const $5 = comptimeArgs$147(self, m, binds);
  m$6: {
    if (($5.$tag === "Some")) {
      const c = $5.$;
      $4 = c;
      break m$6;
    }
    if (($5.$tag === "None")) {
      return { $tag: "None" };
      break m$6;
    }
    $rt.unmatched($5);
  }
  const ct = $4;
  const $7 = $b.HashMap_get(self.specs, $b.String_asStr(("" + String(m) + "|" + specKey$493(ct))));
  m$8: {
    if (($7.$tag === "Some")) {
      const f = $7.$;
      return { $tag: "Some", $: f };
      break m$8;
    }
    if (($7.$tag === "None")) {
      return { $tag: "None" };
      break m$8;
    }
    $rt.unmatched($7);
  }
}
function find$745(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function callOp$746(self, def, op, args, expected, e) {
  const effParams = clone$73($rt.idx(self.v.p.v.defs, def).params);
  const all = { v: clone$73(effParams) };
  for (const $1 of $rt.items(op.tparams)) {
    const g = $1;
    $b.Vec_push(all, clone$194(g));
  }
  let s = clone$22(op);
  s.tparams = all.v;
  const inst = instantiate$614(self, s, $b.Vec_new(), false);
  const $2 = expected;
  m$3: {
    if (($2.$tag === "Some")) {
      const x = $2.$;
      {
        tryUnify$237(self, inst.ret, x);
      }
      break m$3;
    }
    if (true) {
      {
      }
      break m$3;
    }
    $rt.unmatched($2);
  }
  const regions = { v: $b.Vec_new() };
  const targs = { v: $b.Vec_new() };
  const $4 = min$146($b.slice_len(effParams), $b.slice_len(inst.args));
  for (let i = 0n; i < $4; i++) {
    const $5 = [$rt.idx(effParams, i).kind, clone$290($rt.idx(inst.args, i))];
    m$6: {
      if ((($5[0].$tag === "Region") && ($5[1].$tag === "Region"))) {
        const r = $5[1].$;
        $b.Vec_push(regions, r);
        break m$6;
      }
      if ((($5[0].$tag === "Type") && ($5[1].$tag === "Ty"))) {
        const t = $5[1].$;
        $b.Vec_push(targs, t);
        break m$6;
      }
      if (true) {
        {
        }
        break m$6;
      }
      $rt.unmatched($5);
    }
  }
  const row = { effs: [{ def: def, regions: regions.v, args: targs.v }], tail: { $tag: "Closed" } };
  perform$437(self, row, $rt.copy(e.span), e.id);
  const params = { v: $b.Vec_new() };
  for (const $7 of $rt.items(inst.params)) {
    const t = $7[1];
    $b.Vec_push(params, clone$23(t));
  }
  checkArgs$621(self, params.v, args, $rt.copy(e.span));
  return inst.ret;
}
function isNone$747(self) {
  return (!$b.Option_isSome(self));
}
function hasSelf$748(self, fid) {
  const $1 = first$664($rt.idx(self.p.v.fns, fid).scheme.params);
  m$2: {
    if (($1.$tag === "Some")) {
      const n = $1.$[0];
      return (n === "self");
      break m$2;
    }
    if (($1.$tag === "None")) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function boundMethodOf$749(self, recv, name) {
  let t = resolve$109(self.v.s, recv);
  while (true) {
    const $1 = t;
    m$2: {
      if (($1.$tag === "Borrow")) {
        const inner = $1.$[1];
        {
          t = resolve$109(self.v.s, inner);
        }
        break m$2;
      }
      if (true) {
        break;
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  let $3;
  const $4 = t;
  m$5: {
    if (($4.$tag === "Param")) {
      const s = $4.$;
      $3 = clone$34(s);
      break m$5;
    }
    if (true) {
      return { $tag: "None" };
      break m$5;
    }
    $rt.unmatched($4);
  }
  const sym = $3;
  let $6;
  const $7 = $b.HashMap_get(self.v.bounds, sym.id);
  m$8: {
    if (($7.$tag === "Some")) {
      const b = $7.$;
      $6 = clone$35(b);
      break m$8;
    }
    if (($7.$tag === "None")) {
      return { $tag: "None" };
      break m$8;
    }
    $rt.unmatched($7);
  }
  const bounds = $6;
  let $9;
  const $10 = boundMethod$742(self.v.p.v, bounds, name);
  m$11: {
    if (($10.$tag === "Some")) {
      const r = $10.$;
      $9 = r;
      break m$11;
    }
    if (($10.$tag === "None")) {
      return { $tag: "None" };
      break m$11;
    }
    $rt.unmatched($10);
  }
  const $12 = $9;
  const fid = $12[0];
  const via = $12[1];
  let $13;
  const $14 = via;
  m$15: {
    if (($14.$tag === "Named")) {
      const a = $14.$[1];
      $13 = a;
      break m$15;
    }
    if (true) {
      return { $tag: "None" };
      break m$15;
    }
    $rt.unmatched($14);
  }
  const bargs = $13;
  const fixed = { v: [{ $tag: "Ty", $: clone$23(t) }] };
  for (const $16 of $rt.items(bargs)) {
    const a = $16;
    $b.Vec_push(fixed, clone$290(a));
  }
  return { $tag: "Some", $: [fid, fixed.v] };
}
function find$750(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function ensureAssocs$751(self, t) {
  const $1 = resolve$109(self.v.s, t);
  m$2: {
    if (($1.$tag === "Assoc")) {
      const base = $1.$[0];
      const name = $1.$[1];
      {
        const b = zonk$134(self.v.s, base);
        ensureAssoc$823(self.v.p, b, $b.String_asStr(name));
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      const f = $1.$;
      {
        for (const $3 of $rt.items(f.params)) {
          const x = $3;
          ensureAssocs$751(self, x);
        }
        ensureAssocs$751(self, f.ret);
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const inner = $1.$[1];
      return ensureAssocs$751(self, inner);
      break m$2;
    }
    if (true) {
      {
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function boxed$752(self, t) {
  const $1 = resolve$109(self.s, t);
  m$2: {
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      if ((d === known$104(self, "Box"))) {
        const $3 = first$258(args);
        m$4: {
          if (($3.$tag === "Some" && ($3.$.$tag === "Ty"))) {
            const inner = $3.$.$;
            return { $tag: "Some", $: clone$23(inner) };
            break m$4;
          }
          if (true) {
            return { $tag: "None" };
            break m$4;
          }
          $rt.unmatched($3);
        }
        break m$2;
      }
    }
    if (true) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function typeOf$753(self, x) {
  const $1 = $b.HashMap_get(self.typed.exprs, x.id);
  m$2: {
    if (($1.$tag === "Some")) {
      const t = $1.$;
      return { $tag: "Some", $: resolve$109(self.s, t) };
      break m$2;
    }
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function irrefutable$754(p) {
  const $1 = p.kind;
  m$2: {
    if ((($1.$tag === "Wild") || ($1.$tag === "Bind"))) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ps = $1.$;
      return every$755($b.slice_iter(ps), ((q) => {
  return irrefutable$754(q);
      }));
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      return every$756($b.slice_iter(fields), (($0$$3) => {
  {
    const $4 = $0$$3;
    const q = $4[1];
    const $5 = q;
    m$6: {
      if (($5.$tag === "Some")) {
        const x = $5.$;
        return irrefutable$754(x);
        break m$6;
      }
      if (($5.$tag === "None")) {
        return true;
        break m$6;
      }
      $rt.unmatched($5);
    }
  }
      }));
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function every$755(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if ((!test(x))) {
      return false;
    }
  }
  return true;
}
function every$756(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if ((!test(x))) {
      return false;
    }
  }
  return true;
}
function clone$757(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$174(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function escapes$758(self, sym, result) {
  if (mentionsRegion$637(zonk$134(self.s, result), sym)) {
    return true;
  }
  for (const $1 of $rt.items(self.scopes)) {
    const sc = $1;
    const $2 = $b.Gen_each($b.HashMap_values(sc));
    let $4;
    for (let $3 = $2.next(); !$3.done; $3 = $2.next($4)) {
      $4 = undefined;
      const $5 = $3.value.item;
      const t = $5;
      if (mentionsRegion$637(zonk$134(self.s, t), sym)) {
        return true;
      }
    }
  }
  return false;
}
function clone$759(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$824(x));
  }
  return v.v;
}
function get$760(self, i) {
  if ((i < $b.slice_len(self))) {
    return { $tag: "Some", $: $rt.idx(self, i) };
  } else {
    {
      return { $tag: "None" };
    }
  }
}
function get$761(self, i) {
  if ((i < $b.slice_len(self))) {
    return { $tag: "Some", $: $rt.idx(self, i) };
  } else {
    {
      return { $tag: "None" };
    }
  }
}
function last$762(self) {
  if (($b.slice_len(self) === 0n)) {
    return { $tag: "None" };
  } else {
    {
      return { $tag: "Some", $: $rt.idx(self, $rt.usize($b.slice_len(self) - 1n)) };
    }
  }
}
function eq$763(self, other) {
  {
    {
      {
        if ((!eq$605(self.def, other.def))) {
          return false;
        }
      }
      {
        if ((!eq$825(self.regions, other.regions))) {
          return false;
        }
      }
      {
        if ((!eq$411(self.args, other.args))) {
          return false;
        }
      }
    }
    return true;
  }
}
function clone$764(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const x = $1.$;
      return { $tag: "Tuple", $: clone$649(x) };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const x = $1.$;
      return { $tag: "Record", $: clone$765(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$765(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$826(x));
  }
  return v.v;
}
function clone$766(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$475(x));
  }
  return v.v;
}
function includes$767(self, x) {
  for (const $1 of $rt.items(self)) {
    const y = $1;
    if ((y === x)) {
      return true;
    }
  }
  return false;
}
function matchArg$768(pat, arg, vars, binds) {
  const $1 = [pat, arg];
  m$2: {
    if ((($1[0].$tag === "Ty") && ($1[1].$tag === "Ty"))) {
      const p = $1[0].$;
      const t = $1[1].$;
      return matchTy$660(p, t, vars, binds);
      break m$2;
    }
    if (((($1[0].$tag === "Region" && ($1[0].$.$tag === "Param"))) || (($1[0].$tag === "Len" && ($1[0].$.$tag === "Param"))))) {
      let s, a;
      if ((($1[0].$tag === "Region" && ($1[0].$.$tag === "Param")))) { s = $1[0].$.$; a = $1[1]; }
      else if ((($1[0].$tag === "Len" && ($1[0].$.$tag === "Param")))) { s = $1[0].$.$; a = $1[1]; }
      if (includes$767(vars, s.id)) {
        {
          $b.HashMap_insert(binds, s.id, clone$290(a));
          return true;
        }
        break m$2;
      }
    }
    if ((($1[0].$tag === "Row"))) {
      const r = $1[0].$;
      const a = $1[1];
      {
        const $3 = r.tail;
        m$4: {
          if (($3.$tag === "Param")) {
            const s = $3.$;
            {
              if (includes$767(vars, s.id)) {
                $b.HashMap_insert(binds, s.id, clone$290(a));
              }
            }
            break m$4;
          }
          if (true) {
            {
            }
            break m$4;
          }
          $rt.unmatched($3);
        }
        return true;
      }
      break m$2;
    }
    if (true) {
      return true;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function lentName$769(self, name, scopes) {
  let i = $b.slice_len(scopes);
  while ((i > 0n)) {
    i = $rt.usize(i - 1n);
    const $1 = $b.HashMap_get($rt.idx(scopes, i), name);
    m$2: {
      if (($1.$tag === "Some")) {
        const param = $1.$[0];
        const key = $1.$[1];
        {
          if (param) {
            insert$20(new $rt.FieldRef(self.v, "cellParams"), key);
          } else {
            {
              insert$20(new $rt.FieldRef(self.v, "cells"), key);
            }
          }
          return;
        }
        break m$2;
      }
      if (true) {
        {
        }
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  return undefined;
}
function isString$770(self, t) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Prim" && ($1.$.$tag === "Str"))) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const inner = $1.$[1];
      return isString$770(self, inner);
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      return isKnown$479(self.p, d, "String");
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function calleeJs$771(self, c) {
  const $1 = c;
  m$2: {
    if (($1.$tag === "Inst")) {
      const i = $1.$;
      return $b.String_clone($rt.idx(self.insts, i).js);
      break m$2;
    }
    if (($1.$tag === "Builtin")) {
      const k = $1.$;
      return ("" + "$b." + k);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function constant$772(self, c) {
  const $1 = $b.HashMap_get(self.v.consts, c);
  m$2: {
    if (($1.$tag === "Some")) {
      const js = $1.$;
      {
        return $b.String_clone(js);
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const js = ("" + "$c" + String(c) + "$" + $rt.idx(self.v.p.consts, c).name);
  $b.HashMap_insert(new $rt.FieldRef(self.v, "consts"), c, $b.String_clone(js));
  const value = clone$60($rt.idx(self.v.p.consts, c).value);
  const ty = clone$23($rt.idx(self.v.p.consts, c).ty);
  const module = $b.replace(new $rt.FieldRef(self.v, "module"), $rt.idx(self.v.p.consts, c).module);
  let $3;
  try {
    $3 = constValue$827(self, value, ty);
  } catch ($4) {
    if (!($4 instanceof $rt.Fail)) throw $4;
    const d = $4.value;
    self.v.module = module;
    throw new $rt.Fail(d);
  }
  const v = $3;
  self.v.module = module;
  $b.String_push(new $rt.FieldRef(self.v, "head"), ("" + "const " + js + " = " + v + ";\n"));
  return js;
}
function args$773(self, args, params) {
  let last = 0n;
  const $1 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(args)));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const i = $4[0];
    const a = $4[1];
    if ((!simple$522(a))) {
      last = i;
    }
  }
  const out = { v: $b.Vec_new() };
  const $5 = $b.Gen_each($b.Gen_enumerate($b.slice_iter(args)));
  let $7;
  for (let $6 = $5.next(); !$6.done; $6 = $5.next($7)) {
    $7 = undefined;
    const $8 = $6.value.item;
    const i = $8[0];
    const a = $8[1];
    let $9;
    const $10 = get$761(params, i);
    m$11: {
      if (($10.$tag === "Some")) {
        const t = $10.$;
        $9 = exAs$314(self, a, t);
        break m$11;
      }
      if (($10.$tag === "None")) {
        $9 = value$313(self, a);
        break m$11;
      }
      $rt.unmatched($10);
    }
    const x = $9;
    const $12 = out;
    let $13;
    if ((i < last)) {
      $13 = save$319(self, x);
    } else {
      {
        $13 = x;
      }
    }
    $b.Vec_push($12, $13);
  }
  return out.v;
}
function calleeSuspends$774(self, c, fid, args) {
  const $1 = c;
  m$2: {
    if (($1.$tag === "Inst")) {
      const i = $1.$;
      return $rt.idx(self.insts, i).suspends;
      break m$2;
    }
    if (($1.$tag === "Builtin")) {
      return fnSuspends$160(self, fid, args);
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function rowYields$775(p, r) {
  return some$500($b.slice_iter(r.effs), ((e) => {
  return ($rt.idx(p.defs, e.def).name === "Yield");
  }));
}
function builtin$776(self, key, vs, e, delegate) {
  const all = { v: vs };
  if ((key === "repeat")) {
    const $1 = exprTy$316(self.v, e.id);
    m$2: {
      if (($1.$tag === "Array" && ($1.$[1].$tag === "Known"))) {
        const n = $1.$[1].$;
        $b.Vec_push(all, ("" + String(n)));
        break m$2;
      }
      if (true) {
        fail$514(self.v, $rt.copy(e.span), "`repeat` needs an array type of a known length");
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  const call = ("" + "$b." + key + "(" + join$53(all.v, ", ") + ")");
  if (delegate) {
    return ("" + "(yield* " + call + ")");
  } else {
    {
      return call;
    }
  }
}
function isNone$777(self) {
  return (!$b.Option_isSome(self));
}
function arith$778(self, op, x, y, t, operand) {
  if ((op === "==")) {
    return ("" + "(" + x + " === " + y + ")");
  }
  if ((op === "!=")) {
    return ("" + "(" + x + " !== " + y + ")");
  }
  const $1 = intPrim$171(t);
  m$2: {
    if (($1.$tag === "Some")) {
      const p = $1.$;
      {
        const name = primName$300(p);
        const $3 = op;
        m$4: {
          if ($3 === "/") {
            return ("" + "$rt.div(" + x + ", " + y + ", $rt." + name + ")");
            break m$4;
          }
          if ($3 === "%") {
            return ("" + "$rt.rem(" + x + ", " + y + ")");
            break m$4;
          }
          if (($3 === "&" || $3 === "|" || $3 === "^")) {
            return ("" + "(" + x + " " + op + " " + y + ")");
            break m$4;
          }
          if ($3 === ">>") {
            return ("" + "(" + x + " >> " + y + ")");
            break m$4;
          }
          if (true) {
            return ("" + "$rt." + name + "(" + x + " " + op + " " + y + ")");
            break m$4;
          }
          $rt.unmatched($3);
        }
      }
      break m$2;
    }
    if (($1.$tag === "None")) {
      {
        if ((floatTy$511(operand) && (op === "%"))) {
          return ("" + "$rt.fmod(" + x + ", " + y + ")");
        }
        return ("" + "(" + x + " " + op + " " + y + ")");
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function place$779(self, e) {
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "Ident")) {
      const n = $1.$;
      {
        const $3 = local$311(self.v, $b.String_asStr(n));
        m$4: {
          if (($3.$tag === "Some")) {
            const l = $3.$;
            if ((l.cell || isMutBorrow$508(exprTy$316(self.v, e.id)))) {
              return ("" + l.js + ".v");
            } else {
              {
                return l.js;
              }
            }
            break m$4;
          }
          if (($3.$tag === "None")) {
            return fail$514(self.v, $rt.copy(e.span), "this is not a place");
            break m$4;
          }
          $rt.unmatched($3);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      const name = $1.$.name;
      {
        const t0 = obj$668(self, target);
        let $5;
        if (simple$522(target)) {
          $5 = t0;
        } else {
          {
            $5 = save$319(self, t0);
          }
        }
        const t = $5;
        return ("" + t + "." + mangleField$669($b.String_asStr(name.name)));
      }
      break m$2;
    }
    if (($1.$tag === "Index")) {
      const target = $1.$.target;
      const index = $1.$.index;
      {
        const $6 = index.kind;
        m$7: {
          if (($6.$tag === "Range")) {
            {
              unsupported$828(self.v, $rt.copy(e.span), "assigning a slice");
            }
            break m$7;
          }
          if (true) {
            {
            }
            break m$7;
          }
          $rt.unmatched($6);
        }
        const a0 = obj$668(self, target);
        const a = save$319(self, a0);
        const i = value$313(self, index);
        return ("" + a + "[$rt.at(" + a + ", " + i + ")]");
      }
      break m$2;
    }
    if (($1.$tag === "BorrowMut")) {
      const x = $1.$;
      return place$779(self, x);
      break m$2;
    }
    if (true) {
      {
        if (isMutBorrow$508(exprTy$316(self.v, e.id))) {
          const v = ex$507(self, e);
          return ("" + v + ".v");
        }
        return fail$514(self.v, $rt.copy(e.span), "this is not a place");
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function slotTy$780(self, id) {
  const $1 = $b.HashMap_get(self.p.typed, self.fid);
  m$2: {
    if (($1.$tag === "Some")) {
      const t = $1.$;
      const $3 = $b.HashMap_get(t.slots, id);
      m$4: {
        if (($3.$tag === "Some")) {
          const x = $3.$;
          return { $tag: "Some", $: concrete$163(self, x) };
          break m$4;
        }
        if (($3.$tag === "None")) {
          return { $tag: "None" };
          break m$4;
        }
        $rt.unmatched($3);
      }
      break m$2;
    }
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function blockReturns$781(b) {
  let $3 = some$89($b.slice_iter(b.stmts), ((s) => {
  const $1 = s;
  m$2: {
    if (($1.$tag === "Let")) {
      const init = $1.$.init;
      return returns$829(init);
      break m$2;
    }
    if ((($1.$tag === "Expr") || ($1.$tag === "Defer"))) {
      let x;
      if (($1.$tag === "Expr")) { x = $1.$; }
      else if (($1.$tag === "Defer")) { x = $1.$; }
      return returns$829(x);
      break m$2;
    }
    $rt.unmatched($1);
  }
  }));
  if (!$3) {
    let $4;
    const $5 = b.tail;
    m$6: {
      if (($5.$tag === "Some")) {
        const t = $5.$;
        $4 = returns$829(t);
        break m$6;
      }
      if (($5.$tag === "None")) {
        $4 = false;
        break m$6;
      }
      $rt.unmatched($5);
    }
    $3 = $4;
  }
  return $3;
}
function handlerPart$782(self, params, resumes, body, result) {
  const saved = $b.replace(new $rt.FieldRef(self.v, "out"), $b.String_new());
  const savedIndent = $b.replace(new $rt.FieldRef(self.v, "indent"), 1n);
  const savedSuspends = $b.replace(new $rt.FieldRef(self.v, "suspends"), true);
  const savedRet = $b.replace(new $rt.FieldRef(self.v, "ret"), result);
  const savedInHandle = $b.replace(new $rt.FieldRef(self.v, "inHandle"), true);
  push$165(self);
  const names = { v: $b.Vec_new() };
  const celled = { v: $b.Vec_new() };
  const all = { v: clone$400(params) };
  const $1 = resumes;
  m$2: {
    if (($1.$tag === "Some")) {
      const k = $1.$;
      {
        $b.Vec_push(all, clone$218(k));
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  for (const $3 of $rt.items(all.v)) {
    const p = $3;
    const cell = has$19(self.v.cellParams, p.span.start);
    const js = declare$166(self, $b.String_asStr(p.name), cell);
    if (cell) {
      const raw = fresh$167(self);
      $b.Vec_push(names, $b.String_clone(raw));
      $b.Vec_push(celled, [js, raw]);
    } else {
      {
        $b.Vec_push(names, js);
      }
    }
  }
  for (const $4 of $rt.items(celled.v)) {
    const js = $4[0];
    const raw = $4[1];
    line$168(self, ("" + "const " + js + " = { v: " + raw + " };"));
  }
  blockInto$520(self, body, { $tag: "Return" });
  pop$170(self);
  const inner = $b.replace(new $rt.FieldRef(self.v, "out"), saved);
  self.v.indent = savedIndent;
  self.v.suspends = savedSuspends;
  self.v.ret = savedRet;
  self.v.inHandle = savedInHandle;
  const close = { v: $b.String_new() };
  const $5 = self.v.indent;
  for (let $6$$7 = 0n; $6$$7 < $5; $6$$7++) {
    $b.String_push(close, "  ");
  }
  return ("" + "(function* (" + join$53(names.v, ", ") + ") {\n" + inner + close.v + "})");
}
function clone$783(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Field")) {
      const x = $1.$;
      return { $tag: "Field", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Index")) {
      const x = $1.$;
      return { $tag: "Index", $: clone$174(x) };
      break m$2;
    }
    if (($1.$tag === "Payload")) {
      return { $tag: "Payload" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function every$784(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if ((!test(x))) {
      return false;
    }
  }
  return true;
}
function clone$785(self) {
  const m = { v: $b.HashMap_new() };
  const $1 = $b.Gen_each($b.HashMap_entries(self));
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const k = $4[0];
    const v = $4[1];
    $b.HashMap_insert(m, clone$77(k), clone$290(v));
  }
  return m.v;
}
function skipTrivia$786(self) {
  while (true) {
    const c = peek$788(self.v);
    if (((self.v.pos < self.v.end) && isSpace$830(c))) {
      self.v.pos = $rt.usize(self.v.pos + 1n);
    } else {
      if (((c === 47n) && (peekAt$789(self.v, 1n) === 47n))) {
        while (((self.v.pos < self.v.end) && (peek$788(self.v) !== 10n))) {
          self.v.pos = $rt.usize(self.v.pos + 1n);
        }
      } else {
        if (((c === 47n) && (peekAt$789(self.v, 1n) === 42n))) {
          const start = self.v.pos;
          self.v.pos = $rt.usize(self.v.pos + 2n);
          while ((!((peek$788(self.v) === 42n) && (peekAt$789(self.v, 1n) === 47n)))) {
            if ((self.v.pos >= self.v.end)) {
              throw new $rt.Fail(err$791(self.v, start, "unterminated block comment"));
            }
            self.v.pos = $rt.usize(self.v.pos + 1n);
          }
          self.v.pos = $rt.usize(self.v.pos + 2n);
        } else {
          {
            return;
          }
        }
      }
    }
  }
  return undefined;
}
function push$787(self, tok, start) {
  $b.Vec_push(new $rt.FieldRef(self.v, "out"), { tok: tok, span: { start: start, end: self.v.pos } });
  return undefined;
}
function peek$788(self) {
  return peekAt$789(self, 0n);
}
function peekAt$789(self, n) {
  if (($rt.usize(self.pos + n) < self.end)) {
    return $rt.idx(self.bytes, $rt.usize(self.pos + n));
  } else {
    {
      return 0n;
    }
  }
}
function byteChar$790(self, start) {
  if ((self.v.pos >= self.v.end)) {
    throw new $rt.Fail(err$791(self.v, start, "unterminated byte literal"));
  }
  const c = peek$788(self.v);
  self.v.pos = $rt.usize(self.v.pos + 1n);
  let $1;
  if ((c === 92n)) {
    $1 = escape$831(self, start);
  } else {
    {
      $1 = $rt.wrap_u32(c);
    }
  }
  const v = $1;
  if ((v > 0x7fn)) {
    throw new $rt.Fail(err$791(self.v, start, "byte literal must be ASCII"));
  }
  return $rt.wrap_u8(v);
}
function err$791(self, start, message) {
  return { $tag: "Diagnostic", $: { span: { start: start, end: max$156(self.pos, $rt.usize(start + 1n)) }, message: $b.str_toString(message) } };
}
function isAlpha$792(c) {
  return ((((c >= 97n) && (c <= 122n)) || ((c >= 65n) && (c <= 90n))) || (c >= 0x80n));
}
function word$793(self) {
  const start = self.v.pos;
  while (((self.v.pos < self.v.end) && ((isAlpha$792(peek$788(self.v)) || isDigit$794(peek$788(self.v))) || (peek$788(self.v) === 95n)))) {
    self.v.pos = $rt.usize(self.v.pos + 1n);
  }
  return $b.str_toString($b.str_slice(self.v.src, start, self.v.pos));
}
function isDigit$794(c) {
  return ((c >= 48n) && (c <= 57n));
}
function number$795(self) {
  const start = self.v.pos;
  if (((peek$788(self.v) === 48n) && (((peekAt$789(self.v, 1n) === 120n) || (peekAt$789(self.v, 1n) === 98n)) || (peekAt$789(self.v, 1n) === 111n)))) {
    self.v.pos = $rt.usize(self.v.pos + 2n);
    while (((self.v.pos < self.v.end) && (isHex$832(peek$788(self.v)) || (peek$788(self.v) === 95n)))) {
      self.v.pos = $rt.usize(self.v.pos + 1n);
    }
    return { $tag: "Int", $: $b.str_replaceAll($b.str_slice(self.v.src, start, self.v.pos), "_", "") };
  }
  digits$833(self);
  let float = false;
  if (((peek$788(self.v) === 46n) && isDigit$794(peekAt$789(self.v, 1n)))) {
    float = true;
    self.v.pos = $rt.usize(self.v.pos + 1n);
    digits$833(self);
  }
  const e = peek$788(self.v);
  const sign = ((peekAt$789(self.v, 1n) === 43n) || (peekAt$789(self.v, 1n) === 45n));
  if ((((e === 101n) || (e === 69n)) && (isDigit$794(peekAt$789(self.v, 1n)) || (sign && isDigit$794(peekAt$789(self.v, 2n)))))) {
    float = true;
    self.v.pos = $rt.usize(self.v.pos + 1n);
    if (((peek$788(self.v) === 43n) || (peek$788(self.v) === 45n))) {
      self.v.pos = $rt.usize(self.v.pos + 1n);
    }
    digits$833(self);
  }
  const text = $b.str_replaceAll($b.str_slice(self.v.src, start, self.v.pos), "_", "");
  if (float) {
    return { $tag: "Float", $: text };
  } else {
    {
      return { $tag: "Int", $: text };
    }
  }
}
function string$796(self, start, close) {
  const s = { v: $b.String_new() };
  let run = self.v.pos;
  while (true) {
    if ((self.v.pos >= self.v.end)) {
      throw new $rt.Fail(err$791(self.v, start, "unterminated string"));
    }
    const c = peek$788(self.v);
    if ((c === close)) {
      $b.String_push(s, $b.str_slice(self.v.src, run, self.v.pos));
      self.v.pos = $rt.usize(self.v.pos + 1n);
      return s.v;
    }
    if ((c === 92n)) {
      $b.String_push(s, $b.str_slice(self.v.src, run, self.v.pos));
      self.v.pos = $rt.usize(self.v.pos + 1n);
      pushChar$834(s, escape$831(self, start));
      run = self.v.pos;
    } else {
      {
        self.v.pos = $rt.usize(self.v.pos + 1n);
      }
    }
  }
  return s.v;
}
function template$797(self, start) {
  const parts = { v: $b.Vec_new() };
  const lit = { v: $b.String_new() };
  let run = self.v.pos;
  while (true) {
    if ((self.v.pos >= self.v.end)) {
      throw new $rt.Fail(err$791(self.v, start, "unterminated template literal"));
    }
    const c = peek$788(self.v);
    if ((c === 96n)) {
      $b.String_push(lit, $b.str_slice(self.v.src, run, self.v.pos));
      self.v.pos = $rt.usize(self.v.pos + 1n);
      break;
    }
    if ((c === 92n)) {
      $b.String_push(lit, $b.str_slice(self.v.src, run, self.v.pos));
      self.v.pos = $rt.usize(self.v.pos + 1n);
      pushChar$834(lit, escape$831(self, start));
      run = self.v.pos;
    } else {
      if (((c === 36n) && (peekAt$789(self.v, 1n) === 123n))) {
        $b.String_push(lit, $b.str_slice(self.v.src, run, self.v.pos));
        self.v.pos = $rt.usize(self.v.pos + 2n);
        $b.Vec_push(parts, { $tag: "Lit", $: $b.replace(lit, $b.String_new()) });
        const from = self.v.pos;
        skipBalanced$835(self, start);
        $b.Vec_push(parts, { $tag: "Expr", $: { start: from, end: $rt.usize(self.v.pos - 1n) } });
        run = self.v.pos;
      } else {
        {
          self.v.pos = $rt.usize(self.v.pos + 1n);
        }
      }
    }
  }
  $b.Vec_push(parts, { $tag: "Lit", $: lit.v });
  return parts.v;
}
function startsWith$798(self, p) {
  const pb = $b.str_asBytes(p);
  if (($rt.usize(self.pos + $b.slice_len(pb)) > self.end)) {
    return false;
  }
  const $1 = $b.slice_len(pb);
  for (let i = 0n; i < $1; i++) {
    if (($rt.idx(self.bytes, $rt.usize(self.pos + i)) !== $rt.idx(pb, i))) {
      return false;
    }
  }
  return true;
}
function eq$799(self, other) {
  const $1 = [self, other];
  m$2: {
    if ((($1[0].$tag === "Lit") && ($1[1].$tag === "Lit"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$6(a, b);
      break m$2;
    }
    if ((($1[0].$tag === "Expr") && ($1[1].$tag === "Expr"))) {
      const a = $1[0].$;
      const b = $1[1].$;
      return eq$570(a, b);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function fieldItems$800(self) {
  const fields = { v: $b.Vec_new() };
  while (((!at$532(self.v, "}")) && (!at$532(self.v, "...")))) {
    const generated = ((isKw$538(tokAt$537(self.v, 1n), "for") || isKw$538(tokAt$537(self.v, 1n), "if")) || wordAt$836(self.v, 1n, "match"));
    if ((atKw$530(self.v, "comptime") && (!generated))) {
      const start = span$528(self.v);
      bump$539(self);
      const e = expr$545(self);
      expect$544(self, ";");
      $b.Vec_push(fields, { name: mkIdent$801("", since$554(self.v, $rt.copy(start))), ty: { kind: { $tag: "EmptyRow" }, span: $rt.copy(start) }, private: false, computed: { $tag: "None" }, generate: { $tag: "Some", $: $b.Box_new({ $tag: "Do", $: e }) } });
      continue;
    }
    if (atKw$530(self.v, "comptime")) {
      const start = span$528(self.v);
      const g = generate$837(self, ((p) => {
  return fieldItems$800(p);
      }));
      $b.Vec_push(fields, { name: mkIdent$801("", since$554(self.v, $rt.copy(start))), ty: { kind: { $tag: "EmptyRow" }, span: $rt.copy(start) }, private: false, computed: { $tag: "None" }, generate: { $tag: "Some", $: $b.Box_new(g) } });
      if ((!eat$542(self, ";"))) {
        eat$542(self, ",");
      }
      continue;
    }
    const private$ = (atWord$536(self.v, "private") && isIdent$549(tokAt$537(self.v, 1n)));
    if (private$) {
      bump$539(self);
    }
    const $1 = entryName$838(self);
    const name = $1[0];
    const computed = $1[1];
    expect$544(self, ":");
    const ty = ty$543(self);
    $b.Vec_push(fields, { name: name, ty: ty, private: private$, computed: computed, generate: { $tag: "None" } });
    if (((!eat$542(self, ";")) && (!eat$542(self, ",")))) {
      break;
    }
  }
  return fields.v;
}
function mkIdent$801(name, span) {
  return { name: $b.str_toString(name), span: span };
}
function tyAtom$802(self) {
  const start = span$528(self.v);
  let $1;
  if (at$532(self.v, "[")) {
    bump$539(self);
    if (eat$542(self, "]")) {
      $1 = { $tag: "EmptyRow" };
    } else {
      {
        const tys = { v: $b.Vec_new() };
        $b.Vec_push(tys, ty$543(self));
        while (eat$542(self, ",")) {
          if (at$532(self.v, "]")) {
            break;
          }
          $b.Vec_push(tys, ty$543(self));
        }
        expect$544(self, "]");
        $1 = { $tag: "Tuple", $: tys.v };
      }
    }
  } else {
    if (at$532(self.v, "{")) {
      bump$539(self);
      const fields = { v: $b.Vec_new() };
      let rest = { $tag: "None" };
      while ((!at$532(self.v, "}"))) {
        if (eat$542(self, "...")) {
          rest = { $tag: "Some", $: ident$541(self) };
          eat$542(self, ";");
          break;
        }
        const items = { v: fieldItems$800(self) };
        if (($b.slice_len(items.v) === 0n)) {
          break;
        }
        const $2 = $b.Gen_each($b.Vec_drain(items));
        let $4;
        for (let $3 = $2.next(); !$3.done; $3 = $2.next($4)) {
          $4 = undefined;
          const $5 = $3.value.item;
          const f = $5;
          $b.Vec_push(fields, f);
        }
      }
      expect$544(self, "}");
      $1 = { $tag: "Record", $: { fields: fields.v, rest: rest } };
    } else {
      if (eatKw$529(self, "dyn")) {
        $1 = { $tag: "Dyn", $: path$839(self) };
      } else {
        if (isIdent$549(tok$527(self.v))) {
          const segments = path$839(self);
          $1 = { $tag: "Path", $: { segments: segments, args: typeArgs$840(self) } };
        } else {
          let $6;
          const $7 = tok$527(self.v);
          m$8: {
            if (($7.$tag === "Int")) {
              $6 = true;
              break m$8;
            }
            if (true) {
              $6 = false;
              break m$8;
            }
            $rt.unmatched($7);
          }
          if ($6) {
            $1 = { $tag: "Expr", $: $b.Box_new(primary$841(self)) };
          } else {
            {
              $1 = error$552(self.v, "a type");
            }
          }
        }
      }
    }
  }
  const kind = $1;
  return { kind: kind, span: since$554(self.v, $rt.copy(start)) };
}
function params$803(self, typed) {
  expect$544(self, "(");
  const out = { v: $b.Vec_new() };
  while ((!at$532(self.v, ")"))) {
    const isComptime = eatKw$529(self, "comptime");
    const name = ident$541(self);
    let $1;
    if (eat$542(self, ":")) {
      $1 = { $tag: "Some", $: ty$543(self) };
    } else {
      if (typed) {
        $1 = error$552(self.v, "`:` and a parameter type");
      } else {
        {
          $1 = { $tag: "None" };
        }
      }
    }
    const ty = $1;
    $b.Vec_push(out, { isComptime: isComptime, name: name, ty: ty });
    if ((!eat$542(self, ","))) {
      break;
    }
  }
  expect$544(self, ")");
  return out.v;
}
function ret$804(self) {
  const ty = ty$543(self);
  const from = { v: $b.Vec_new() };
  if (eatWord$534(self, "from")) {
    $b.Vec_push(from, ident$541(self));
    while (((at$532(self.v, ",") && isIdent$549(tokAt$537(self.v, 1n))) && (!isPunct$695(tokAt$537(self.v, 2n), ":")))) {
      bump$539(self);
      $b.Vec_push(from, ident$541(self));
    }
  }
  return { ty: ty, from: from.v };
}
function uses$805(self) {
  if ((!eatKw$529(self, "uses"))) {
    return { $tag: "None" };
  }
  const row = { v: $b.Vec_new() };
  $b.Vec_push(row, rowItem$842(self));
  while ((at$532(self.v, ",") && rowContinues$843(self.v))) {
    bump$539(self);
    $b.Vec_push(row, rowItem$842(self));
  }
  return { $tag: "Some", $: row.v };
}
function binary$806(self, level) {
  if ((level === $b.slice_len($c8$BINARY))) {
    return cast$844(self);
  }
  const start = span$528(self.v);
  let lhs = binary$806(self, $rt.usize(level + 1n));
  while (true) {
    const $1 = binaryOp$845(self.v, level);
    m$2: {
      if (($1.$tag === "Some")) {
        const op = $1.$[0];
        const width = $1.$[1];
        {
          const $3 = width;
          for (let $4$$5 = 0n; $4$$5 < $3; $4$$5++) {
            bump$539(self);
          }
          const rhs = binary$806(self, $rt.usize(level + 1n));
          lhs = expr_$706(self, { $tag: "Binary", $: { op: op, lhs: $b.Box_new(lhs), rhs: $b.Box_new(rhs) } }, since$554(self.v, $rt.copy(start)));
        }
        break m$2;
      }
      if (true) {
        break;
        break m$2;
      }
      $rt.unmatched($1);
    }
  }
  return lhs;
}
function patternOne$807(self) {
  const start = span$528(self.v);
  const t = clone$846(tok$527(self.v));
  let $1;
  const $2 = t;
  m$3: {
    if (($2.$tag === "Ident")) {
      const name = $2.$;
      if ((name === "_")) {
        {
          bump$539(self);
          $1 = { $tag: "Wild" };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Ident")) {
      const name = $2.$;
      if ((isUpper$847($b.String_asStr(name)) && atN$702(self.v, 1n, "{"))) {
        {
          const path = { v: $b.Vec_new() };
          $b.Vec_push(path, ident$541(self));
          $1 = { $tag: "Record", $: { name: { $tag: "Some", $: path.v }, fields: fieldPats$848(self) } };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Ident")) {
      const name = $2.$;
      {
        bump$539(self);
        $1 = { $tag: "Bind", $: name };
      }
      break m$3;
    }
    if (($2.$tag === "Tag")) {
      const name = $2.$;
      {
        bump$539(self);
        $1 = { $tag: "Tag", $: { name: name, args: tagPatArgs$849(self) } };
      }
      break m$3;
    }
    if (($2.$tag === "Punct")) {
      const p = $2.$;
      if ((p === "#[")) {
        {
          bump$539(self);
          const name = expr$545(self);
          expect$544(self, "]");
          $1 = { $tag: "TagAt", $: { name: $b.Box_new(name), args: tagPatArgs$849(self) } };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Kw")) {
      const k = $2.$;
      if ((k === "comptime")) {
        {
          const cstart = span$528(self.v);
          bump$539(self);
          const e = postfix$850(self);
          $1 = { $tag: "Lit", $: $b.Box_new(expr_$706(self, { $tag: "Comptime", $: $b.Box_new(e) }, since$554(self.v, $rt.copy(cstart)))) };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Punct")) {
      const p = $2.$;
      if ((p === "[")) {
        {
          bump$539(self);
          const pats = { v: $b.Vec_new() };
          while ((!at$532(self.v, "]"))) {
            $b.Vec_push(pats, pattern$851(self));
            if ((!eat$542(self, ","))) {
              break;
            }
          }
          expect$544(self, "]");
          $1 = { $tag: "Tuple", $: pats.v };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Punct")) {
      const p = $2.$;
      if ((p === "{")) {
        $1 = { $tag: "Record", $: { name: { $tag: "None" }, fields: fieldPats$848(self) } };
        break m$3;
      }
    }
    if ((($2.$tag === "Int") || ($2.$tag === "Float") || ($2.$tag === "Byte") || ($2.$tag === "Str"))) {
      $1 = { $tag: "Lit", $: $b.Box_new(primary$841(self)) };
      break m$3;
    }
    if (($2.$tag === "Kw")) {
      const k = $2.$;
      if (((k === "true") || (k === "false"))) {
        $1 = { $tag: "Lit", $: $b.Box_new(primary$841(self)) };
        break m$3;
      }
    }
    if (($2.$tag === "Punct")) {
      const p = $2.$;
      if ((p === "-")) {
        $1 = { $tag: "Lit", $: $b.Box_new(unary$852(self)) };
        break m$3;
      }
    }
    if (true) {
      $1 = error$552(self.v, "a pattern");
      break m$3;
    }
    $rt.unmatched($2);
  }
  const kind = $1;
  return pat_$853(self, kind, since$554(self.v, $rt.copy(start)));
}
function blockLike$808(self) {
  if (at$532(self.v, "{")) {
    const b = block$709(self);
    const span = $rt.copy(b.span);
    return expr_$706(self, { $tag: "Block", $: b }, $rt.copy(span));
  }
  if (atKw$530(self.v, "comptime")) {
    const start = span$528(self.v);
    bump$539(self);
    const e = primary$841(self);
    return expr_$706(self, { $tag: "Comptime", $: $b.Box_new(e) }, since$554(self.v, $rt.copy(start)));
  }
  return primary$841(self);
}
function atBlockLike$809(self) {
  if ((at$532(self, "{") && recordAt$854(self, self.pos))) {
    return false;
  }
  return (((((((((atKw$530(self, "if") || atKw$530(self, "while")) || atKw$530(self, "for")) || atKw$530(self, "try")) || atKw$530(self, "unsafe")) || at$532(self, "{")) || matchAt$855(self, self.pos)) || atHandle$856(self)) || atRegion$857(self)) || (atKw$530(self, "comptime") && ((isKw$538(tokAt$537(self, 1n), "if") || isKw$538(tokAt$537(self, 1n), "for")) || matchAt$855(self, $rt.usize(self.pos + 1n)))));
}
function memberName$810(self) {
  const $1 = tok$527(self.v);
  m$2: {
    if (($1.$tag === "Kw")) {
      const k = $1.$;
      {
        const name = $b.String_clone(k);
        const span = bump$539(self);
        return { name: name, span: span };
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  return ident$541(self);
}
function clone$811(self) {
  {
    const v = [clone$218($rt.idx(self, 0n)), clone$218($rt.idx(self, 1n))];
    return v;
  }
}
function clone$812(self) {
  {
    return { name: clone$218(self.name), payload: clone$858(self.payload) };
  }
}
function clone$813(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Method")) {
      const x = $1.$;
      return { $tag: "Method", $: clone$93(x) };
      break m$2;
    }
    if (($1.$tag === "AssocType")) {
      const x = $1.$;
      return { $tag: "AssocType", $: clone$859(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$814(self) {
  {
    const v = [clone$218($rt.idx(self, 0n)), clone$193($rt.idx(self, 1n))];
    return v;
  }
}
function clone$815(self) {
  {
    return { decl: clone$29(self.decl), exported: clone$199(self.exported) };
  }
}
function clone$816(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$60(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$817(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$860(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$818(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$861(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$819(self) {
  return $b.Box_new(clone$862($b.Box_get(self)));
}
function cvsEq$820(xs, ys) {
  const $1 = $b.slice_len(xs);
  for (let i = 0n; i < $1; i++) {
    if ((!cvEq$725($rt.idx(xs, i), $rt.idx(ys, i)))) {
      return false;
    }
  }
  return true;
}
function info$821(self, t, span) {
  const $1 = t;
  m$2: {
    if (($1.$tag === "Prim")) {
      const p = $1.$;
      if (isInt$324(p)) {
        {
          let $3;
          const $4 = p;
          m$5: {
            if ((($4.$tag === "I8") || ($4.$tag === "I16") || ($4.$tag === "I32") || ($4.$tag === "I64") || ($4.$tag === "I128") || ($4.$tag === "Isize"))) {
              $3 = true;
              break m$5;
            }
            if (true) {
              $3 = false;
              break m$5;
            }
            $rt.unmatched($4);
          }
          const signed = $3;
          let $6;
          const $7 = p;
          m$8: {
            if ((($7.$tag === "I8") || ($7.$tag === "U8"))) {
              $6 = 8n;
              break m$8;
            }
            if ((($7.$tag === "I16") || ($7.$tag === "U16"))) {
              $6 = 16n;
              break m$8;
            }
            if ((($7.$tag === "I32") || ($7.$tag === "U32"))) {
              $6 = 32n;
              break m$8;
            }
            if (($7.$tag === "I128")) {
              $6 = 128n;
              break m$8;
            }
            if (true) {
              $6 = 64n;
              break m$8;
            }
            $rt.unmatched($7);
          }
          const bits = $6;
          return tagOf$864("Int", rec$863([["signed", { $tag: "Bool", $: signed }], ["bits", { $tag: "Int", $: bits }]]));
        }
        break m$2;
      }
    }
    if (($1.$tag === "Prim" && ($1.$.$tag === "F32"))) {
      return tagOf$864("Float", { $tag: "Int", $: 32n });
      break m$2;
    }
    if (($1.$tag === "Prim" && ($1.$.$tag === "F64"))) {
      return tagOf$864("Float", { $tag: "Int", $: 64n });
      break m$2;
    }
    if (($1.$tag === "Prim" && ($1.$.$tag === "Bool"))) {
      return { $tag: "Tag", $: [$b.str_toString("Bool"), { $tag: "None" }] };
      break m$2;
    }
    if (($1.$tag === "Prim" && ($1.$.$tag === "Str"))) {
      return { $tag: "Tag", $: [$b.str_toString("Str"), { $tag: "None" }] };
      break m$2;
    }
    if (($1.$tag === "Prim" && ($1.$.$tag === "Void"))) {
      return { $tag: "Tag", $: [$b.str_toString("Void"), { $tag: "None" }] };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const r = $1.$;
      {
        const fs = { v: $b.Vec_new() };
        for (const $9 of $rt.items(r.labels)) {
          const k = $9[0];
          const x = $9[1];
          $b.Vec_push(fs, fieldInfo$865(k, x));
        }
        return tagOf$864("Record", { $tag: "List", $: fs.v });
      }
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const ts = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $10 of $rt.items(ts)) {
          const x = $10;
          $b.Vec_push(out, { $tag: "Type", $: clone$23(x) });
        }
        return tagOf$864("Tuple", { $tag: "List", $: out.v });
      }
      break m$2;
    }
    if (($1.$tag === "Union")) {
      const r = $1.$;
      {
        const out = { v: $b.Vec_new() };
        for (const $11 of $rt.items(r.labels)) {
          const k = $11[0];
          const x = $11[1];
          $b.Vec_push(out, tagInfo$866($b.String_asStr(k), x));
        }
        return tagOf$864("Union", { $tag: "List", $: out.v });
      }
      break m$2;
    }
    if (($1.$tag === "Array" && ($1.$[1].$tag === "Known"))) {
      const e = $1.$[0];
      const n = $1.$[1].$;
      return tagOf$864("Array", rec$863([["item", { $tag: "Type", $: clone$23($b.Box_get(e)) }], ["len", { $tag: "Int", $: $rt.wrap_i128(n) }]]));
      break m$2;
    }
    if (($1.$tag === "Slice")) {
      const e = $1.$;
      return tagOf$864("Slice", { $tag: "Type", $: clone$23($b.Box_get(e)) });
      break m$2;
    }
    if (($1.$tag === "Borrow")) {
      const m = $1.$[0];
      const inner = $1.$[1];
      return tagOf$864("Borrow", rec$863([["mutable", { $tag: "Bool", $: m }], ["type", { $tag: "Type", $: clone$23($b.Box_get(inner)) }]]));
      break m$2;
    }
    if (($1.$tag === "Named")) {
      const d = $1.$[0];
      const args = $1.$[1];
      {
        const name = { $tag: "Str", $: $b.String_clone($rt.idx(self.v.p.v.defs, d).name) };
        const targs = { v: $b.Vec_new() };
        for (const $12 of $rt.items(args)) {
          const a = $12;
          const $13 = a;
          m$14: {
            if (($13.$tag === "Ty")) {
              const x = $13.$;
              {
                $b.Vec_push(targs, { $tag: "Type", $: clone$23(x) });
              }
              break m$14;
            }
            if (true) {
              {
              }
              break m$14;
            }
            $rt.unmatched($13);
          }
        }
        let $15;
        const $16 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, d), "kind");
        const $17 = $16.v;
        m$18: {
          if (($17.$tag === "Struct" && ($17.$.fields.$tag === "Some"))) {
            $15 = true;
            break m$18;
          }
          if (true) {
            $15 = false;
            break m$18;
          }
          $rt.unmatched($17);
        }
        const isStruct = $15;
        if ((isStruct && (($b.slice_len($rt.idx(self.v.p.v.defs, d).private) === 0n) || privileged$867(self.v, d)))) {
          ensureInstance$231(self.v.p, d, args);
          let $19;
          const $20 = structFields$449(self.v.p.v, d, args);
          m$21: {
            if (($20.$tag === "Some")) {
              const x = $20.$;
              $19 = x;
              break m$21;
            }
            if (($20.$tag === "None")) {
              $19 = $b.Vec_new();
              break m$21;
            }
            $rt.unmatched($20);
          }
          const fs = $19;
          const infos = { v: $b.Vec_new() };
          for (const $22 of $rt.items(fs)) {
            const k = $22[0];
            const x = $22[1];
            $b.Vec_push(infos, fieldInfo$865(k, x));
          }
          return tagOf$864("Struct", rec$863([["name", name], ["fields", { $tag: "List", $: infos.v }]]));
        }
        const $23 = new $rt.FieldRef($rt.idx(self.v.p.v.defs, d), "kind");
        const $24 = $23.v;
        m$25: {
          if (($24.$tag === "Enum")) {
            const tags = new $rt.FieldRef($24.$, "tags");
            {
              const infos = { v: $b.Vec_new() };
              for (const $26 of $rt.items($rt.idx(self.v.p.v.defs, d).tagOrder)) {
                const k = $26;
                const $27 = labelGet$233(tags.v, $b.String_asStr(k));
                m$28: {
                  if (($27.$tag === "Some")) {
                    const x = $27.$;
                    {
                      const pt = substParams$230(x, $rt.idx(self.v.p.v.defs, d).params, args);
                      $b.Vec_push(infos, tagInfo$866($b.String_asStr(k), pt));
                    }
                    break m$28;
                  }
                  if (true) {
                    {
                    }
                    break m$28;
                  }
                  $rt.unmatched($27);
                }
              }
              return tagOf$864("Enum", rec$863([["name", name], ["tags", { $tag: "List", $: infos.v }]]));
            }
            break m$25;
          }
          if (true) {
            return tagOf$864("Opaque", rec$863([["name", name], ["args", { $tag: "List", $: targs.v }]]));
            break m$25;
          }
          $rt.unmatched($24);
        }
      }
      break m$2;
    }
    if (($1.$tag === "Fn")) {
      return { $tag: "Tag", $: [$b.str_toString("Fn"), { $tag: "None" }] };
      break m$2;
    }
    if (true) {
      return fail$391($rt.copy(span), $b.String_asStr(("" + "`" + show$136(self.v.p.v, t) + "` cannot be reflected on")));
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function eq$822(self, other) {
  if (($b.slice_len(self) !== $b.slice_len(other))) {
    return false;
  }
  let i = 0n;
  while ((i < $b.slice_len(self))) {
    if ((!eq$763($rt.idx(self, i), $rt.idx(other, i)))) {
      return false;
    }
    i = $rt.usize(i + 1n);
  }
  return true;
}
function ensureAssoc$823(self, base, name) {
  if (containsParams$148(base)) {
    return;
  }
  let $1;
  const $2 = assocImpl$451(self.v, base, name);
  m$3: {
    if (($2.$tag === "Some")) {
      const r = $2.$;
      $1 = r;
      break m$3;
    }
    if (($2.$tag === "None")) {
      return;
      break m$3;
    }
    $rt.unmatched($2);
  }
  const $4 = $1;
  const imp = $4[0];
  const binds = $4[1];
  const key = ("" + String(imp) + "|" + bindsKey$452(binds) + "|" + name);
  if (((!isTemplateImpl$288(self.v, imp)) || $b.HashMap_has(self.v.assocInstances, $b.String_asStr(key)))) {
    return;
  }
  let $5;
  const $8 = find$868($b.slice_iter($rt.idx(self.v.impls, imp).assoc), (($0$$6) => {
  {
    const $7 = $0$$6;
    const n = $7[0];
    return (n === name);
  }
  }));
  m$9: {
    if (($8.$tag === "Some")) {
      const t = $8.$[1];
      $5 = clone$193(t);
      break m$9;
    }
    if (($8.$tag === "None")) {
      return;
      break m$9;
    }
    $rt.unmatched($8);
  }
  const astTy = $5;
  const params = clone$73($rt.idx(self.v.impls, imp).params);
  const module = $rt.idx(self.v.impls, imp).module;
  const env = { v: $b.Vec_new() };
  for (const $10 of $rt.items(params)) {
    const g = $10;
    if (g.isComptime) {
      const $11 = $b.HashMap_get(binds, g.sym.id);
      m$12: {
        if (($11.$tag === "Some" && ($11.$.$tag === "Ty"))) {
          const t = $11.$.$;
          {
            $b.Vec_push(env, [$b.String_clone(g.sym.name), { $tag: "Type", $: clone$23(t) }]);
          }
          break m$12;
        }
        if (true) {
          {
          }
          break m$12;
        }
        $rt.unmatched($11);
      }
    }
  }
  const ex = { v: expander$27(self, module, { $tag: "None" }, env.v) };
  let $13;
  const $14 = expandType$869(ex, astTy);
  m$15: {
    if (($14.$tag === "Some")) {
      const t = $14.$;
      $13 = t;
      break m$15;
    }
    if (($14.$tag === "None")) {
      return;
      break m$15;
    }
    $rt.unmatched($14);
  }
  const expanded = $13;
  const scope = withParams$32(moduleScope$31(module), params);
  const t = elabTy$101(self, expanded, scope);
  $b.HashMap_insert(new $rt.FieldRef(self.v, "assocInstances"), key, subst$308(t, bindsMap$453(binds)));
  return undefined;
}
function clone$824(self) {
  {
    const v = [$b.String_clone($rt.idx(self, 0n)), clone$22($rt.idx(self, 1n))];
    return v;
  }
}
function eq$825(self, other) {
  if (($b.slice_len(self) !== $b.slice_len(other))) {
    return false;
  }
  let i = 0n;
  while ((i < $b.slice_len(self))) {
    if ((!eq$457($rt.idx(self, i), $rt.idx(other, i)))) {
      return false;
    }
    i = $rt.usize(i + 1n);
  }
  return true;
}
function clone$826(self) {
  {
    const v = [clone$218($rt.idx(self, 0n)), clone$870($rt.idx(self, 1n))];
    return v;
  }
}
function constValue$827(self, e, ty) {
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "Int")) {
      const n = $1.$;
      if (floatTy$511(ty)) {
        return $b.String_clone(n);
      } else {
        {
          return ("" + n + "n");
        }
      }
      break m$2;
    }
    if (($1.$tag === "Float")) {
      const n = $1.$;
      return $b.String_clone(n);
      break m$2;
    }
    if (($1.$tag === "Str")) {
      const s = $1.$;
      return quote$512(s);
      break m$2;
    }
    if (($1.$tag === "Byte")) {
      const b = $1.$;
      return ("" + String(b) + "n");
      break m$2;
    }
    if (($1.$tag === "Bool")) {
      const b = $1.$;
      if (b) {
        return $b.str_toString("true");
      } else {
        {
          return $b.str_toString("false");
        }
      }
      break m$2;
    }
    if (($1.$tag === "Unary")) {
      const op = $1.$.op;
      const operand = $1.$.operand;
      {
        const v = constValue$827(self, operand, ty);
        return ("" + "(" + op + v + ")");
      }
      break m$2;
    }
    if (($1.$tag === "Binary")) {
      const op = $1.$.op;
      const lhs = $1.$.lhs;
      const rhs = $1.$.rhs;
      {
        const a = constValue$827(self, lhs, ty);
        const b = constValue$827(self, rhs, ty);
        return ("" + "(" + a + " " + op + " " + b + ")");
      }
      break m$2;
    }
    if (($1.$tag === "List")) {
      const items = $1.$;
      {
        let $3;
        const $4 = stripBorrow$317(ty);
        m$5: {
          if ((($4.$tag === "Array") || ($4.$tag === "Slice"))) {
            let x;
            if (($4.$tag === "Array")) { x = $4.$[0]; }
            else if (($4.$tag === "Slice")) { x = $4.$; }
            $3 = clone$23($b.Box_get(x));
            break m$5;
          }
          if (($4.$tag === "Named")) {
            const args = $4.$[1];
            const $6 = first$258(args);
            m$7: {
              if (($6.$tag === "Some" && ($6.$.$tag === "Ty"))) {
                const x = $6.$.$;
                $3 = clone$23(x);
                break m$7;
              }
              if (true) {
                $3 = { $tag: "Error" };
                break m$7;
              }
              $rt.unmatched($6);
            }
            break m$5;
          }
          if (true) {
            $3 = { $tag: "Error" };
            break m$5;
          }
          $rt.unmatched($4);
        }
        const elem = $3;
        const vs = { v: $b.Vec_new() };
        for (const $8 of $rt.items(items)) {
          const it = $8;
          $b.Vec_push(vs, constValue$827(self, it, elem));
        }
        return ("" + "[" + join$53(vs.v, ", ") + "]");
      }
      break m$2;
    }
    if (($1.$tag === "Ident")) {
      const n = $1.$;
      const $9 = lookup$47(self.v.p, self.v.module, $b.String_asStr(n));
      m$10: {
        if (($9.$tag === "Some" && ($9.$.$tag === "Const"))) {
          const c = $9.$.$;
          return constant$772(self, c);
          break m$10;
        }
        if (true) {
          return fail$514(self.v, $rt.copy(e.span), "a constant can be built only of literals and other constants");
          break m$10;
        }
        $rt.unmatched($9);
      }
      break m$2;
    }
    if (($1.$tag === "Tag" && ($1.$.args.$tag === "None"))) {
      const name = $1.$.name;
      return ("" + "{ $tag: " + quote$512(name) + " }");
      break m$2;
    }
    if (true) {
      return fail$514(self.v, $rt.copy(e.span), "a constant can be built only of literals and other constants");
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function unsupported$828(self, span, what) {
  return fail$514(self, $rt.copy(span), ("" + what + " is not supported by this compiler yet"));
}
function returns$829(e) {
  const $1 = e.kind;
  m$2: {
    if (($1.$tag === "Return")) {
      return true;
      break m$2;
    }
    if (($1.$tag === "Lambda")) {
      return false;
      break m$2;
    }
    if ((($1.$tag === "Block") || ($1.$tag === "Unsafe"))) {
      let b;
      if (($1.$tag === "Block")) { b = $1.$; }
      else if (($1.$tag === "Unsafe")) { b = $1.$; }
      return blockReturns$781(b);
      break m$2;
    }
    if (($1.$tag === "Region")) {
      const body = $1.$.body;
      return blockReturns$781(body);
      break m$2;
    }
    if (($1.$tag === "If")) {
      const cond = $1.$.cond;
      const then = $1.$.then;
      const otherwise = $1.$.otherwise;
      let $3 = (returns$829(cond) || blockReturns$781(then));
      if (!$3) {
        let $4;
        const $5 = otherwise;
        m$6: {
          if (($5.$tag === "Some")) {
            const o = $5.$;
            $4 = returns$829(o);
            break m$6;
          }
          if (($5.$tag === "None")) {
            $4 = false;
            break m$6;
          }
          $rt.unmatched($5);
        }
        $3 = $4;
      }
      return $3;
      break m$2;
    }
    if (($1.$tag === "While")) {
      const cond = $1.$.cond;
      const body = $1.$.body;
      return (returns$829(cond) || blockReturns$781(body));
      break m$2;
    }
    if (($1.$tag === "For")) {
      const iter = $1.$.iter;
      const body = $1.$.body;
      return (returns$829(iter) || blockReturns$781(body));
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const scrutinee = $1.$.scrutinee;
      const arms = $1.$.arms;
      return (returns$829(scrutinee) || some$207($b.slice_iter(arms), ((a) => {
  return returns$829(a.body);
      })));
      break m$2;
    }
    if (($1.$tag === "Try")) {
      const body = $1.$.body;
      const handler = $1.$.handler;
      return (blockReturns$781(body) || blockReturns$781(handler));
      break m$2;
    }
    if (($1.$tag === "Handle")) {
      const body = $1.$.body;
      const arms = $1.$.arms;
      return (blockReturns$781(body) || some$208($b.slice_iter(arms), ((a) => {
  return blockReturns$781(a.body);
      })));
      break m$2;
    }
    if (($1.$tag === "Call")) {
      const callee = $1.$.callee;
      const args = $1.$.args;
      return (returns$829(callee) || some$202($b.slice_iter(args), ((a) => {
  return returns$829(a);
      })));
      break m$2;
    }
    if (($1.$tag === "Binary")) {
      const lhs = $1.$.lhs;
      const rhs = $1.$.rhs;
      return (returns$829(lhs) || returns$829(rhs));
      break m$2;
    }
    if (($1.$tag === "Assign")) {
      const target = $1.$.target;
      const value = $1.$.value;
      return (returns$829(target) || returns$829(value));
      break m$2;
    }
    if (($1.$tag === "Field")) {
      const target = $1.$.target;
      return returns$829(target);
      break m$2;
    }
    if (($1.$tag === "Unary")) {
      const operand = $1.$.operand;
      return returns$829(operand);
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function isSpace$830(c) {
  return ((((c === 32n) || (c === 10n)) || (c === 9n)) || (c === 13n));
}
function escape$831(self, start) {
  const c = peek$788(self.v);
  self.v.pos = $rt.usize(self.v.pos + 1n);
  if ((c === 110n)) {
    return 10n;
  }
  if ((c === 116n)) {
    return 9n;
  }
  if ((c === 114n)) {
    return 13n;
  }
  if ((c === 48n)) {
    return 0n;
  }
  if ((((((c === 92n) || (c === 39n)) || (c === 34n)) || (c === 96n)) || (c === 36n))) {
    return $rt.wrap_u32(c);
  }
  if (((c === 117n) && (peek$788(self.v) === 123n))) {
    self.v.pos = $rt.usize(self.v.pos + 1n);
    let v = 0n;
    let n = 0n;
    while (((self.v.pos < self.v.end) && (peek$788(self.v) !== 125n))) {
      const h = peek$788(self.v);
      if (((!isHex$832(h)) || (n === 6n))) {
        throw new $rt.Fail(err$791(self.v, start, "invalid unicode escape"));
      }
      let $1;
      if (isDigit$794(h)) {
        $1 = $rt.u8(h - 48n);
      } else {
        if ((h >= 97n)) {
          $1 = $rt.u8($rt.u8(h - 97n) + 10n);
        } else {
          {
            $1 = $rt.u8($rt.u8(h - 65n) + 10n);
          }
        }
      }
      const d = $1;
      v = $rt.u32($rt.u32(v * 16n) + $rt.wrap_u32(d));
      n = $rt.usize(n + 1n);
      self.v.pos = $rt.usize(self.v.pos + 1n);
    }
    self.v.pos = $rt.usize(self.v.pos + 1n);
    if ((((n === 0n) || (v > 0x10ffffn)) || ((v >= 0xd800n) && (v < 0xe000n)))) {
      throw new $rt.Fail(err$791(self.v, start, "invalid unicode escape"));
    }
    return v;
  }
  throw new $rt.Fail(err$791(self.v, start, "invalid escape sequence"));
}
function isHex$832(c) {
  return ((isDigit$794(c) || ((c >= 97n) && (c <= 102n))) || ((c >= 65n) && (c <= 70n)));
}
function digits$833(self) {
  while (((self.v.pos < self.v.end) && (isDigit$794(peek$788(self.v)) || (peek$788(self.v) === 95n)))) {
    self.v.pos = $rt.usize(self.v.pos + 1n);
  }
  return undefined;
}
function pushChar$834(s, c) {
  const bytes = { v: $b.Vec_new() };
  if ((c < 0x80n)) {
    $b.Vec_push(bytes, $rt.wrap_u8(c));
  } else {
    if ((c < 0x800n)) {
      $b.Vec_push(bytes, $rt.wrap_u8((0xc0n | (c >> 6n))));
      $b.Vec_push(bytes, $rt.wrap_u8((0x80n | (c & 0x3fn))));
    } else {
      if ((c < 0x10000n)) {
        $b.Vec_push(bytes, $rt.wrap_u8((0xe0n | (c >> 12n))));
        $b.Vec_push(bytes, $rt.wrap_u8((0x80n | ((c >> 6n) & 0x3fn))));
        $b.Vec_push(bytes, $rt.wrap_u8((0x80n | (c & 0x3fn))));
      } else {
        {
          $b.Vec_push(bytes, $rt.wrap_u8((0xf0n | (c >> 18n))));
          $b.Vec_push(bytes, $rt.wrap_u8((0x80n | ((c >> 12n) & 0x3fn))));
          $b.Vec_push(bytes, $rt.wrap_u8((0x80n | ((c >> 6n) & 0x3fn))));
          $b.Vec_push(bytes, $rt.wrap_u8((0x80n | (c & 0x3fn))));
        }
      }
    }
  }
  const $1 = $b.String_fromUtf8(bytes.v);
  m$2: {
    if (($1.$tag === "Some")) {
      const t = $1.$;
      return $b.String_push(s, $b.String_asStr(t));
      break m$2;
    }
    if (($1.$tag === "None")) {
      {
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function skipBalanced$835(self, start) {
  let depth = 1n;
  while ((depth > 0n)) {
    if ((self.v.pos >= self.v.end)) {
      throw new $rt.Fail(err$791(self.v, start, "unterminated template interpolation"));
    }
    const c = peek$788(self.v);
    self.v.pos = $rt.usize(self.v.pos + 1n);
    if ((c === 123n)) {
      depth = $rt.usize(depth + 1n);
    } else {
      if ((c === 125n)) {
        depth = $rt.usize(depth - 1n);
      } else {
        if (((c === 34n) || (c === 39n))) {
          string$796(self, start, c);
        } else {
          if ((c === 96n)) {
            template$797(self, start);
          }
        }
      }
    }
  }
  return undefined;
}
function wordAt$836(self, n, w) {
  return isWord$698(tokAt$537(self, n), w);
}
function generate$837(self, items) {
  expectKw$693(self, "comptime");
  if (eatKw$529(self, "for")) {
    expect$544(self, "(");
    if (((!eatKw$529(self, "const")) && (!eatKw$529(self, "let")))) {
      error$552(self.v, "`const`");
    }
    const pat = patternOne$807(self);
    expectWord$694(self, "of");
    const iter = expr$545(self);
    expect$544(self, ")");
    expect$544(self, "{");
    const body = items(self);
    expect$544(self, "}");
    return { $tag: "For", $: { pat: pat, iter: iter, body: body } };
  }
  if (eatKw$529(self, "if")) {
    const cond = parenExpr$871(self);
    expect$544(self, "{");
    const then = items(self);
    expect$544(self, "}");
    let otherwise = $b.Vec_new();
    if (eatKw$529(self, "else")) {
      expect$544(self, "{");
      otherwise = items(self);
      expect$544(self, "}");
    }
    return { $tag: "If", $: { cond: cond, then: then, otherwise: otherwise } };
  }
  if (eatWord$534(self, "match")) {
    const scrutinee = parenExpr$871(self);
    expect$544(self, "{");
    const arms = { v: $b.Vec_new() };
    while ((!at$532(self.v, "}"))) {
      const pat = pattern$851(self);
      expect$544(self, "=>");
      expect$544(self, "{");
      const group = items(self);
      expect$544(self, "}");
      $b.Vec_push(arms, [pat, group]);
      eat$542(self, ",");
    }
    expect$544(self, "}");
    return { $tag: "Match", $: { scrutinee: scrutinee, arms: arms.v } };
  }
  return error$552(self.v, "`for`, `if` or `match` after `comptime`");
}
function entryName$838(self) {
  if (at$532(self.v, "[")) {
    const start = span$528(self.v);
    bump$539(self);
    const e = expr$545(self);
    expect$544(self, "]");
    return [mkIdent$801("", since$554(self.v, $rt.copy(start))), { $tag: "Some", $: $b.Box_new(e) }];
  }
  return [memberName$810(self), { $tag: "None" }];
}
function path$839(self) {
  const segments = { v: $b.Vec_new() };
  $b.Vec_push(segments, ident$541(self));
  while (true) {
    let $1 = at$532(self.v, ".");
    if ($1) {
      let $2;
      const $3 = tokAt$537(self.v, 1n);
      m$4: {
        if ((($3.$tag === "Ident") || ($3.$tag === "Kw"))) {
          $2 = true;
          break m$4;
        }
        if (true) {
          $2 = false;
          break m$4;
        }
        $rt.unmatched($3);
      }
      $1 = $2;
    }
    if (!($1)) break;
    bump$539(self);
    $b.Vec_push(segments, memberName$810(self));
  }
  return segments.v;
}
function typeArgs$840(self) {
  const args = { v: $b.Vec_new() };
  if ((!eat$542(self, "<"))) {
    return args.v;
  }
  while ((!at$532(self.v, ">"))) {
    $b.Vec_push(args, ty$543(self));
    if ((!eat$542(self, ","))) {
      break;
    }
  }
  expect$544(self, ">");
  return args.v;
}
function primary$841(self) {
  const start = span$528(self.v);
  const t = clone$846(tok$527(self.v));
  let $1;
  const $2 = t;
  m$3: {
    if (($2.$tag === "Int")) {
      const s = $2.$;
      {
        bump$539(self);
        $1 = { $tag: "Int", $: s };
      }
      break m$3;
    }
    if (($2.$tag === "Float")) {
      const s = $2.$;
      {
        bump$539(self);
        $1 = { $tag: "Float", $: s };
      }
      break m$3;
    }
    if (($2.$tag === "Byte")) {
      const b = $2.$;
      {
        bump$539(self);
        $1 = { $tag: "Byte", $: b };
      }
      break m$3;
    }
    if (($2.$tag === "Str")) {
      const s = $2.$;
      {
        bump$539(self);
        $1 = { $tag: "Str", $: s };
      }
      break m$3;
    }
    if (($2.$tag === "Template")) {
      const parts = $2.$;
      {
        bump$539(self);
        $1 = { $tag: "Template", $: template$872(self, parts) };
      }
      break m$3;
    }
    if (($2.$tag === "Kw")) {
      const k = $2.$;
      if ((k === "true")) {
        {
          bump$539(self);
          $1 = { $tag: "Bool", $: true };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Kw")) {
      const k = $2.$;
      if ((k === "false")) {
        {
          bump$539(self);
          $1 = { $tag: "Bool", $: false };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Kw")) {
      const k = $2.$;
      if ((k === "break")) {
        {
          bump$539(self);
          $1 = { $tag: "Break" };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Kw")) {
      const k = $2.$;
      if ((k === "continue")) {
        {
          bump$539(self);
          $1 = { $tag: "Continue" };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Tag")) {
      const name = $2.$;
      {
        bump$539(self);
        $1 = { $tag: "Tag", $: { name: name, args: tagArgs$873(self) } };
      }
      break m$3;
    }
    if (($2.$tag === "Punct")) {
      const p = $2.$;
      if ((p === "#[")) {
        {
          bump$539(self);
          const name = expr$545(self);
          expect$544(self, "]");
          $1 = { $tag: "TagAt", $: { name: $b.Box_new(name), args: tagArgs$873(self) } };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Ident")) {
      const name = $2.$;
      if ((((!matchAt$855(self.v, self.v.pos)) && (!atRegion$857(self.v))) && (!atHandle$856(self.v)))) {
        {
          if ((isUpper$847($b.String_asStr(name)) && atN$702(self.v, 1n, "{"))) {
            const path = { v: $b.Vec_new() };
            $b.Vec_push(path, ident$541(self));
            $1 = { $tag: "Record", $: { name: { $tag: "Some", $: path.v }, fields: fieldInits$874(self) } };
          } else {
            {
              bump$539(self);
              $1 = { $tag: "Ident", $: name };
            }
          }
        }
        break m$3;
      }
    }
    if (($2.$tag === "Punct")) {
      const p = $2.$;
      if (((p === "(") && isLambda$875(self.v))) {
        {
          const $4 = lambdaParams$876(self);
          const params = $4[0];
          const unpack = $4[1];
          expect$544(self, "=>");
          let $5;
          if (at$532(self.v, "{")) {
            let b = block$709(self);
            const stmts = { v: unpack };
            const $6 = $b.Gen_each($b.Vec_drain(new $rt.FieldRef(b, "stmts")));
            let $8;
            for (let $7 = $6.next(); !$7.done; $7 = $6.next($8)) {
              $8 = undefined;
              const $9 = $7.value.item;
              const s = $9;
              $b.Vec_push(stmts, s);
            }
            b.stmts = stmts.v;
            const span = $rt.copy(b.span);
            $5 = expr_$706(self, { $tag: "Block", $: b }, $rt.copy(span));
          } else {
            {
              const e = expr$545(self);
              if (($b.slice_len(unpack) === 0n)) {
                $5 = e;
              } else {
                {
                  const span = $rt.copy(e.span);
                  $5 = expr_$706(self, { $tag: "Block", $: { stmts: unpack, tail: { $tag: "Some", $: $b.Box_new(e) }, span: span } }, $rt.copy(span));
                }
              }
            }
          }
          const body = $5;
          $1 = { $tag: "Lambda", $: { params: params, body: $b.Box_new(body) } };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Punct")) {
      const p = $2.$;
      if ((p === "(")) {
        {
          bump$539(self);
          const e = expr$545(self);
          expect$544(self, ")");
          return e;
          $1 = undefined;
        }
        break m$3;
      }
    }
    if (($2.$tag === "Punct")) {
      const p = $2.$;
      if ((p === "[")) {
        {
          bump$539(self);
          const items = { v: $b.Vec_new() };
          while ((!at$532(self.v, "]"))) {
            $b.Vec_push(items, expr$545(self));
            if ((!eat$542(self, ","))) {
              break;
            }
          }
          expect$544(self, "]");
          $1 = { $tag: "List", $: items.v };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Punct")) {
      const p = $2.$;
      if ((p === "{")) {
        $1 = { $tag: "Record", $: { name: { $tag: "None" }, fields: fieldInits$874(self) } };
        break m$3;
      }
    }
    if (($2.$tag === "Kw")) {
      const k = $2.$;
      if ((k === "if")) {
        $1 = ifExpr$877(self);
        break m$3;
      }
    }
    if (($2.$tag === "Kw")) {
      const k = $2.$;
      if ((k === "while")) {
        $1 = whileExpr$878(self);
        break m$3;
      }
    }
    if (($2.$tag === "Kw")) {
      const k = $2.$;
      if ((k === "for")) {
        {
          bump$539(self);
          expect$544(self, "(");
          let $10;
          if (atKw$530(self.v, "const")) {
            $10 = false;
          } else {
            if (atKw$530(self.v, "let")) {
              $10 = true;
            } else {
              {
                $10 = error$552(self.v, "`const` or `let`");
              }
            }
          }
          const mutable = $10;
          bump$539(self);
          const pat = patternOne$807(self);
          expectWord$694(self, "of");
          const iter = expr$545(self);
          expect$544(self, ")");
          $1 = { $tag: "For", $: { mutable: mutable, pat: pat, iter: $b.Box_new(iter), body: block$709(self) } };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Ident")) {
      const w = $2.$;
      if (((w === "match") && matchAt$855(self.v, self.v.pos))) {
        {
          bump$539(self);
          const scrutinee = parenExpr$871(self);
          expect$544(self, "{");
          const arms = armItems$879(self);
          expect$544(self, "}");
          $1 = { $tag: "Match", $: { scrutinee: $b.Box_new(scrutinee), arms: arms } };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Kw")) {
      const k = $2.$;
      if ((k === "try")) {
        {
          bump$539(self);
          const body = block$709(self);
          expectKw$693(self, "catch");
          expect$544(self, "(");
          const pat = pattern$851(self);
          expect$544(self, ")");
          $1 = { $tag: "Try", $: { body: body, pat: pat, handler: block$709(self) } };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Ident")) {
      if (atRegion$857(self.v)) {
        {
          bump$539(self);
          expect$544(self, "(");
          const name = ident$541(self);
          expect$544(self, ")");
          $1 = { $tag: "Region", $: { name: name, body: block$709(self) } };
        }
        break m$3;
      }
    }
    if (($2.$tag === "Ident")) {
      if (atHandle$856(self.v)) {
        $1 = handleExpr$880(self, $rt.copy(start));
        break m$3;
      }
    }
    if (($2.$tag === "Kw")) {
      const k = $2.$;
      if ((k === "unsafe")) {
        {
          bump$539(self);
          $1 = { $tag: "Unsafe", $: block$709(self) };
        }
        break m$3;
      }
    }
    if (true) {
      $1 = error$552(self.v, "an expression");
      break m$3;
    }
    $rt.unmatched($2);
  }
  const kind = $1;
  return expr_$706(self, kind, since$554(self.v, $rt.copy(start)));
}
function rowItem$842(self) {
  if (eat$542(self, "...")) {
    return { $tag: "Spread", $: ident$541(self) };
  }
  const start = span$528(self.v);
  const segments = path$839(self);
  const args = typeArgs$840(self);
  return { $tag: "Effect", $: { kind: { $tag: "Path", $: { segments: segments, args: args } }, span: since$554(self.v, $rt.copy(start)) } };
}
function rowContinues$843(self) {
  const $1 = tokAt$537(self, 1n);
  m$2: {
    if (($1.$tag === "Punct")) {
      const p = $1.$;
      return (p === "...");
      break m$2;
    }
    if (($1.$tag === "Ident")) {
      return (!atN$702(self, 2n, ":"));
      break m$2;
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function cast$844(self) {
  const start = span$528(self.v);
  let e = unary$852(self);
  while (eatKw$529(self, "as")) {
    const ty = tyPostfix$701(self);
    e = expr_$706(self, { $tag: "Cast", $: { expr: $b.Box_new(e), ty: ty } }, since$554(self.v, $rt.copy(start)));
  }
  return e;
}
function binaryOp$845(self, level) {
  for (const $1 of $rt.items($rt.idx($c8$BINARY, level))) {
    const op = $1;
    if ((op === "<<")) {
      if (adjacent$881(self, "<", "<")) {
        return { $tag: "Some", $: [$b.str_toString("<<"), 2n] };
      }
      continue;
    }
    if ((op === ">>")) {
      if (adjacent$881(self, ">", ">")) {
        return { $tag: "Some", $: [$b.str_toString(">>"), 2n] };
      }
      continue;
    }
    if ((((op === "<") || (op === ">")) && adjacent$881(self, op, op))) {
      continue;
    }
    if (at$532(self, op)) {
      return { $tag: "Some", $: [$b.str_toString(op), 1n] };
    }
  }
  return { $tag: "None" };
}
function clone$846(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Ident")) {
      const x = $1.$;
      return { $tag: "Ident", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Kw")) {
      const x = $1.$;
      return { $tag: "Kw", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Int")) {
      const x = $1.$;
      return { $tag: "Int", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Float")) {
      const x = $1.$;
      return { $tag: "Float", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Byte")) {
      const x = $1.$;
      return { $tag: "Byte", $: clone$329(x) };
      break m$2;
    }
    if (($1.$tag === "Str")) {
      const x = $1.$;
      return { $tag: "Str", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Template")) {
      const x = $1.$;
      return { $tag: "Template", $: clone$882(x) };
      break m$2;
    }
    if (($1.$tag === "Tag")) {
      const x = $1.$;
      return { $tag: "Tag", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Punct")) {
      const x = $1.$;
      return { $tag: "Punct", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Eof")) {
      return { $tag: "Eof" };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function isUpper$847(s) {
  const b = $b.str_asBytes(s);
  return ((($b.slice_len(b) > 0n) && ($rt.idx(b, 0n) >= 65n)) && ($rt.idx(b, 0n) <= 90n));
}
function fieldPats$848(self) {
  expect$544(self, "{");
  const fields = { v: $b.Vec_new() };
  while ((!at$532(self.v, "}"))) {
    let $1;
    const $2 = tok$527(self.v);
    m$3: {
      if (($2.$tag === "Kw")) {
        $1 = true;
        break m$3;
      }
      if (true) {
        $1 = false;
        break m$3;
      }
      $rt.unmatched($2);
    }
    const reserved = $1;
    const name = memberName$810(self);
    let $4;
    if (eat$542(self, ":")) {
      $4 = { $tag: "Some", $: pattern$851(self) };
    } else {
      if (reserved) {
        throw new $rt.Fail({ $tag: "Diagnostic", $: { span: name.span, message: ("" + "`" + name.name + "` is a reserved word: bind the field to a name, `" + name.name + ": x`") } });
      } else {
        {
          $4 = { $tag: "Some", $: pat_$853(self, { $tag: "Bind", $: $b.String_clone(name.name) }, $rt.copy(name.span)) };
        }
      }
    }
    const pat = $4;
    $b.Vec_push(fields, [name, pat]);
    if ((!eat$542(self, ","))) {
      break;
    }
  }
  expect$544(self, "}");
  return fields.v;
}
function tagPatArgs$849(self) {
  if (at$532(self.v, "(")) {
    bump$539(self);
    const pats = { v: $b.Vec_new() };
    while ((!at$532(self.v, ")"))) {
      $b.Vec_push(pats, pattern$851(self));
      if ((!eat$542(self, ","))) {
        break;
      }
    }
    expect$544(self, ")");
    return { $tag: "Tuple", $: pats.v };
  } else {
    if (at$532(self.v, "{")) {
      return { $tag: "Record", $: fieldPats$848(self) };
    } else {
      {
        return { $tag: "None" };
      }
    }
  }
}
function postfix$850(self) {
  const start = span$528(self.v);
  let e = primary$841(self);
  while (true) {
    if ((at$532(self.v, ".") && atN$702(self.v, 1n, "["))) {
      bump$539(self);
      bump$539(self);
      const name = expr$545(self);
      expect$544(self, "]");
      e = expr_$706(self, { $tag: "FieldAt", $: { target: $b.Box_new(e), name: $b.Box_new(name) } }, since$554(self.v, $rt.copy(start)));
    } else {
      if (at$532(self.v, ".")) {
        bump$539(self);
        const name = memberName$810(self);
        e = expr_$706(self, { $tag: "Field", $: { target: $b.Box_new(e), name: name } }, since$554(self.v, $rt.copy(start)));
      } else {
        if (at$532(self.v, "(")) {
          const args = args$883(self);
          e = expr_$706(self, { $tag: "Call", $: { callee: $b.Box_new(e), typeArgs: $b.Vec_new(), args: args } }, since$554(self.v, $rt.copy(start)));
        } else {
          if (at$532(self.v, "[")) {
            bump$539(self);
            const index = expr$545(self);
            expect$544(self, "]");
            e = expr_$706(self, { $tag: "Index", $: { target: $b.Box_new(e), index: $b.Box_new(index) } }, since$554(self.v, $rt.copy(start)));
          } else {
            let $1 = at$532(self.v, "<");
            if ($1) {
              let $2;
              const $3 = e.kind;
              m$4: {
                if ((($3.$tag === "Ident") || ($3.$tag === "Field"))) {
                  $2 = true;
                  break m$4;
                }
                if (true) {
                  $2 = false;
                  break m$4;
                }
                $rt.unmatched($3);
              }
              $1 = $2;
            }
            if ($1) {
              const saved = self.v.pos;
              let $5;
              try {
                const ta = typeArgs$840(self);
                if (at$532(self.v, "(")) {
                  $5 = { $tag: "Some", $: ta };
                } else {
                  {
                    $5 = { $tag: "None" };
                  }
                }
              } catch ($6) {
                if (!($6 instanceof $rt.Fail)) throw $6;
                $5 = { $tag: "None" };
              }
              const typeArgs = $5;
              const $7 = typeArgs;
              m$8: {
                if (($7.$tag === "Some")) {
                  const ta = $7.$;
                  {
                    const args = args$883(self);
                    e = expr_$706(self, { $tag: "Call", $: { callee: $b.Box_new(e), typeArgs: ta, args: args } }, since$554(self.v, $rt.copy(start)));
                  }
                  break m$8;
                }
                if (($7.$tag === "None")) {
                  {
                    self.v.pos = saved;
                    return e;
                  }
                  break m$8;
                }
                $rt.unmatched($7);
              }
            } else {
              {
                return e;
              }
            }
          }
        }
      }
    }
  }
  return e;
}
function pattern$851(self) {
  const start = span$528(self.v);
  const first = patternOne$807(self);
  if ((!at$532(self.v, "|"))) {
    return first;
  }
  const alts = { v: $b.Vec_new() };
  $b.Vec_push(alts, first);
  while (eat$542(self, "|")) {
    $b.Vec_push(alts, patternOne$807(self));
  }
  return pat_$853(self, { $tag: "Or", $: alts.v }, since$554(self.v, $rt.copy(start)));
}
function unary$852(self) {
  const start = span$528(self.v);
  if (((at$532(self.v, "!") || at$532(self.v, "-")) || at$532(self.v, "~"))) {
    let $1;
    const $2 = tok$527(self.v);
    m$3: {
      if (($2.$tag === "Punct")) {
        const p = $2.$;
        $1 = $b.String_clone(p);
        break m$3;
      }
      if (true) {
        $1 = $b.String_new();
        break m$3;
      }
      $rt.unmatched($2);
    }
    const op = $1;
    bump$539(self);
    const operand = unary$852(self);
    return expr_$706(self, { $tag: "Unary", $: { op: op, operand: $b.Box_new(operand) } }, since$554(self.v, $rt.copy(start)));
  }
  if (eatKw$529(self, "mut")) {
    const inner = unary$852(self);
    return expr_$706(self, { $tag: "BorrowMut", $: $b.Box_new(inner) }, since$554(self.v, $rt.copy(start)));
  }
  if (eatKw$529(self, "throw")) {
    const inner = expr$545(self);
    return expr_$706(self, { $tag: "Throw", $: $b.Box_new(inner) }, since$554(self.v, $rt.copy(start)));
  }
  if (eatKw$529(self, "yield")) {
    const inner = expr$545(self);
    return expr_$706(self, { $tag: "Yield", $: $b.Box_new(inner) }, since$554(self.v, $rt.copy(start)));
  }
  if (eatKw$529(self, "comptime")) {
    const inner = unary$852(self);
    return expr_$706(self, { $tag: "Comptime", $: $b.Box_new(inner) }, since$554(self.v, $rt.copy(start)));
  }
  if (eatKw$529(self, "return")) {
    const bare = (((at$532(self.v, ";") || at$532(self.v, "}")) || at$532(self.v, ",")) || at$532(self.v, ")"));
    let $4;
    if (bare) {
      $4 = { $tag: "None" };
    } else {
      {
        $4 = { $tag: "Some", $: $b.Box_new(expr$545(self)) };
      }
    }
    const value = $4;
    return expr_$706(self, { $tag: "Return", $: value }, since$554(self.v, $rt.copy(start)));
  }
  return postfix$850(self);
}
function pat_$853(self, kind, span) {
  self.v.nextId = $rt.usize(self.v.nextId + 1n);
  return { kind: kind, span: span, id: self.v.nextId };
}
function recordAt$854(self, at) {
  const next = tokIndex$884(self, $rt.usize(at + 1n));
  const $1 = next;
  m$2: {
    if ((($1.$tag === "Ident") || ($1.$tag === "Kw"))) {
      if (isPunct$695(tokIndex$884(self, $rt.usize(at + 2n)), ":")) {
        return (!isKw$538(next, "comptime"));
        break m$2;
      }
    }
    if (($1.$tag === "Ident")) {
      if (isPunct$695(tokIndex$884(self, $rt.usize(at + 2n)), ",")) {
        return true;
        break m$2;
      }
    }
    if (($1.$tag === "Punct")) {
      const p = $1.$;
      if ((p === "[")) {
        const $3 = closeFrom$885(self, $rt.usize(at + 1n));
        m$4: {
          if (($3.$tag === "Some")) {
            const c = $3.$;
            return isPunct$695(tokIndex$884(self, $rt.usize(c + 1n)), ":");
            break m$4;
          }
          if (($3.$tag === "None")) {
            return false;
            break m$4;
          }
          $rt.unmatched($3);
        }
        break m$2;
      }
    }
    if (($1.$tag === "Kw")) {
      const k = $1.$;
      if ((((k === "comptime") && (isKw$538(tokIndex$884(self, $rt.usize(at + 2n)), "for") || isKw$538(tokIndex$884(self, $rt.usize(at + 2n)), "if"))) && isPunct$695(tokIndex$884(self, $rt.usize(at + 3n)), "("))) {
        {
          const $5 = closeFrom$885(self, $rt.usize(at + 3n));
          m$6: {
            if (($5.$tag === "Some")) {
              const c = $5.$;
              return (isPunct$695(tokIndex$884(self, $rt.usize(c + 1n)), "{") && recordAt$854(self, $rt.usize(c + 1n)));
              break m$6;
            }
            if (($5.$tag === "None")) {
              return false;
              break m$6;
            }
            $rt.unmatched($5);
          }
        }
        break m$2;
      }
    }
    if (true) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function matchAt$855(self, at) {
  let $1 = (isWord$698(tokIndex$884(self, at), "match") && isPunct$695(tokIndex$884(self, $rt.usize(at + 1n)), "("));
  if ($1) {
    let $2;
    const $3 = closeFrom$885(self, $rt.usize(at + 1n));
    m$4: {
      if (($3.$tag === "Some")) {
        const c = $3.$;
        $2 = isPunct$695(tokIndex$884(self, $rt.usize(c + 1n)), "{");
        break m$4;
      }
      if (($3.$tag === "None")) {
        $2 = false;
        break m$4;
      }
      $rt.unmatched($3);
    }
    $1 = $2;
  }
  return $1;
}
function atHandle$856(self) {
  return (atWord$536(self, "handle") && atN$702(self, 1n, "{"));
}
function atRegion$857(self) {
  return ((((atWord$536(self, "region") && atN$702(self, 1n, "(")) && isIdent$549(tokAt$537(self, 2n))) && atN$702(self, 3n, ")")) && atN$702(self, 4n, "{"));
}
function clone$858(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Tuple")) {
      const x = $1.$;
      return { $tag: "Tuple", $: clone$567(x) };
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const x = $1.$;
      return { $tag: "Record", $: clone$356(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$859(self) {
  {
    return { bounds: clone$567(self.bounds), name: clone$218(self.name) };
  }
}
function clone$860(self) {
  return $b.Box_new(clone$886($b.Box_get(self)));
}
function clone$861(self) {
  return $b.Box_new(clone$887($b.Box_get(self)));
}
function clone$862(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "For")) {
      const x = $1.$;
      return { $tag: "For", $: clone$888(x) };
      break m$2;
    }
    if (($1.$tag === "If")) {
      const x = $1.$;
      return { $tag: "If", $: clone$889(x) };
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const x = $1.$;
      return { $tag: "Match", $: clone$890(x) };
      break m$2;
    }
    if (($1.$tag === "Do")) {
      const x = $1.$;
      return { $tag: "Do", $: clone$60(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function rec$863(fs) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(fs)) {
    const k = $1[0];
    const v = $1[1];
    recordSet$727(out, k, clone$90(v));
  }
  return { $tag: "Record", $: out.v };
}
function tagOf$864(n, v) {
  return { $tag: "Tag", $: [$b.str_toString(n), { $tag: "Some", $: $b.Box_new(v) }] };
}
function fieldInfo$865(k, t) {
  return rec$863([["name", { $tag: "Str", $: $b.String_clone(k) }], ["type", { $tag: "Type", $: clone$23(t) }]]);
}
function tagInfo$866(name, payload) {
  let $1;
  const $2 = payload;
  m$3: {
    if (($2.$tag === "Prim" && ($2.$.$tag === "Void"))) {
      $1 = { $tag: "Tag", $: [$b.str_toString("None"), { $tag: "None" }] };
      break m$3;
    }
    if (($2.$tag === "Tuple")) {
      const ts = $2.$;
      if (($b.slice_len(ts) === 1n)) {
        $1 = { $tag: "Tag", $: [$b.str_toString("Some"), { $tag: "Some", $: $b.Box_new({ $tag: "Type", $: clone$23($rt.idx(ts, 0n)) }) }] };
        break m$3;
      }
    }
    if (true) {
      const t = $2;
      $1 = { $tag: "Tag", $: [$b.str_toString("Some"), { $tag: "Some", $: $b.Box_new({ $tag: "Type", $: clone$23(t) }) }] };
      break m$3;
    }
    $rt.unmatched($2);
  }
  const p = $1;
  return rec$863([["name", { $tag: "Str", $: $b.str_toString(name) }], ["payload", p]]);
}
function privileged$867(self, d) {
  return (($rt.idx(self.p.v.defs, d).module === self.module) || eq$447(self.requested, { $tag: "Some", $: d }));
}
function find$868(self, test) {
  const $1 = $b.Gen_each(self);
  let $3;
  for (let $2 = $1.next(); !$2.done; $2 = $1.next($3)) {
    $3 = undefined;
    const $4 = $2.value.item;
    const x = $4;
    if (test(x)) {
      return { $tag: "Some", $: x };
    }
  }
  return { $tag: "None" };
}
function expandType$869(self, t) {
  try {
    return { $tag: "Some", $: ty$216(self, t) };
  } catch ($1) {
    if (!($1 instanceof $rt.Fail)) throw $1;
    const s = $1.value;
    report$92(self, s);
    return { $tag: "None" };
  }
}
function clone$870(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "None")) {
      return { $tag: "None" };
      break m$2;
    }
    if (($1.$tag === "Some")) {
      const x = $1.$;
      return { $tag: "Some", $: clone$274(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function parenExpr$871(self) {
  expect$544(self, "(");
  const e = expr$545(self);
  expect$544(self, ")");
  return e;
}
function template$872(self, parts) {
  const out = { v: $b.Vec_new() };
  for (const $1 of $rt.items(parts)) {
    const part = $1;
    const $2 = part;
    m$3: {
      if (($2.$tag === "Lit")) {
        const s = $2.$;
        $b.Vec_push(out, { $tag: "Lit", $: $b.String_clone(s) });
        break m$3;
      }
      if (($2.$tag === "Expr")) {
        const span = $2.$;
        {
          const sub = { v: { src: self.v.src, toks: lexRange$525(self.v.src, span.start, span.end), pos: 0n, declarations: false, nextId: self.v.nextId, guardArrow: { $tag: "None" } } };
          const e = expr$545(sub);
          expectEof$891(sub.v);
          self.v.nextId = sub.v.nextId;
          $b.Vec_push(out, { $tag: "Expr", $: e });
        }
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return out.v;
}
function tagArgs$873(self) {
  if (at$532(self.v, "(")) {
    return { $tag: "Tuple", $: args$883(self) };
  } else {
    if (at$532(self.v, "{")) {
      return { $tag: "Record", $: fieldInits$874(self) };
    } else {
      {
        return { $tag: "None" };
      }
    }
  }
}
function fieldInits$874(self) {
  expect$544(self, "{");
  const fields = initItems$892(self);
  expect$544(self, "}");
  return fields;
}
function isLambda$875(self) {
  const $1 = closeFrom$885(self, self.pos);
  m$2: {
    if (($1.$tag === "Some")) {
      const c = $1.$;
      return (isPunct$695(tokIndex$884(self, $rt.usize(c + 1n)), "=>") && !eq$447(self.guardArrow, { $tag: "Some", $: $rt.usize(c + 1n) }));
      break m$2;
    }
    if (($1.$tag === "None")) {
      return false;
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function lambdaParams$876(self) {
  expect$544(self, "(");
  const out = { v: $b.Vec_new() };
  const unpack = { v: $b.Vec_new() };
  while ((!at$532(self.v, ")"))) {
    if ((at$532(self.v, "[") || at$532(self.v, "{"))) {
      const pat = pattern$851(self);
      let $1;
      if (eat$542(self, ":")) {
        $1 = { $tag: "Some", $: ty$543(self) };
      } else {
        {
          $1 = { $tag: "None" };
        }
      }
      const ty = $1;
      const at = { start: pat.span.end, end: pat.span.end };
      const name = mkIdent$801($b.String_asStr(("" + "$" + String($b.slice_len(out.v)))), $rt.copy(pat.span));
      const init = expr_$706(self, { $tag: "Ident", $: $b.String_clone(name.name) }, $rt.copy(at));
      const span = $rt.copy(pat.span);
      $b.Vec_push(unpack, { $tag: "Let", $: { mutable: false, pat: pat, ty: { $tag: "None" }, init: init, span: span } });
      $b.Vec_push(out, { isComptime: false, name: name, ty: ty });
    } else {
      {
        const isComptime = eatKw$529(self, "comptime");
        const name = ident$541(self);
        let $2;
        if (eat$542(self, ":")) {
          $2 = { $tag: "Some", $: ty$543(self) };
        } else {
          {
            $2 = { $tag: "None" };
          }
        }
        const ty = $2;
        $b.Vec_push(out, { isComptime: isComptime, name: name, ty: ty });
      }
    }
    if ((!eat$542(self, ","))) {
      break;
    }
  }
  expect$544(self, ")");
  return [out.v, unpack.v];
}
function ifExpr$877(self) {
  expectKw$693(self, "if");
  const $1 = letHead$893(self);
  m$2: {
    if (($1.$tag === "Some")) {
      const pat = $1.$[0];
      const scrutinee = $1.$[1];
      const then = $1.$[2];
      {
        const start = span$528(self.v);
        let $3;
        if (eatKw$529(self, "else")) {
          if (atKw$530(self.v, "if")) {
            const kind = ifExpr$877(self);
            $3 = expr_$706(self, kind, since$554(self.v, $rt.copy(start)));
          } else {
            {
              const b = block$709(self);
              const span = $rt.copy(b.span);
              $3 = expr_$706(self, { $tag: "Block", $: b }, $rt.copy(span));
            }
          }
        } else {
          {
            $3 = expr_$706(self, { $tag: "Block", $: { stmts: $b.Vec_new(), tail: { $tag: "None" }, span: $rt.copy(start) } }, $rt.copy(start));
          }
        }
        const otherwise = $3;
        const span = $rt.copy(then.span);
        const rest = pat_$853(self, { $tag: "Wild" }, $rt.copy(otherwise.span));
        const thenExpr = expr_$706(self, { $tag: "Block", $: then }, $rt.copy(span));
        const arms = { v: $b.Vec_new() };
        $b.Vec_push(arms, { pat: pat, guard: { $tag: "None" }, body: thenExpr, generate: { $tag: "None" } });
        $b.Vec_push(arms, { pat: rest, guard: { $tag: "None" }, body: otherwise, generate: { $tag: "None" } });
        return { $tag: "Match", $: { scrutinee: $b.Box_new(scrutinee), arms: arms.v } };
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const cond = parenExpr$871(self);
  const then = block$709(self);
  let $4;
  if (eatKw$529(self, "else")) {
    const start = span$528(self.v);
    let $5;
    if (atKw$530(self.v, "if")) {
      const kind = ifExpr$877(self);
      $5 = expr_$706(self, kind, since$554(self.v, $rt.copy(start)));
    } else {
      {
        const b = block$709(self);
        const span = $rt.copy(b.span);
        $5 = expr_$706(self, { $tag: "Block", $: b }, $rt.copy(span));
      }
    }
    const e = $5;
    $4 = { $tag: "Some", $: $b.Box_new(e) };
  } else {
    {
      $4 = { $tag: "None" };
    }
  }
  const otherwise = $4;
  return { $tag: "If", $: { cond: $b.Box_new(cond), then: then, otherwise: otherwise } };
}
function whileExpr$878(self) {
  const kw = span$528(self.v);
  bump$539(self);
  const $1 = letHead$893(self);
  m$2: {
    if (($1.$tag === "Some")) {
      const pat = $1.$[0];
      const scrutinee = $1.$[1];
      const body = $1.$[2];
      {
        const all = { start: kw.start, end: body.span.end };
        const end = { start: body.span.end, end: body.span.end };
        const head = { start: scrutinee.span.start, end: body.span.end };
        const bspan = $rt.copy(body.span);
        const thenExpr = expr_$706(self, { $tag: "Block", $: body }, $rt.copy(bspan));
        const wild = pat_$853(self, { $tag: "Wild" }, $rt.copy(end));
        const brk = expr_$706(self, { $tag: "Break" }, $rt.copy(end));
        const arms = { v: $b.Vec_new() };
        $b.Vec_push(arms, { pat: pat, guard: { $tag: "None" }, body: thenExpr, generate: { $tag: "None" } });
        $b.Vec_push(arms, { pat: wild, guard: { $tag: "None" }, body: brk, generate: { $tag: "None" } });
        const m = expr_$706(self, { $tag: "Match", $: { scrutinee: $b.Box_new(scrutinee), arms: arms.v } }, $rt.copy(head));
        const yes = expr_$706(self, { $tag: "Bool", $: true }, $rt.copy(kw));
        const stmts = { v: $b.Vec_new() };
        $b.Vec_push(stmts, { $tag: "Expr", $: m });
        return { $tag: "While", $: { cond: $b.Box_new(yes), body: { stmts: stmts.v, tail: { $tag: "None" }, span: $rt.copy(all) } } };
      }
      break m$2;
    }
    if (true) {
      {
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
  const cond = parenExpr$871(self);
  return { $tag: "While", $: { cond: $b.Box_new(cond), body: block$709(self) } };
}
function armItems$879(self) {
  const arms = { v: $b.Vec_new() };
  while ((!at$532(self.v, "}"))) {
    if ((atKw$530(self.v, "comptime") && ((isKw$538(tokAt$537(self.v, 1n), "for") || isKw$538(tokAt$537(self.v, 1n), "if")) || wordAt$836(self.v, 1n, "match")))) {
      const start = span$528(self.v);
      const g = generate$894(self, ((p) => {
  return armItems$879(p);
      }));
      const span = since$554(self.v, $rt.copy(start));
      const pat = pat_$853(self, { $tag: "Wild" }, $rt.copy(span));
      const body = expr_$706(self, { $tag: "Break" }, $rt.copy(span));
      $b.Vec_push(arms, { pat: pat, guard: { $tag: "None" }, body: body, generate: { $tag: "Some", $: $b.Box_new(g) } });
      eat$542(self, ",");
      continue;
    }
    const pat = pattern$851(self);
    let $1;
    if (eatKw$529(self, "if")) {
      const saved = $b.replace(new $rt.FieldRef(self.v, "guardArrow"), arrowAhead$895(self.v));
      let $2;
      try {
        $2 = expr$545(self);
      } catch ($3) {
        if (!($3 instanceof $rt.Fail)) throw $3;
        const d = $3.value;
        self.v.guardArrow = saved;
        throw new $rt.Fail(d);
      }
      const g = $2;
      self.v.guardArrow = saved;
      $1 = { $tag: "Some", $: g };
    } else {
      {
        $1 = { $tag: "None" };
      }
    }
    const guard = $1;
    expect$544(self, "=>");
    if (at$532(self.v, "{")) {
      const b = block$709(self);
      const span = $rt.copy(b.span);
      const body = expr_$706(self, { $tag: "Block", $: b }, $rt.copy(span));
      $b.Vec_push(arms, { pat: pat, guard: guard, body: body, generate: { $tag: "None" } });
      eat$542(self, ",");
    } else {
      {
        const body = expr$545(self);
        $b.Vec_push(arms, { pat: pat, guard: guard, body: body, generate: { $tag: "None" } });
        if ((!eat$542(self, ","))) {
          break;
        }
      }
    }
  }
  return arms.v;
}
function handleExpr$880(self, start) {
  bump$539(self);
  const body = { v: block$709(self) };
  const handled = { v: { $tag: "None" } };
  while (eatWord$534(self, "with")) {
    const $1 = $b.Option_take(handled);
    m$2: {
      if (($1.$tag === "Some")) {
        const kind = $1.$;
        {
          const span = since$554(self.v, $rt.copy(start));
          const inner = expr_$706(self, kind, $rt.copy(span));
          body.v = { stmts: $b.Vec_new(), tail: { $tag: "Some", $: $b.Box_new(inner) }, span: span };
        }
        break m$2;
      }
      if (true) {
        {
        }
        break m$2;
      }
      $rt.unmatched($1);
    }
    const effect = tyPostfix$701(self);
    expect$544(self, "{");
    const arms = { v: $b.Vec_new() };
    while ((!at$532(self.v, "}"))) {
      const op = memberName$810(self);
      expect$544(self, "(");
      const params = { v: $b.Vec_new() };
      while ((!at$532(self.v, ")"))) {
        $b.Vec_push(params, ident$541(self));
        if ((!eat$542(self, ","))) {
          break;
        }
      }
      expect$544(self, ")");
      let $3;
      if (eatWord$534(self, "resumes")) {
        $3 = { $tag: "Some", $: ident$541(self) };
      } else {
        {
          $3 = { $tag: "None" };
        }
      }
      const resumes = $3;
      expect$544(self, "=>");
      let $4;
      if (at$532(self.v, "{")) {
        const b = block$709(self);
        eat$542(self, ",");
        $4 = b;
      } else {
        {
          const e = expr$545(self);
          const span = $rt.copy(e.span);
          eat$542(self, ",");
          $4 = { stmts: $b.Vec_new(), tail: { $tag: "Some", $: $b.Box_new(e) }, span: span };
        }
      }
      const armBody = $4;
      $b.Vec_push(arms, { op: op, params: params.v, resumes: resumes, body: armBody });
    }
    expect$544(self, "}");
    handled.v = { $tag: "Some", $: { $tag: "Handle", $: { body: $b.replace(body, { stmts: $b.Vec_new(), tail: { $tag: "None" }, span: $rt.copy(start) }), effect: effect, arms: arms.v } } };
  }
  const $5 = handled.v;
  m$6: {
    if (($5.$tag === "Some")) {
      const kind = $5.$;
      return kind;
      break m$6;
    }
    if (($5.$tag === "None")) {
      return error$552(self.v, "`with`");
      break m$6;
    }
    $rt.unmatched($5);
  }
}
function adjacent$881(self, a, b) {
  return ((at$532(self, a) && atN$702(self, 1n, b)) && ($rt.idx(self.toks, self.pos).span.end === $rt.idx(self.toks, $rt.usize(self.pos + 1n)).span.start));
}
function clone$882(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$896(x));
  }
  return v.v;
}
function args$883(self) {
  expect$544(self, "(");
  const out = { v: $b.Vec_new() };
  while ((!at$532(self.v, ")"))) {
    $b.Vec_push(out, expr$545(self));
    if ((!eat$542(self, ","))) {
      break;
    }
  }
  expect$544(self, ")");
  return out.v;
}
function tokIndex$884(self, i) {
  return $rt.idx(self.toks, min$146(i, $rt.usize($b.slice_len(self.toks) - 1n))).tok;
}
function closeFrom$885(self, from) {
  let depth = 0n;
  let i = from;
  while ((i < $b.slice_len(self.toks))) {
    const $1 = $rt.idx(self.toks, i).tok;
    m$2: {
      if (($1.$tag === "Punct")) {
        const p = $1.$;
        {
          if ((((p === "(") || (p === "[")) || (p === "{"))) {
            depth = $rt.usize(depth + 1n);
          } else {
            if ((((p === ")") || (p === "]")) || (p === "}"))) {
              depth = $rt.usize(depth - 1n);
              if ((depth === 0n)) {
                return { $tag: "Some", $: i };
              }
            }
          }
        }
        break m$2;
      }
      if (($1.$tag === "Eof")) {
        return { $tag: "None" };
        break m$2;
      }
      if (true) {
        {
        }
        break m$2;
      }
      $rt.unmatched($1);
    }
    i = $rt.usize(i + 1n);
  }
  return { $tag: "None" };
}
function clone$886(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "For")) {
      const x = $1.$;
      return { $tag: "For", $: clone$897(x) };
      break m$2;
    }
    if (($1.$tag === "If")) {
      const x = $1.$;
      return { $tag: "If", $: clone$898(x) };
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const x = $1.$;
      return { $tag: "Match", $: clone$899(x) };
      break m$2;
    }
    if (($1.$tag === "Do")) {
      const x = $1.$;
      return { $tag: "Do", $: clone$60(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$887(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "For")) {
      const x = $1.$;
      return { $tag: "For", $: clone$900(x) };
      break m$2;
    }
    if (($1.$tag === "If")) {
      const x = $1.$;
      return { $tag: "If", $: clone$901(x) };
      break m$2;
    }
    if (($1.$tag === "Match")) {
      const x = $1.$;
      return { $tag: "Match", $: clone$902(x) };
      break m$2;
    }
    if (($1.$tag === "Do")) {
      const x = $1.$;
      return { $tag: "Do", $: clone$60(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$888(self) {
  {
    return { body: clone$356(self.body), iter: clone$60(self.iter), pat: clone$274(self.pat) };
  }
}
function clone$889(self) {
  {
    return { cond: clone$60(self.cond), otherwise: clone$356(self.otherwise), then: clone$356(self.then) };
  }
}
function clone$890(self) {
  {
    return { arms: clone$903(self.arms), scrutinee: clone$60(self.scrutinee) };
  }
}
function expectEof$891(self) {
  if ((!atEof$326(self))) {
    error$552(self, "end of input");
    return undefined;
  }
}
function initItems$892(self) {
  const fields = { v: $b.Vec_new() };
  while ((!at$532(self.v, "}"))) {
    if ((atKw$530(self.v, "comptime") && ((isKw$538(tokAt$537(self.v, 1n), "for") || isKw$538(tokAt$537(self.v, 1n), "if")) || wordAt$836(self.v, 1n, "match")))) {
      const start = span$528(self.v);
      const g = generate$904(self, ((p) => {
  return initItems$892(p);
      }));
      $b.Vec_push(fields, { name: mkIdent$801("", since$554(self.v, $rt.copy(start))), value: { $tag: "None" }, computed: { $tag: "None" }, generate: { $tag: "Some", $: $b.Box_new(g) } });
      eat$542(self, ",");
      continue;
    }
    const $1 = entryName$838(self);
    const name = $1[0];
    const computed = $1[1];
    let $2;
    if (($b.Option_isSome(computed) || at$532(self.v, ":"))) {
      expect$544(self, ":");
      $2 = { $tag: "Some", $: expr$545(self) };
    } else {
      {
        $2 = { $tag: "None" };
      }
    }
    const value = $2;
    $b.Vec_push(fields, { name: name, value: value, computed: computed, generate: { $tag: "None" } });
    if ((!eat$542(self, ","))) {
      break;
    }
  }
  return fields.v;
}
function letHead$893(self) {
  if ((!(at$532(self.v, "(") && (isKw$538(tokAt$537(self.v, 1n), "const") || isKw$538(tokAt$537(self.v, 1n), "let"))))) {
    return { $tag: "None" };
  }
  bump$539(self);
  const mutable = eatKw$529(self, "let");
  if ((!mutable)) {
    bump$539(self);
  }
  const pat = pattern$851(self);
  expect$544(self, "=");
  const scrutinee = expr$545(self);
  expect$544(self, ")");
  let body = block$709(self);
  if (mutable) {
    const names = { v: $b.Vec_new() };
    boundNames$905(pat, names);
    const stmts = { v: $b.Vec_new() };
    for (const $1 of $rt.items(names.v)) {
      const name = $1[0];
      const span = $1[1];
      const bind = pat_$853(self, { $tag: "Bind", $: $b.String_clone(name) }, $rt.copy(span));
      const init = expr_$706(self, { $tag: "Ident", $: $b.String_clone(name) }, $rt.copy(span));
      $b.Vec_push(stmts, { $tag: "Let", $: { mutable: true, pat: bind, ty: { $tag: "None" }, init: init, span: span } });
    }
    const $2 = $b.Gen_each($b.Vec_drain(new $rt.FieldRef(body, "stmts")));
    let $4;
    for (let $3 = $2.next(); !$3.done; $3 = $2.next($4)) {
      $4 = undefined;
      const $5 = $3.value.item;
      const s = $5;
      $b.Vec_push(stmts, s);
    }
    body.stmts = stmts.v;
  }
  return { $tag: "Some", $: [pat, scrutinee, body] };
}
function generate$894(self, items) {
  expectKw$693(self, "comptime");
  if (eatKw$529(self, "for")) {
    expect$544(self, "(");
    if (((!eatKw$529(self, "const")) && (!eatKw$529(self, "let")))) {
      error$552(self.v, "`const`");
    }
    const pat = patternOne$807(self);
    expectWord$694(self, "of");
    const iter = expr$545(self);
    expect$544(self, ")");
    expect$544(self, "{");
    const body = items(self);
    expect$544(self, "}");
    return { $tag: "For", $: { pat: pat, iter: iter, body: body } };
  }
  if (eatKw$529(self, "if")) {
    const cond = parenExpr$871(self);
    expect$544(self, "{");
    const then = items(self);
    expect$544(self, "}");
    let otherwise = $b.Vec_new();
    if (eatKw$529(self, "else")) {
      expect$544(self, "{");
      otherwise = items(self);
      expect$544(self, "}");
    }
    return { $tag: "If", $: { cond: cond, then: then, otherwise: otherwise } };
  }
  if (eatWord$534(self, "match")) {
    const scrutinee = parenExpr$871(self);
    expect$544(self, "{");
    const arms = { v: $b.Vec_new() };
    while ((!at$532(self.v, "}"))) {
      const pat = pattern$851(self);
      expect$544(self, "=>");
      expect$544(self, "{");
      const group = items(self);
      expect$544(self, "}");
      $b.Vec_push(arms, [pat, group]);
      eat$542(self, ",");
    }
    expect$544(self, "}");
    return { $tag: "Match", $: { scrutinee: scrutinee, arms: arms.v } };
  }
  return error$552(self.v, "`for`, `if` or `match` after `comptime`");
}
function arrowAhead$895(self) {
  let depth = 0n;
  let i = self.pos;
  while ((i < $b.slice_len(self.toks))) {
    const $1 = $rt.idx(self.toks, i).tok;
    m$2: {
      if (($1.$tag === "Punct")) {
        const p = $1.$;
        {
          if ((((p === "(") || (p === "[")) || (p === "{"))) {
            depth = $rt.usize(depth + 1n);
          } else {
            if ((((p === ")") || (p === "]")) || (p === "}"))) {
              if ((depth === 0n)) {
                return { $tag: "None" };
              }
              depth = $rt.usize(depth - 1n);
            } else {
              if (((p === "=>") && (depth === 0n))) {
                return { $tag: "Some", $: i };
              }
            }
          }
        }
        break m$2;
      }
      if (($1.$tag === "Eof")) {
        return { $tag: "None" };
        break m$2;
      }
      if (true) {
        {
        }
        break m$2;
      }
      $rt.unmatched($1);
    }
    i = $rt.usize(i + 1n);
  }
  return { $tag: "None" };
}
function clone$896(self) {
  const $1 = self;
  m$2: {
    if (($1.$tag === "Lit")) {
      const x = $1.$;
      return { $tag: "Lit", $: $b.String_clone(x) };
      break m$2;
    }
    if (($1.$tag === "Expr")) {
      const x = $1.$;
      return { $tag: "Expr", $: clone$94(x) };
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$897(self) {
  {
    return { body: clone$565(self.body), iter: clone$60(self.iter), pat: clone$274(self.pat) };
  }
}
function clone$898(self) {
  {
    return { cond: clone$60(self.cond), otherwise: clone$565(self.otherwise), then: clone$565(self.then) };
  }
}
function clone$899(self) {
  {
    return { arms: clone$906(self.arms), scrutinee: clone$60(self.scrutinee) };
  }
}
function clone$900(self) {
  {
    return { body: clone$568(self.body), iter: clone$60(self.iter), pat: clone$274(self.pat) };
  }
}
function clone$901(self) {
  {
    return { cond: clone$60(self.cond), otherwise: clone$568(self.otherwise), then: clone$568(self.then) };
  }
}
function clone$902(self) {
  {
    return { arms: clone$907(self.arms), scrutinee: clone$60(self.scrutinee) };
  }
}
function clone$903(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$908(x));
  }
  return v.v;
}
function generate$904(self, items) {
  expectKw$693(self, "comptime");
  if (eatKw$529(self, "for")) {
    expect$544(self, "(");
    if (((!eatKw$529(self, "const")) && (!eatKw$529(self, "let")))) {
      error$552(self.v, "`const`");
    }
    const pat = patternOne$807(self);
    expectWord$694(self, "of");
    const iter = expr$545(self);
    expect$544(self, ")");
    expect$544(self, "{");
    const body = items(self);
    expect$544(self, "}");
    return { $tag: "For", $: { pat: pat, iter: iter, body: body } };
  }
  if (eatKw$529(self, "if")) {
    const cond = parenExpr$871(self);
    expect$544(self, "{");
    const then = items(self);
    expect$544(self, "}");
    let otherwise = $b.Vec_new();
    if (eatKw$529(self, "else")) {
      expect$544(self, "{");
      otherwise = items(self);
      expect$544(self, "}");
    }
    return { $tag: "If", $: { cond: cond, then: then, otherwise: otherwise } };
  }
  if (eatWord$534(self, "match")) {
    const scrutinee = parenExpr$871(self);
    expect$544(self, "{");
    const arms = { v: $b.Vec_new() };
    while ((!at$532(self.v, "}"))) {
      const pat = pattern$851(self);
      expect$544(self, "=>");
      expect$544(self, "{");
      const group = items(self);
      expect$544(self, "}");
      $b.Vec_push(arms, [pat, group]);
      eat$542(self, ",");
    }
    expect$544(self, "}");
    return { $tag: "Match", $: { scrutinee: scrutinee, arms: arms.v } };
  }
  return error$552(self.v, "`for`, `if` or `match` after `comptime`");
}
function boundNames$905(p, out) {
  const $1 = p.kind;
  m$2: {
    if (($1.$tag === "Bind")) {
      const n = $1.$;
      return $b.Vec_push(out, [$b.String_clone(n), $rt.copy(p.span)]);
      break m$2;
    }
    if ((($1.$tag === "Tuple") || ($1.$tag === "Or"))) {
      let ps;
      if (($1.$tag === "Tuple")) { ps = $1.$; }
      else if (($1.$tag === "Or")) { ps = $1.$; }
      {
        for (const $3 of $rt.items(ps)) {
          const q = $3;
          boundNames$905(q, out);
        }
        return undefined;
      }
      break m$2;
    }
    if (($1.$tag === "Record")) {
      const fields = $1.$.fields;
      {
        boundFields$909(fields, out);
        return undefined;
      }
      break m$2;
    }
    if ((($1.$tag === "Tag") || ($1.$tag === "TagAt"))) {
      let args;
      if (($1.$tag === "Tag")) { args = $1.$.args; }
      else if (($1.$tag === "TagAt")) { args = $1.$.args; }
      const $4 = args;
      m$5: {
        if (($4.$tag === "None")) {
          {
            return undefined;
          }
          break m$5;
        }
        if (($4.$tag === "Tuple")) {
          const ps = $4.$;
          {
            for (const $6 of $rt.items(ps)) {
              const q = $6;
              boundNames$905(q, out);
            }
            return undefined;
          }
          break m$5;
        }
        if (($4.$tag === "Record")) {
          const fs = $4.$;
          {
            boundFields$909(fs, out);
            return undefined;
          }
          break m$5;
        }
        $rt.unmatched($4);
      }
      break m$2;
    }
    if (true) {
      {
        return undefined;
      }
      break m$2;
    }
    $rt.unmatched($1);
  }
}
function clone$906(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$910(x));
  }
  return v.v;
}
function clone$907(self) {
  const v = { v: $b.Vec_new() };
  for (const $1 of $rt.items(self)) {
    const x = $1;
    $b.Vec_push(v, clone$911(x));
  }
  return v.v;
}
function clone$908(self) {
  {
    const v = [clone$274($rt.idx(self, 0n)), clone$356($rt.idx(self, 1n))];
    return v;
  }
}
function boundFields$909(fields, out) {
  for (const $1 of $rt.items(fields)) {
    const n = $1[0];
    const q = $1[1];
    const $2 = q;
    m$3: {
      if (($2.$tag === "Some")) {
        const q$$4 = $2.$;
        boundNames$905(q$$4, out);
        break m$3;
      }
      if (($2.$tag === "None")) {
        $b.Vec_push(out, [$b.String_clone(n.name), $rt.copy(n.span)]);
        break m$3;
      }
      $rt.unmatched($2);
    }
  }
  return undefined;
}
function clone$910(self) {
  {
    const v = [clone$274($rt.idx(self, 0n)), clone$565($rt.idx(self, 1n))];
    return v;
  }
}
function clone$911(self) {
  {
    const v = [clone$274($rt.idx(self, 0n)), clone$568($rt.idx(self, 1n))];
    return v;
  }
}
$rt.start(() => main$0($rt.argStr(0), $rt.argStr(1), $rt.argStr(2)), false, false);
