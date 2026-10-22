"use strict";
// The runtime of Flyscript compiled to JavaScript.
//
// Values: integers are BigInts and floats numbers; a string holds one byte per character, so
// that lengths and offsets are the byte counts Flyscript defines; `void` is `undefined`. A struct
// is an object whose `$t` names it, a tag an object whose `$tag` names it, with its payload in
// `$`. Vectors, slices, arrays and tuples are arrays. `Box`, `Arc` and region references are the
// values they hold: the garbage collector owns everything. A `mut` argument is a `Ref`.
const $rt = (() => {
  const fs = require("fs");

  class Fail {
    constructor(value) { this.value = value; }
  }
  class Panic extends Error {}

  class Ref {
    constructor(get, set) { this.get = get; this.set = set; }
    get v() { return this.get(); }
    set v(x) { this.set(x); }
  }
  const ref = (get, set) => new Ref(get, set);

  const none = () => ({ $tag: "None" });
  const some = (v) => ({ $tag: "Some", $: v });
  const LESS = { $tag: "Less" }, EQUAL = { $tag: "Equal" }, GREATER = { $tag: "Greater" };

  function panic(message) { throw new Panic(message); }

  // ---- what programs declare ----

  const methods = new Map();
  const fallbacks = new Map();
  const impls = new Map();
  const tagOwners = new Map();
  const tagIndex = new Map();
  const structs = new Map();

  function table(map, key) {
    let t = map.get(key);
    if (t === undefined) { t = new Map(); map.set(key, t); }
    return t;
  }
  function method(type, name, fn) { table(methods, type).set(name, fn); }
  function fallback(iface, name, fn) { table(fallbacks, iface).set(name, fn); }
  function implement(type, iface) {
    if (!impls.has(type)) impls.set(type, []);
    impls.get(type).push(iface);
  }
  function enumTags(name, tags) {
    tags.forEach((t, i) => {
      if (!tagOwners.has(t)) tagOwners.set(t, []);
      tagOwners.get(t).push(name);
      tagIndex.set(t, i);
    });
  }
  function struct(name, fields) { structs.set(name, fields); shapes = undefined; }

  // The structs whose fields a record has: a record a struct's type gave its type to, as
  // `alloc({ parent, names })` builds a `Scope`, has no `$t` (compiled code has no types).
  let shapes;
  function structsShaped(v) {
    if (shapes === undefined) {
      shapes = new Map();
      for (const [name, fields] of structs) {
        const key = [...fields].sort().join(",");
        if (!shapes.has(key)) shapes.set(key, []);
        shapes.get(key).push(name);
      }
    }
    return shapes.get(Object.keys(v).sort().join(",")) || [];
  }

  function userMethod(type, name) {
    const own = methods.get(type);
    if (own !== undefined && own.has(name)) return own.get(name);
    for (const i of impls.get(type) || []) {
      const f = fallbacks.get(i);
      if (f !== undefined && f.has(name)) return f.get(name);
    }
    return undefined;
  }

  const INTS = ["i64", "usize", "u8", "i32", "u32", "u64", "i8", "i16", "u16", "isize", "i128"];
  function userTypes(v) {
    switch (typeof v) {
      case "string": return ["String", "str"];
      case "bigint": return INTS;
      case "number": return ["f64", "f32"];
      case "boolean": return ["bool"];
      case "object":
        if (v === null) return [];
        if (v.$t !== undefined) return [v.$t];
        if (v.$tag !== undefined) return tagOwners.get(v.$tag) || [];
        if (Object.getPrototypeOf(v) === Object.prototype) return structsShaped(v);
        return [];
      default: return [];
    }
  }

  // ---- iteration ----

  class Gen {
    constructor(it) { this.it = it; }
    [Symbol.iterator]() { return this.it; }
  }
  const gen = (iterable) => new Gen(iterable[Symbol.iterator]());
  const isIterator = (v) => v !== null && typeof v === "object" && typeof v.next === "function" && typeof v[Symbol.iterator] === "function";

  function iter(v) {
    if (Array.isArray(v) || v instanceof Gen || v instanceof Bytes || isIterator(v)) return v;
    for (const t of userTypes(v)) {
      const each = userMethod(t, "each");
      if (each !== undefined) return each(v);
    }
    if (v instanceof HashMap) return v.entries();
    if (v instanceof HashSet) return v.values();
    panic(`cannot iterate over ${show(v)}`);
  }

  function* rangeOf(a, b) { for (let i = a; i < b; i++) yield i; }
  const range = (a, b) => new Gen(rangeOf(a, b));

  // ---- collections ----

  // A key's identity: strings and integers as they are, anything else by its structure.
  function keyOf(k) {
    switch (typeof k) {
      case "string": return "s" + k;
      case "bigint": return "i" + k;
      default: return "v" + show(k);
    }
  }

  class HashMap {
    constructor() { this.m = new Map(); }
    insert(k, v) { this.m.set(keyOf(k), [k, v]); }
    get(k) { const e = this.m.get(keyOf(k)); return e === undefined ? none() : some(e[1]); }
    has(k) { return this.m.has(keyOf(k)); }
    remove(k) {
      const key = keyOf(k);
      const e = this.m.get(key);
      if (e === undefined) return none();
      this.m.delete(key);
      return some(e[1]);
    }
    len() { return BigInt(this.m.size); }
    *keys() { for (const [k] of this.m.values()) yield k; }
    *values() { for (const [, v] of this.m.values()) yield v; }
    *entries() { for (const [k, v] of this.m.values()) yield [k, v]; }
    clone() {
      const out = new HashMap();
      for (const [key, [k, v]] of this.m) out.m.set(key, [clone(k), clone(v)]);
      return out;
    }
  }

  class HashSet {
    constructor() { this.m = new Map(); }
    insert(v) { const key = keyOf(v); if (this.m.has(key)) return false; this.m.set(key, v); return true; }
    has(v) { return this.m.has(keyOf(v)); }
    remove(v) { return this.m.delete(keyOf(v)); }
    len() { return BigInt(this.m.size); }
    *values() { yield* this.m.values(); }
    clone() { const out = new HashSet(); for (const [k, v] of this.m) out.m.set(k, clone(v)); return out; }
  }

  class File {
    constructor(text) { this.text = text; }
  }

  // A string's bytes, `s.asBytes()`: a view of the string, not a copy of it.
  class Bytes {
    constructor(s) { this.s = s; }
    get length() { return this.s.length; }
    *[Symbol.iterator]() { for (let i = 0; i < this.s.length; i++) yield BigInt(this.s.charCodeAt(i)); }
    array() { return Array.from(this); }
  }
  const BYTES = {
    len: (b) => BigInt(b.s.length),
    iter: (b) => gen(b), iterMut: (b) => gen(b),
    *each(b) { yield* b; },
    includes: (b, x) => b.s.indexOf(String.fromCharCode(Number(x))) >= 0,
    clone: (b) => b.array(),
  };

  // A region's mutable cell; copies of it are the same cell.
  class Cell {
    constructor(v) { this.v = v; }
  }

  // FNV-1a, 64 bits.
  class Hasher {
    constructor() { this.h = 0xcbf29ce484222325n; }
    bytes(bs) { for (const b of bs) this.h = BigInt.asUintN(64, (this.h ^ BigInt(b)) * 0x100000001b3n); }
  }
  const HASHER = {
    writeStr: (h, s) => h.bytes(Array.from(s, (c) => c.charCodeAt(0))),
    writeInt: (h, i) => { const b = []; let x = BigInt.asUintN(64, i); for (let k = 0; k < 8; k++) { b.push(Number(x & 255n)); x >>= 8n; } h.bytes(b); },
    writeBool: (h, b) => h.bytes([b ? 1 : 0]),
    // -0.0 hashes as 0.0, as it equals it (§3.5).
    writeFloat: (h, f) => HASHER.writeStr(h, String(f === 0 ? 0 : f)),
    finish: (h) => h.h,
  };

  // ---- generic operations: what `Eq`, `Ord`, `Clone` and `Show` derive ----

  function eq(a, b) {
    if (a === b) return true;
    if (a instanceof Bytes) return eq(a.array(), b instanceof Bytes ? b.array() : b);
    if (b instanceof Bytes) return eq(a, b.array());
    // `Eq` on floats is total: NaN equals itself (§3.5).
    if (typeof a === "number" && typeof b === "number") return Number.isNaN(a) && Number.isNaN(b);
    if (typeof a !== "object" || typeof b !== "object" || a === null || b === null) return false;
    if (Array.isArray(a)) {
      if (!Array.isArray(b) || a.length !== b.length) return false;
      for (let i = 0; i < a.length; i++) if (!eq(a[i], b[i])) return false;
      return true;
    }
    if (a.$t !== undefined) {
      const user = userMethod(a.$t, "eq");
      if (user !== undefined) return user(a, b);
    }
    if (a.$tag !== undefined) {
      if (a.$tag !== b.$tag) return false;
      for (const t of userTypes(a)) {
        const user = userMethod(t, "eq");
        if (user !== undefined) return user(a, b);
      }
      return eq(a.$, b.$);
    }
    if (a instanceof HashMap || a instanceof HashSet) {
      if (a.m.size !== b.m.size) return false;
      for (const [k, v] of a.m) if (!b.m.has(k) || !eq(v, b.m.get(k))) return false;
      return true;
    }
    const ka = Object.keys(a), kb = Object.keys(b);
    if (ka.length !== kb.length) return false;
    for (const k of ka) if (!eq(a[k], b[k])) return false;
    return true;
  }

  // -1, 0 or 1.
  function compare(a, b) {
    switch (typeof a) {
      case "number":
        // `Ord` on floats is total: NaN orders after every number (§3.5).
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
    for (const t of userTypes(a)) {
      const user = userMethod(t, "cmp");
      if (user !== undefined) return ordinal(user(a, b));
    }
    if (a.$tag !== undefined) {
      if (a.$tag !== b.$tag) return (tagIndex.get(a.$tag) || 0) < (tagIndex.get(b.$tag) || 0) ? -1 : 1;
      return a.$ === undefined ? 0 : compare(a.$, b.$);
    }
    for (const k of Object.keys(a)) {
      if (k === "$t") continue;
      const c = compare(a[k], b[k]);
      if (c !== 0) return c;
    }
    return 0;
  }
  const ordinal = (o) => (o.$tag === "Less" ? -1 : o.$tag === "Greater" ? 1 : 0);
  const ordering = (c) => (c < 0 ? LESS : c > 0 ? GREATER : EQUAL);

  function cmpOp(a, b, op) {
    if (typeof a !== "object") {
      switch (op) {
        case "<": return a < b;
        case ">": return a > b;
        case "<=": return a <= b;
        default: return a >= b;
      }
    }
    const c = compare(a, b);
    switch (op) {
      case "<": return c < 0;
      case ">": return c > 0;
      case "<=": return c <= 0;
      default: return c >= 0;
    }
  }

  function clone(v) {
    if (typeof v !== "object" || v === null) return v;
    if (Array.isArray(v)) return v.map(clone);
    if (v instanceof HashMap || v instanceof HashSet) return v.clone();
    if (v instanceof Gen || v instanceof File || isIterator(v)) return v;
    for (const t of userTypes(v)) {
      const user = userMethod(t, "clone");
      if (user !== undefined) return user(v);
    }
    const out = {};
    for (const k of Object.keys(v)) out[k] = clone(v[k]);
    return out;
  }

  // A value as assigning it copies it: JavaScript shares objects, Flyscript copies `Copy` ones.
  function copy(v) {
    if (typeof v !== "object" || v === null || Array.isArray(v) || Object.getPrototypeOf(v) !== Object.prototype) return v;
    const out = {};
    for (const k of Object.keys(v)) out[k] = copy(v[k]);
    return out;
  }

  // ---- display ----

  function float(f) {
    if (Number.isInteger(f) && Math.abs(f) < 1e15) return f.toFixed(1);
    return String(f);
  }

  function quoted(s) {
    return "\"" + s.replace(/[\\"\n\t\r]/g, (c) => ({ "\\": "\\\\", "\"": "\\\"", "\n": "\\n", "\t": "\\t", "\r": "\\r" })[c]) + "\"";
  }

  function show(v) {
    switch (typeof v) {
      case "string": return quoted(v);
      case "bigint": case "boolean": return String(v);
      case "number": return float(v);
      case "undefined": return "void";
      case "function": return "<function>";
    }
    for (const t of userTypes(v)) {
      const user = userMethod(t, "show");
      if (user !== undefined) {
        let out = "";
        user(v, ref(() => out, (x) => { out = x; }));
        return out;
      }
    }
    if (Array.isArray(v)) return "[" + v.map(show).join(", ") + "]";
    if (v instanceof Bytes) return show(v.array());
    if (v.$tag !== undefined) return v.$ === undefined ? "#" + v.$tag : "#" + v.$tag + "(" + show(v.$) + ")";
    if (v instanceof HashMap) return "{ " + [...v.m.values()].map(([k, x]) => show(k) + ": " + show(x)).join(", ") + " }";
    const fields = Object.keys(v).filter((k) => k !== "$t").map((k) => k + ": " + show(v[k]));
    return (v.$t !== undefined ? v.$t + " " : "") + (fields.length === 0 ? "{ }" : "{ " + fields.join(", ") + " }");
  }

  // A value in a template: a string as it is.
  const str = (v) => (typeof v === "string" ? v : show(v));

  // ---- operators ----

  function idx(a, i) {
    const n = Number(i);
    if (n < 0 || n >= a.length) panic(`index ${i} out of bounds (length ${a.length})`);
    if (typeof a === "string") return BigInt(a.charCodeAt(n));
    if (a instanceof Bytes) return BigInt(a.s.charCodeAt(n));
    return a[n];
  }
  function at(a, i) {
    const n = Number(i);
    if (n < 0 || n >= a.length) panic(`index ${i} out of bounds (length ${a.length})`);
    return n;
  }
  function slice(a, lo, hi) {
    const l = Number(lo), h = hi === undefined ? a.length : Number(hi);
    if (l > h || h > a.length) panic(`range ${l}..${h} out of bounds (length ${a.length})`);
    // A string's bounds fall between characters: not on a UTF-8 continuation byte (§3.1).
    if (typeof a === "string" && (continuation(a, l) || continuation(a, h))) panic(`range ${l}..${h} splits a character`);
    if (a instanceof Bytes) return new Bytes(a.s.slice(l, h));
    return a.slice(l, h);
  }
  const continuation = (s, i) => i < s.length && (s.charCodeAt(i) & 0xc0) === 0x80;

  const WIDTHS = { i8: [8, true], i16: [16, true], i32: [32, true], i64: [64, true], i128: [128, true], isize: [64, true],
    u8: [8, false], u16: [16, false], u32: [32, false], u64: [64, false], usize: [64, false] };
  function cast(v, ty) {
    if (ty === "f64" || ty === "f32") return Number(v);
    const w = WIDTHS[ty];
    if (w === undefined) return v;
    const i = typeof v === "number" ? BigInt(Math.trunc(v)) : typeof v === "boolean" ? (v ? 1n : 0n) : v;
    return w[1] ? BigInt.asIntN(w[0], i) : BigInt.asUintN(w[0], i);
  }

  function unmatched(v) { panic(`no arm matches ${show(v)}`); }

  // ---- the standard library's methods ----

  const S = {
    asStr: (s) => s, toString: (s) => s, clone: (s) => s,
    len: (s) => BigInt(s.length),
    asBytes: (s) => new Bytes(s),
    *bytes(s) { for (let i = 0; i < s.length; i++) yield BigInt(s.charCodeAt(i)); },
    *lines(s) { const ls = s.split("\n"); if (ls[ls.length - 1] === "") ls.pop(); yield* ls; },
    *splitWhitespace(s) { yield* s.split(/[ \t\n\r]+/).filter((w) => w !== ""); },
    startsWith: (s, p) => s.startsWith(p),
    endsWith: (s, p) => s.endsWith(p),
    includes: (s, p) => s.includes(p),
    indexOf: (s, p) => { const i = s.indexOf(p); return i < 0 ? none() : some(BigInt(i)); },
    replaceAll: (s, a, b) => s.split(a).join(b),
    slice: (s, i, j) => slice(s, i, j),
    split: (s, sep) => s.split(sep),
    trim: (s) => s.replace(/^[ \t\n\r]+|[ \t\n\r]+$/g, ""),
    // Byte strings hold UTF-8: only ASCII letters change case.
    toLowerCase: (s) => s.replace(/[A-Z]/g, (c) => c.toLowerCase()),
    toUpperCase: (s) => s.replace(/[a-z]/g, (c) => c.toUpperCase()),
    cmp: (a, b) => ordering(compare(a, b)),
  };
  // Methods that change a string, given a reference to it.
  const SW = {
    push: (r, s) => { r.v = r.v + s; },
    clear: (r) => { r.v = ""; },
  };
  // `Option.take`, given a reference to the option: the place becomes `#None`, never the value,
  // which others may share.
  const OW = {
    take: (r) => { const old = r.v; r.v = none(); return old; },
  };

  const A = {
    len: (a) => BigInt(a.length),
    push: (a, x) => { a.push(x); },
    pop: (a) => (a.length === 0 ? none() : some(a.pop())),
    insert: (a, i, x) => { a.splice(Number(i), 0, x); },
    remove: (a, i) => { at(a, i); return a.splice(Number(i), 1)[0]; },
    retain: (a, keep) => { let j = 0; for (const x of a) if (keep(x)) a[j++] = x; a.length = j; },
    truncate: (a, n) => { if (a.length > Number(n)) a.length = Number(n); },
    drain: (a) => gen(a.splice(0)),
    iter: (a) => gen(a), iterMut: (a) => gen(a),
    *each(a) { yield* a; },
    get: (a, i) => (Number(i) < a.length ? some(a[Number(i)]) : none()),
    first: (a) => (a.length === 0 ? none() : some(a[0])),
    last: (a) => (a.length === 0 ? none() : some(a[a.length - 1])),
    reverse: (a) => { a.reverse(); },
    sortBy: (a, f) => { a.sort((x, y) => ordinal(f(x, y))); },
    sort: (a) => { a.sort(compare); },
    splitAt: (a, i) => [a.slice(0, Number(i)), a.slice(Number(i))],
    join: (a, sep) => a.map(str).join(sep),
    includes: (a, x) => a.some((y) => eq(y, x)),
    indexOf: (a, x) => { const i = a.findIndex((y) => eq(y, x)); return i < 0 ? none() : some(BigInt(i)); },
  };

  const G = {
    next: (g) => { const n = g[Symbol.iterator]().next(); return n.done ? none() : some(n.value); },
    map: (g, f) => new Gen((function* () { for (const x of g) yield f(x); })()),
    filter: (g, f) => new Gen((function* () { for (const x of g) if (f(x)) yield x; })()),
    take: (g, n) => new Gen((function* () { let i = 0n; if (i >= n) return; for (const x of g) { yield x; if (++i >= n) return; } })()),
    zip: (g, h) => new Gen((function* () { const it = h[Symbol.iterator](); for (const x of g) { const y = it.next(); if (y.done) return; yield [x, y.value]; } })()),
    enumerate: (g) => new Gen((function* () { let i = 0n; for (const x of g) yield [i++, x]; })()),
    collect: (g) => Array.from(g),
    find: (g, f) => { for (const x of g) if (f(x)) return some(x); return none(); },
    findIndex: (g, f) => { let i = 0n; for (const x of g) { if (f(x)) return some(i); i++; } return none(); },
    some: (g, f) => { for (const x of g) if (f(x)) return true; return false; },
    every: (g, f) => { for (const x of g) if (!f(x)) return false; return true; },
    reduce: (g, f, init) => { let acc = init; for (const x of g) acc = f(acc, x); return acc; },
    cloned: (g) => G.map(g, clone),
    join: (g, sep) => Array.from(g, str).join(sep),
    *each(g) { yield* g; },
  };

  const O = {
    isSome: (o) => o.$tag === "Some",
    isNone: (o) => o.$tag === "None",
    unwrap: (o) => (o.$tag === "Some" ? o.$ : panic("unwrap of #None")),
    unwrapOr: (o, d) => (o.$tag === "Some" ? o.$ : d),
    map: (o, f) => (o.$tag === "Some" ? some(f(o.$)) : o),
    cloned: (o) => (o.$tag === "Some" ? some(clone(o.$)) : o),
  };
  const R = {
    isOk: (r) => r.$tag === "Ok",
    isErr: (r) => r.$tag === "Err",
    unwrap: (r) => (r.$tag === "Ok" ? r.$ : panic(`unwrap of ${show(r)}`)),
  };

  const HM = {
    insert: (m, k, v) => m.insert(k, v), get: (m, k) => m.get(k), getMut: (m, k) => m.get(k),
    has: (m, k) => m.has(k), remove: (m, k) => m.remove(k), len: (m) => m.len(),
    keys: (m) => new Gen(m.keys()), values: (m) => new Gen(m.values()), valuesMut: (m) => new Gen(m.values()),
    entries: (m) => new Gen(m.entries()), clone: (m) => m.clone(),
    sortedByValue: (m) => Array.from(m.entries()).sort((a, b) => compare(b[1], a[1]) || compare(a[0], b[0])),
  };
  const HS = {
    insert: (s, v) => s.insert(v), has: (s, v) => s.has(v), remove: (s, v) => s.remove(v),
    len: (s) => s.len(), iter: (s) => new Gen(s.values()), clone: (s) => s.clone(),
  };
  const CELL = { get: (c) => c.v, set: (c, v) => { c.v = v; }, clone: (c) => c };
  const FILE = {
    readText: (f) => f.text,
    *lines(f) { yield* S.lines(f.text); },
  };

  // What any value has: the derived interfaces, and `Box`'s and `Ref`'s identity.
  const ANY = {
    clone, eq, show: (v, out) => { out.v = out.v + show(v); },
    cmp: (a, b) => ordering(compare(a, b)),
    min: (a, b) => (compare(b, a) < 0 ? b : a),
    max: (a, b) => (compare(b, a) > 0 ? b : a),
    get: (v) => v, into: (v) => v,
    iter: (v) => new Gen(iter(v)[Symbol.iterator]()),
    hash: (v, h) => HASHER.writeStr(h.v, show(v)),
  };

  function builtinTable(v) {
    switch (typeof v) {
      case "string": return S;
      case "object":
        if (v === null) return undefined;
        if (Array.isArray(v)) return A;
        if (v instanceof Gen || isIterator(v)) return G;
        if (v instanceof HashMap) return HM;
        if (v instanceof HashSet) return HS;
        if (v instanceof File) return FILE;
        if (v instanceof Cell) return CELL;
        if (v instanceof Bytes) return BYTES;
        if (v instanceof Hasher) return HASHER;
        if (v.$tag === "Some" || v.$tag === "None") return O;
        if (v.$tag === "Ok" || v.$tag === "Err") return R;
    }
    return undefined;
  }

  function find(v, name) {
    for (const t of userTypes(v)) {
      const f = userMethod(t, name);
      if (f !== undefined) return f;
    }
    const table = builtinTable(v);
    if (table !== undefined && Object.prototype.hasOwnProperty.call(table, name)) return table[name];
    // A field holding a function: `(self.f)(x)` reads as a method call once parsed.
    if (v !== null && typeof v === "object" && typeof v[name] === "function" && !(v instanceof HashMap) && !(v instanceof HashSet)) {
      return (self, ...args) => self[name](...args);
    }
    if (Object.prototype.hasOwnProperty.call(ANY, name)) return ANY[name];
    return undefined;
  }

  function call(v, name, ...args) {
    // A closure's parameter lent `mut` without a written type arrives as a reference.
    if (v instanceof Ref) return callRef(v, name, ...args);
    const f = find(v, name);
    if (f === undefined) panic(`no method \`${name}\` on ${show(v)}`);
    return f(v, ...args);
  }

  // A method call on a place, which a method of a string replaces.
  function callRef(r, name, ...args) {
    const v = r.v;
    if (typeof v === "string" && Object.prototype.hasOwnProperty.call(SW, name)) return SW[name](r, ...args);
    if (v !== null && typeof v === "object" && (v.$tag === "Some" || v.$tag === "None") && Object.prototype.hasOwnProperty.call(OW, name)) return OW[name](r, ...args);
    return call(v, name, ...args);
  }

  const STATICS = {
    Vec: { new: () => [], ...A },
    String: { new: () => "", fromUtf8: (bytes) => some(String.fromCharCode(...bytes.map(Number))), ...S },
    str: S,
    HashMap: { new: () => new HashMap(), ...HM },
    HashSet: { new: () => new HashSet(), ...HS },
    Box: { new: (v) => v, get: (v) => v, into: (v) => v },
    Arc: { new: (v) => v, get: (v) => v, clone: (v) => v },
    Option: O,
    Result: R,
    Cell: { new: (v) => new Cell(v), ...CELL },
    RegionList: { new: () => [], ...A },
    Hasher: { new: () => new Hasher(), ...HASHER },
    Fail: {
      capture: (body) => {
        try { return { $tag: "Ok", $: body() }; }
        catch (e) { if (e instanceof Fail) return { $tag: "Err", $: e.value }; throw e; }
      },
      map: (body, wrap) => {
        try { return body(); }
        catch (e) { if (e instanceof Fail) throw new Fail(wrap(e.value)); throw e; }
      },
    },
    File: {
      open: (path) => {
        try { return new File(fs.readFileSync(Buffer.from(path, "latin1").toString("utf8")).toString("latin1")); }
        catch (e) { throw new Fail({ $tag: "NotFound" }); }
      },
      ...FILE,
    },
  };

  // `T.f`: a function of a type.
  function st(type, name) {
    const user = userMethod(type, name);
    if (user !== undefined) return user;
    const table = STATICS[type];
    if (table !== undefined && Object.prototype.hasOwnProperty.call(table, name)) return table[name];
    if (Object.prototype.hasOwnProperty.call(ANY, name)) return ANY[name];
    panic(`no function \`${type}.${name}\``);
  }

  // ---- free functions of the standard library ----

  function println(s) { process.stdout.write(Buffer.from(s + "\n", "latin1")); }
  function writeFile(path, content) {
    fs.writeFileSync(Buffer.from(path, "latin1").toString("utf8"), Buffer.from(content, "latin1"));
  }
  const min = (a, b) => (compare(b, a) < 0 ? b : a);
  const max = (a, b) => (compare(b, a) > 0 ? b : a);
  function replace(r, v) { const old = r.v; r.v = v; return old; }
  function swap(a, b) { const t = a.v; a.v = b.v; b.v = t; }
  const alloc = (v) => v;
  const allocAll = (vs) => vs.slice();
  const fmt = (s) => s;
  const copyUtf8 = (s) => s;
  function parseInt(s) { return /^[+-]?\d+$/.test(s) ? some(BigInt(s)) : none(); }
  function parseFloat(s) { const f = Number(s); return s.trim() !== "" && !Number.isNaN(f) ? some(f) : none(); }
  function writeQuoted(s, out) { out.v = out.v + quoted(s); }
  // `producer` is compiled as a generator function, since it yields.
  const generate = (producer) => new Gen(producer());

  // Runs a program's `main` with the command line, as `flyc run` does.
  function start(main) {
    const args = process.argv.slice(2).map((a) => {
      const s = Buffer.from(a, "utf8").toString("latin1");
      return /^-?\d+$/.test(s) ? BigInt(s) : s;
    });
    try {
      const r = main(...args);
      if (isIterator(r)) for (const _ of r);
    } catch (e) {
      if (e instanceof Panic) { process.stderr.write(`panic: ${e.message}\n`); process.exit(101); }
      if (e instanceof Fail) { process.stderr.write(`uncaught: ${show(e.value)}\n`); process.exit(1); }
      throw e;
    }
  }

  return {
    Fail, Panic, Ref, ref, method, fallback, implement, enumTags, struct, iter, range,
    eq, cmpOp, clone, copy, show, str, idx, at, slice, cast, unmatched, call, callRef, st,
    println, writeFile, min, max, panic, replace, swap, alloc, allocAll, fmt, copyUtf8,
    parseInt, parseFloat, writeQuoted, generate, start,
  };
})();
