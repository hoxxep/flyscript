# One data model for every format: `std/codec` — a design

A proposal, for review, for Fly's counterpart of Rust's serde: one way for a type to say what it is on the wire, which every format reads. It builds on the attributes design (`2026-10-25-attributes-design.md`), which gives it `@wire(…)` and the reflection that reads it. It starts from how `std/json` works today, weighs per-format derivations against a shared data model, and takes what serde and deser each got right. It then proposes `std/codec`, shows JSON, TOML and CBOR on it, and works through protobuf, the hardest format to fit. Nothing here is implemented, and `docs/spec.md` is not changed. A `§` number refers to the specification, and a "section" to this document.

Examples use today's imports. Wherever a feature already exists, the code parses today once its attributes are removed. Everything in `std/codec` is a sketch.

## The design in brief

1. **One data model.** A type is encoded through `Encode` and decoded through `Decode`, each derived once over reflection. A format implements `Encoder` and `Decoder`. A third party's type works with a third party's format, and both depend only on `std/codec`.
2. **Formats are told everything at compile time.** Each field and tag reaches the format as a compile-time *key*: its name on the wire, its index, and its declaration, attributes included. JSON escapes a key once, in the compiler, and matches keys without allocating. Protobuf reads a field's number from `@proto(number = 3)` on the same declaration.
3. **The type pulls.** The derivation knows the type's shape, so decoding asks for what it expects, as `JsonParser` does now, and needs no visitor traits. `kind()` serves the self-describing cases: untagged enums, a dynamic `Value`, and transcoding.
4. **`@wire(…)`** covers serde's attributes: `rename`, `renameAll`, `alias`, `skip`, `default`, `flatten`, `omitNone`, `omitDefault`, `via`, `tag`/`content`/`untagged`, `other` and `denyUnknown`. JSON's output for a type without it is unchanged.
5. **Binary and readable formats each get their natural form.** Bytes, `Timestamp`, `Duration` and `Uuid` are values of the data model. CBOR writes them as byte strings and tags 1, 1002 and 37, and JSON as base64, RFC 3339, `"1.5s"` and hyphenated hex. `@wire(via = Hex)` changes only the readable form. A type with two forms of its own says `@wire(text, bytes)`.
6. **From deser:** flattening and internal tags need no buffering, because every key is known at compile time. Untagged enums rewind the input rather than copying it. Errors say where they happened. Duplicate keys and nesting deeper than a limit are errors by default. Encodings compose through adapters.

---

## 1. How JSON works today

`std/json` is a JSON codec written in Flyscript, and the compiler knows nothing about it (spec §7.5, std.md §16).

**Two interfaces.** `ToJson.toJson(self: readonly Self, out: mut String)` writes a value. `FromJson.fromJson(p: mut JsonParser): Self uses Fail<JsonError>` reads one. They are separate because a value that borrows, such as `{ status: "ok", user: req.user }`, can be encoded without being decodable, and `FromJson extends Send` means that what is decoded owns everything in it. `stringify(v)` and `parse<T>(text)` are the front doors.

**Impls written by hand** cover `String`, `Vec<T>` and `Option<T>`. An `Option` is its value or `null`. Every other type gets one **derivation** per interface, `impl<comptime T: Type> ToJson for T`. It is specialized for each type it is used at, and it branches with `comptime match (Type.info(T))`:

- numbers and booleans are written with `${self}`, and `str` by `writeString`, which copies runs between escapes whole, finding them sixteen bytes at a time with `Simd`;
- a struct or record is an object. A `comptime for` over its fields writes `writeString(f.name)`, `:`, and `self.[f.name].toJson(out)`, so the loop is unrolled into straight-line code for that type;
- tuples, arrays and slices are arrays;
- a tag without a payload is `"Name"`, and a tag with one is `{ "Name": payload }`. The `match` arms are generated, one per tag.

**Decoding** is the same shape. For a struct, the derivation builds a record type of `Option` slots, one per field (`{ comptime for (const f of fields) { [f.name]: Option<f.type>; } }`). It loops over the object's keys, matching each `key.asStr()` against arms generated from the field names, so unknown keys are skipped and keys may come in any order. It then builds the value, and a missing key is `#MissingField` unless the field is an `Option`. That last test is `isOption`, a `comptime function`. Integers of every width share one arm, which checks the range against bounds computed at compile time. A key that appears twice silently overwrites the first.

**A type asks for the derivation** with an empty impl in its own module, `impl FromJson for Signup;` (§7.3). Records, tuples and tag unions belong to no module, so they get it automatically. That is why `stringify(#Created { id: nextId, name: s.name })` in `examples/derive_json.fly` (spec A.9) needs no declaration. A derivation a struct asked for may read and build the struct's private fields.

**`JsonParser`** is a `view struct` over the text, a cursor with a pull API: `peek`, `bool`, `int`, `uint`, `float`, `string`, `beginObject`/`nextKey`/`key`, `beginArray`/`nextItem`, `skip` and `finish`. A hand-written `fromJson` reads through it, and so does the derivation. `JsonError` is `#BadJson(at) | #MissingField(name) | #UnknownTag(name) | #OutOfRange(at)`.

**`tests/run/json.fly` is a different thing.** It tests `examples/json.fly` (spec A.1), a dynamic JSON tree, `Json`, parsed into a region and matched by hand. That is the "value" approach, with no derivation at all.

## 2. What it lacks

- **The wire format is the declaration.** A Flyscript field is `userName` and an API's key is `user_name`, and nothing can say so. Nor can a field be skipped, defaulted or flattened, a `#None` be left out instead of written as `null`, an unknown key be refused, or an enum be tagged in any way but `{ "Name": payload }`.
- **Each format derives itself.** A TOML or CBOR package would write its own `impl<comptime T: Type> ToToml for T`, repeating the walk over `Type.info`, and would have to re-implement every attribute above to match JSON.
- **Each type asks for each format**, `impl ToJson for User; impl ToToml for User; …`.
- **A hand-written encoding is written once per format.** A `Uuid` that is a string in every format needs an impl for each.
- **The orphan rule makes that impossible across packages.** An impl lives with its interface or with its type. A `uuid` package cannot implement a `cbor` package's interface without depending on it, and `cbor` cannot implement it for `Uuid` without depending on `uuid`. This is the problem serde's data model exists to solve.
- **Keys cost at run time** even though they are known when the program is compiled. The encoder escapes each field name with `writeString` on every value it writes. The decoder makes a `String` of every key it reads (`p.key()`) before matching it.
- **Untrusted input is trusted.** Nesting has no limit, so a deep enough document exhausts the stack, which ends the task with a panic (§5.7). A duplicate key quietly wins, and an error names a field but not where it was.

## 3. Two designs

**Per-format derivations**, today's approach: each format has its own `ToX`/`FromX` and its own derivation over `Type.info`.

**One data model**, serde's approach: the type side implements `Encode`/`Decode` once, against an `Encoder`/`Decoder` interface. Each format implements that interface once.

| | Per-format derivations | One data model |
| :--- | :--- | :--- |
| **Work, for M types and N formats** | M·N comptime specializations: each format's derivation runs once for each type. | M per direction: the derivation runs once for each type, and is then an ordinary generic over the encoder, monomorphized per format without running `comptime` again. |
| **Code size** | One straight-line encoder per (type, format). | The same after monomorphization. Every call through `C extends Encoder` is static and inlined, so the machine code matches what a hand-written per-format encoder would be. |
| **Attributes** | Each format interprets `rename`, `flatten` and tagging itself, and may disagree with the others. | `@wire` is interpreted once, in the derivation. A format reads only its own attributes, such as `@proto`, from the keys it is given. |
| **Hand-written impls** | One per (type, format). | One per type: `impl Encode for Uuid` serves every format. |
| **Across packages** | Impossible for a third party's type and a third party's format. | Both depend only on `std/codec`. |
| **What a format can see** | The type itself. | The type too: each key carries its field's declaration, and `beginStruct<T>` names the type. A format that needs more structure than the calls give, such as TOML putting tables after scalars, builds a tree inside its encoder. |
| **Effects** | Each format declares its own. | Each `Encoder` declares its own, as a row (`Encoder<[Io]>`). `Encode.encode` carries that row through, so encoding to a `String` stays pure. |
| **Ownership** | `readonly Self` in, owned out. | The same, and a decoder lends what it reads (`string(): str from self`), so a key is matched where it lies and a value is copied only into the field that keeps it. |

Two features of Flyscript change the usual trade-off.

**Reflection replaces visitors.** serde's `Deserialize` is a visitor. The format drives decoding and calls `visit_map`, `visit_str` and so on, and a proc macro generates the visitor, a `__Field` enum for the keys and a visitor for that enum too. Rust needs this because a derive macro sees only tokens. In Fly, the derivation sees the type's whole shape at compile time, so the type can drive: it asks for a struct, receives keys as indexes into keys it already knows, and decodes each field by its type. Decoding is a *pull* API, the same one `JsonParser` has today, and no visitor trait is needed. Where a format must say what comes next, which is for untagged enums, `Value` and transcoding, a single method, `kind()`, does it (section 8).

**Keys are compile-time constants.** serde passes field names to the format as `&'static str`, and `serde_json` escapes them again for every value. Here a key is a `comptime` parameter of the encoder's method, so a format may do its work on the key in the compiler. JSON pushes the literal `"user_name":`, escaped once. On the decoding side, the decoder is handed the list of keys at compile time and returns an index, so JSON can compare the key's bytes in place against constants with no `String` at all. A key also carries its field's declaration, as deser's descriptors do, but at compile time and at no cost.

**Effects as the data model** were considered and rejected. An `Encode` could perform `Emit` operations that a format's handler interprets, and that would be very Flyscript. But a handler is reached dynamically, at the cost of a call per scalar that a monomorphized interface does not pay, and an encoder has nothing to suspend. Interfaces, monomorphized, are the zero-cost form. Effects remain the right tool at the edges: an encoder that writes to a file has `Io` in its row, and a decoder over JSON Lines can be a generator, `uses Yield<T>`.

**Recommendation: one data model**, `std/codec`, with the type side generated by `comptime` over reflection and attributes, and the format side made of interfaces whose keys are compile-time constants. It keeps today's speed and today's output, and adds attributes and third-party formats.

## 4. What serde and deser teach

serde is the model for the data model and for the attribute vocabulary. deser (Armin Ronacher's experimental successor, after miniserde) is a list of what serde's stability keeps it from fixing. Here is each of deser's points and where this design stands on it:

| deser's point | serde | Here |
| :--- | :--- | :--- |
| **Buffering keeps what it buffers** (positions, exact numbers, numeric keys). | Internally tagged and untagged enums buffer into `Content`, losing positions and `u128`. | Mostly no buffering at all. Internal tags share slots across tags, because every key is known at compile time (section 6). Untagged enums *rewind the input*, a byte offset for JSON and CBOR, and re-read it with full fidelity. A decoder that cannot rewind, such as one over a socket, is wrapped in `Recorded<D>`, which records `D`'s events with `D`'s positions and replays them, as deser does. |
| **Flattening is native**, without buffering, even with `deny_unknown_fields`. | Flattening forces a map and buffering, and conflicts with `deny_unknown_fields`. | Native: a flattened field's keys join its parent's at compile time, and `denyUnknown` knows the whole set. |
| **No stack overflows.** | Recursive; `serde_json` stops at depth 128. | Recursive, because comptime-generated straight-line code is what makes the derivation fast, and deser's arena of sinks would give that up. A decoder has a depth limit, 128 unless set, and fails cleanly past it. A stack that runs out anyway panics its task alone (§5.7), so a server survives. |
| **Enums are more capable**: a catch-all, a default when the tag is missing, tags that are not strings. | Limited (`#[serde(other)]` on a unit variant only). | `@wire(other)` on a tag that keeps what was not recognized, and `@wire(default)` on the tag to use when the key is missing (section 6). Integer and boolean tag values are an open question. |
| **Customizations compose** (`as = Option<Vec<DisplayFromStr>>`). | `serde_with`, outside serde. | `@wire(via = A)`, where `A` is an adapter type, and adapters take adapters: `Maybe<Each<Base64>>` (section 6). |
| **Attributes are code, not strings.** | `default = "path::to::fn"`, as a string. | Attributes are typed compile-time values (attributes design, section 4). |
| **Ready for async**: a deserialization in progress is `Send` and can be fed input as it arrives. | No. | Free: there is no `async`. A decoder over a socket performs `Io`, and the task waits inside its read, compiled to a state machine like any other task (§11.3). |
| **Errors point at the problem**, with a path, and separate malformed input from input that does not fit. | Line and column only, and lost inside buffered values. | The decoder sees every key and index it passes, so it keeps the path. JSON's `#MissingField` names `users[3].email`, not `email`, and its `#BadJson` keeps its byte offset. Malformed input (`#BadJson`) and input that does not fit (`#MissingField`, `#UnknownTag`, `#OutOfRange`) are already separate tags. |
| **Layers** between format and types. | No. | A decoder wrapping a decoder, `impl<row E, D extends Decoder<E>> Decoder<E> for Strict<D>`, monomorphized away. Nothing new is needed. |
| **Safe defaults for untrusted input**: duplicate keys are errors, and limits are set once. | Duplicates are last-wins, with no limits. | Duplicates are errors by default (`d.again(key)`, section 5), and depth, string and collection limits are set on the decoder. That changes today's last-wins JSON. |
| **Only self-describing formats.** | Both. | Both. The type pulls, so postcard-like formats work. Only what needs `kind()` (`Value`, `untagged`, `other`) needs a self-describing one. |

What deser gives up and this design keeps: static dispatch. deser and miniserde dispatch dynamically for compile time. Here the comptime work is already once per type per direction, and monomorphization over the format is cheap, so the remaining cost is code size, which open question 2 takes up.

## 5. `std/codec`

A sketch of the whole interface:

```ts
// std/codec.fly, sketch. What a type is on the wire, in any format.

// A value, written.
export interface Encode {
  function encode<row E, C extends Encoder<E>>(self: readonly Self, out: mut C): void uses ...E;
}

// A value, read; it owns all it holds.
export interface Decode extends Send {
  function decode<row E, D extends Decoder<E>>(d: mut D): Self uses ...E;
}

// What a format is told of a field: its key on the wire, its place among its type's keys, and
// its declaration, attributes and all. Every part is known at compile time.
export type Key = { name: str; index: usize; field: Field };
// And of a tag: its name on the wire, its index among its type's tags, and its declaration.
export type TagKey = { name: str; index: usize; tag: TagInfo };

// A format's writer. `E` is what it performs: `[]` for one into a `String`, `[Io]` for one into
// a file, with its own failures, such as a TOML writer's for a value TOML cannot hold.
export interface Encoder<row E = []> {
  function bool(self: mut Self, v: bool): void uses ...E;
  function int(self: mut Self, v: i64): void uses ...E;
  function uint(self: mut Self, v: u64): void uses ...E;
  function float(self: mut Self, v: f64): void uses ...E;
  function string(self: mut Self, v: str): void uses ...E;
  function bytes(self: mut Self, v: readonly u8[]): void uses ...E;
  function none(self: mut Self): void uses ...E;
  // Whether `none` can be written where a field is; TOML has no null, so a `#None` field is left out.
  function writesNull(self: readonly Self): bool;
  // Whether the format is for people to read: JSON, TOML and YAML are; CBOR, MessagePack and
  // protobuf are not (section 7).
  function readable(self: readonly Self): bool;

  // Values most formats hold natively (section 7), and the others as `Fallback` writes them.
  function timestamp(self: mut Self, t: Timestamp): void uses ...E;
  function duration(self: mut Self, d: Duration): void uses ...E;
  function uuid(self: mut Self, id: readonly u8[16]): void uses ...E;
  // Bytes written as they come: `len` if it is known, then each chunk.
  function beginBytes(self: mut Self, len: Option<usize>): void uses ...E;
  function chunk(self: mut Self, b: readonly u8[]): void uses ...E;
  function endBytes(self: mut Self): void uses ...E;

  // A list of `len` items, each after `item()`.
  function beginSeq(self: mut Self, len: usize): void uses ...E;
  function item(self: mut Self): void uses ...E;
  function endSeq(self: mut Self): void uses ...E;

  // A map of `len` entries, each after `entry()`: a key's value, then the value's.
  function beginMap(self: mut Self, len: usize): void uses ...E;
  function entry(self: mut Self): void uses ...E;
  function endMap(self: mut Self): void uses ...E;

  // A struct or record of `T`'s, `len` fields of it written, each after `field(key)`.
  function beginStruct<comptime T: Type>(self: mut Self, len: usize): void uses ...E;
  function field(self: mut Self, comptime key: Key): void uses ...E;
  function endStruct(self: mut Self): void uses ...E;

  // A tag of `T`'s; one with a payload is followed by it, then `endVariant()`.
  function unitVariant<comptime T: Type>(self: mut Self, comptime tag: TagKey): void uses ...E;
  function beginVariant<comptime T: Type>(self: mut Self, comptime tag: TagKey): void uses ...E;
  function endVariant(self: mut Self): void uses ...E;
}

export type Next = #Field(usize) | #Unknown | #End;
export type Kind = #Null | #Bool | #Int | #Float | #Str | #Bytes | #Seq | #Map | #Timestamp | #Uuid;

// A format's reader, pulled by the type being read.
export interface Decoder<row E = []> {
  type Mark extends Copy;

  function bool(self: mut Self): bool uses ...E;
  function int(self: mut Self): i64 uses ...E;
  function uint(self: mut Self): u64 uses ...E;
  function float(self: mut Self): f64 uses ...E;
  // Lent: the text itself where it needs no unescaping, or the decoder's buffer.
  function string(self: mut Self): str from self uses ...E;
  function bytes(self: mut Self): readonly u8[] from self uses ...E;
  // Consumes a null if one is next.
  function isNone(self: mut Self): bool uses ...E;
  function readable(self: readonly Self): bool;
  // Each reads the native form, or the fallback's: an RFC 3339 string in JSON, say.
  function timestamp(self: mut Self): Timestamp uses ...E;
  function duration(self: mut Self): Duration uses ...E;
  function uuid(self: mut Self): u8[16] uses ...E;
  function beginBytes(self: mut Self): void uses ...E;
  function nextChunk(self: mut Self): Option<readonly u8[]> from self uses ...E;
  // What comes next; a format that cannot say fails.
  function kind(self: mut Self): Kind uses ...E;
  function skip(self: mut Self): void uses ...E;

  function beginSeq(self: mut Self): void uses ...E;
  function nextItem(self: mut Self): bool uses ...E;
  function beginMap(self: mut Self): void uses ...E;
  function nextEntry(self: mut Self): bool uses ...E;
  // The next field of `T`'s, as its index among `keys`.
  function beginStruct<comptime T: Type>(self: mut Self, comptime keys: Key[]): void uses ...E;
  function nextField(self: mut Self, comptime keys: Key[]): Next uses ...E;
  // A key read a second time: the format fails, keeps the last, or, for a list, adds to it.
  function again(self: mut Self, comptime key: Key): #Last | #Append uses ...E;
  // A tag of `T`'s, as its index among `tags`, and whether a payload follows.
  function beginVariant<comptime T: Type>(self: mut Self, comptime tags: TagKey[]): [usize, bool] uses ...E;
  function endVariant(self: mut Self): void uses ...E;

  // What the derivation finds wrong, failed by the format, so the failure says where.
  function missing(self: mut Self, comptime key: Key): never uses ...E;
  function unknownField(self: mut Self): never uses ...E;
  function outOfRange(self: mut Self): never uses ...E;

  // Where the decoder is, and a way back there: for an untagged enum, which tries each tag.
  function mark(self: readonly Self): Self.Mark;
  function rewind(self: mut Self, m: Self.Mark): void uses ...E;
}
```

**The interfaces' rules:**

- **Effects.** An `Encoder<E>` or `Decoder<E>` names its whole row, failures included: JSON's is `[Fail<JsonError>]`, and a CBOR reader over a socket has `[Io, Fail<CborError>]`. `Encode.encode` and `Decode.decode` perform exactly that row and nothing more. A derived `encode` adds no effect of its own, so `stringify` stays pure (law 2).
- **Failures belong to the format.** When a field is missing, the derivation calls `d.missing(key)`, and the format fails with its own error. JSON's is `#MissingField("users[3].email")`, the same tag as now with the path in it. The codec therefore defines no error type, and `JsonError` keeps its tags, adding `#DuplicateKey` and `#TooDeep`.
- **Untrusted input.** A decoder counts its depth at each `begin…` and fails past its limit: 128 unless set, as in `serde_json`. It may also limit a string's length and a list's. `again` is the format's choice: JSON fails with `#DuplicateKey` by default, a lenient JSON keeps the last value, and protobuf adds to a repeated field (section 10).
- **Ownership.** `encode` borrows `readonly`, so a value that borrows can be encoded. `Decode extends Send`, as `FromJson` does. Strings are lent out of the decoder with `from self` and are copied only when a `String` field keeps them. Because a lent `str` is second-class, nothing can hold one past the next call to the decoder.
- **Lengths are given up front.** A definite-length format (CBOR, MessagePack) writes the length first. The derivation knows it at compile time, less the `#None` and default fields it leaves out, which it counts first.
- **Keys are the formats' descriptors.** `key.name` is the name after `@wire` has renamed it. `key.field` is the declaration, so a format reads its own attributes there (`key.field.attrs.get<proto>()`) and its type (`key.field.type`), all at compile time. A format that needs something every field must carry, such as protobuf's numbers, reports a field that lacks it at that field's declaration (`key.field.attrs.fail(…)`).

**Impls written by hand** cover what reflection does not show: `String`, `Vec<T>`, `Option<T>`, `HashMap<K, V>` (a map) and `Box<T>` (its contents), and section 7's values. `Vec<T>`'s impl is a template over `T`, so `Vec<u8>` is bytes and every other `Vec` a list, decided at compile time. Every other type gets the derivation. A type that knows its own encoding writes it once, for every format:

```ts
// In uuid's own package, sketch: a string in JSON, TOML and CBOR alike.
impl Encode for Uuid {
  function encode<row E, C extends Encoder<E>>(self: readonly Self, out: mut C): void uses ...E {
    out.string(self.text().asStr());
  }
}
```

**The derivation** has one arm per kind of type, as JSON's does today. Its struct arm, with the attributes that act there, is a sketch:

```ts
// std/codec.fly, sketch: structs and records.
impl<comptime T: Type> Encode for T {
  function encode<row E, C extends Encoder<E>>(self: readonly Self, out: mut C): void uses ...E {
    comptime match (Type.info(T)) {
      #Record(_) | #Struct { fields: _ } => {
        // How many fields are written: known at compile time, less those left out.
        const len = present(self, out);
        out.beginStruct<T>(len);
        encodeFields(self, mut out);
        out.endStruct();
      }
      // … numbers, strings, tuples, arrays; tags by how the enum is tagged
      _ => comptime panic(`${Type.name(T)} cannot be encoded`),
    }
  }
}

// What a field is on the wire, decided at compile time from its type and its `@wire`.
type Role = #Skip | #Flatten | #Optional(bool) | #Via(Type) | #Plain(bool);

comptime function roleOf(f: Field): Role {
  const w = checked(f);
  if (w.skip) { #Skip }
  else if (w.flatten) { #Flatten }
  else if (const #Some(a) = w.via) { #Via(a) }
  else if (isOption(f.type)) { #Optional(w.omitNone) }
  else { #Plain(w.omitDefault) }
}

// Writes the fields of a struct or record as the keys of the object being written: renamed,
// the skipped left out, a `#None` left out where it is not written as null, and a flattened
// field's own fields in its place.
function encodeFields<comptime T: Type, row E, C extends Encoder<E>>(v: readonly T, out: mut C): void uses ...E {
  comptime for (const f of fieldsOf(T)) {
    comptime match (roleOf(f)) {
      #Skip => {}
      #Flatten => { encodeFields(v.[f.name], mut out); }
      #Via(A) => {
        out.field(comptime keyOf(T, f));
        A.encodeAs(v.[f.name], mut out);
      }
      #Optional(omit) => {
        if (const #Some(x) = v.[f.name]) {
          out.field(comptime keyOf(T, f));
          x.encode(mut out);
        } else if (!omit && out.writesNull()) {
          out.field(comptime keyOf(T, f));
          out.none();
        }
      }
      #Plain(omitDefault) => {
        comptime if (omitDefault) {
          if (v.[f.name] != f.type.default()) {
            out.field(comptime keyOf(T, f));
            v.[f.name].encode(mut out);
          }
        } else {
          out.field(comptime keyOf(T, f));
          v.[f.name].encode(mut out);
        }
      }
    }
  }
}

// A field's key: its `rename`, or its name recased as its type's `renameAll` says, with its
// index and its declaration.
comptime function keyOf(T: Type, f: Field): Key {
  const name = match (checked(f).rename) {
    #Some(k) => k,
    #None => match (wireOf(attrsOf(T)).renameAll) {
      #Some(c) => recase(f.name, c),
      #None => f.name,
    },
  };
  { name, index: indexOf(T, f), field: f }
}
```

Decoding a struct is today's decoder with four changes. Keys are matched by index. A key read twice asks the format. Missing fields consult `@wire`. A flattened field's fields have slots of their own in the same record, and the field's value is built from them:

```ts
// std/codec.fly, sketch: `Decode`'s derivation, at structs and records.
impl<comptime T: Type> Decode for T {
  function decode<row E, D extends Decoder<E>>(d: mut D): T uses ...E {
    comptime match (Type.info(T)) {
      #Record(fields) | #Struct { fields } => {
        let slots: { comptime for (const f of fields) { [f.name]: Option<f.type>; } } =
          { comptime for (const f of fields) { [f.name]: #None, } };
        d.beginStruct<T>(comptime keysOf(T));
        while (true) {
          match (d.nextField(comptime keysOf(T))) {
            // One arm for each key a field is read from: its own, then its aliases.
            comptime for (const k of keysOf(T)) {
              #Field(comptime k.index) => {
                // A format answers `#Append` only for a list.
                if (slots.[k.field.name].isSome() && d.again(comptime k) == #Append) {
                  appendTo(mut slots.[k.field.name], mut d);
                } else {
                  slots.[k.field.name] = #Some(k.field.type.decode(mut d));
                }
              },
            }
            #Unknown => { comptime if (wireOf(attrsOf(T)).denyUnknown) { d.unknownField(); } else { d.skip(); } }
            #End => { break; }
          }
        }
        {
          comptime for (const f of fields) {
            [f.name]: match (slots.[f.name]) {
              #Some(v) => v,
              #None => comptime match (ifMissing(T, f)) {
                #Default => f.type.default(),
                #Absent => #None,
                #Required => d.missing(comptime keyOf(T, f)),
              },
            },
          }
        }
      }
      // … numbers, strings, tuples, arrays; tags by how the enum is tagged
      _ => comptime panic(`${Type.name(T)} cannot be decoded`),
    }
  }
}
```

**Compile time.** The comptime work for a type runs once per direction, whatever the number of formats. `keyOf`, `keysOf` and `roleOf` are evaluated once per field. The interpreter's memo of specializations (§7.1) already makes the struct arm's work proportional to the number of fields.

## 6. `@wire`

`wire` is declared in `std/codec` as the attributes design shows (section 5 there), with the arguments below.

| Argument | On | Encoding | Decoding |
| :--- | :--- | :--- | :--- |
| `rename = "k"` | field, tag | The key or tag name is `k`. | Read from `k`. |
| `renameAll = #SnakeCase` (`#CamelCase`, `#KebabCase`, `#PascalCase`, `#ScreamingSnakeCase`) | struct, enum | Every field's key, or every tag's name, recased at compile time. A field's own `rename` wins. | The same. |
| `alias = ["a", "b"]` | field | — | Also read from `a` and `b`. |
| `skip` | field | Left out. | Not read; its type's `Default`. |
| `default` | field | — | A missing field is its type's `Default`. |
| `default` | struct | — | A missing field is that field of the struct's own `Default`, as in serde (`port: 8080` comes from `impl Default for Config`). |
| `default` | tag | — | With `tag = "…"`, the tag read when the tag key is missing. |
| `flatten` | field of a struct or record type | Its fields are written as the outer object's. | Read from the outer object. No buffering, because every key is known at compile time. |
| `flatten` | field of an enum type | Its tag is written as a key of the outer object, its payload as that key's value. | Whichever of its tags' keys comes. This is protobuf's `oneof` (section 10). |
| `omitNone` | `Option` field, or struct (every `Option` field) | `#None` is left out instead of `null`. | Unchanged: missing or `null` is `#None`. |
| `omitDefault` | field, or struct (every field) | Left out when it equals its type's `Default`, which needs `Eq`. | A missing field is its `Default`. |
| `via = A` | field | Written by the adapter `A` (`A.encodeAs`). | Read by `A.decodeAs`. |
| `denyUnknown` | struct | — | An unknown key fails (`d.unknownField()`) instead of being skipped. |
| `text`, `bytes` | struct, enum | Its `Text` in readable formats and its `Binary` in binary ones; either alone, everywhere (section 7). | The same. |
| (none) | enum | External: `"Name"`, or `{ "Name": payload }`, as now. | The same. |
| `tag = "type"` | enum | Internal: `{ "type": "Name", …payload's fields }`. Each tag's payload must be a struct or record, which is checked at compile time. | The tag is read wherever it falls among the keys. Every tag's fields are known at compile time, so they share one set of slots and the tag is matched at the end. If two tags share a key with different types, the decoder falls back to `mark`/`rewind`. |
| `tag = "t", content = "c"` | enum | Adjacent: `{ "t": "Name", "c": payload }`. | The same. |
| `untagged` | enum | The payload alone. | Each tag in order, from a mark; the first that decodes wins. |
| `other` | tag whose payload is `Value` or a unit tag | — | Any tag not recognized, kept whole as a `Value` (section 8) so that it encodes again as it came. |

`Option` is `null` by default, which is today's behaviour and TypeScript's `T | null`. `omitNone` gives TypeScript's optional property, `x?: T`. Decoding accepts both either way, as `parse` does now. A format without null, such as TOML, leaves a `#None` field out whatever the attribute says (`writesNull()`).

**Adapters** are types that say how to write a type other than its own:

```ts
// std/codec.fly, sketch.
export interface Via<T> {
  function encodeAs<row E, C extends Encoder<E>>(v: readonly T, out: mut C): void uses ...E;
  function decodeAs<row E, D extends Decoder<E>>(d: mut D): T uses ...E;
}

// Bytes as a base64 string; an adapter applied to each item of a list; to what an Option holds.
export struct Base64 {}
export struct Each<A> {}
export struct Maybe<A> {}
impl Via<Vec<u8>> for Base64 { … }
impl<T, A extends Via<T>> Via<Vec<T>> for Each<A> { … }
impl<T, A extends Via<T>> Via<Option<T>> for Maybe<A> { … }

type Base64s = Maybe<Each<Base64>>;
struct Attachments { @wire(via = Base64s) blobs: Option<Vec<Vec<u8>>>; }
```

An attribute's argument is an expression, so a composed adapter is named through an alias, here `Base64s`. A rule that lets a type stand as an argument is an open question.

Structural types get the defaults and nothing else (attributes design, section 2). An API whose tags need names of their own declares an enum:

```ts
// Sketch: what `@wire` looks like at the declaration.
import { wire, Encode, Decode, Value } from "std/codec";

@wire(renameAll = #SnakeCase, denyUnknown)
struct Signup {
  email: String;
  @wire(rename = "name") displayName: String;
  @wire(omitNone) referrer: Option<String>;
  @wire(alias = ["utm"]) campaign: Option<String>;
  @wire(skip) private seen: u64;
}
impl Encode for Signup;
impl Decode for Signup;

@wire(tag = "type", renameAll = #SnakeCase)
enum Shape {
  #Circle { radius: f64 },
  @wire(rename = "rect") #Rectangle { @wire(rename = "w") width: f64; @wire(rename = "h") height: f64 },
  @wire(other) #Unknown(Value),
}
impl Encode for Shape;
impl Decode for Shape;
```

`{"email":"a@b.c","name":"Ada","utm":"x"}` decodes as a `Signup`, with `campaign` as `#Some("x")`, `referrer` as `#None` and `seen` as `0`. `{"email":"a@b.c","name":"Ada","seen":3}` is an error under `denyUnknown`: a skipped field is not read from the wire, so `"seen"` is an unknown key. A `Shape` that is `#Rectangle { width: 2, height: 3 }` encodes as `{"type":"rect","w":2,"h":3}`. A newer peer's `{"type":"hexagon","side":1}` decodes as `#Unknown` and encodes back unchanged.

**What reflection must give** (attributes design, section 10):

1. `attrs` on `Field`, `TagInfo`, `#Struct` and `#Enum`, with `Attrs.get<A>()`, `all<A>()` and `fail(message)`.
2. `TagInfo.fields`: a tag's record payload with its fields' attributes, in declaration order.
3. An attribute found by its declaration, never by its name.
4. Attribute values as comptime constants, `Type`, `str` and lists included, usable at run time as literals.
5. A `comptime function` that returns a `str` it built (`recase`). Comptime strings belong to the compiler, and as literals they last as long as the program.
6. Comptime parameters on interface methods: values (`field(self, comptime key: Key)`) and template type parameters (`beginStruct<comptime T: Type>`), each impl's method specialized per argument as a template is. The grammar has both, but nothing in the standard library uses one on an interface yet.
7. `Default`, a derived prelude interface, for `skip`, `default` and `omitDefault`: zero, `false`, empty, `#None`, and fieldwise for records and structs that ask (`impl Default for Config;`).

## 7. Binary and readable formats

Formats come in two kinds. A **readable** format, such as JSON, TOML or YAML, is text for people. A **binary** format, such as CBOR, MessagePack, protobuf or postcard, is compact bytes for machines. Bytes, instants, durations and UUIDs have a native form in most binary formats, such as a byte string or a CBOR tag. In most readable formats they need a convention, such as base64, RFC 3339 or a hyphenated UUID. A codec that gets this wrong either packs bytes as a list of numbers, as serde does for `Vec<u8>` until `serde_bytes` is added, or makes each type decide its JSON form by hand.

The design has three parts:

1. **The data model has these values in it.** `Encoder` and `Decoder` have `timestamp`, `duration`, `uuid` and chunked `bytes` beside `string` and `int`, and every format implements them. A format with a native form uses it, for example CBOR's tag 37 for a UUID or TOML's own datetime. A format without one calls `std/codec`'s fallback for its kind, which is one line.
2. **The standard types use them.** `Vec<u8>`, `u8[N]` and `Bytes` are bytes, not lists. `std/time`'s `Timestamp` and `Duration`, and `std/uuid`'s `Uuid`, are their own values. A type that holds these gets the right form in every format with no attribute.
3. **A type with its own two forms says so once.** `@wire(text, bytes)` on a type means its text in readable formats and its bytes in binary ones, written by two small interfaces. The type's author writes no encoder.

**The defaults**, chosen where a standard says how, and otherwise as protobuf's JSON mapping does, which is the most widely deployed canonical form:

| Value | CBOR | Other binary formats | JSON | Other readable formats |
| :--- | :--- | :--- | :--- | :--- |
| Bytes: `Vec<u8>`, `u8[N]`, `Bytes` | A byte string (major type 2), copied whole. | MessagePack's `bin`; protobuf's `bytes`. | Base64, standard alphabet, padded (RFC 4648 §4). Decoding also accepts the URL-safe alphabet and no padding. | TOML and YAML: a base64 string. |
| `Timestamp` | Tag 1: an integer of seconds, or a float when there is a fraction (RFC 8949). | MessagePack's timestamp extension (−1), which holds nanoseconds. | RFC 3339 in UTC, `"2026-10-25T17:39:14Z"`, with as many fraction digits as it needs. Decoding accepts any offset. | TOML's offset datetime; YAML's timestamp. |
| `Duration` | Tag 1002, seconds and nanoseconds (RFC 9581). | An integer of nanoseconds. | `"1.5s"`, protobuf's form. | The same string. |
| `Uuid` | Tag 37 on a 16-byte string (RFC 9562). | MessagePack's `bin` of 16. | Lowercase and hyphenated, `"550e8400-e29b-41d4-a716-446655440000"`. Decoding accepts uppercase. | The same string. |
| `Vec<f32>`, `Vec<i64>`, … | A list, as every reader expects. `@wire(via = Packed)` gives a typed array (RFC 8746, tags 64–87): one byte string, no per-item header. | A list. | A list. | A list. |

Two of the defaults are worth a word. CBOR's tag 1 float holds microseconds for present-day instants, and `@wire(via = ExactTime)` writes tag 1001 (RFC 9581) with nanoseconds instead. Typed arrays are left to an attribute because many CBOR readers do not understand them, and a default should be what every reader reads.

**Choosing another form** is an adapter on the field (section 6):

```ts
// Sketch: a webhook whose JSON says hex and epoch milliseconds.
import { wire, Encode, Decode, Hex, UnixMillis } from "std/codec";
import { Timestamp } from "std/time";

struct Webhook {
  @wire(via = Hex) signature: u8[32];
  @wire(via = UnixMillis) sentAt: Timestamp;
  body: Vec<u8>;
}
impl Encode for Webhook;
impl Decode for Webhook;
```

In JSON, `signature` is a hex string, `sentAt` an integer of milliseconds, and `body` base64. In CBOR, all three keep their native forms: `signature` is a byte string, `sentAt` is tag 1, and `body` is a byte string. An adapter that names a readable form (`Hex`, `Base64`, `Base64Url`, `Rfc3339`, `UnixSeconds`, `UnixMillis`) changes only readable formats, so choosing how JSON looks never makes CBOR larger. CBOR even records the choice: it tags `signature` with 23, "expected conversion to base16", so a CBOR-to-JSON converter writes hex as the author asked. `Always<A>` applies `A` in every format, for a peer that wants epoch milliseconds in CBOR too.

A format may change its own default once, for every field without an adapter: `JsonWriter.with({ bytes: #Hex })`. The order is field adapter, then the format's setting, then the default.

**A type with two forms**, such as an IP address, a colour or a hash, implements the two interfaces and asks for both:

```ts
// Sketch, in the type's own module.
import { wire, Encode, Decode, Text, Binary } from "std/codec";

@wire(text, bytes)
struct Ipv4 { octets: u8[4]; }

impl Text for Ipv4 {
  function writeText(self: readonly Self, out: mut String): void { … }
  function parseText(s: str): Option<Ipv4> { … }
}
impl Binary for Ipv4 {
  function writeBytes(self: readonly Self, out: mut Vec<u8>): void { … }
  function parseBytes(b: readonly u8[]): Option<Ipv4> { … }
}
impl Encode for Ipv4;
impl Decode for Ipv4;
```

JSON gets `"10.0.0.1"` and CBOR four bytes. `@wire(text)` alone is the text everywhere and `@wire(bytes)` alone is the bytes everywhere, base64 in JSON. A type with neither is encoded by its fields, as any struct is. A parse that answers `#None` is the format's failure at that place, as `#BadJson` is now.

**What a format implements** is one method for each of these values, and `std/codec` gives the fallback for a format without a native form. A readable fallback writes the string above, and a binary fallback writes the bytes. So a format with nothing native writes, for instance, `function uuid(self: mut Self, id: readonly u8[16]): void { Fallback.uuid(id, mut self) }`. Interfaces have no default methods, which would make even that line unnecessary (open question 9). `readable()` tells a hand-written `Encode` which kind it is writing, for any type the above does not cover. It is constant in each format, so the branch is compiled away.

**Byte streams.** A payload too large to hold, such as a file or a generator's chunks, is written as it comes: `beginBytes(len)`, `chunk(b)` for each piece, and `endBytes()`. CBOR writes an indefinite-length byte string, or a definite one when `len` is known. JSON writes base64 as the chunks arrive, carrying the one or two bytes left over between them. Decoding mirrors it: `beginBytes()`, then `nextChunk()` until `#None`, each chunk lent from the decoder's buffer.

## 8. Self-describing formats and `Value`

A self-describing format says what comes next: JSON, CBOR, MessagePack, TOML and YAML do, and postcard and bincode do not. Protobuf says only how to skip a field (section 10). `kind()` is where a decoder says it. Most decoding never calls it, because the type already knows what it expects. Three things do call it:

- **`Value`**, any value a self-describing format can hold, decoded from whatever comes:

  ```ts
  // std/codec.fly, sketch.
  export enum Value {
    #Null, #Bool(bool), #Int(i64), #Float(f64), #Str(String), #Bytes(Vec<u8>),
    #Timestamp(Timestamp), #Uuid(u8[16]), #Seq(Vec<Value>), #Map(Vec<[Value, Value]>),
  }

  impl Decode for Value {
    function decode<row E, D extends Decoder<E>>(d: mut D): Value uses ...E {
      match (d.kind()) {
        #Null => { d.isNone(); #Null }
        #Bool => #Bool(d.bool()),
        #Int => #Int(d.int()),
        #Float => #Float(d.float()),
        #Str => #Str(d.string().toString()),
        #Timestamp => #Timestamp(d.timestamp()),
        #Uuid => #Uuid(d.uuid()),
        #Bytes | #Seq | #Map => decodeCompound(mut d),
      }
    }
  }
  ```

  It is what `@wire(other)` keeps, what a field of no fixed shape is declared as (`extra: Value`), and what a `HashMap<String, Value>` flattened into a struct gathers: every key the struct does not name. Today's region-allocated `Json` tree (spec A.1) can be one more such type, written by hand, for programs that want the tree in a region.
- **Untagged enums and `other`**, which try a tag, rewind, and try the next.
- **Transcoding** without an intermediate tree: `transcode(d, out)` reads one value from any self-describing decoder and writes it to any encoder, with `kind()` choosing each call. JSON becomes CBOR in one pass, with no `Value` built. A CBOR timestamp or UUID becomes JSON's string for it. Going the other way, a JSON string stays a string, because JSON cannot say it was a timestamp:

  ```ts
  // std/codec.fly, sketch.
  export function transcode<row A, row B, D extends Decoder<A>, C extends Encoder<B>>(d: mut D, out: mut C): void uses ...A, ...B { … }
  ```

A format that cannot say fails in `kind()`, so `Value` from postcard is a decoding failure with a clear message. Everything that does not call `kind()`, which is every struct, list and externally tagged enum, works in either kind of format.

## 9. A format of one's own

A format package depends on `std/codec` alone, and every type that asks for `Encode`/`Decode` works with it, including types from packages it has never seen.

**JSON**, as `std/json` would be:

```ts
// std/json.fly, sketch: the writer.
export struct JsonWriter { out: String; first: bool; }

impl Encoder for JsonWriter {
  function beginStruct<comptime T: Type>(self: mut Self, len: usize): void {
    self.out.push("{");
    self.first = true;
  }
  function field(self: mut Self, comptime key: Key): void {
    if (!self.first) { self.out.push(","); }
    self.first = false;
    // `"user_name":`, escaped once, by the compiler.
    self.out.push(comptime quoted(key.name));
  }
  function endStruct(self: mut Self): void {
    self.out.push("}");
    self.first = false;
  }
  function writesNull(self: readonly Self): bool { true }
  …
}

export function stringify<T extends Encode>(v: readonly T): String {
  let w = JsonWriter { out: String.new(), first: true };
  v.encode(mut w);
  w.out
}
```

```ts
// std/json.fly, sketch: the reader matches a key where it lies in the text.
impl Decoder<[Fail<JsonError>]> for JsonParser {
  function nextField(self: mut Self, comptime keys: Key[]): Next uses Fail<JsonError> {
    if (!self.nextKey()) { return #End; }
    const k = self.rawKey();
    comptime for (const key of keys) {
      if (k == key.name) { return #Field(key.index); }
    }
    #Unknown
  }
  function again(self: mut Self, comptime key: Key): #Last | #Append uses Fail<JsonError> {
    throw #DuplicateKey(self.path(key.name))
  }
  function missing(self: mut Self, comptime key: Key): never uses Fail<JsonError> {
    throw #MissingField(self.path(key.name))
  }
  …
}
```

`rawKey` lends the key's bytes from the text when the key has no escapes, and decodes it into the parser's buffer otherwise. Either way it allocates no `String`. `parse<T extends Decode>(text)`, `stringify<T extends Encode>(v)` and `JsonError`'s tags keep their names, and `JsonParser` keeps its methods, so a hand-written reader still works. `ToJson`/`FromJson` become `Encode`/`Decode`: `impl FromJson for Signup;` becomes `impl Decode for Signup;`. The output for every type without `@wire` is byte for byte what it is now. Decoding changes in two ways: a duplicate key fails instead of winning, and a missing field's name is its path. So spec A.9 and `examples/derive_json.fly` change only their imports.

**TOML** is the hard case, and it shows where a format does the work the data model leaves to it. A TOML document is a table, and its nested tables come after its scalar keys, as `[a.b]` sections. The writer therefore builds a tree and prints it at the end:

```ts
// toml/encode.fly, in a package of its own, sketch.
import { Encoder, Encode, Key } from "std/codec";

export type TomlError = #NotATable | #NullInArray | #MixedArray;

export struct TomlWriter { stack: Vec<Value>; keys: Vec<String>; }

impl Encoder<[Fail<TomlError>]> for TomlWriter {
  function field(self: mut Self, comptime key: Key): void uses Fail<TomlError> {
    self.keys.push(key.name.toString());
  }
  function none(self: mut Self): void uses Fail<TomlError> { throw #NullInArray }
  function writesNull(self: readonly Self): bool { false }
  …
}

export function toToml<T extends Encode>(v: readonly T): String uses Fail<TomlError> {
  let w = TomlWriter { stack: Vec.new(), keys: Vec.new() };
  v.encode(mut w);
  w.finish()
}
```

`writesNull` is `false`, so the derivation leaves `#None` fields out, and `none()` is reached only for a `#None` inside a list, which TOML cannot hold. A top-level value that is not a struct fails with `#NotATable`. The TOML package declares no attribute of its own, and `renameAll = #KebabCase` on a config struct is the same `@wire` that JSON obeys.

**CBOR** is the easy case: a binary format, self-describing, with definite lengths. `beginStruct<T>(len)` writes major type 5 with `len`, and `field(key)` writes the key's text string, which the compiler can encode in full (`comptime cborText(key.name)` is its header byte and bytes). `bytes()` is major type 2, and `kind()` reads the next item's major type. `Mark` is an offset into the input, as it is for JSON. A CBOR package that wants COSE's integer keys reads `@cbor(key = 3)` from `key.field`, with no change to the data model.

## 10. Protobuf

Protobuf is the hardest format to fit, because its meaning is in the schema, not on the wire. Fields are numbers, an `i32` may be `int32`, `sint32` or `sfixed32`, lists are packed, and a field may arrive twice. prost and the other Rust implementations do not use serde for this reason. Here it fits, given what the earlier sections already have: keys that carry their declarations, `again`, enum flattening, and `omitDefault`.

A message is a struct whose fields carry a protobuf attribute of the protobuf package's own:

```ts
// Sketch: what a .proto's message is, written as Flyscript.
import { wire, Encode, Decode } from "std/codec";
import { proto } from "protobuf/attrs";

@wire(default, omitDefault)
struct Order {
  @proto(number = 1) id: u64;
  @proto(number = 2, encoding = #ZigZag) delta: i32;
  @proto(number = 3) lines: Vec<Line>;
  @proto(number = 4) note: Option<String>;
  @wire(flatten) payment: Payment;
}

// A oneof: its tags are fields of the message that holds it.
enum Payment {
  @proto(number = 5) #Card(String),
  @proto(number = 6) #Iban(String),
}
```

How each part of protobuf maps:

| Protobuf | Flyscript | How |
| :--- | :--- | :--- |
| Field numbers | `@proto(number = n)` | `field(key)` writes the tag, `n << 3` with the wire type, computed at compile time from `key.field`. A field without a number is an error at its declaration. |
| `int32`/`sint32`/`sfixed32` | `@proto(encoding = #ZigZag \| #Fixed)` | `field` notes how the next integer is written, which inlining makes a constant. |
| proto3 implicit presence | `@wire(default, omitDefault)` | A zero is not written, and a missing field is its zero. |
| `optional` | `Option<T>` | Present or not, as written. |
| `repeated` | `Vec<T>` | Packed for scalars. An unpacked list's elements arrive as the same key again, and `again` answers `#Append`. A scalar sent twice keeps the last, and a message sent twice merges, as protobuf says. |
| `map<K, V>` | `HashMap<K, V>` | Repeated entries of `{ 1: key, 2: value }`. |
| `oneof` | an enum field, `@wire(flatten)` | Each tag is a field number of the message (section 6). |
| `enum` | a payload-less enum, `@proto(number = n)` on each tag | `unitVariant` writes the number. Open enums keep an unknown number through `@wire(other) #Unrecognized(i32)`. |
| Unknown fields | skipped by their wire type | `skip()` needs no schema. Keeping them for re-encoding is an open question. |
| Sub-messages | length-delimited | The writer measures first, or writes into its buffer and puts the length in front, as prost does. |

What it takes:

- **The format package** is ordinary work: varints, wire types, packed lists, length prefixes and the merge rules. It is about the size of the TOML package.
- **The schema.** `.proto` files are the source of truth, and `comptime` cannot read a file, since it performs no effects. A generator writes the structs above from them, as prost-build does, either as a `fly` build step or as `protoc --fly_out`. Most of the work is here.
- **One struct, two encodings.** proto3's canonical JSON uses the fields' lowerCamelCase names, which are Flyscript's own, so the generated `Order` also encodes to protobuf's JSON through `std/json` with no attribute. The exceptions are that JSON wants 64-bit integers as strings and enums by name. That is a format's own view of a type (open question 5).
- **gRPC** is out of scope. A service maps naturally onto an effect whose operations are its calls: the client performs it, and the server handles it.

So clean protobuf interop is a package plus a generator, with no change to `std/codec` beyond what other formats already needed. It is not a special case.

## 11. Where it would be built

To give the reviewer a sense of size, not as a plan to follow. Everything here comes after the attributes design is built:

- **`std/codec`** (new): `Encode`, `Decode`, `Encoder`, `Decoder`, `Key`, `Value`, the derivations, `wire`, the adapters and `transcode`.
- **`Default`** in the prelude, derived.
- **The values of section 7**: `Bytes`, and `std/uuid`'s `Uuid`, both new; `Encode` and `Decode` for `std/time`'s `Timestamp` and `Duration`; the adapters (`Hex`, `Base64`, `Base64Url`, `Rfc3339`, `UnixSeconds`, `UnixMillis`, `ExactTime`, `Packed`, `Always`); `Text`, `Binary` and `Fallback`. `std/time`'s `DateTime` is a record, and a record cannot carry an encoding of its own. The time design (`2026-10-25-time-design.md`) moves it, as a struct, to the `calendar` package, and adds the data-model values for dates, times and zoned instants that its types need.
- **`std/json`** on `std/codec`, with paths, limits and duplicate keys.
- **Reflection**: comptime parameters on interface methods, specialized (section 6, item 6).
- **Docs**: spec §7.5 and A.9, std.md §16, and a new section for `std/codec`.

TOML, CBOR and protobuf are packages of their own, outside the standard library.

## Open questions

1. **Lowercase attribute types.** This design writes `@wire` as the attributes design proposes. If that design takes a declaration of its own instead (`attribute wire { … }`), `wire` changes its spelling here and nothing else.
2. **Keys at compile time, or `dyn`.** A `comptime key` parameter makes `Encoder` a template interface, so `dyn Encoder` is impossible, and with it miniserde's and deser's single copy of each type's code for every format. That copy matters for a page's WebAssembly size. Should the codec also offer a `DynEncoder` with keys passed at run time, trading speed for code size?
3. **Zero-copy decoding.** serde's `'de` lets a `&str` field borrow the input. In Fly that would be a `view struct` decoded with `parse<T>(text): T from text`, which `Decode extends Send` forbids today. Is that worth a second interface, `DecodeIn`, whose result is tied to the decoder?
4. **Context through effects.** serde passes state to a nested decoder with `DeserializeSeed`, and deser with its context. Fly's answer would be an effect: a `Symbol` that interns itself as it is read, in a table the caller handles. That needs `Decode` to be generic in a row of effects that the derivation gathers from its fields, and decoders whose row is open (`[Fail<JsonError>, ...R]`), which today's grammar cannot write in a type argument.
5. **Views beyond readable and binary.** Section 7 covers the split that serde's `is_human_readable` exists for. Protobuf's JSON mapping wants more: 64-bit integers as strings and enums by name. Is that a JSON setting (`JsonWriter.with({ int64: #String })`), or should a format be able to read another format's attributes (`@proto`) from the keys?
6. **`default = e` per field**, a value instead of the type's `Default`. Functions are not compile-time values, so `e` would be an expression spliced where the field is built. That is a quotation, which this design avoids. Is the struct-level `@wire(default)` with `impl Default` enough?
7. **Tags that are not strings**: deser's integer and boolean tag values (`{"kind": 2}`). Should `@wire(rename = …)` on a tag take an integer?
8. **Protobuf's unknown fields.** Should a message keep the fields it did not recognize, so that it encodes again byte for byte as it came, as protobuf's own libraries do? That would be `@wire(other)` on a field of a struct, holding raw fields.
9. **Default methods on interfaces.** Every format implements `timestamp`, `uuid` and the rest, mostly as one-line calls to `Fallback`. A default body in the interface would remove those lines, and would let the data model grow a value, such as decimals or big integers (CBOR tags 2–4), without breaking every format. Is that a language change worth making for this?
10. **Decimals and big integers.** Should `Decimal` and `BigInt` join `Timestamp` and `Uuid` as values of the data model now, and if so, should their JSON form default to a string or to a number written exactly?
