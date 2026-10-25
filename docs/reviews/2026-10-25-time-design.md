# Time: machine time in `std`, human time in `calendar` — a design

A proposal, for review, to split `std/time` in two. Instants, durations and the clocks stay in `std`, because the runtime, the simulator, `std/http` and the codec depend on them. Calendar dates, wall-clock times, time zones and calendar arithmetic move to `calendar`, a first-party package shipped with the installation as `web` is, and are redesigned there after the current state of the art, TC39's Temporal and Rust's jiff. Every type becomes a nominal struct whose invalid values cannot be built, with one text form, one form in each binary format, and an interface meant to last. It builds on the codec design (`2026-10-25-codec-design.md`) for serialization and on the packages and imports design for how the package is found. Nothing here is implemented, and `docs/spec.md` is not changed. A `§` number refers to the specification, and a "section" to this document.

Examples use today's imports. The code parses today, except that a method's body is left out where only its signature matters, as `std`'s declaration files do. Everything in `calendar` is a sketch.

## The design in brief

1. **`std` keeps machine time.** `Instant` (monotonic), `Timestamp` (an instant of UTC), `Duration` (exact, now signed), and the standard text forms of an instant: RFC 3339 and HTTP dates.
2. **`calendar` holds human time.** `PlainDate`, `PlainTime` and `PlainDateTime` are what a calendar and a clock show, with no zone. `DateTime` is an instant in a time zone. `Period` is an amount of calendar units. `TimeZone`, `Offset` and `Tzdb` hold the rules.
3. **Hard types.** Private fields and checked constructors, so there is no 31 February, no 25 o'clock and no mixed-sign period. Ordering is by the timeline, not by field names. Ranges cover years −9999 to 9999, to the nanosecond.
4. **The questions every time library gets wrong are answered by the types.** A wall-clock time in a gap or a fold says how it is resolved. A stored offset that disagrees with the zone's rules is an error unless the caller says otherwise. Adding a day and adding 24 hours are different operations with different argument types.
5. **One text form for each type**, the one the standards give. ISO 8601 and RFC 3339, with RFC 9557's `[Europe/London]` for a zone. `Show` prints it, `parse` reads it, and JSON uses it.
6. **One binary form for each type**, the standard tag where one exists. CBOR has tag 100 for a date, tag 1001 with a time-zone hint for a `DateTime`, and tag 1002 for a `Duration`. Protobuf has its well-known types and `google.type`'s.
7. **The tz database ships with the package**, as Java and every browser ship theirs, so time zones work the same on every host and in WebAssembly, and decoding a `DateTime` is pure. The host's own database is a choice, not the default.

---

## 1. What `std/time` has today

`std/time` (std.md §7) has `Timestamp`, an instant held as `i64` nanoseconds since 1970. It has `DateTime`, a record of `year`, `month`, `day`, `hour`, `minute`, `second`, `nanos` and `offset`. It has Hinnant's civil-date algorithms, `Zone` (read from a TZif file or from a POSIX `TZ` rule), `zone(name)` (read from `/usr/share/zoneinfo`), and ISO 8601 `format` and `parse`. The prelude has `Duration`, `u64` nanoseconds, and `Instant`, the monotonic clock `Io.now()` reads. The arithmetic is sound and is kept, but the types around it are not:

| | What goes wrong |
| :--- | :--- |
| **`DateTime` is a record.** | A record's fields have no declared order, since `{ a, b }` and `{ b, a }` are one type, and its derived `Ord` takes them by name. So `day` is compared first, and `2025-12-31 < 2026-01-01` is `false`: run today, it prints exactly that. Anyone can also write `{ month: 13, … }`, and a record can carry no impl of its own: no `Show` as ISO 8601, and no encoding (codec design, section 11). |
| **`DateTime` is two things.** | It is a date and time *plus an offset*, which is neither a plain date and time nor a time in a zone. `local(t, zone)` keeps the offset and forgets the zone, so adding a day to the result cannot follow a change to daylight saving time. |
| **Missing offsets become UTC.** | `parse("2026-10-25T09:00")` is 09:00 UTC. RFC 3339 requires an offset, and guessing one is how a meeting moves by an hour. |
| **Ranges are narrow.** | `i64` nanoseconds reach only from 1677 to 2262, so a birth date in 1650 or a lease ending in 2300 cannot be a `Timestamp`, or a `DateTime` built on one. |
| **`Duration` is unsigned.** | `nanosSince` returns a bare `i64` to work around it, and `Instant.since` panics if its argument is later. |
| **No calendar arithmetic.** | There is nothing to add a month, find how many days lie between two dates, round to the hour, or tell what weekday a date is in ISO's numbering. `weekday` answers `0` for Sunday. |
| **Zones exist only where the host keeps them.** | A WebAssembly program, a JavaScript one, or a host without `/usr/share/zoneinfo` has none. |

## 2. Where the line goes, and why

Rust's standard library has `Instant`, `SystemTime` and `Duration` and nothing human. chrono, `time` and jiff live outside it. The reasons are sound:

- **`std` cannot break.** Calendar libraries take several attempts to get right. Java went through `Date`, then `Calendar`, then Joda-Time, then `java.time`. JavaScript's `Date` is being replaced by Temporal after a decade of design. Python still lives with naive and aware `datetime`. Rust's own ecosystem went from chrono to `time` 0.3 to jiff. Whatever `std` had taken first, it would now be stuck with.
- **The tz database changes several times a year**, on no compiler's schedule.
- **What `std` needs is the clocks:** timeouts, sleeps, measurement and log stamps. Calendar arithmetic needs no privileged access, so it can be a library.

Go puts everything in `time`, and it is well liked. Java ships `java.time`, and Python ships `zoneinfo`. The lesson is that a standard library can take calendar time once the design has settled, and takes on its upkeep forever when it does.

Flyscript takes Rust's line and avoids Rust's cost, which is three competing libraries and a decade of churn. Human time goes in a **first-party package**: written and shipped with the installation, so it is there with no dependency to choose, but versioned on its own, so it can take a new tz database or a second major version without touching `std`. The line between the two halves is drawn by what depends on them. The runtime, `Io`, the simulator, `std/http`, logging and the codec need instants and durations. Nothing in `std` needs to know what a month is.

## 3. What stays in `std`

`Duration` and `Instant` stay in the prelude. `Timestamp` stays in `std/time`, which loses everything else.

```ts
// Sketch: the prelude and std/time after the move.

// An exact, signed amount of time: seconds and nanoseconds, the nanoseconds with the seconds' sign.
export struct Duration { private secs: i64; private nanos: i32 }

impl Duration {
  export function zero(): Duration;
  export function hours(n: i64): Duration;
  export function minutes(n: i64): Duration;
  export function secs(n: i64): Duration;
  export function ms(n: i64): Duration;
  export function micros(n: i64): Duration;
  export function nanos(n: i64): Duration;
  export function toSecs(self: readonly Self): i64;
  export function toMs(self: readonly Self): i64;
  export function toNanos(self: readonly Self): i128;
  export function subsecNanos(self: readonly Self): i32;
  export function plus(self: readonly Self, d: readonly Duration): Duration;
  export function minus(self: readonly Self, d: readonly Duration): Duration;
  export function times(self: readonly Self, n: i64): Duration;
  export function negated(self: readonly Self): Duration;
  export function abs(self: readonly Self): Duration;
  export function isNegative(self: readonly Self): bool;
  export function round(self: readonly Self, unit: TimeUnit, mode: Rounding): Duration;
  export function parse(text: str): Duration uses Fail<TimeErr>;
}

// A point on the program's monotonic clock: only differences between two mean anything.
export struct Instant { private nanos: u64 }

impl Instant {
  // How long after `earlier` this is: negative if `earlier` is later.
  export function since(self: readonly Self, earlier: readonly Instant): Duration;
  export function plus(self: readonly Self, d: readonly Duration): Instant;
}

// The units an exact amount of time is counted and rounded in, and the ways to round: Temporal's nine.
export type TimeUnit = #Hour | #Minute | #Second | #Milli | #Micro | #Nano;
export type Rounding = #Ceil | #Floor | #Expand | #Trunc | #HalfCeil | #HalfFloor | #HalfExpand | #HalfTrunc | #HalfEven;
export type TimeErr = #OutOfRange | #Syntax { at: usize; expected: String };

// An instant: seconds and nanoseconds since 1970 began, in UTC. Its range is years -9999 to 9999,
// a day inside at either end, so that every instant is a date of those years at any offset.
export struct Timestamp { private secs: i64; private nanos: u32 }

impl Timestamp {
  export function now(): Timestamp uses Io;
  export function fromUnixSecs(s: i64): Timestamp uses Fail<TimeErr>;
  export function fromUnixMs(ms: i64): Timestamp uses Fail<TimeErr>;
  export function fromUnixNanos(ns: i128): Timestamp uses Fail<TimeErr>;
  export function unixSecs(self: readonly Self): i64;
  export function unixMs(self: readonly Self): i64;
  export function unixNanos(self: readonly Self): i128;
  export function subsecNanos(self: readonly Self): u32;
  export function plus(self: readonly Self, d: readonly Duration): Timestamp;
  export function checkedPlus(self: readonly Self, d: readonly Duration): Option<Timestamp>;
  export function since(self: readonly Self, earlier: readonly Timestamp): Duration;
  export function round(self: readonly Self, unit: TimeUnit, mode: Rounding): Timestamp;
  // RFC 3339, any offset, RFC 9557's suffixes allowed and ignored: `2026-10-25T17:39:14.5+01:00`.
  export function parse(text: str): Timestamp uses Fail<TimeErr>;
  // RFC 9110's HTTP-date: IMF-fixdate written, and the two obsolete forms read too.
  export function parseHttp(text: str): Timestamp uses Fail<TimeErr>;
  export function formatHttp(self: readonly Self): String;
}
```

`TimeUnit`, `Rounding` and `TimeErr` join `Duration` in the prelude, since `Duration` uses them. All three types are `Copy`, `Eq`, `Ord`, `Hash` and `Show`.

**`Show`** prints the standard text form. A `Timestamp` is RFC 3339 in UTC, `2026-10-25T17:39:14.5Z`, with as many fraction digits as it needs. Under RFC 9557, `Z` now means "the instant is known, the local offset is not", which is exactly what a `Timestamp` is. A `Duration` is ISO 8601, `PT1H30M0.5S`, in hours, minutes and seconds and never days, because a day is a calendar unit.

**What changes for existing code:**

- `Duration` and `Timestamp` are each two words instead of one. `Duration` is signed. Its constructors take `i64`, and `toMs` answers `i64`.
- `Instant.since` no longer panics.
- `Timestamp.nanosSince`, `fromNanos` and `toNanos` become `since`, `fromUnixNanos` and `unixNanos`.
- `Io.sleep` of a negative duration returns at once.
- The 59 uses of `Duration` in the repository are literals and `toMs()`, and change only where a `u64` was spelled out.

**Arithmetic that leaves the range panics**, as integer overflow does, and the `checked…` forms answer `#None` instead. A constructor given a number or text from outside fails with `TimeErr`, because that number or text may be untrusted.

**Leap seconds** are not counted, as POSIX, every operating system and every library named here leave them out. `parse` reads a second of `60` as `59`, and nothing writes one.

## 4. The `calendar` package

```ts
// Sketch: what `calendar` exports.
import { Timestamp, TimeUnit, Rounding, TimeErr } from "std/time";

export type CalendarErr = #NoSuchDate | #Skipped | #Ambiguous | #OffsetMismatch | #UnknownZone(String) | #BadZone(String);
export type Unit = #Year | #Month | #Week | #Day | TimeUnit;
// A wall-clock time that does not exist (a gap) or exists twice (a fold), resolved: Temporal's names.
export type Disambiguation = #Compatible | #Earlier | #Later | #Reject;
// A text's offset that disagrees with its zone's rules, resolved.
export type OffsetConflict = #Reject | #PreferOffset | #UseOffset | #UseZone;
// A day of the month that the result's month does not have, resolved: 31 January plus a month.
export type Overflow = #Constrain | #Reject;

export enum Weekday { #Monday, #Tuesday, #Wednesday, #Thursday, #Friday, #Saturday, #Sunday }
```

| Type | What it is | Temporal | jiff | java.time |
| :--- | :--- | :--- | :--- | :--- |
| `PlainDate` | A day of the proleptic Gregorian calendar. | `PlainDate` | `civil::Date` | `LocalDate` |
| `PlainTime` | A time on a clock, to the nanosecond. | `PlainTime` | `civil::Time` | `LocalTime` |
| `PlainDateTime` | Both: what a calendar and a clock on a wall show, with no zone. | `PlainDateTime` | `civil::DateTime` | `LocalDateTime` |
| `DateTime` | An instant in a time zone: the timeline and the wall clock at once. | `ZonedDateTime` | `Zoned` | `ZonedDateTime` |
| `Period` | Years, months, weeks, days, and time: what a calendar adds. | `Duration` | `Span` | `Period` and `Duration` |
| `Offset` | A fixed difference from UTC, to the second. | — | `tz::Offset` | `ZoneOffset` |
| `TimeZone` | Rules for a place: its offsets, and when they change. | a string | `tz::TimeZone` | `ZoneId` |
| `Tzdb` | A database of zones by IANA name. | — | `tz::TimeZoneDatabase` | `ZoneRulesProvider` |
| `IsoWeek` | ISO 8601's week-numbering year, week and weekday. | — | `civil::ISOWeekDate` | `IsoFields` |

The plain types tell you what a date or a clock shows. A `DateTime` tells you when something happens, and `Timestamp` (in `std`) is the same instant with no zone attached. Converting between the two kinds always takes a `TimeZone`, and from plain to `DateTime` a `Disambiguation` too. So the step where wall-clock times go wrong is written in the program, where it can be seen.

### Names

`DateTime` is the zoned type, as chrono's `DateTime<Tz>` is. It is the type most programs want when they say "a date and time". Its plain counterpart says what it lacks: `PlainDateTime`, Temporal's name.

The prefix `Plain` means *not on the timeline*, and it goes on all three plain types. So the date is `PlainDate`, not `Date`. That costs a word, but `Date` is the name JavaScript and old Java gave to an *instant*, and every JavaScript programmer reading `Date` would be misled. It also keeps `PlainTime` from reading as "a time", which is what `Timestamp` is. Temporal's names will be the ones the largest population of programmers knows.

For the zoned type, `Zoned` (jiff) names a property rather than a thing, and `ZonedDateTime` (Temporal, Java) says "zoned" about what is, in this package, the normal case.

The calendar amount is the hardest name to pick:

| Name | Precedent | Against it |
| :--- | :--- | :--- |
| `Span` | jiff | Generic: a span of what? Text has spans, and so do ranges. |
| `Duration` | Temporal | Taken by the exact `Duration`. Temporal's one type for both is its most criticized corner: a month inside it makes most operations need a `relativeTo` at run time. |
| `Interval` | SQL, PostgreSQL | ISO 8601 and RFC 9581 use *interval* for a start and an end. |
| `CalendarDuration` | — | Accurate, and long for something written often. |
| `RelativeDelta` | Python's dateutil | A delta suggests subtraction, and "relative" says little. |
| **`Period`** | java.time, Noda Time (all units, years to nanoseconds); ISO 8601's `P` designator | RFC 9581 calls a start and end a *period* (CBOR tag 1003). `calendar` never writes that tag, so the clash is only one of words. |

**Recommendation: `Period`**. It is what Java and .NET programmers already call it, it reads as a calendar amount ("a period of two months"), it matches the `P` in `P1Y2M`, and it cannot be mistaken for `Duration`.

So the rule is: **`Duration` is exact, and `Period` counts calendar units.** A `Period` may carry hours as well, as Noda Time's does. Adding it applies the calendar units on the wall clock and the time units on the timeline (section 5).

### The plain types

```ts
// Sketch: a date. Declared in this order so derived `Ord` is the calendar's order.
export struct PlainDate { private year: i16; private month: u8; private day: u8 }

impl PlainDate {
  // Fails with #NoSuchDate for 31 April or 29 February 2026, and #OutOfRange past years -9999 to 9999.
  export function of(year: i16, month: u8, day: u8): PlainDate uses Fail<TimeErr | CalendarErr>;
  export function fromUnixDays(days: i64): PlainDate uses Fail<TimeErr>;
  export function year(self: readonly Self): i16;
  export function month(self: readonly Self): u8;
  export function day(self: readonly Self): u8;
  export function weekday(self: readonly Self): Weekday;
  export function dayOfYear(self: readonly Self): u16;
  export function daysInMonth(self: readonly Self): u8;
  export function inLeapYear(self: readonly Self): bool;
  export function isoWeek(self: readonly Self): IsoWeek;
  export function unixDays(self: readonly Self): i64;
  // Calendar units only: a period with time units in it panics. A day the month lacks is clamped.
  export function plus(self: readonly Self, p: readonly Period): PlainDate;
  export function plusWith(self: readonly Self, p: readonly Period, overflow: Overflow): PlainDate uses Fail<TimeErr | CalendarErr>;
  export function until(self: readonly Self, later: readonly PlainDate, largest: Unit): Period;
  export function withDay(self: readonly Self, day: u8): PlainDate uses Fail<CalendarErr>;
  export function firstOfMonth(self: readonly Self): PlainDate;
  export function lastOfMonth(self: readonly Self): PlainDate;
  export function at(self: readonly Self, t: readonly PlainTime): PlainDateTime;
  export function parse(text: str): PlainDate uses Fail<TimeErr | CalendarErr>;
}

export struct PlainTime { private hour: u8; private minute: u8; private second: u8; private nanos: u32 }
export struct PlainDateTime { private date: PlainDate; private time: PlainTime }

impl PlainDateTime {
  // The zone's instant for this wall-clock time, a gap or a fold resolved as RFC 5545 and
  // Temporal do: in a gap the time after it, in a fold the earlier of the two.
  export function inZone(self: readonly Self, zone: readonly TimeZone): DateTime;
  export function inZoneWith(self: readonly Self, zone: readonly TimeZone, d: Disambiguation): DateTime uses Fail<CalendarErr>;
}
```

A `PlainTime` has `of(hour, minute, second, nanos)`, `midnight()`, its four parts, `plus(d)` of a `Duration` (wrapping round midnight, as a clock does), `round`, and `parse`. A `PlainDateTime` has its date's and its time's methods, and `plus` of a `Period`, the days carried into the date. Each plain type is `Copy`, `Eq`, `Ord`, `Hash` and `Show`, with ordering derived because the fields are declared most significant first. A `PlainDate` is four bytes, and a `PlainDateTime` twelve.

**Constants are checked when they are compiled.** `const launch = comptime PlainDate.of(2026, 10, 25);` is a `PlainDate` with no failure left to handle, and `PlainDate.of(2026, 2, 30)` in the same place is a compile error, as any failing `comptime` evaluation is. `Period.parse("P1Y2M")` and `TimeZone.get("Europe/London")` work the same way. No new mechanism is needed for literals.

### `DateTime`

```ts
// Sketch: an instant, and the zone it is seen in. The offset and the wall clock are worked out once
// and kept; the zone's rules are shared.
export struct DateTime {
  private at: Timestamp;
  private zone: TimeZone;
  private offset: Offset;
  private plain: PlainDateTime;
}

impl DateTime {
  export function now(zone: TimeZone): DateTime uses Io;
  export function fromTimestamp(t: readonly Timestamp, zone: TimeZone): DateTime;
  export function timestamp(self: readonly Self): Timestamp;
  export function zone(self: readonly Self): TimeZone;
  export function offset(self: readonly Self): Offset;
  export function plain(self: readonly Self): PlainDateTime;
  export function date(self: readonly Self): PlainDate;
  export function time(self: readonly Self): PlainTime;
  // The same instant, seen in another zone.
  export function withZone(self: readonly Self, zone: TimeZone): DateTime;
  export function plus<A extends Amount>(self: readonly Self, a: readonly A): DateTime;
  export function until(self: readonly Self, later: readonly DateTime, largest: Unit): Period;
  // The first instant of this date in this zone: midnight, unless the zone skipped it.
  export function startOfDay(self: readonly Self): DateTime;
  export function round(self: readonly Self, unit: Unit, mode: Rounding): DateTime;
  // RFC 9557: `2026-10-25T01:30:00+01:00[Europe/London]`. The zone is required; an offset that
  // disagrees with it is #OffsetMismatch.
  export function parse(text: str): DateTime uses Fail<TimeErr | CalendarErr>;
  export function parseWith(text: str, conflict: OffsetConflict): DateTime uses Fail<TimeErr | CalendarErr>;
}

// What `plus` accepts: an exact `Duration`, or a `Period`.
export interface Amount { function addTo(self: readonly Self, d: readonly DateTime): DateTime; }
impl Amount for Duration { function addTo(self: readonly Self, d: readonly DateTime): DateTime { … } }
impl Amount for Period { function addTo(self: readonly Self, d: readonly DateTime): DateTime { … } }
```

`Amount` is `calendar`'s own interface, so implementing it for `std`'s `Duration` is allowed under the orphan rule (§3.4). The zone's rules are held in an `Arc`, so a `DateTime` is `Clone` and `Send` but not `Copy`.

**Ordering.** `cmp` is by instant, and two `DateTime`s at the same instant in different zones are ordered by the zone's name. So `Ord` agrees with `Eq`, which holds only when the instant and the zone are both the same. To compare instants alone, compare `a.timestamp()` with `b.timestamp()`.

### Zones

```ts
export struct Offset { private secs: i32 }

impl Offset {
  export function utc(): Offset;
  // Within ±25:59:59, as jiff's offsets are.
  export function of(secs: i32): Offset uses Fail<TimeErr>;
  export function secs(self: readonly Self): i32;
  export function parse(text: str): Offset uses Fail<TimeErr>;
}

export struct TimeZone { private id: String; private rules: Arc<Rules> }
type Rules = { at: Vec<i64>; which: Vec<u8>; kinds: Vec<OffsetInfo>; rule: Option<String> };
export type OffsetInfo = { offset: Offset; dst: bool; abbreviation: String };
export type Transition = { at: Timestamp; before: OffsetInfo; after: OffsetInfo };

impl TimeZone {
  export function utc(): TimeZone;
  export function fixed(offset: Offset): TimeZone;
  // From the database `calendar` ships: pure, and the same on every host.
  export function get(name: str): TimeZone uses Fail<CalendarErr>;
  // The host's own zone: `TZ`, else `/etc/localtime`, else UTC.
  export function system(): TimeZone uses Io;
  export function fromRule(tz: str): TimeZone uses Fail<CalendarErr>;
  export function fromTzif(name: str, b: readonly u8[]): TimeZone uses Fail<CalendarErr>;
  // `Europe/London`, `UTC`, or a fixed zone's offset, `+05:30`.
  export function id(self: readonly Self): String;
  export function offsetAt(self: readonly Self, t: readonly Timestamp): Offset;
  export function infoAt(self: readonly Self, t: readonly Timestamp): OffsetInfo;
  export function nextTransition(self: readonly Self, t: readonly Timestamp): Option<Transition>;
  export function previousTransition(self: readonly Self, t: readonly Timestamp): Option<Transition>;
}

export struct Tzdb { private version: String; private zones: Vec<TimeZone> }

impl Tzdb {
  export function bundled(): Tzdb;
  export function system(): Tzdb uses Io, Fail<CalendarErr>;
  export function get(self: readonly Self, name: str): TimeZone uses Fail<CalendarErr>;
  export function names(self: readonly Self): Vec<String>;
  // IANA's release, `2026b`.
  export function version(self: readonly Self): String;
}
```

`TimeZone.get` and `TimeZone.system` replace today's `zone(name)`. The TZif and POSIX-rule readers move over from `std/time` unchanged, and `ZoneKind` becomes `OffsetInfo`. `TimeZone` is `Eq` and `Hash` by id, and its `Show` prints the id.

### `Period`

```ts
// Sketch: every field has the same sign, or is zero. Calendar units are i32; time units are i64,
// so `PT1000000H` is a period too.
export struct Period {
  private years: i32; private months: i32; private weeks: i32; private days: i32;
  private hours: i64; private minutes: i64; private secs: i64; private nanos: i64;
}

impl Period {
  export function ofYears(n: i32): Period;
  export function ofMonths(n: i32): Period;
  export function ofWeeks(n: i32): Period;
  export function ofDays(n: i32): Period;
  export function ofDuration(d: readonly Duration): Period;
  export function withYears(self: readonly Self, n: i32): Period uses Fail<CalendarErr>;
  export function withMonths(self: readonly Self, n: i32): Period uses Fail<CalendarErr>;
  export function withDays(self: readonly Self, n: i32): Period uses Fail<CalendarErr>;
  export function withHours(self: readonly Self, n: i64): Period uses Fail<CalendarErr>;
  export function years(self: readonly Self): i32;
  export function months(self: readonly Self): i32;
  export function days(self: readonly Self): i32;
  export function negated(self: readonly Self): Period;
  export function isZero(self: readonly Self): bool;
  // A period's length depends on where it starts: P1M is 28 to 31 days, and P1D 23 to 25 hours.
  export function compare(self: readonly Self, other: readonly Period, from: readonly DateTime): Ordering;
  export function toDuration(self: readonly Self, from: readonly DateTime): Duration;
  export function round(self: readonly Self, smallest: Unit, mode: Rounding, from: readonly DateTime): Period;
  export function parse(text: str): Period uses Fail<TimeErr | CalendarErr>;
}
```

A `Period` is `Eq` and `Hash` by its fields, so `P1D` is not `PT24H`. That is correct: across a change to daylight saving time they are different amounts. It is **not `Ord`**, because no order exists without a starting point, and that is why `compare` takes one. Temporal has the same rule and enforces it at run time; here the type enforces it at compile time.

## 5. Semantics

These are the rules that make a time library right or wrong. Each follows Temporal and jiff, which agree with each other and with RFC 5545.

**Gaps and folds.** When clocks go forward, 01:30 on that day does not exist in London; when they go back, it exists twice. `PlainDateTime.inZone` resolves both the *compatible* way: a time in a gap moves forward by the gap's length, and a time in a fold takes the earlier instant. That is what RFC 5545, Java, Temporal and jiff all do. `inZoneWith(zone, #Reject)` fails with `#Skipped` or `#Ambiguous` instead, and `#Earlier` and `#Later` choose explicitly.

**Adding.** `DateTime.plus(Period)` applies years, months, weeks and days to the wall clock, then resolves the result in the zone (compatibly), then adds the time units to the instant. So, in London:

- `2026-03-28T09:00[Europe/London]` plus `P1D` is 09:00 the next day, 23 hours later;
- the same time plus `PT24H` is 10:00, 24 hours later;
- plus `Duration.hours(24)` is also 10:00.

Months clamp: 31 January plus `P1M` is 28 February, unless `#Reject` is asked for. Years, then months, then weeks, then days are applied in that order, so `P1M1D` from 31 January is 1 March.

**Differences.** `a.until(b, largest)` gives the `Period` from `a` to `b` in units no larger than `largest`, and `a.plus(a.until(b, u))` is `b` for every unit `u`. The unit has no default: what "the difference between two dates" means depends on the question, and Temporal's default (hours for a zoned time) surprises people.

**Offsets in text.** `2030-06-01T12:00:00+01:00[Europe/London]` written today may not match London's rules when it is read in 2030, if the rules change in between. By default `parse` fails with `#OffsetMismatch`, as Temporal and jiff do: silently moving a stored time is worse than failing. `parseWith` chooses otherwise:

- `#UseOffset` keeps the instant;
- `#UseZone` keeps the wall clock;
- `#PreferOffset` keeps the instant if the offset is still one the zone uses at that time, and otherwise keeps the wall clock.

Per RFC 9557, an elective time zone (`[Europe/London]`) and a critical one (`[!Europe/London]`) are both acted on. `calendar` is not an application that may ignore the zone.

**Future events.** A meeting set for 09:00 London time in 2031 is a wall-clock time, not an instant, and should be stored as one. A record of a `PlainDateTime` and a `TimeZone`, resolved when it is used, survives any change to the rules. A `DateTime` is right for something that has happened, or must happen at a fixed instant, such as a flight's departure or an expiry. The docs should say so, because no type can tell the two intents apart.

**Ranges.**

- Years run from −9999 to 9999, as in jiff, so every value has a short text form and a `PlainDate` fits in four bytes.
- Precision is the nanosecond everywhere.
- Offsets go to the second, because tzdb's local mean times have seconds in them.

Temporal reaches ±271,821 years, which only astronomy needs, at the price of six-digit years in its text forms.

**The calendar is ISO 8601's**, the proleptic Gregorian calendar, with ISO weekdays (Monday is 1) and ISO week numbering. `parse` ignores an elective calendar annotation `[u-ca=iso8601]`, and fails on a critical one, or on any calendar other than ISO's. Other calendars can be packages that convert through `unixDays`. Open question 3 asks whether that is enough.

**Localized text** ("25 October 2026", "25/10/2026", "il y a 3 jours") needs CLDR's data and belongs in a later `intl` package, as Temporal defers to `Intl.DateTimeFormat`. `calendar` has `strftime`-style `format` and `parse` for fixed layouts. A format given as a constant is checked when it is compiled.

## 6. Text forms

| Type | `Show`, `parse`, JSON | Notes |
| :--- | :--- | :--- |
| `Timestamp` | `2026-10-25T17:39:14.5Z` | RFC 3339. Read with any offset. |
| `Duration` | `PT1H30M0.5S` | ISO 8601, never days. `"5400.5s"`, protobuf's JSON form, is read too. |
| `PlainDate` | `2026-10-25` | RFC 3339 `full-date`. Years outside 0–9999 are ISO 8601's extended form, `-000044-03-15`. |
| `PlainTime` | `14:05:09.25` | A fraction only if there is one. |
| `PlainDateTime` | `2026-10-25T14:05:09` | No offset, and none accepted: a text with one is not a plain time. |
| `DateTime` | `2026-10-25T14:05:09+00:00[Europe/London]` | RFC 9557. The offset is always numeric, never `Z`, because the local offset is known. A fixed zone is `[+05:30]`, which RFC 9557 permits but discourages. |
| `Offset` | `+05:30` | `+00:00` for UTC. |
| `TimeZone` | `Europe/London` | IANA's name. |
| `Period` | `P1Y2M3DT4H` | ISO 8601. Negative as `-P1D`, as Temporal writes it. Zero as `PT0S`. |
| `Weekday` | `Monday` | |

Each `parse` reads exactly its type's form. A `Timestamp` text without an offset is not a `Timestamp`, and a `DateTime` text without a zone is not a `DateTime`. `Timestamp.parse(text)`, then `DateTime.fromTimestamp(t, zone)`, is the way to say which zone. A tool that must accept anything, such as a log reader, uses `Parsed.of(text)`, which returns the parts found (a `PlainDateTime`, an `Option<Offset>` and an `Option<String>` zone) and leaves the choice to the caller, as jiff's `Pieces` does.

## 7. Serialization

The codec design (section 7) puts `Timestamp`, `Duration`, bytes and `Uuid` in the data model, so each format writes them in its native form. Human time needs four more values there, each made of plain numbers, so `std/codec` still knows nothing of months:

```ts
// Sketch: additions to std/codec's Encoder; Decoder mirrors them.
interface CivilEncoder<row E> {
  // Days since 1970-01-01.
  function date(self: mut Self, days: i64): void uses ...E;
  // Nanoseconds since midnight.
  function time(self: mut Self, nanos: u64): void uses ...E;
  function plainDateTime(self: mut Self, days: i64, nanos: u64): void uses ...E;
  // An instant, the offset it had, and the zone's name.
  function zoned(self: mut Self, t: readonly Timestamp, offset: i32, zone: str): void uses ...E;
}
```

`calendar`'s types implement `Encode` and `Decode` by hand on those values, and `Period`, `Offset`, `TimeZone` and `Weekday` as strings. Any field of any of these types then gets the right form in every format, with no attribute:

| Type | CBOR | TOML | protobuf |
| :--- | :--- | :--- | :--- |
| `Timestamp` | Tag 1, or tag 1001 with `@wire(via = ExactTime)` (codec design). | Offset date-time. | `google.protobuf.Timestamp` |
| `Duration` | Tag 1002, `{1: secs, -9: nanos}` (RFC 9581). | String. | `google.protobuf.Duration` |
| `PlainDate` | Tag 100, days since 1970 (RFC 8943). Tag 1004, the `full-date` text, is also read. | Local date. | `google.type.Date` |
| `PlainTime` | Text, as above: no tag exists. | Local time. | `google.type.TimeOfDay` |
| `PlainDateTime` | Text, as above. Never tag 0, which requires an offset. | Local date-time. | `google.type.DateTime`, no `time_offset` |
| `DateTime` | Tag 1001, `{1: secs, -9: nanos, -10: "Europe/London"}`: an exact instant with RFC 9581's time-zone hint. | String, as above: TOML has no zones. | `google.type.DateTime` with `time_zone` |
| `Period`, `Offset`, `TimeZone` | Text. `Offset` is an integer of seconds. | String. | String; `google.type.TimeZone` for a zone. |
| `Weekday` | Its ISO number, 1 to 7. | String. | `google.type.DayOfWeek` (Monday is 1 there too). |

A few choices in that table need a word:

- **A `DateTime` in CBOR** is the instant, which is what tag 1001 means, with the zone as an elective hint (key −10, not the critical 10). A reader that knows nothing of zones still gets the right instant, and `calendar` reads the zone back. The offset is not written, since the instant and the zone determine it, so the binary form behaves like `#UseOffset`. The text form carries both and detects a change of rules. Protobuf's `google.type.DateTime` holds a wall clock and a zone, and so behaves like `#UseZone`. Each follows what its format's standard type means, and the guidance on future events in section 5 is what makes the difference harmless.
- **Decoding stays pure.** A `DateTime` or `TimeZone` decoded from any format looks its zone up in the bundled database, so `Decode` needs no `Io` in its row, and the same bytes decode to the same value on every host.
- **Changing the form** uses the codec's adapters: `@wire(via = UnixMillis)` on a `Timestamp`, or `@wire(via = Always<Text>)` to keep a `PlainDate` as text in CBOR for a reader that does not know tag 100.
- **The codec design changes in two places** if this is accepted. A `Duration`'s JSON becomes ISO 8601 instead of protobuf's `"1.5s"`, following its own rule that a standard's form wins, while protobuf's form is still read. And the four values above join the data model.

## 8. The tz database

`calendar` ships with IANA's database compiled into it, and `TimeZone.get` reads from that copy. Java ships its own copy in the JDK, browsers ship ICU's, and Go has `time/tzdata` for hosts without one. That makes zones:

- **available everywhere**, including WebAssembly, JavaScript and Windows;
- **pure**, since looking one up performs nothing, so `Decode` can do it, `comptime` can do it, and a simulated world needs nothing from the host;
- **reproducible**, since a given version of `calendar` gives the same answers on every machine, and `Tzdb.bundled().version()` says which release of IANA's data that is.

Go's embedded database costs about 450 KB. Two things keep that down here. A program links the database only if it looks up a zone by a name that is not known when it is compiled. A `comptime` lookup, `TimeZone.get("Europe/London")`, embeds that one zone, a kilobyte or two.

**The host's database** is a choice: `Tzdb.system()` reads `TZDIR` or `/usr/share/zoneinfo`, as `zone()` does now. A server that wants its distribution's tz updates without upgrading `calendar` uses it. `TimeZone.system()`, the host's own zone, always performs `Io`, since which zone a machine is in is a fact about the machine.

**New tz releases** go out as new patch releases of `calendar`. The installation's copy updates with the toolchain, and a project that needs a new release sooner names a newer `calendar` in its manifest (open question 2).

## 9. What was weighed

| Choice | Taken | Not taken, and why |
| :--- | :--- | :--- |
| Where human time lives | A first-party package | **All in `std`**, as Go does: frozen at the first design, and tz data tied to the compiler. **Left to third parties**, as Rust does: three competing libraries, and the codec and `std/http` would have no type to agree on for a date. |
| Where `Timestamp` lives | `std` | **In `calendar`:** `std/http`'s `Date` header, logs, the codec's data model and `Io.wall` all need it, and none of them needs a month. |
| Exact and calendar amounts | Two types, `Duration` and `Period` | **One type**, as Temporal has: every operation on it then needs a starting point at run time, or throws. |
| `Duration`'s sign | Signed | **Unsigned, plus a `SignedDuration`**, jiff's workaround for a `std` it cannot change. Flyscript still can change its own. |
| Representation | Seconds and nanoseconds | **`i64` nanoseconds:** years 1677 to 2262 only. **`i128` nanoseconds:** simpler arithmetic, but slow on JavaScript and WebAssembly and twice the size of what the range needs. |
| Range | Years −9999 to 9999 | **Temporal's ±271,821:** six-digit years in every text form, for nobody's benefit. |
| Default tz database | Bundled | **The host's:** absent on WebAssembly and JavaScript, different from machine to machine, and only reachable through `Io`, which `Decode` does not have. |
| Gaps, folds and offset conflicts | Compatible on construction, reject on parse | **Reject everywhere:** constructing a meeting at 02:30 on the day clocks change should work as people expect. **Lenient everywhere:** silently moving stored data. |
| A zone as an effect | A value, `TimeZone`, and a database, `Tzdb` | **An effect, `Zones`,** that handlers answer: neat, but it would have to appear in every `Decode` row and every function that formats a time, for what is constant data. |
| An `OffsetDateTime` type | None. A `DateTime` in a fixed zone, or a `Timestamp`, covers it. | **Its own type**, as Java has: RFC 9557 discourages copying an offset into a zone, and a type for it would encourage exactly that. |

## 10. Where it would be built

1. **`std`.** `Duration` signed, `Timestamp` widened, `Instant.since` total, and RFC 3339 and HTTP dates in `std/time`. Then std.md §1 and §7 and the 59 uses of `Duration`. `std/http` takes `parseHttp` for `Date`, `Expires`, `Last-Modified` and cookie expiry.
2. **`calendar/`**, beside `web/`, with its own version. Hinnant's algorithms and the TZif and POSIX-rule readers move from `std/time`. The new parts are the plain types, `DateTime`, `Period`, arithmetic, differences, rounding and the parsers.
3. **The database.** A tool in `tools/` compiles a release of IANA's database into `calendar/tzdb.fly`, records its version, and runs on each release.
4. **`std/time` loses** `DateTime`, `civil`, `instant`, `local`, `Zone`, `ZoneKind`, `zone`, `format`, `parse`, `daysFromCivil`, `civilFromDays`, `weekday` and `isLeapYear`. `tests/run/time_zones.fly` moves to `calendar`'s tests. A regression test pins the bug of section 1: `2025-12-31` comes before `2026-01-01`.
5. **The tests** check gaps, folds and conflicts against Temporal's test262 cases, where they apply to the ISO calendar. Arithmetic and differences are checked against jiff's tests, and round trips of every text form against random values.
6. **The codec values** of section 7, once `std/codec` exists.

Until step 2 lands, the bug in section 1 has a stopgap: `DateTime` becomes a struct with `Ord` written by instant. The plan replaces it, and does not depend on it.

## Open questions

1. **The package's name.** `calendar` is proposed. `time` would read better, but `import std.time;` binds `time`, and a package of the same name beside it would confuse every reader. `chrono` is familiar from Rust and says nothing. `civil` is jiff's word, and precise but obscure.
2. **Overriding an installation package.** `calendar` should be importable with no manifest entry, as `web` is. A project that needs a newer tz release should also be able to name a newer `calendar` in `fly.toml`. Does a declared dependency shadow the installation's package of the same name? The imports design should decide that once for every installation package.
3. **Other calendars.** Temporal carries a calendar inside every date. That is general, but most programs pay for it in API surface and never use it. This design is ISO-only, with other calendars as packages that convert through `unixDays`. If a calendar parameter were added later, `PlainDate` would become `PlainDate<C = Iso>`. Is that a change that can be made later without breaking existing code, or must the parameter be reserved now?
4. **`PlainYearMonth` and `PlainMonthDay`.** Temporal has them, for a card's expiry and a birthday. They are left out to keep the type count down. Do they carry their weight?
5. **The `#Compatible` default on construction.** It matches every precedent, but it means `PlainDateTime.inZone` never fails on a gap or fold. A linter could flag uses in code that also performs `Io`, where the wall-clock time probably came from a person. Is that worth anything, or is it noise?
6. **Interval types.** A start and an end, as a `[DateTime, DateTime]` or a `Range`, with `contains` and `overlaps`, is common in scheduling code. It is RFC 9581's period, tag 1003. Is it `calendar`'s to define, or left to applications?
7. **Monotonic and wall time in one value.** Go's `time.Time` carries a monotonic reading so that `t2.Sub(t1)` is immune to clock jumps. Here `Instant` and `Timestamp` stay apart, and a program that wants both reads both. Is that friction worth a `Stamp` pair in `std`?
