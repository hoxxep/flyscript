//! Random patterns, each written twice: as std/regex reads it, and as the same expression for Rust's
//! `regex` crate, whose `\d`, `\w`, `\s` and `\b` are Unicode's where RE2's are ASCII's. Each case
//! is a line `pattern TAB text TAB matches`: every match `captures_iter` finds, `;` between them,
//! each its groups' spans `start-end`, or `-` for a group that took no part, `,` between them. In
//! the pattern and the text `%`, a tab and a newline are written `%25`, `%09` and `%0A`.

use regex::Regex;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn pick<'a>(&mut self, xs: &[&'a str]) -> &'a str {
        xs[self.below(xs.len())]
    }
}

/// A pattern for std/regex and the same for Rust.
type Pair = (String, String);

const LETTERS: &[&str] = &["a", "b", "c", "A", "K", "k", "é", "É", "1", "_", " "];

fn class_item(r: &mut Rng) -> Pair {
    let (f, s) = match r.below(9) {
        0 => ("a-c", "a-c"),
        1 => ("\\d", "0-9"),
        2 => ("\\w", "0-9A-Za-z_"),
        3 => ("\\s", "\\t\\n\\f\\r "),
        4 => ("[:alpha:]", "[:alpha:]"),
        5 => ("[:^digit:]", "[:^digit:]"),
        6 => ("\\pL", "\\pL"),
        7 => ("A-Z", "A-Z"),
        _ => {
            let l = r.pick(LETTERS);
            return (l.to_string(), l.to_string());
        }
    };
    (f.to_string(), s.to_string())
}

fn atom(r: &mut Rng, depth: u32, groups: &mut u32) -> Pair {
    let n = if depth >= 3 { 14 } else { 20 };
    let p = |a: &str, b: &str| (a.to_string(), b.to_string());
    match r.below(n) {
        0..=5 => {
            let l = r.pick(LETTERS);
            p(l, l)
        }
        6 => p(".", "."),
        7 => p("\\d", "[0-9]"),
        8 => match r.below(4) {
            0 => p("\\w", "[0-9A-Za-z_]"),
            1 => p("\\W", "[^0-9A-Za-z_]"),
            2 => p("\\s", "[\\t\\n\\f\\r ]"),
            _ => p("\\S", "[^\\t\\n\\f\\r ]"),
        },
        9 => {
            let neg = if r.below(3) == 0 { "^" } else { "" };
            let mut f = format!("[{neg}");
            let mut s = format!("[{neg}");
            for _ in 0..1 + r.below(3) {
                let (a, b) = class_item(r);
                f += &a;
                s += &b;
            }
            (f + "]", s + "]")
        }
        10 => match r.below(7) {
            0 => p("^", "^"),
            1 => p("$", "$"),
            2 => p("\\b", "(?-u:\\b)"),
            3 => p("\\B", "(?-u:\\B)"),
            4 => p("\\A", "\\A"),
            5 => p("\\z", "\\z"),
            _ => p("\\.", "\\."),
        },
        11 => p("\\x{E9}", "\\x{E9}"),
        12 => p("\\p{Lu}", "\\p{Lu}"),
        13 => p("", ""),
        _ => {
            let (f, s) = alternation(r, depth + 1, groups);
            match r.below(5) {
                0 => (format!("(?:{f})"), format!("(?:{s})")),
                1 => {
                    *groups += 1;
                    let g = *groups;
                    (format!("(?P<g{g}>{f})"), format!("(?P<g{g}>{s})"))
                }
                2 => {
                    let fl = r.pick(&["i", "m", "s", "U", "i-s", "-i"]);
                    (format!("(?{fl}:{f})"), format!("(?{fl}:{s})"))
                }
                _ => {
                    *groups += 1;
                    (format!("({f})"), format!("({s})"))
                }
            }
        }
    }
}

fn repeated(r: &mut Rng, depth: u32, groups: &mut u32) -> Pair {
    let (f, s) = atom(r, depth, groups);
    // An empty atom or an assertion repeated is legal but says little; repeat letters and groups.
    if f.is_empty() || r.below(3) != 0 {
        return (f, s);
    }
    let q = match r.below(9) {
        0 | 1 => "*".to_string(),
        2 | 3 => "+".to_string(),
        4 | 5 => "?".to_string(),
        // Not `{0}` or `{0,0}`, after which Rust's `regex` leaves the groups inside out of the
        // count, where RE2 counts them.
        6 => format!("{{{}}}", 1 + r.below(2)),
        7 => format!("{{{},}}", r.below(3)),
        _ => {
            let lo = r.below(3);
            format!("{{{},{}}}", lo, (lo + r.below(3)).max(1))
        }
    };
    let lazy = if r.below(4) == 0 { "?" } else { "" };
    (format!("{f}{q}{lazy}"), format!("{s}{q}{lazy}"))
}

fn concatenation(r: &mut Rng, depth: u32, groups: &mut u32) -> Pair {
    let (mut f, mut s) = (String::new(), String::new());
    for _ in 0..1 + r.below(4) {
        let (a, b) = repeated(r, depth, groups);
        f += &a;
        s += &b;
    }
    (f, s)
}

fn alternation(r: &mut Rng, depth: u32, groups: &mut u32) -> Pair {
    let (mut f, mut s) = concatenation(r, depth, groups);
    for _ in 0..r.below(3).saturating_sub(1) {
        let (a, b) = concatenation(r, depth, groups);
        f = format!("{f}|{a}");
        s = format!("{s}|{b}");
    }
    (f, s)
}

const TEXT: &[&str] = &["a", "a", "b", "b", "c", "A", "K", "k", "\u{212A}", "é", "É", "e\u{301}", "1", "_", " ", "\n", ".", "ab"];

fn text(r: &mut Rng) -> String {
    (0..r.below(12)).map(|_| r.pick(TEXT)).collect()
}

fn escape(s: &str) -> String {
    s.replace('%', "%25").replace('\t', "%09").replace('\n', "%0A")
}

fn main() {
    let mut r = Rng(0x5eed_f1e5_c4a1_7001);
    let mut cases = 0;
    // A few by hand: the empty pattern, empty matches, leftmost-first alternation, laziness.
    let mut fixed: Vec<Pair> = ["", "a*", "a|ab", "ab|a", "(a+)(b+)?", "(a|b)*?b", "x*", "(?m)^", "(?m)$", "\\b", "(?i)k", "(?i)[k-l]", "[^a]", "(?s).", "(a*)+", "(a*)*b", "(?U)a+", "a{2,3}", "a{2}?"]
        .iter()
        .map(|p| (p.to_string(), p.replace("\\b", "(?-u:\\b)")))
        .collect();
    fixed.reverse();
    while cases < 3000 {
        let (fly, rust) = match fixed.pop() {
            Some(p) => p,
            None => {
                let mut groups = 0;
                let (mut f, mut s) = alternation(&mut r, 0, &mut groups);
                if r.below(4) == 0 {
                    let fl = r.pick(&["(?i)", "(?m)", "(?s)", "(?U)", "(?im)"]);
                    f = format!("{fl}{f}");
                    s = format!("{fl}{s}");
                }
                (f, s)
            }
        };
        let Ok(re) = Regex::new(&rust) else { continue };
        for _ in 0..3 {
            let t = text(&mut r);
            let found: Vec<String> = re
                .captures_iter(&t)
                .map(|c| {
                    (0..c.len())
                        .map(|g| c.get(g).map_or("-".to_string(), |m| format!("{}-{}", m.start(), m.end())))
                        .collect::<Vec<_>>()
                        .join(",")
                })
                .collect();
            println!("{}\t{}\t{}", escape(&fly), escape(&t), found.join(";"));
        }
        cases += 1;
    }
}
