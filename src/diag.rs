use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{BuildHasherDefault, Hasher};

/// A half-open byte range into a source file.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// Maps keyed by what the compiler makes itself: spans and ids. The checker's results are found by
/// span for every expression the evaluator meets, and no adversary chooses these keys, so they are
/// hashed by multiplication rather than SipHash.
pub type FastMap<K, V> = HashMap<K, V, BuildHasherDefault<FastHasher>>;
pub type SpanMap<V> = FastMap<Span, V>;
pub type SpanSet = HashSet<Span, BuildHasherDefault<FastHasher>>;

#[derive(Default)]
pub struct FastHasher(u64);

impl Hasher for FastHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.write_u64(b as u64);
        }
    }
    fn write_u64(&mut self, n: u64) {
        self.0 = (self.0.rotate_left(5) ^ n).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
    fn write_usize(&mut self, n: usize) {
        self.write_u64(n as u64);
    }
}

impl Span {
    pub fn new(start: usize, end: usize) -> Span {
        Span { start, end }
    }

    pub fn to(self, other: Span) -> Span {
        Span::new(self.start.min(other.start), self.end.max(other.end))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub span: Span,
    pub message: String,
}

impl Diagnostic {
    pub fn new(span: Span, message: impl Into<String>) -> Diagnostic {
        Diagnostic { span, message: message.into() }
    }

    /// Renders `file:line:col: message` followed by the source line and a caret.
    pub fn render(&self, file: &str, source: &str) -> String {
        let (line, col) = line_col(source, self.span.start);
        let text = source.lines().nth(line - 1).unwrap_or("");
        let width = self.span.end.saturating_sub(self.span.start).max(1);
        let width = width.min(text.len().saturating_sub(col - 1).max(1));
        format!(
            "{file}:{line}:{col}: {}\n  {text}\n  {}{}",
            self.message,
            " ".repeat(col - 1),
            "^".repeat(width)
        )
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}..{}", self.message, self.span.start, self.span.end)
    }
}

/// 1-based line and column (in characters) of a byte offset.
pub fn line_col(source: &str, offset: usize) -> (usize, usize) {
    let offset = offset.min(source.len());
    let before = &source[..offset];
    let line = before.matches('\n').count() + 1;
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    let col = source[line_start..offset].chars().count() + 1;
    (line, col)
}
