use std::fmt;

/// A half-open byte range into a source file.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
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
