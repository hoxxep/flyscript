use crate::diag::{Diagnostic, Span};

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Ident(String),
    Kw(Kw),
    Int(String),
    Float(String),
    Byte(u8),
    Str(String),
    Template(Vec<TemplatePart>),
    /// `#Name`
    Tag(String),
    Punct(&'static str),
    Eof,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TemplatePart {
    Lit(String),
    /// The byte range of an interpolated expression's source.
    Expr(Span),
}

macro_rules! keywords {
    ($($name:ident => $text:literal),* $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Kw { $($name),* }

        impl Kw {
            pub fn lookup(s: &str) -> Option<Kw> {
                match s { $($text => Some(Kw::$name),)* _ => None }
            }

            pub fn as_str(self) -> &'static str {
                match self { $(Kw::$name => $text),* }
            }
        }
    };
}

// `from`, `of`, `with`, `resumes` and `row` are contextual and lex as identifiers.
keywords! {
    As => "as", Break => "break", Catch => "catch", Comptime => "comptime", Const => "const",
    Continue => "continue", Defer => "defer", Dyn => "dyn", Effect => "effect", Else => "else",
    Enum => "enum", Export => "export", Extends => "extends", Extern => "extern", False => "false",
    For => "for", Function => "function", Handle => "handle", If => "if", Impl => "impl",
    Import => "import", Interface => "interface", Let => "let", Match => "match", Mut => "mut",
    Once => "once", Readonly => "readonly", Region => "region", Return => "return",
    Struct => "struct", Throw => "throw", True => "true", Try => "try", Type => "type",
    Unsafe => "unsafe", Uses => "uses", While => "while", Yield => "yield",
}

// Longest first. `>>` and `<<` are deliberately absent: the parser joins adjacent `<`/`>` so
// that `Option<Ref<Scope>>` closes two type-argument lists.
const PUNCT: &[&str] = &[
    "...", "..", "=>", "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=",
    "^=", "{", "}", "(", ")", "[", "]", "<", ">", ",", ";", ":", ".", "=", "+", "-", "*", "/", "%",
    "&", "|", "^", "!", "?", "@", "~",
];

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

pub fn lex(source: &str) -> Result<Vec<Token>, Diagnostic> {
    lex_range(source, 0, source.len())
}

/// Lexes `source[start..end]`, producing spans relative to the whole source.
pub fn lex_range(source: &str, start: usize, end: usize) -> Result<Vec<Token>, Diagnostic> {
    let mut lx = Lexer { src: source, pos: start, end, out: Vec::new() };
    lx.run()?;
    Ok(lx.out)
}

struct Lexer<'a> {
    src: &'a str,
    pos: usize,
    end: usize,
    out: Vec<Token>,
}

impl<'a> Lexer<'a> {
    fn peek(&self) -> Option<char> {
        self.src[self.pos..self.end].chars().next()
    }

    fn peek_at(&self, n: usize) -> Option<char> {
        self.src[self.pos..self.end].chars().nth(n)
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    fn err(&self, start: usize, msg: impl Into<String>) -> Diagnostic {
        Diagnostic::new(Span::new(start, self.pos.max(start + 1)), msg)
    }

    fn push(&mut self, tok: Tok, start: usize) {
        self.out.push(Token { tok, span: Span::new(start, self.pos) });
    }

    fn run(&mut self) -> Result<(), Diagnostic> {
        loop {
            self.skip_trivia()?;
            let start = self.pos;
            let Some(c) = self.peek() else {
                self.push(Tok::Eof, start);
                return Ok(());
            };
            if c == 'b' && self.peek_at(1) == Some('\'') {
                self.pos += 2;
                let b = self.byte_char(start)?;
                if self.bump() != Some('\'') {
                    return Err(self.err(start, "unterminated byte literal"));
                }
                self.push(Tok::Byte(b), start);
            } else if c.is_alphabetic() || c == '_' {
                let word = self.word();
                let tok = match Kw::lookup(word) {
                    Some(kw) => Tok::Kw(kw),
                    None => Tok::Ident(word.to_string()),
                };
                self.push(tok, start);
            } else if c == '#' {
                self.bump();
                if !self.peek().is_some_and(|c| c.is_alphabetic() || c == '_') {
                    return Err(self.err(start, "expected a tag name after `#`"));
                }
                let name = self.word().to_string();
                self.push(Tok::Tag(name), start);
            } else if c.is_ascii_digit() {
                let tok = self.number();
                self.push(tok, start);
            } else if c == '"' {
                self.bump();
                let s = self.string(start, '"')?;
                self.push(Tok::Str(s), start);
            } else if c == '`' {
                self.bump();
                let parts = self.template(start)?;
                self.push(Tok::Template(parts), start);
            } else if let Some(p) = PUNCT.iter().find(|p| self.src[self.pos..self.end].starts_with(**p)) {
                self.pos += p.len();
                self.push(Tok::Punct(p), start);
            } else {
                self.bump();
                return Err(self.err(start, format!("unexpected character `{c}`")));
            }
        }
    }

    fn skip_trivia(&mut self) -> Result<(), Diagnostic> {
        loop {
            match (self.peek(), self.peek_at(1)) {
                (Some(c), _) if c.is_whitespace() => {
                    self.bump();
                }
                (Some('/'), Some('/')) => {
                    while self.peek().is_some_and(|c| c != '\n') {
                        self.bump();
                    }
                }
                (Some('/'), Some('*')) => {
                    let start = self.pos;
                    self.pos += 2;
                    loop {
                        match self.peek() {
                            None => return Err(self.err(start, "unterminated block comment")),
                            Some('*') if self.peek_at(1) == Some('/') => {
                                self.pos += 2;
                                break;
                            }
                            Some(_) => {
                                self.bump();
                            }
                        }
                    }
                }
                _ => return Ok(()),
            }
        }
    }

    fn word(&mut self) -> &'a str {
        let start = self.pos;
        while self.peek().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            self.bump();
        }
        &self.src[start..self.pos]
    }

    fn number(&mut self) -> Tok {
        let start = self.pos;
        if self.peek() == Some('0') && matches!(self.peek_at(1), Some('x' | 'b' | 'o')) {
            self.pos += 2;
            while self.peek().is_some_and(|c| c.is_ascii_hexdigit() || c == '_') {
                self.bump();
            }
            return Tok::Int(self.src[start..self.pos].replace('_', ""));
        }
        let digits = |lx: &mut Self| {
            while lx.peek().is_some_and(|c| c.is_ascii_digit() || c == '_') {
                lx.bump();
            }
        };
        digits(self);
        let mut float = false;
        // `0..8` is a range, not the float `0.` followed by `.8`.
        if self.peek() == Some('.') && self.peek_at(1).is_some_and(|c| c.is_ascii_digit()) {
            float = true;
            self.bump();
            digits(self);
        }
        if matches!(self.peek(), Some('e' | 'E'))
            && (self.peek_at(1).is_some_and(|c| c.is_ascii_digit())
                || (matches!(self.peek_at(1), Some('+' | '-')) && self.peek_at(2).is_some_and(|c| c.is_ascii_digit())))
        {
            float = true;
            self.bump();
            if matches!(self.peek(), Some('+' | '-')) {
                self.bump();
            }
            digits(self);
        }
        let text = self.src[start..self.pos].replace('_', "");
        if float { Tok::Float(text) } else { Tok::Int(text) }
    }

    fn escape(&mut self, start: usize) -> Result<char, Diagnostic> {
        match self.bump() {
            Some('n') => Ok('\n'),
            Some('t') => Ok('\t'),
            Some('r') => Ok('\r'),
            Some('0') => Ok('\0'),
            Some(c @ ('\\' | '\'' | '"' | '`' | '$')) => Ok(c),
            Some('u') if self.peek() == Some('{') => {
                self.bump();
                let from = self.pos;
                while self.peek().is_some_and(|c| c != '}') {
                    self.bump();
                }
                let hex = &self.src[from..self.pos];
                self.bump();
                u32::from_str_radix(hex, 16)
                    .ok()
                    .and_then(char::from_u32)
                    .ok_or_else(|| self.err(start, "invalid unicode escape"))
            }
            _ => Err(self.err(start, "invalid escape sequence")),
        }
    }

    fn byte_char(&mut self, start: usize) -> Result<u8, Diagnostic> {
        let c = match self.bump() {
            Some('\\') => self.escape(start)?,
            Some(c) => c,
            None => return Err(self.err(start, "unterminated byte literal")),
        };
        u8::try_from(u32::from(c)).map_err(|_| self.err(start, "byte literal must be ASCII"))
    }

    fn string(&mut self, start: usize, close: char) -> Result<String, Diagnostic> {
        let mut s = String::new();
        loop {
            match self.bump() {
                None => return Err(self.err(start, "unterminated string")),
                Some(c) if c == close => return Ok(s),
                Some('\\') => s.push(self.escape(start)?),
                Some(c) => s.push(c),
            }
        }
    }

    fn template(&mut self, start: usize) -> Result<Vec<TemplatePart>, Diagnostic> {
        let mut parts = Vec::new();
        let mut lit = String::new();
        loop {
            match self.bump() {
                None => return Err(self.err(start, "unterminated template literal")),
                Some('`') => break,
                Some('\\') => lit.push(self.escape(start)?),
                Some('$') if self.peek() == Some('{') => {
                    self.bump();
                    parts.push(TemplatePart::Lit(std::mem::take(&mut lit)));
                    let from = self.pos;
                    self.skip_balanced(start)?;
                    parts.push(TemplatePart::Expr(Span::new(from, self.pos - 1)));
                }
                Some(c) => lit.push(c),
            }
        }
        parts.push(TemplatePart::Lit(lit));
        Ok(parts)
    }

    /// Skips to just past the `}` closing an interpolation, honouring nested braces and strings.
    fn skip_balanced(&mut self, start: usize) -> Result<(), Diagnostic> {
        let mut depth = 1;
        while depth > 0 {
            match self.bump() {
                None => return Err(self.err(start, "unterminated template interpolation")),
                Some('{') => depth += 1,
                Some('}') => depth -= 1,
                Some(q @ ('"' | '\'')) => {
                    self.string(start, q)?;
                }
                Some('`') => {
                    self.template(start)?;
                }
                Some(_) => {}
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(s: &str) -> Vec<Tok> {
        lex(s).unwrap().into_iter().map(|t| t.tok).collect()
    }

    #[test]
    fn ranges_are_not_floats() {
        assert_eq!(
            toks("raw[0..8]"),
            vec![
                Tok::Ident("raw".into()),
                Tok::Punct("["),
                Tok::Int("0".into()),
                Tok::Punct(".."),
                Tok::Int("8".into()),
                Tok::Punct("]"),
                Tok::Eof
            ]
        );
    }

    #[test]
    fn tags_bytes_and_numbers() {
        assert_eq!(
            toks("#Some(b'n') 0x5eed 1_000 2.5e3"),
            vec![
                Tok::Tag("Some".into()),
                Tok::Punct("("),
                Tok::Byte(b'n'),
                Tok::Punct(")"),
                Tok::Int("0x5eed".into()),
                Tok::Int("1000".into()),
                Tok::Float("2.5e3".into()),
                Tok::Eof
            ]
        );
    }

    #[test]
    fn templates_record_interpolation_spans() {
        let src = "`${a.b} and ${ {x: 1}.x }`";
        let Tok::Template(parts) = &lex(src).unwrap()[0].tok else { panic!() };
        let exprs: Vec<&str> = parts
            .iter()
            .filter_map(|p| match p {
                TemplatePart::Expr(s) => Some(&src[s.start..s.end]),
                TemplatePart::Lit(_) => None,
            })
            .collect();
        assert_eq!(exprs, vec!["a.b", " {x: 1}.x "]);
    }

    #[test]
    fn contextual_keywords_are_identifiers() {
        assert_eq!(toks("from of with row")[..4], [
            Tok::Ident("from".into()),
            Tok::Ident("of".into()),
            Tok::Ident("with".into()),
            Tok::Ident("row".into())
        ]);
    }
}
