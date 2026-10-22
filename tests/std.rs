//! Every standard-library declaration file parses.

use std::fs;
use std::path::Path;

use flyscript::syntax::parse_declarations;

#[test]
fn std_declarations_parse() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("std");
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        let source = fs::read_to_string(&path).unwrap();
        if let Err(d) = parse_declarations(&source) {
            panic!("{}", d.render(&path.display().to_string(), &source));
        }
    }
}

/// The names a library file exports, each with the line declaring it.
fn exports(source: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for line in source.lines() {
        let Some(rest) = line.trim_start().strip_prefix("export ") else { continue };
        let rest = rest.strip_prefix("view ").unwrap_or(rest);
        let Some((kind, rest)) = rest.split_once(' ') else { continue };
        if !matches!(kind, "function" | "struct" | "type" | "interface" | "effect" | "enum") {
            continue;
        }
        let name: String = rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
        if !name.is_empty() {
            out.push((name, line.trim().to_string()));
        }
    }
    out
}

/// The standard library is specified as carefully as the core: every name it exports is in its
/// specification, `docs/std.md`, in code.
#[test]
fn std_reference_covers_every_export() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let doc = fs::read_to_string(root.join("docs/std.md")).unwrap();
    // The words of every code span in the document.
    let mut words = std::collections::HashSet::new();
    for (i, span) in doc.split('`').enumerate() {
        if i % 2 == 1 {
            for w in span.split(|c: char| !(c.is_alphanumeric() || c == '_')) {
                words.insert(w.to_string());
            }
        }
    }
    let mut missing = Vec::new();
    for entry in fs::read_dir(root.join("std")).unwrap() {
        let path = entry.unwrap().path();
        let source = fs::read_to_string(&path).unwrap();
        for (name, line) in exports(&source) {
            if !words.contains(&name) {
                missing.push(format!("{}: {line}", path.file_name().unwrap().to_string_lossy()));
            }
        }
    }
    assert!(missing.is_empty(), "exported but not specified in docs/std.md:\n{}", missing.join("\n"));
}
