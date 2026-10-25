//! Every program in docs/spec.md is mirrored in examples/, every example must parse, and so must
//! every fragment of code the spec shows.

use std::fs;
use std::path::Path;

use flyscript::syntax::{parse_declarations, parse_module};

/// Spec section heading prefix → example file. The appendix and §10.2 are complete modules.
const PROGRAMS: &[(&str, &str)] = &[
    ("### 10.2 ", "http_handler"),
    ("### A.1 ", "json"),
    ("### A.2 ", "word_count"),
    ("### A.3 ", "iteration"),
    ("### A.4 ", "particles"),
    ("### A.5 ", "symbol_table"),
    ("### A.6 ", "kv_actor"),
    ("### A.7 ", "server"),
    ("### A.8 ", "counter_ui"),
    ("### A.9 ", "derive_json"),
    ("### A.10 ", "inventory"),
    ("### A.11 ", "limiter"),
];

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

/// The first ```ts block after the heading that starts with `heading`.
fn spec_program(spec: &str, heading: &str) -> String {
    let at = spec
        .lines()
        .position(|l| l.starts_with(heading))
        .unwrap_or_else(|| panic!("spec has no heading `{heading}`"));
    let rest: Vec<&str> = spec.lines().skip(at).collect();
    let open = rest.iter().position(|l| *l == "```ts").expect("a ts code block");
    let close = open + 1 + rest[open + 1..].iter().position(|l| *l == "```").expect("closing fence");
    rest[open + 1..close].iter().map(|l| format!("{l}\n")).collect()
}

#[test]
fn examples_match_the_spec() {
    let spec = fs::read_to_string(root().join("docs/spec.md")).unwrap();
    for (heading, name) in PROGRAMS {
        let file = root().join(format!("examples/{name}.fly"));
        let example = fs::read_to_string(&file).unwrap();
        assert_eq!(example, spec_program(&spec, heading), "{} differs from spec `{heading}`", file.display());
    }
}

#[test]
fn examples_parse() {
    for entry in fs::read_dir(root().join("examples")).unwrap() {
        let path = entry.unwrap().path();
        // A directory is a program of several modules: each parses.
        let files: Vec<_> = if path.is_dir() { fs::read_dir(&path).unwrap().map(|e| e.unwrap().path()).collect() } else { vec![path] };
        for path in files.into_iter().filter(|p| p.extension().is_some_and(|e| e == "fly")) {
            let source = fs::read_to_string(&path).unwrap();
            if let Err(d) = parse_module(&source) {
                panic!("{}", d.render(&path.display().to_string(), &source));
            }
        }
    }
}

/// A fragment parses as a module, as declarations (signatures ending in `;`, as `.d.fly` files are
/// written), as statements, or as declarations followed by statements: what the spec shows of a
/// library and then a use of it. `…` marks what a fragment leaves out.
fn fragment_parses(code: &str) -> bool {
    let code = code.replace('…', "");
    let stmts = |s: &str| parse_module(&format!("function f(): void {{\n{s}\n}}\n")).is_ok();
    let decls = |s: &str| parse_declarations(s).is_ok() || parse_declarations(&format!("{s};")).is_ok();
    if parse_module(&code).is_ok() || decls(&code) || stmts(&code) {
        return true;
    }
    let lines: Vec<&str> = code.lines().collect();
    (1..lines.len()).any(|k| decls(&lines[..k].join("\n")) && stmts(&lines[k..].join("\n")))
}

#[test]
fn spec_fragments_parse() {
    let spec = fs::read_to_string(root().join("docs/spec.md")).unwrap();
    let lines: Vec<&str> = spec.lines().collect();
    let mut bad = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        if lines[i] == "```ts" {
            let close = i + 1 + lines[i + 1..].iter().position(|l| *l == "```").expect("closing fence");
            let code = lines[i + 1..close].join("\n");
            if !fragment_parses(&code) {
                bad.push(format!("docs/spec.md:{}", i + 1));
            }
            i = close;
        }
        i += 1;
    }
    assert!(bad.is_empty(), "these fragments do not parse:\n{}", bad.join("\n"));
}
