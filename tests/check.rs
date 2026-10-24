//! The checker accepts every example and rejects every program in tests/reject/, each with the
//! error named on its first line (`// error: <text>`).

use std::fs;
use std::path::{Path, PathBuf};

use flyscript::check::check_files;

mod common;
use common::on_every_core;

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn files(dir: &str) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = fs::read_dir(root().join(dir)).unwrap().map(|e| e.unwrap().path()).collect();
    v.sort();
    v
}

#[test]
fn examples_and_acceptance_programs_check() {
    let programs: Vec<PathBuf> = files("examples").into_iter().chain(files("tests/accept")).collect();
    on_every_core(&programs, |path| {
        // A directory is a program of several modules, entered at its `main.fly`.
        let path = if path.is_dir() { path.join("main.fly") } else { path.clone() };
        if !path.exists() {
            return;
        }
        let checked = check_files(std::slice::from_ref(&path));
        assert!(checked.errors.is_empty(), "{} should check:\n{}", path.display(), checked.render().join("\n\n"));
    });
}

#[test]
fn bad_programs_are_rejected() {
    let failures: Vec<String> = on_every_core(&files("tests/reject"), |path| {
        let source = fs::read_to_string(path).unwrap();
        let expected = source
            .lines()
            .next()
            .and_then(|l| l.strip_prefix("// error: "))
            .unwrap_or_else(|| panic!("{} must start with `// error: …`", path.display()))
            .trim()
            .to_string();
        let checked = check_files(std::slice::from_ref(path));
        let rendered = checked.render();
        (!rendered.iter().any(|e| e.contains(&expected))).then(|| {
            format!(
                "{}: expected an error containing `{expected}`, got:\n{}",
                path.display(),
                if rendered.is_empty() { "(no errors)".to_string() } else { rendered.join("\n") }
            )
        })
    })
    .into_iter()
    .flatten()
    .collect();
    assert!(failures.is_empty(), "\n{}", failures.join("\n\n"));
}
