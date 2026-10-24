//! `fly`, the package tool (docs/fly.md), end to end: a package made, built, run and tested; a
//! dependency from git added, locked, and held to its lock — an update that performs `Io` where
//! the version accepted did not, or vouches for unchecked code, stops the build until accepted,
//! and files changed after they were fetched stop it too; two builds from one lockfile the same;
//! and the example site and the compiler built from their manifests.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn has(program: &str) -> bool {
    Command::new(program).arg("--version").output().is_ok_and(|o| o.status.success())
}

/// A directory of its own for this test, emptied.
fn scratch(name: &str) -> PathBuf {
    let dir = root().join("target/fly-test").join(name);
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn fly(dir: &Path, home: &Path, args: &[&str]) -> Output {
    // The launcher builds the tool and the compiler when they are stale: once, before any test
    // runs it, so that two tests never build them at once.
    static BUILT: std::sync::Once = std::sync::Once::new();
    BUILT.call_once(|| {
        let o = Command::new(root().join("fly")).output().unwrap();
        assert!(o.status.success(), "{}", said(&o));
    });
    Command::new(root().join("fly")).args(args).current_dir(dir).env("FLY_HOME", home).output().unwrap()
}

fn said(o: &Output) -> String {
    format!("{}{}", String::from_utf8_lossy(&o.stdout), String::from_utf8_lossy(&o.stderr))
}

fn ok(o: Output) -> String {
    assert!(o.status.success(), "{}", said(&o));
    said(&o)
}

fn git(dir: &Path, args: &[&str]) {
    let o = Command::new("git").args(["-c", "user.email=fly@example.com", "-c", "user.name=fly"]).args(args).current_dir(dir).output().unwrap();
    assert!(o.status.success(), "git {args:?}: {}", said(&o));
}

/// A release of the library `json`: its module, committed and tagged.
fn release(repo: &Path, tag: &str, module: &str) {
    std::fs::write(repo.join("parse.fly"), module).unwrap();
    git(repo, &["add", "-A"]);
    git(repo, &["commit", "-qm", tag]);
    git(repo, &["tag", tag]);
}

#[test]
fn builds_packages_and_holds_dependencies_to_their_lock() {
    if !has("git") || !has("cc") || !has("node") {
        return;
    }
    let dir = scratch("packages");
    let home = dir.join("home");
    let repo = dir.join("json");
    std::fs::create_dir_all(&repo).unwrap();
    git(&repo, &["init", "-q"]);
    std::fs::write(repo.join("fly.toml"), "[package]\nname = \"json\"\nversion = \"1.0.0\"\nkind = \"lib\"\n").unwrap();
    release(&repo, "v1.0.0", "// How long a document is.\nexport function size(s: str): usize { s.len() }\n");

    ok(fly(&dir, &home, &["new", "app"]));
    let app = dir.join("app");
    assert_eq!(ok(fly(&app, &home, &["run"])), "Hello from app!\n");
    assert!(ok(fly(&app, &home, &["test"])).contains("1/1 passed"));

    std::fs::write(app.join("main.fly"), "import { println } from \"std/io\";\nimport { size } from \"json/parse\";\n\nexport function main(): void uses Io {\n  println(`${size(\"four\")}`);\n}\n").unwrap();
    let url = format!("file://{}", repo.display());
    assert!(ok(fly(&app, &home, &["add", "json", &url])).contains(&format!("added json = {{ git = \"{url}\", version = \"1.0\" }}")));
    let lock = std::fs::read_to_string(app.join("fly.lock")).unwrap();
    assert!(lock.contains("version = \"1.0.0\"") && lock.contains("unsafe = false") && lock.contains("\"parse size:\""), "{lock}");
    assert_eq!(ok(fly(&app, &home, &["run"])), "4\n");

    // A failing test fails `fly test`.
    std::fs::write(app.join("tests/wrong.fly"), "// expect: right\nimport { println } from \"std/io\";\nexport function main(): void uses Io { println(\"wrong\"); }\n").unwrap();
    let t = fly(&app, &home, &["test"]);
    assert!(!t.status.success() && said(&t).contains("FAIL wrong") && said(&t).contains("1/2 passed"), "{}", said(&t));
    std::fs::remove_file(app.join("tests/wrong.fly")).unwrap();

    // An update that performs `Io` where the version accepted did not stops the build until it
    // is accepted.
    release(&repo, "v1.1.0", "import { println } from \"std/io\";\nexport function size(s: str): usize { s.len() }\nexport function report(s: str): void uses Io { println(s); }\n");
    let u = fly(&app, &home, &["update"]);
    assert!(!u.status.success(), "{}", said(&u));
    assert!(said(&u).contains("json 1.1.0 performs what the version accepted did not:\n    parse report now performs Io"), "{}", said(&u));
    let b = fly(&app, &home, &["build"]);
    assert!(!b.status.success() && said(&b).contains("parse report now performs Io"), "{}", said(&b));
    ok(fly(&app, &home, &["accept", "json"]));
    ok(fly(&app, &home, &["build"]));
    assert!(std::fs::read_to_string(app.join("fly.lock")).unwrap().contains("\"parse report: Io\""));

    // So does one that vouches for code the compiler cannot check.
    release(&repo, "v1.2.0", "extern \"C\" function abs(x: i32): i32;\nexport function size(s: str): usize { s.len() }\nexport function magnitude(x: i32): i32 { unsafe { abs(x) } }\n");
    let u = fly(&app, &home, &["update"]);
    assert!(!u.status.success() && said(&u).contains("parse now vouches for code the compiler cannot check"), "{}", said(&u));
    ok(fly(&app, &home, &["accept", "json"]));

    // Files changed after they were fetched are not what the lock says.
    let lock = std::fs::read_to_string(app.join("fly.lock")).unwrap();
    let commit = lock.lines().find_map(|l| l.strip_prefix("commit = \"")).unwrap().trim_end_matches('"').to_string();
    let fetched = home.join("packages").join(format!("json-{}", &commit[..12])).join("parse.fly");
    let original = std::fs::read_to_string(&fetched).unwrap();
    std::fs::write(&fetched, format!("{original}// changed\n")).unwrap();
    let b = fly(&app, &home, &["build"]);
    assert!(!b.status.success() && said(&b).contains("is not what fly.lock says"), "{}", said(&b));
    std::fs::write(&fetched, original).unwrap();

    // Two builds from one lockfile, the second fetching afresh, are the same.
    ok(fly(&app, &home, &["build"]));
    let first = std::fs::read(app.join("target/app")).unwrap();
    std::fs::remove_dir_all(app.join("target")).unwrap();
    ok(fly(&app, &dir.join("home2"), &["build"]));
    assert!(first == std::fs::read(app.join("target/app")).unwrap(), "two builds from one lockfile differ");
}

#[test]
fn builds_the_example_site_and_the_compiler_from_their_manifests() {
    if !has("cc") || !has("node") {
        return;
    }
    let home = scratch("manifests");
    let site = root().join("examples/todo");
    assert!(ok(fly(&site, &home, &["build"])).starts_with("built todo"));
    for f in ["target/site/server", "target/site/_fly/app.wasm", "target/site/_fly/flynext.js"] {
        assert!(site.join(f).exists(), "the site's build has no {f}");
    }
    let compiler = root().join("selfhost");
    assert!(ok(fly(&compiler, &home, &["build"])).starts_with("built flyc"));
    // The compiler fly built compiles the compiler to what the launcher's does.
    let (a, b) = (home.join("a.c"), home.join("b.c"));
    for (exe, out) in [(compiler.join("target/flyc"), &a), (root().join("target/fly/flyc"), &b)] {
        let o = Command::new(exe).arg(compiler.join("main.fly")).arg(out).arg(root()).output().unwrap();
        assert!(o.status.success(), "{}", said(&o));
    }
    assert!(std::fs::read(a).unwrap() == std::fs::read(b).unwrap());
}
