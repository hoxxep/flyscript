//! The self-hosted compiler (selfhost/) compiles itself to JavaScript at a fixpoint, and compiles
//! programs as the Rust prototype runs them. `selfhost/seed.js` is the compiler compiled by
//! itself: the reference implementation, running the compiler's source, must produce it, and it
//! must reproduce itself. Compiled to C, it is a native compiler at a fixpoint too. The tests that
//! run JavaScript need node, and those that build C a C compiler; without them they stop early.

use std::path::{Path, PathBuf};
use std::process::Command;

use flyscript::check::check_files;
use flyscript::eval::{Value, World, run};

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn out() -> PathBuf {
    let out = root().join("target/selfhost-test");
    std::fs::create_dir_all(&out).unwrap();
    out
}

fn has_node() -> bool {
    Command::new("node").arg("--version").output().is_ok()
}

/// Compiles `entry` to `js` with a compiled compiler.
fn compile(compiler: &Path, entry: &Path, js: &Path) {
    let r = Command::new("node").arg("--stack-size=65500").arg(compiler).arg(entry).arg(js).arg(root()).output().unwrap();
    assert!(r.status.success() && r.stdout.is_empty(), "{}{}", String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
}

#[test]
fn seed_reproduces_itself() {
    if !has_node() {
        return;
    }
    let seed = root().join("selfhost/seed.js");
    let again = out().join("seed-again.js");
    compile(&seed, &root().join("selfhost/main.fly"), &again);
    assert!(std::fs::read(&again).unwrap() == std::fs::read(&seed).unwrap(), "the seed is stale: run selfhost/bootstrap.sh --update-seed");
}

fn has_cc() -> bool {
    Command::new("cc").arg("--version").output().is_ok()
}

/// The compiler compiled to C and built is a native compiler, which compiles itself to the same C,
/// and to the seed.
#[test]
fn compiles_itself_natively() {
    if !has_node() || !has_cc() {
        return;
    }
    let main = root().join("selfhost/main.fly");
    let c = out().join("native.c");
    compile(&root().join("selfhost/seed.js"), &main, &c);
    let exe = out().join("native");
    let built = Command::new("cc").args(["-std=gnu11", "-O1", "-w", "-o"]).arg(&exe).arg(&c).arg("-lm").output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    for (name, want) in [("native-again.c", &c), ("native.js", &root().join("selfhost/seed.js"))] {
        let again = out().join(name);
        let r = Command::new(&exe).arg(&main).arg(&again).arg(root()).output().unwrap();
        assert!(r.status.success() && r.stdout.is_empty(), "{}{}", String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
        assert!(std::fs::read(&again).unwrap() == std::fs::read(want).unwrap(), "the native compiler makes other than {}", want.display());
    }
}

/// The slowest check, the interpreter running the whole compiler on itself: run it with
/// `cargo test -- --ignored`, as before a release, or `selfhost/bootstrap.sh --from-flyc`.
#[test]
#[ignore = "runs the compiler in the interpreter for minutes"]
fn flyc_builds_the_seed() {
    // The interpreter recurses as deeply as the program it runs.
    std::thread::Builder::new().stack_size(1 << 30).spawn(build_with_flyc).unwrap().join().unwrap();
}

fn build_with_flyc() {
    let main = root().join("selfhost/main.fly");
    let stage1 = out().join("stage1.js");
    let checked = check_files(std::slice::from_ref(&main));
    assert!(checked.errors.is_empty(), "{}", checked.render().join("\n"));
    let text = |p: &Path| Value::text(p.to_str().unwrap());
    let mut world = World::default();
    world.real_fs = true;
    let (result, world) = run(checked.program, "main", vec![text(&main), text(&stage1), text(root())], world);
    assert!(result.is_ok(), "{:?}", result.err());
    assert!(world.out.is_empty(), "{}", world.out.join("\n"));
    let seed = std::fs::read(root().join("selfhost/seed.js")).unwrap();
    assert!(std::fs::read(&stage1).unwrap() == seed, "flyc compiles the compiler to other than the seed: run selfhost/bootstrap.sh --update-seed");
}

/// Every program of the test suite and the examples.
fn programs() -> Vec<PathBuf> {
    let mut programs: Vec<PathBuf> = Vec::new();
    for dir in ["tests/run", "tests/accept", "tests/reject", "examples"] {
        let mut files: Vec<PathBuf> = std::fs::read_dir(root().join(dir)).unwrap().map(|e| e.unwrap().path()).collect();
        files.sort();
        for f in files {
            let f = if f.is_dir() { f.join("main.fly") } else { f };
            if f.extension().is_some_and(|e| e == "fly") && f.exists() {
                programs.push(f);
            }
        }
    }
    programs
}

/// The self-hosted checker reports what the Rust prototype's reports: `flyc check` and
/// selfhost/typecheck.fly print the same diagnostics, of types and effects and then of ownership.
/// Ownership's are compared as a set: each pass meets some bindings in a hash map's order.
#[test]
fn checks_as_flyc_does() {
    if !has_node() {
        return;
    }
    let typecheck = out().join("typecheck.js");
    compile(&root().join("selfhost/seed.js"), &root().join("selfhost/typecheck.fly"), &typecheck);
    let mut differ = Vec::new();
    for f in programs() {
        let mut p = flyscript::check::env::Program::load(std::slice::from_ref(&f));
        let mut fid = 0;
        while fid < p.fns.len() {
            flyscript::check::expr::check_fn(&mut p, fid);
            fid += 1;
        }
        if p.diags.is_empty() {
            for fid in 0..p.fns.len() {
                flyscript::check::own::check_function(&mut p, fid);
            }
        }
        let mut rust: Vec<String> = p.diags.iter().map(|(m, d)| format!("error {m} {}..{}: {}", d.span.start, d.span.end, d.message)).collect();
        let js = Command::new("node").arg("--stack-size=65500").arg(&typecheck).arg(&f).arg(root().join("std")).output().unwrap();
        let mut ours: Vec<String> = String::from_utf8_lossy(&js.stdout).lines().map(str::to_string).collect();
        rust.sort();
        ours.sort();
        if ours != rust {
            differ.push(format!("{}\n  flyc: {rust:?}\n  ours: {ours:?}", f.display()));
        }
    }
    assert!(differ.is_empty(), "checked differently:\n{}", differ.join("\n"));
}

/// The self-hosted checker elaborates programs' declarations as the Rust prototype does:
/// `flyc schemes` and selfhost/schemes.fly print the same lines.
#[test]
fn elaborates_as_flyc_does() {
    if !has_node() {
        return;
    }
    let schemes = out().join("schemes.js");
    compile(&root().join("selfhost/seed.js"), &root().join("selfhost/schemes.fly"), &schemes);
    let mut differ = Vec::new();
    for f in programs() {
        let rust = flyscript::check::env::describe(&flyscript::check::env::Program::load(std::slice::from_ref(&f))).join("\n");
        let js = Command::new("node").arg("--stack-size=65500").arg(&schemes).arg(&f).arg(root().join("std")).output().unwrap();
        if String::from_utf8_lossy(&js.stdout).trim_end() != rust {
            differ.push(f.display().to_string());
        }
    }
    assert!(differ.is_empty(), "elaborated differently:\n{}", differ.join("\n"));
}

/// The run suite's programs, compiled to JavaScript, print what they expect, as they do run by
/// `flyc`, against the same simulated world.
#[test]
fn compiled_programs_run_as_expected() {
    if !has_node() {
        return;
    }
    let r = Command::new("sh").arg(root().join("selfhost/corpus.sh")).arg(root().join("selfhost/seed.js")).output().unwrap();
    let report = String::from_utf8_lossy(&r.stdout);
    let failed: Vec<&str> = report.lines().filter_map(|l| l.strip_prefix("FAIL ")).collect();
    assert!(failed.is_empty(), "failed compiled:\n{}", failed.join("\n"));
}
