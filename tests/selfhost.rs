//! The self-hosted compiler (selfhost/) compiles itself to JavaScript, and the JavaScript compiles
//! the same source to the same file.

use std::path::{Path, PathBuf};
use std::process::Command;

use flyscript::check::check_files;
use flyscript::eval::{Value, World, run};

#[test]
fn selfhost_reaches_a_fixpoint() {
    // The interpreter recurses as deeply as the program it runs; a debug build's frames are large.
    std::thread::Builder::new().stack_size(1 << 30).spawn(fixpoint).unwrap().join().unwrap();
}

fn fixpoint() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let dir = root.join("selfhost");
    let out = root.join("target/selfhost-test");
    std::fs::create_dir_all(&out).unwrap();
    let main = dir.join("main.fly");
    let (stage1, stage2) = (out.join("stage1.js"), out.join("stage2.js"));

    let checked = check_files(std::slice::from_ref(&main));
    assert!(checked.errors.is_empty(), "{}", checked.render().join("\n"));
    let text = |p: &Path| Value::text(p.to_str().unwrap());
    let mut world = World::default();
    world.real_fs = true;
    let (result, world) = run(checked.program, "main", vec![text(&main), text(&stage1), text(root)], world);
    assert!(result.is_ok(), "{:?}", result.err());
    assert!(world.out.is_empty(), "{}", world.out.join("\n"));
    let first = std::fs::read(&stage1).unwrap();

    // Stage 2 needs node; without it, stage 1 is as far as this test goes.
    let Ok(status) = Command::new("node").arg(&stage1).arg(&main).arg(&stage2).arg(root).status() else { return };
    assert!(status.success());
    assert!(std::fs::read(&stage2).unwrap() == first, "stage 2 differs from stage 1");
    elaborates_as_flyc_does(root, &stage1, &out);
    checks_as_flyc_does(root, &stage1, &out);
}

/// The programs a quarter of the corpus samples, for time.
fn sample(root: &Path) -> Vec<PathBuf> {
    let mut programs: Vec<PathBuf> = Vec::new();
    for dir in ["tests/run", "tests/accept", "tests/reject", "examples"] {
        let mut files: Vec<PathBuf> = std::fs::read_dir(root.join(dir)).unwrap().map(|e| e.unwrap().path()).collect();
        files.sort();
        for f in files {
            let f = if f.is_dir() { f.join("main.fly") } else { f };
            if f.extension().is_some_and(|e| e == "fly") && f.exists() {
                programs.push(f);
            }
        }
    }
    programs.into_iter().step_by(4).collect()
}

/// The self-hosted checker reports what the Rust prototype's type and effect checker reports:
/// `flyc types` and selfhost/typecheck.fly print the same diagnostics.
fn checks_as_flyc_does(root: &Path, compiler: &Path, out: &Path) {
    let typecheck = out.join("typecheck.js");
    let status = Command::new("node")
        .arg(compiler)
        .arg(root.join("selfhost/typecheck.fly"))
        .arg(&typecheck)
        .arg(root)
        .status()
        .unwrap();
    assert!(status.success());
    let mut differ = Vec::new();
    for f in sample(root) {
        let mut p = flyscript::check::env::Program::load(std::slice::from_ref(&f));
        let mut fid = 0;
        while fid < p.fns.len() {
            flyscript::check::expr::check_fn(&mut p, fid);
            fid += 1;
        }
        let rust: Vec<String> = p.diags.iter().map(|(m, d)| format!("error {m} {}..{}: {}", d.span.start, d.span.end, d.message)).collect();
        let js = Command::new("node").arg(&typecheck).arg(&f).arg(root.join("std")).output().unwrap();
        if String::from_utf8_lossy(&js.stdout).trim_end() != rust.join("\n") {
            differ.push(f.display().to_string());
        }
    }
    assert!(differ.is_empty(), "checked differently:\n{}", differ.join("\n"));
}

/// The self-hosted checker elaborates programs' declarations as the Rust prototype does:
/// `flyc schemes` and selfhost/schemes.fly print the same lines. A quarter of the programs are
/// compared, for time.
fn elaborates_as_flyc_does(root: &Path, compiler: &Path, out: &Path) {
    let schemes = out.join("schemes.js");
    let status = Command::new("node")
        .arg(compiler)
        .arg(root.join("selfhost/schemes.fly"))
        .arg(&schemes)
        .arg(root)
        .status()
        .unwrap();
    assert!(status.success());
    let mut differ = Vec::new();
    for f in sample(root) {
        let rust = flyscript::check::env::describe(&flyscript::check::env::Program::load(std::slice::from_ref(&f))).join("\n");
        let js = Command::new("node").arg(&schemes).arg(&f).arg(root.join("std")).output().unwrap();
        if String::from_utf8_lossy(&js.stdout).trim_end() != rust {
            differ.push(f.display().to_string());
        }
    }
    assert!(differ.is_empty(), "elaborated differently:\n{}", differ.join("\n"));
}

