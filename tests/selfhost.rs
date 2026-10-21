//! The self-hosted compiler (selfhost/) compiles itself to JavaScript, and the JavaScript compiles
//! the same source to the same file.

use std::path::Path;
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
    let (main, runtime) = (dir.join("main.fly"), dir.join("runtime.js"));
    let (stage1, stage2) = (out.join("stage1.js"), out.join("stage2.js"));

    let checked = check_files(std::slice::from_ref(&main));
    assert!(checked.errors.is_empty(), "{}", checked.render().join("\n"));
    let text = |p: &Path| Value::text(p.to_str().unwrap());
    let mut world = World::default();
    world.real_fs = true;
    let (result, world) = run(checked.program, "main", vec![text(&main), text(&stage1), text(&runtime)], world);
    assert!(result.is_ok(), "{:?}", result.err());
    assert!(world.out.is_empty(), "{}", world.out.join("\n"));
    let first = std::fs::read(&stage1).unwrap();

    // Stage 2 needs node; without it, stage 1 is as far as this test goes.
    let Ok(status) = Command::new("node").arg(&stage1).arg(&main).arg(&stage2).arg(&runtime).status() else { return };
    assert!(status.success());
    assert!(std::fs::read(&stage2).unwrap() == first, "stage 2 differs from stage 1");
}
