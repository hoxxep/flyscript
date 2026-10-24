//! The machine-checked proof of the core (`proof/`, spec §9): Lean checks it, and its theorems rest
//! on Lean's standard axioms alone — no `sorry`, no axiom of the proof's own. And the programs of
//! the run corpus in λ-fly's part of the language, each marked `// core: f`, are certified: the
//! compiler elaborates what `f` reaches into λ-fly (`--core=f`), and the proof's checker, proved
//! sound, accepts it. Without Lean (`lake` on the path, or in `~/.elan/bin`) the test says so and
//! passes.

use std::path::{Path, PathBuf};
use std::process::Command;

fn lake() -> Option<PathBuf> {
    let home = std::env::var("HOME").unwrap_or_default();
    [PathBuf::from("lake"), Path::new(&home).join(".elan/bin/lake")]
        .into_iter()
        .find(|candidate| Command::new(candidate).arg("--version").output().is_ok_and(|o| o.status.success()))
}

#[test]
fn the_core_is_proved() {
    let Some(lake) = lake() else {
        eprintln!("no Lean: the proof is not checked");
        return;
    };
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("proof");
    let built = Command::new(&lake).arg("build").current_dir(&dir).output().unwrap();
    assert!(built.status.success(), "the proof does not check:\n{}{}", String::from_utf8_lossy(&built.stdout), String::from_utf8_lossy(&built.stderr));
    // Nothing assumed in the sources.
    for entry in std::fs::read_dir(dir.join("FlyCore")).unwrap() {
        let path = entry.unwrap().path();
        let text = std::fs::read_to_string(&path).unwrap();
        for word in ["sorry", "admit", "axiom ", "native_decide"] {
            assert!(!text.contains(word), "{} uses `{word}`", path.display());
        }
    }
    let axioms = Command::new(&lake).args(["env", "lean", "Axioms.lean"]).current_dir(&dir).output().unwrap();
    let out = String::from_utf8_lossy(&axioms.stdout).to_string() + &String::from_utf8_lossy(&axioms.stderr);
    assert!(axioms.status.success(), "{out}");
    for line in out.lines().filter(|l| l.contains("depends on axioms")) {
        let list = line.split('[').nth(1).unwrap_or("").trim_end_matches(']');
        for ax in list.split(',').map(str::trim) {
            assert!(["propext", "Classical.choice", "Quot.sound"].contains(&ax), "{line}");
        }
    }
    assert!(out.contains("depends on axioms") || out.contains("does not depend on any axioms"), "{out}");

    // The corpus's programs in λ-fly's part, certified.
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let out_dir = root.join("target/proof-core");
    std::fs::create_dir_all(&out_dir).unwrap();
    let mut certified = 0;
    let mut files: Vec<PathBuf> = std::fs::read_dir(root.join("tests/run")).unwrap().map(|e| e.unwrap().path()).collect();
    files.sort();
    for file in files {
        let text = std::fs::read_to_string(&file).unwrap();
        let Some(f) = text.lines().find_map(|l| l.strip_prefix("// core: ")) else { continue };
        let name = file.file_stem().unwrap().to_string_lossy().to_string();
        let lean = out_dir.join(format!("{name}.lean"));
        let made = Command::new("node").arg("--stack-size=65500").arg(root.join("selfhost/seed.js")).arg(&file).arg(&lean).arg(root).arg(format!("--core={f}")).output().unwrap();
        assert!(made.status.success() && made.stdout.is_empty(), "{name} is not in λ-fly's part:\n{}{}", String::from_utf8_lossy(&made.stdout), String::from_utf8_lossy(&made.stderr));
        let mut source = std::fs::read_to_string(&lean).unwrap();
        source.push_str("#print axioms checks\n");
        std::fs::write(&lean, source).unwrap();
        let checked = Command::new(&lake).arg("env").arg("lean").arg(&lean).current_dir(&dir).output().unwrap();
        let said = String::from_utf8_lossy(&checked.stdout).to_string() + &String::from_utf8_lossy(&checked.stderr);
        assert!(checked.status.success(), "{name} is not certified:\n{said}");
        for line in said.lines().filter(|l| l.contains("depends on axioms")) {
            let list = line.split('[').nth(1).unwrap_or("").trim_end_matches(']');
            for ax in list.split(',').map(str::trim) {
                assert!(["propext", "Classical.choice", "Quot.sound"].contains(&ax), "{name}: {line}");
            }
        }
        certified += 1;
    }
    assert!(certified >= 3, "the certified corpus is missing");
}
