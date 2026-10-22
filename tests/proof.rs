//! The machine-checked proof of the core (`proof/`, spec §9): Lean checks it, and its theorems rest
//! on Lean's standard axioms alone — no `sorry`, no axiom of the proof's own. Without Lean (`lake`
//! on the path, or in `~/.elan/bin`) the test says so and passes.

use std::path::{Path, PathBuf};
use std::process::Command;

fn lake() -> Option<PathBuf> {
    let home = std::env::var("HOME").unwrap_or_default();
    for candidate in [PathBuf::from("lake"), Path::new(&home).join(".elan/bin/lake")] {
        if Command::new(&candidate).arg("--version").output().is_ok_and(|o| o.status.success()) {
            return Some(candidate);
        }
    }
    None
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
}
