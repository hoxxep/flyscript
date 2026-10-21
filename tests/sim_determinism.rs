//! Deterministic simulation (§6.4): the same seed reproduces a run exactly; different seeds
//! explore different fault schedules.

use flyscript::check::check_files;
use flyscript::eval::{World, run};

fn transcript(seed: u64) -> Vec<String> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/run/http_simulation.fly");
    let checked = check_files(&[path]);
    assert!(checked.errors.is_empty(), "{}", checked.render().join("\n"));
    let mut world = World::seeded(seed);
    world.fault_percent = 25;
    world.profiles.insert("user0001".into(), "Ada".into());
    world.quotas.insert("tokenAAA".into(), true);
    for _ in 0..12 {
        world.incoming.push_back(b"user0001tokenAAA".to_vec());
    }
    let (result, world) = run(checked.program, "main", Vec::new(), world);
    assert!(result.is_ok(), "{result:?}");
    world.out
}

#[test]
fn same_seed_same_run() {
    let a = transcript(42);
    assert_eq!(a, transcript(42));
    assert_eq!(a.len(), 12, "every connection is answered, faults or not: {a:?}");
    assert!(a.iter().any(|l| l == "-> 200 Ada") && a.iter().any(|l| l == "-> 502 error"), "{a:?}");
}

#[test]
fn different_seeds_explore_different_schedules() {
    let runs: Vec<Vec<String>> = (1..=8).map(transcript).collect();
    assert!(runs.windows(2).any(|w| w[0] != w[1]), "eight seeds gave identical runs");
}
