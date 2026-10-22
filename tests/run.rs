//! Runs every program in tests/run/ and compares what it prints with its `// expect:` lines.
//!
//! A program's header configures the deterministic world it runs in (§6.4):
//!
//! ```text
//! // file: name=contents          (\n in contents is a newline)
//! // request: bytes                a connection waiting to be accepted
//! // profile: user=Display Name    a row in the simulated database
//! // quota: token=true|false
//! // faults: 30                    percent of I/O operations that time out
//! // seed: 1234                    the fault generator's seed
//! // expect: a line of output
//! ```

use std::fs;
use std::path::Path;

use flyscript::check::check_files;
use flyscript::eval::{World, command_line, run};

fn unescape(s: &str) -> String {
    s.replace("\\r", "\r").replace("\\n", "\n")
}

fn world_for(source: &str) -> (World, Vec<String>) {
    let mut world = World::default();
    let mut expected = Vec::new();
    let mut seed = None;
    let mut faults = 0;
    for line in source.lines().take_while(|l| l.starts_with("//")) {
        let line = line.trim_start_matches("//").trim_start();
        let Some((key, value)) = line.split_once(": ").or_else(|| line.split_once(':')) else { continue };
        match key {
            "expect" => expected.push(value.to_string()),
            "file" => {
                let (name, contents) = value.split_once('=').expect("file: name=contents");
                world.files.insert(name.to_string(), unescape(contents));
            }
            "request" => world.incoming.push_back(unescape(value).into_bytes()),
            "peer" => {
                let (peer, reply) = value.split_once('=').expect("peer: host:port=reply");
                world.peers.insert(peer.to_string(), unescape(reply).into_bytes());
            }
            "profile" => {
                let (user, name) = value.split_once('=').expect("profile: user=name");
                world.profiles.insert(user.to_string(), name.to_string());
            }
            "quota" => {
                let (token, allowed) = value.split_once('=').expect("quota: token=bool");
                world.quotas.insert(token.to_string(), allowed == "true");
            }
            "faults" => faults = value.trim().parse().expect("faults: percent"),
            "seed" => seed = Some(value.trim().parse().expect("seed: number")),
            _ => {}
        }
    }
    if let Some(seed) = seed {
        let mut seeded = World::seeded(seed);
        seeded.files = std::mem::take(&mut world.files);
        seeded.incoming = std::mem::take(&mut world.incoming);
        seeded.peers = std::mem::take(&mut world.peers);
        seeded.profiles = std::mem::take(&mut world.profiles);
        seeded.quotas = std::mem::take(&mut world.quotas);
        world = seeded;
    }
    world.fault_percent = faults;
    (world, expected)
}

#[test]
fn programs_run() {
    // The run suite, the programs that print the same however their tasks interleave, which native
    // code also runs on threads (tests/selfhost.rs), and the web framework's.
    let mut paths: Vec<_> = Vec::new();
    for dir in ["tests/run", "tests/threads", "tests/web"] {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join(dir);
        let mut ps: Vec<_> = fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|e| e == "fly")).collect();
        ps.sort();
        paths.extend(ps);
    }
    // Programs of several modules in examples/, entered at their `main.fly`, run too.
    let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut multi: Vec<_> = fs::read_dir(&examples).unwrap().map(|e| e.unwrap().path().join("main.fly")).filter(|p| p.exists()).collect();
    multi.sort();
    paths.extend(multi);
    let mut failures = Vec::new();
    for path in paths {
        let source = fs::read_to_string(&path).unwrap();
        let (world, expected) = world_for(&source);
        let checked = check_files(std::slice::from_ref(&path));
        if !checked.errors.is_empty() {
            failures.push(format!("{} does not check:\n{}", path.display(), checked.render().join("\n")));
            continue;
        }
        // `main` is given an empty command line, as it reads one.
        let args = command_line(&checked.program, "main", &[]).unwrap_or_default();
        let (result, world) = run(checked.program, "main", args, world);
        // What a program prints is lines; one `println` may print several.
        let mut out: Vec<String> = world.out.iter().flat_map(|s| s.split('\n').map(String::from)).collect();
        if let Err(e) = result {
            out.push(format!("<{e}>"));
        }
        if out != expected {
            failures.push(format!("{}:\n  expected: {expected:?}\n  printed:  {out:?}", path.display()));
        }
    }
    assert!(failures.is_empty(), "\n{}", failures.join("\n\n"));
}
