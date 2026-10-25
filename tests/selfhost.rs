//! The self-hosted compiler (selfhost/) compiles itself to JavaScript at a fixpoint, and compiles
//! programs as the Rust prototype runs them. `selfhost/seed.js` is the compiler compiled by
//! itself: the reference implementation, running the compiler's source, must produce it, and it
//! must reproduce itself. Compiled to C, or through LLVM, it is a native compiler at a fixpoint too.
//! The tests that run JavaScript need node, and those that build C or LLVM IR their tools; without
//! them they stop early.

use std::path::{Path, PathBuf};
use std::process::Command;

use flyscript::check::check_files;
use flyscript::eval::{Value, World, run};

mod common;
use common::on_every_core;

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn out() -> PathBuf {
    let out = root().join("target/selfhost-test");
    std::fs::create_dir_all(&out).unwrap();
    out
}

/// The programs of the directories given, in order.
fn suite(dirs: &[&str]) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = Vec::new();
    for dir in dirs {
        let mut fs: Vec<PathBuf> = std::fs::read_dir(root().join(dir)).unwrap().map(|e| e.unwrap().path()).filter(|f| f.extension().is_some_and(|e| e == "fly")).collect();
        fs.sort();
        files.extend(fs);
    }
    files
}

fn has_node() -> bool {
    Command::new("node").arg("--version").output().is_ok()
}

/// Compiles `entry` to `js` with a compiled compiler.
fn compile(compiler: &Path, entry: &Path, js: &Path) {
    let r = Command::new("node").arg("--stack-size=65500").arg(compiler).arg(entry).arg(js).arg(root()).output().unwrap();
    assert!(r.status.success() && r.stdout.is_empty(), "{}{}", String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
}

/// The machine, held by a test that keeps every core busy for its whole run. Two such at once take
/// no less time than one after the other, and more: on macOS the hundreds of processes they make
/// between them, many under the address sanitizer, spend most of their time in the kernel.
fn every_core() -> std::sync::MutexGuard<'static, ()> {
    static MACHINE: std::sync::Mutex<()> = std::sync::Mutex::new(());
    MACHINE.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// The C the seed makes of the compiler, made once for the tests that compare with it.
fn seed_c() -> &'static Path {
    static MADE: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();
    MADE.get_or_init(|| {
        let c = out().join("seed-self.c");
        compile(&root().join("selfhost/seed.js"), &root().join("selfhost/main.fly"), &c);
        c
    })
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

/// The C compiler, with what every build of the compiler's C adds (selfhost/ccflags.sh).
fn cc() -> Command {
    let mut c = Command::new("cc");
    let flags = Command::new("sh").arg(root().join("selfhost/ccflags.sh")).output().map(|o| String::from_utf8_lossy(&o.stdout).into_owned()).unwrap_or_default();
    c.args(flags.split_whitespace());
    c
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
    let c = seed_c();
    let exe = out().join("native");
    let built = cc().args(["-std=gnu11", "-O1", "-w", "-o"]).arg(&exe).arg(c).arg("-lm").output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    let seed = root().join("selfhost/seed.js");
    std::thread::scope(|s| {
        for (name, want) in [("native-again.c", c), ("native.js", &seed)] {
            let (exe, main) = (&exe, &main);
            s.spawn(move || {
                let again = out().join(name);
                let r = Command::new(exe).arg(main).arg(&again).arg(root()).output().unwrap();
                assert!(r.status.success() && r.stdout.is_empty(), "{}{}", String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
                assert!(std::fs::read(&again).unwrap() == std::fs::read(want).unwrap(), "the native compiler makes other than {}", want.display());
            });
        }
    });
}

/// `std/time` reads the machine's own tz database: zones as their files say, their changes and the
/// rule after them, against what is known of them.
#[test]
fn reads_the_systems_time_zones() {
    if !has_node() || !has_cc() || !Path::new("/usr/share/zoneinfo/Europe/London").exists() {
        return;
    }
    let dir = out().join("zones");
    std::fs::create_dir_all(&dir).unwrap();
    let program = dir.join("zones.fly");
    std::fs::write(&program, r#"import { println } from "std/io";
import { Timestamp, ZoneErr, zone, local, format } from "std/time";
export function main(): void uses Io, Fail<ZoneErr> {
  for (const name of ["Europe/London", "America/New_York", "Asia/Tokyo", "UTC"]) {
    const z = zone(name);
    const winter = z.kindAt(Timestamp.fromSeconds(1704110400));
    const summer = z.kindAt(Timestamp.fromSeconds(1719835200));
    println(`${name} ${winter.offset} ${summer.offset} ${format(local(Timestamp.fromSeconds(1719835200), z))}`);
  }
  try { zone("No/Such_Zone"); } catch (e) { println(`${e}`); }
}
"#).unwrap();
    let c = dir.join("zones.c");
    compile(&root().join("selfhost/seed.js"), &program, &c);
    let exe = dir.join("zones");
    let built = cc().args(["-std=gnu11", "-O1", "-w", "-o"]).arg(&exe).arg(&c).arg("-lm").output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    let r = Command::new(&exe).output().unwrap();
    assert_eq!(
        String::from_utf8_lossy(&r.stdout),
        "Europe/London 0 3600 2024-07-01T13:00:00+01:00\nAmerica/New_York -18000 -14400 2024-07-01T08:00:00-04:00\nAsia/Tokyo 32400 32400 2024-07-01T21:00:00+09:00\nUTC 0 0 2024-07-01T12:00:00Z\n#UnknownZone(\"No/Such_Zone\")\n"
    );
}

/// `std/unicode` passes the Unicode Character Database's own tests of grapheme clusters and of
/// normalization: every case of the first, and a sample of the second (tests/unicode).
#[test]
fn passes_unicodes_conformance_tests() {
    if !has_node() || !has_cc() {
        return;
    }
    let dir = out().join("unicode");
    std::fs::create_dir_all(&dir).unwrap();
    let c = dir.join("conformance.c");
    compile(&root().join("selfhost/seed.js"), &root().join("tests/unicode/conformance.fly"), &c);
    let exe = dir.join("conformance");
    let built = cc().args(["-std=gnu11", "-O1", "-w", "-o"]).arg(&exe).arg(&c).arg("-lm").output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    let tests = root().join("tests/unicode");
    let r = Command::new(&exe).arg(tests.join("GraphemeBreakTest.txt")).arg(tests.join("NormalizationTest.txt")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&r.stdout), "graphemes 853/853\nnormalization 4793/4793\n");
}

/// Natively, `Io.random` is the system's generator, and `std/crypto` OpenSSL's libcrypto, found
/// when first used: a program that cannot find it says so and stops.
#[test]
fn draws_on_the_systems_randomness_and_libcrypto() {
    if !has_node() || !has_cc() {
        return;
    }
    let dir = out().join("system_crypto");
    std::fs::create_dir_all(&dir).unwrap();
    let program = dir.join("system_crypto.fly");
    std::fs::write(&program, r#"import { println } from "std/io";
import { sha256 } from "std/crypto";
export function main(): void uses Io {
  let key: u8[32] = repeat(0 as u8);
  Io.random(mut key);
  let zeros: usize = 0;
  for (const b of key) { if (b == 0) { zeros += 1; } }
  println(`${key} ${zeros < 8} ${sha256("abc".asBytes())[0]}`);
}
"#).unwrap();
    let c = dir.join("system_crypto.c");
    compile(&root().join("selfhost/seed.js"), &program, &c);
    let exe = dir.join("system_crypto");
    let built = cc().args(["-std=gnu11", "-O1", "-w", "-o"]).arg(&exe).arg(&c).arg("-lm").output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    let run = || {
        let r = Command::new(&exe).env_remove("FLY_WORLD").output().unwrap();
        assert!(r.status.success(), "{}", String::from_utf8_lossy(&r.stderr));
        String::from_utf8_lossy(&r.stdout).into_owned()
    };
    let (a, b) = (run(), run());
    assert!(a.ends_with(" true 186\n"), "{a}");
    assert_ne!(a, b, "two runs drew the same key");
    let missing = Command::new(&exe).env_remove("FLY_WORLD").env("FLY_LIBCRYPTO", "/nonexistent/libcrypto").output().unwrap();
    assert!(!missing.status.success());
    let said = format!("{}{}", String::from_utf8_lossy(&missing.stdout), String::from_utf8_lossy(&missing.stderr));
    assert!(said.contains("<panic: cryptography needs OpenSSL 3 or later"), "{said}");
}

/// `std/http` over TLS against a real server, Node's, whose certificate a CA made for the test
/// signs: trusted when `SSL_CERT_FILE` names that CA, `#Untrusted` when it does not.
#[test]
fn speaks_https_to_a_real_server() {
    let has_openssl = Command::new("openssl").arg("version").output().is_ok_and(|o| o.status.success());
    if !has_node() || !has_cc() || !has_openssl {
        return;
    }
    let dir = out().join("https");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let openssl = |args: &[&str]| {
        let r = Command::new("openssl").args(args).current_dir(&dir).output().unwrap();
        assert!(r.status.success(), "openssl {args:?}: {}", String::from_utf8_lossy(&r.stderr));
    };
    openssl(&["req", "-x509", "-newkey", "ec", "-pkeyopt", "ec_paramgen_curve:P-256", "-nodes", "-keyout", "ca.key", "-out", "ca.pem", "-days", "2", "-subj", "/CN=Fly Test CA", "-addext", "basicConstraints=critical,CA:TRUE", "-addext", "keyUsage=critical,keyCertSign"]);
    openssl(&["req", "-newkey", "ec", "-pkeyopt", "ec_paramgen_curve:P-256", "-nodes", "-keyout", "key.pem", "-out", "req.pem", "-subj", "/CN=localhost"]);
    std::fs::write(dir.join("ext.cnf"), "subjectAltName=DNS:localhost,IP:127.0.0.1\nbasicConstraints=CA:FALSE\nextendedKeyUsage=serverAuth\n").unwrap();
    openssl(&["x509", "-req", "-in", "req.pem", "-CA", "ca.pem", "-CAkey", "ca.key", "-CAcreateserial", "-out", "cert.pem", "-days", "2", "-extfile", "ext.cnf"]);
    // The server is Node's, which reads the whole of a request before it answers, and closes as TLS
    // says to: `openssl s_server -www` answers having read part of one, and its close may then reset
    // the connection before the answer is read, now and then. It listens on 127.0.0.1, not on
    // Node's default of `::`: on macOS a port taken for IPv6 may be another process's for IPv4, and
    // then connections to 127.0.0.1 are that process's, so now and then another program's plain
    // server answered the handshake ("wrong version number").
    let mut server = Command::new("node")
        .arg("-e")
        .arg(r#"const fs = require("node:fs");
require("node:https").createServer({ key: fs.readFileSync("key.pem"), cert: fs.readFileSync("cert.pem") }, (q, r) => {
  q.resume();
  q.on("end", () => r.end("served by s_server's stand-in\n"));
}).listen(0, "127.0.0.1", function () { console.log(`port ${this.address().port}`); });"#)
        .current_dir(&dir)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .unwrap();
    // It says the port it took.
    let mut lines = std::io::BufRead::lines(std::io::BufReader::new(server.stdout.take().unwrap()));
    let port = loop {
        let line = lines.next().expect("the server said no port").unwrap();
        if let Some(p) = line.strip_prefix("port ") {
            break p.to_string();
        }
    };
    let program = dir.join("https.fly");
    std::fs::write(&program, r#"import { println } from "std/io";
import { get } from "std/http";
export function main(url: str): void uses Io {
  try {
    const r = get(url);
    println(`${r.status} ${r.text().asStr().includes("s_server")}`);
  } catch (e) { println(`${e}`); }
}
"#).unwrap();
    let c = dir.join("https.c");
    compile(&root().join("selfhost/seed.js"), &program, &c);
    let exe = dir.join("https");
    let built = cc().args(["-std=gnu11", "-O1", "-w", "-o"]).arg(&exe).arg(&c).arg("-lm").output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    let fetch = |host: &str, roots: &Path| {
        let r = Command::new(&exe).arg(format!("https://{host}:{port}/")).env_remove("FLY_WORLD").env("SSL_CERT_FILE", roots).env_remove("SSL_CERT_DIR").output().unwrap();
        String::from_utf8_lossy(&r.stdout).into_owned()
    };
    let by_name = fetch("localhost", &dir.join("ca.pem"));
    let by_address = fetch("127.0.0.1", &dir.join("ca.pem"));
    let untrusted = fetch("localhost", &dir.join("cert.pem"));
    let _ = server.kill();
    let _ = server.wait();
    assert_eq!(by_name, "200 true\n");
    assert_eq!(by_address, "200 true\n");
    assert_eq!(untrusted, "#Io(#Untrusted)\n");
}

/// `std/regex` finds what Rust's `regex` crate, of RE2's semantics, finds: the same matches and
/// groups in 9000 cases of random patterns and texts (tests/regex, written by tools/regex-cases).
#[test]
fn agrees_with_re2s_semantics() {
    if !has_node() || !has_cc() {
        return;
    }
    let dir = out().join("regex");
    std::fs::create_dir_all(&dir).unwrap();
    let c = dir.join("conformance.c");
    compile(&root().join("selfhost/seed.js"), &root().join("tests/regex/conformance.fly"), &c);
    let exe = dir.join("conformance");
    let built = cc().args(["-std=gnu11", "-O1", "-w", "-o"]).arg(&exe).arg(&c).arg("-lm").output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    let r = Command::new(&exe).arg(root().join("tests/regex/cases.txt")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&r.stdout), "regex 9000/9000\n");
}

/// `--watch` compiles a program again as its modules change: a change to bodies alone from what the
/// last build left, anything else from scratch, and a build that fails leaves the C as it was.
#[test]
fn compiles_again_as_its_modules_change() {
    if !has_node() || !has_cc() {
        return;
    }
    let dir = out().join("watch");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let lib = dir.join("lib.fly");
    std::fs::write(dir.join("main.fly"), "import { greet } from \"./lib\";\nimport { println } from \"std/io\";\nexport function main(): void uses Io { println(greet(\"world\").asStr()); }\n").unwrap();
    std::fs::write(&lib, "export function greet(name: str): String { `hello ${name}` }\n").unwrap();
    let c = dir.join("out.c");
    let log = dir.join("watch.log");
    // Stopped however the test ends: the compiler watches until it is killed.
    struct Watching(std::process::Child);
    impl Drop for Watching {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let compiler = Command::new("node")
        .arg("--stack-size=65500")
        .arg(root().join("selfhost/seed.js"))
        .arg(dir.join("main.fly"))
        .arg(&c)
        .arg(root())
        .arg("--watch")
        .stderr(std::fs::File::create(&log).unwrap())
        .spawn()
        .unwrap();
    let _watching = Watching(compiler);
    // Waits until the log has `n` lines and the last says `what`, then runs the C if it changed.
    let step = |n: usize, what: &str, want: Option<&str>| {
        let start = std::time::Instant::now();
        loop {
            let text = std::fs::read_to_string(&log).unwrap_or_default();
            let lines: Vec<&str> = text.lines().collect();
            if lines.len() >= n {
                assert!(lines[n - 1].contains(what), "expected `{what}`, got:\n{text}");
                break;
            }
            assert!(start.elapsed().as_secs() < 120, "no build after a change:\n{text}");
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
        if let Some(want) = want {
            let exe = dir.join("prog");
            let built = cc().args(["-std=gnu11", "-O1", "-w", "-o"]).arg(&exe).arg(&c).arg("-lm").output().unwrap();
            assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
            let r = Command::new(&exe).output().unwrap();
            assert_eq!(String::from_utf8_lossy(&r.stdout), want);
        }
    };
    step(1, "compiled in", Some("hello world\n"));
    std::fs::write(&lib, "export function greet(name: str): String { `goodbye ${name}` }\n").unwrap();
    step(2, "compiled again", Some("goodbye world\n"));
    std::fs::write(&lib, "export function greet(name: str): String { exclaim(`hi ${name}`) }\nexport function exclaim(s: String): String { `${s}!` }\n").unwrap();
    step(3, "compiled from scratch", Some("hi world!\n"));
    std::fs::write(&lib, "export function greet(name: str): String { exclaim(1) }\nexport function exclaim(s: String): String { `${s}!` }\n").unwrap();
    step(4, "lib.fly", Some("hi world!\n"));
    std::fs::write(&lib, "export function greet(name: str): String { exclaim(`bye ${name}`) }\nexport function exclaim(s: String): String { `${s}!` }\n").unwrap();
    let lines = std::fs::read_to_string(&log).unwrap().lines().count();
    step(lines + 1, "compiled from scratch", Some("bye world!\n"));
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
    for dir in ["tests/run", "tests/threads", "tests/web", "tests/native", "tests/accept", "tests/reject", "examples"] {
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

/// Runs a driver of the self-hosted checker, `main(std, entries...)`, over every program, and gives
/// `differs` each program with the lines printed after its `program <entry>`. A Node process takes
/// a core's share of the programs: starting one costs more than checking a small program.
fn compare_each(driver: &Path, differs: impl Fn(&Path, Vec<String>) -> Option<String> + Sync) -> Vec<String> {
    let programs = programs();
    let cores = std::thread::available_parallelism().map_or(4, |n| n.get());
    let shares: Vec<&[PathBuf]> = programs.chunks(programs.len().div_ceil(cores)).collect();
    on_every_core(&shares, |share| {
        let r = Command::new("node").arg("--stack-size=65500").arg(driver).arg(root().join("std")).args(*share).output().unwrap();
        assert!(r.status.success(), "{}: {}", driver.display(), String::from_utf8_lossy(&r.stderr));
        let mut printed: Vec<Vec<String>> = Vec::new();
        for line in String::from_utf8_lossy(&r.stdout).lines() {
            match line.strip_prefix("program ") {
                Some(entry) => {
                    assert_eq!(Path::new(entry), share[printed.len()]);
                    printed.push(Vec::new());
                }
                None => printed.last_mut().expect("a line before any program").push(line.to_string()),
            }
        }
        assert_eq!(printed.len(), share.len(), "{} stopped early", driver.display());
        share.iter().zip(printed).filter_map(|(f, lines)| differs(f, lines)).collect::<Vec<String>>()
    })
    .into_iter()
    .flatten()
    .collect()
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
    let _machine = every_core();
    let differ = compare_each(&typecheck, |f, mut ours| {
        let mut p = flyscript::check::env::Program::load(&[f.to_path_buf()]);
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
        rust.sort();
        ours.sort();
        (ours != rust).then(|| format!("{}\n  flyc: {rust:?}\n  ours: {ours:?}", f.display()))
    });
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
    let _machine = every_core();
    let differ = compare_each(&schemes, |f, ours| {
        let rust = flyscript::check::env::describe(&flyscript::check::env::Program::load(&[f.to_path_buf()])).join("\n");
        (ours.join("\n").trim_end() != rust).then(|| f.display().to_string())
    });
    assert!(differ.is_empty(), "elaborated differently:\n{}", differ.join("\n"));
}

/// The run suite's programs, compiled to JavaScript, print what they expect, as they do run by
/// `flyc`, against the same simulated world.
#[test]
fn compiled_programs_run_as_expected() {
    if !has_node() {
        return;
    }
    let _machine = every_core();
    let r = Command::new("sh").arg(root().join("selfhost/corpus.sh")).arg(root().join("selfhost/seed.js")).args(suite(&["tests/run", "tests/web"])).output().unwrap();
    let report = String::from_utf8_lossy(&r.stdout);
    let failed: Vec<&str> = report.lines().filter_map(|l| l.strip_prefix("FAIL ")).collect();
    assert!(failed.is_empty(), "failed compiled:\n{}", failed.join("\n"));
}

/// Every program of the run corpus compiled to C, built with the address and undefined-behavior
/// sanitizers, prints what it should, and leaks nothing.
#[test]
fn native_programs_run_as_expected() {
    if !has_node() || !has_cc() {
        return;
    }
    let _machine = every_core();
    // The run suite, and the programs that run only natively: those with raw memory and C (§8.2).
    let mut files: Vec<PathBuf> = Vec::new();
    for dir in ["tests/run", "tests/web", "tests/native"] {
        let mut fs: Vec<PathBuf> = std::fs::read_dir(root().join(dir)).unwrap().map(|e| e.unwrap().path()).filter(|f| f.extension().is_some_and(|e| e == "fly")).collect();
        fs.sort();
        files.extend(fs);
    }
    let r = Command::new("sh").arg(root().join("selfhost/corpus.sh")).arg("--c").arg("--leaks").arg(root().join("selfhost/seed.js")).args(&files).output().unwrap();
    let report = String::from_utf8_lossy(&r.stdout);
    let failed: Vec<&str> = report.lines().filter_map(|l| l.strip_prefix("FAIL ")).collect();
    assert!(failed.is_empty(), "failed natively:\n{}", failed.join("\n"));
}

/// The kernel in examples/kernel boots on QEMU's AArch64 `virt` board, runs to its end and prints
/// what it is expected to, built through C and through LLVM, where clang, ld.lld and QEMU are there
/// to build and run it.
#[test]
fn kernel_runs_on_qemu() {
    let have = |tool: &str| Command::new(tool).arg("--version").output().is_ok_and(|o| o.status.success());
    if !has_node() || !have("clang") || !have("ld.lld") || !have("qemu-system-aarch64") {
        return;
    }
    let want = std::fs::read_to_string(root().join("examples/kernel/expected.txt")).unwrap();
    let ways: &[&[&str]] = if has_llvm() { &[&[], &["--llvm"]] } else { &[&[]] };
    for way in ways {
        let r = Command::new("sh").arg(root().join("examples/kernel/run.sh")).args(*way).arg(root().join("selfhost/seed.js")).output().unwrap();
        assert!(r.status.success(), "the kernel did not exit cleanly ({way:?}):\n{}{}", String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
        assert_eq!(String::from_utf8_lossy(&r.stdout), want, "{way:?}");
    }
}

/// Whether WebAssembly for WASI can be built here: LLVM's tools, wasm-ld, and a WASI sysroot.
fn has_wasm() -> bool {
    let have = |tool: &str| Command::new(tool).arg("--version").output().is_ok_and(|o| o.status.success());
    let sysroot = std::env::var("WASI_SYSROOT").map(PathBuf::from).ok().or_else(|| {
        Command::new("brew").args(["--prefix", "wasi-libc"]).output().ok().filter(|o| o.status.success()).map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim()).join("share/wasi-sysroot"))
    });
    has_node() && has_llvm() && have("wasm-ld") && sysroot.is_some_and(|p| p.exists())
}

/// The run suite, compiled to WebAssembly and run under WASI, prints what it expects.
#[test]
fn wasm_programs_run_as_expected() {
    if !has_wasm() {
        return;
    }
    let _machine = every_core();
    let r = Command::new("sh").arg(root().join("selfhost/corpus.sh")).arg("--wasm").arg(root().join("selfhost/seed.js")).args(suite(&["tests/run", "tests/web"])).output().unwrap();
    let report = String::from_utf8_lossy(&r.stdout);
    let failed: Vec<&str> = report.lines().filter_map(|l| l.strip_prefix("FAIL ")).collect();
    assert!(failed.is_empty(), "failed as WebAssembly:\n{}", failed.join("\n"));
}

/// The compiler, compiled to WebAssembly, compiles itself to the C the seed makes of it.
#[test]
fn compiles_itself_in_wasm() {
    if !has_wasm() {
        return;
    }
    let wasm = out().join("flyc.wasm");
    // The C to compare with is made meanwhile.
    let want = std::thread::spawn(seed_c);
    let built = Command::new("sh").arg(root().join("selfhost/wasm.sh")).arg(root().join("selfhost/seed.js")).arg(root().join("selfhost/main.fly")).arg(&wasm).output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    // WASI reaches only the working directory: the compiler writes its C there.
    let made = "target/selfhost-test/wasm-self.c";
    let r = Command::new("node").args(["--no-warnings", "--stack-size=65500"]).arg(root().join("selfhost/wasm.js")).arg(&wasm).args(["selfhost/main.fly", made, "."]).current_dir(root()).output().unwrap();
    assert!(r.status.success() && r.stdout.is_empty(), "{}{}", String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
    let want = want.join().unwrap();
    assert!(std::fs::read(root().join(made)).unwrap() == std::fs::read(want).unwrap(), "the compiler in WebAssembly made other C than the seed");
}

/// LLVM's tools, where `selfhost/llvm.sh` finds them: `LLVM_BIN`, or Homebrew's llvm.
fn has_llvm() -> bool {
    let bin = std::env::var("LLVM_BIN").map(PathBuf::from).ok().or_else(|| {
        Command::new("brew").args(["--prefix", "llvm"]).output().ok().filter(|o| o.status.success()).map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim()).join("bin"))
    });
    has_node() && bin.is_some_and(|b| b.join("clang").exists() && b.join("llvm-link").exists())
}

/// The run suite and the native programs, compiled through LLVM and built with the address and
/// undefined behavior sanitizers, print what they expect.
#[test]
fn llvm_programs_run_as_expected() {
    if !has_llvm() {
        return;
    }
    let _machine = every_core();
    let mut files: Vec<PathBuf> = Vec::new();
    for dir in ["tests/run", "tests/web", "tests/native"] {
        let mut fs: Vec<PathBuf> = std::fs::read_dir(root().join(dir)).unwrap().map(|e| e.unwrap().path()).filter(|f| f.extension().is_some_and(|e| e == "fly")).collect();
        fs.sort();
        files.extend(fs);
    }
    let r = Command::new("sh").arg(root().join("selfhost/corpus.sh")).arg("--llvm").arg(root().join("selfhost/seed.js")).args(&files).output().unwrap();
    let report = String::from_utf8_lossy(&r.stdout);
    let failed: Vec<&str> = report.lines().filter_map(|l| l.strip_prefix("FAIL ")).collect();
    assert!(failed.is_empty(), "failed through LLVM:\n{}", failed.join("\n"));
}

/// Tasks interleave alike on every implementation, from any seed (§6.4, §11.1): the reference,
/// and the compiler's JavaScript, C, LLVM and WebAssembly, each print the order in which four
/// tasks' messages arrived, which the seed chooses, the same for every seed tried.
#[test]
fn interleaves_alike_from_any_seed() {
    if !has_wasm() || !has_cc() {
        return;
    }
    let program = root().join("tests/run/interleave_by_seed.fly");
    let dir = out().join("interleave");
    std::fs::create_dir_all(&dir).unwrap();
    let seed = root().join("selfhost/seed.js");
    compile(&seed, &program, &dir.join("p.js"));
    compile(&seed, &program, &dir.join("p.c"));
    let cc = cc().args(["-std=gnu11", "-O1", "-w", "-o"]).arg(dir.join("c")).arg(dir.join("p.c")).arg("-lm").output().unwrap();
    assert!(cc.status.success(), "{}", String::from_utf8_lossy(&cc.stderr));
    for (script, made) in [("selfhost/llvm.sh", "llvm"), ("selfhost/wasm.sh", "p.wasm")] {
        let r = Command::new("sh").arg(root().join(script)).arg(&seed).arg(&program).arg(dir.join(made)).output().unwrap();
        assert!(r.status.success(), "{script}: {}{}", String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
    }
    let mut orders = std::collections::HashSet::new();
    for s in 1..=25u64 {
        let world = format!("{{\"seed\":{s}}}");
        // `run` consumes the program it is given, so each seed checks it afresh.
        let checked = check_files(std::slice::from_ref(&program));
        assert!(checked.errors.is_empty(), "{:?}", checked.render());
        let (r, w) = run(checked.program, "main", Vec::new(), World::from_json(&world).unwrap());
        assert!(matches!(r, Ok(Value::Unit)), "{r:?}");
        let want: String = w.out.iter().map(|l| format!("{l}\n")).collect();
        let runs: [(&str, Command); 4] = [
            ("JavaScript", { let mut c = Command::new("node"); c.arg(dir.join("p.js")); c }),
            ("C", Command::new(dir.join("c"))),
            ("LLVM", Command::new(dir.join("llvm"))),
            ("WebAssembly", { let mut c = Command::new("node"); c.arg("--no-warnings").arg(root().join("selfhost/wasm.js")).arg(dir.join("p.wasm")); c }),
        ];
        for (name, mut cmd) in runs {
            let got = cmd.env("FLY_WORLD", &world).output().unwrap();
            assert_eq!(String::from_utf8_lossy(&got.stdout), want, "{name} interleaves otherwise than the reference from seed {s}");
        }
        orders.insert(want);
    }
    assert!(orders.len() > 20, "the seed hardly changes the interleaving: {} orders from 25 seeds", orders.len());
}

/// Programs that start tasks, built through LLVM as `fly build` builds them — the module split into
/// a part per core and linked by ThinLTO — link, the runtime's C and its Flyscript one program,
/// and run as the simulated world and the machine's threads have them.
#[test]
fn tasks_link_and_run_through_split_llvm() {
    if !has_llvm() {
        return;
    }
    let dir = out().join("split");
    std::fs::create_dir_all(&dir).unwrap();
    for name in ["channel_each", "kv_actor", "receiver_gone"] {
        let program = root().join(format!("tests/run/{name}.fly"));
        let exe = dir.join(name);
        let built = Command::new("sh").arg(root().join("selfhost/llvm.sh")).arg(root().join("selfhost/seed.js")).arg(&program).arg(&exe).output().unwrap();
        assert!(built.status.success(), "{name}: {}{}", String::from_utf8_lossy(&built.stdout), String::from_utf8_lossy(&built.stderr));
        let want: String = std::fs::read_to_string(&program).unwrap().lines().filter_map(|l| l.strip_prefix("// expect: ")).map(|l| format!("{l}\n")).collect();
        let r = Command::new(&exe).env("FLY_WORLD", "{}").output().unwrap();
        assert_eq!(String::from_utf8_lossy(&r.stdout), want, "{name} in a simulated world");
        let threaded = Command::new(&exe).env_remove("FLY_WORLD").env("FLY_THREADS", "4").output().unwrap();
        assert!(threaded.status.success(), "{name} on threads: {}", String::from_utf8_lossy(&threaded.stderr));
    }
}

/// Programs that panic, built through LLVM as `fly build` builds them, unwind as they do under the
/// sanitizers, which build one module: every cleanup runs, waiting ones too, and catch points take
/// the panic up. Linked by ThinLTO, each function keeps its unwind entry, and so its landing pads.
#[test]
fn panics_unwind_through_split_llvm() {
    if !has_llvm() {
        return;
    }
    let dir = out().join("split-panics");
    std::fs::create_dir_all(&dir).unwrap();
    for name in ["panic_runs_cleanup", "fork_panic", "panic_in_a_generator", "panic_cleanup_waits"] {
        let program = root().join(format!("tests/run/{name}.fly"));
        let exe = dir.join(name);
        let built = Command::new("sh").arg(root().join("selfhost/llvm.sh")).arg(root().join("selfhost/seed.js")).arg(&program).arg(&exe).output().unwrap();
        assert!(built.status.success(), "{name}: {}{}", String::from_utf8_lossy(&built.stdout), String::from_utf8_lossy(&built.stderr));
        let want: String = std::fs::read_to_string(&program).unwrap().lines().filter_map(|l| l.strip_prefix("// expect: ")).map(|l| format!("{l}\n")).collect();
        let r = Command::new(&exe).env("FLY_WORLD", "{}").output().unwrap();
        // The panic that ends it, last, is on standard error.
        let got = format!("{}{}", String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
        assert_eq!(got, want, "{name}");
    }
}

/// `File.lines` reads lines as splitting on `\n` reads them, one `\r` before it dropped and each
/// line's bytes made text as Rust's `from_utf8_lossy` makes them, eight bytes at a time or not:
/// through C, under the sanitizers, and through LLVM, on random lines of every length, of ASCII,
/// of every width of UTF-8 sequence, of bytes that begin none or end one early, and on a line
/// longer than what is read ahead, and one without a newline at the end.
#[test]
fn reads_lines_as_they_split() {
    if !has_node() || !has_cc() {
        return;
    }
    let dir = out().join("lines");
    std::fs::create_dir_all(&dir).unwrap();
    let pieces: [&[u8]; 13] = [b"a", b"bc", "é".as_bytes(), "€".as_bytes(), "😀".as_bytes(), b"\r", b"\xff", b"\xc3", b"\x80", b"xxxxxxx", b"yyyyyyyy", b"zzzzzzzzz", b"\t"];
    let mut state: u64 = 11;
    let mut next = |n: u64| {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (state >> 33) % n
    };
    let mut data: Vec<u8> = Vec::new();
    for _ in 0..20000 {
        for _ in 0..next(24) {
            data.extend_from_slice(pieces[next(pieces.len() as u64) as usize]);
        }
        data.extend_from_slice(if next(5) == 0 { b"\r\n" } else { b"\n" });
    }
    data.extend(std::iter::repeat_n(b'q', 70000));
    data.extend_from_slice("é\ntail without a newline ".as_bytes());
    data.extend_from_slice(b"\xe2\x82");
    let path = dir.join("data.txt");
    std::fs::write(&path, &data).unwrap();
    let mut lines: Vec<&[u8]> = data.split(|b| *b == b'\n').collect();
    if lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    let (mut total, mut h) = (0u64, 0u64);
    for l in &lines {
        let l = l.strip_suffix(b"\r").unwrap_or(l);
        let text = String::from_utf8_lossy(l);
        total += text.len() as u64;
        for b in text.bytes() {
            h = (h * 31 + b as u64) % 1_000_000_007;
        }
    }
    let want = format!("{} {total} {h}\n", lines.len());
    let program = dir.join("lines.fly");
    std::fs::write(&program, r#"import { println, File } from "std/io";
export function main(path: str): void uses Io {
  try {
    let f = File.open(path);
    let n: u64 = 0;
    let total: u64 = 0;
    let h: u64 = 0;
    for (const l of f.lines()) {
      n += 1;
      total += l.len() as u64;
      for (const b of l.asStr().bytes()) { h = (h * 31 + b as u64) % 1000000007; }
    }
    println(`${n} ${total} ${h}`);
  } catch (e) { println("failed"); }
}
"#).unwrap();
    let c = dir.join("lines.c");
    compile(&root().join("selfhost/seed.js"), &program, &c);
    let exe = dir.join("lines");
    let built = cc().args(["-std=gnu11", "-O1", "-w", "-fsanitize=address,undefined", "-o"]).arg(&exe).arg(&c).arg("-lm").output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    let mut builds = vec![exe];
    if has_llvm() {
        let exe = dir.join("lines-llvm");
        let built = Command::new("sh").arg(root().join("selfhost/llvm.sh")).arg(root().join("selfhost/seed.js")).arg(&program).arg(&exe).output().unwrap();
        assert!(built.status.success(), "{}{}", String::from_utf8_lossy(&built.stdout), String::from_utf8_lossy(&built.stderr));
        builds.push(exe);
    }
    for exe in builds {
        let r = Command::new(&exe).arg(&path).env_remove("FLY_WORLD").output().unwrap();
        assert_eq!(String::from_utf8_lossy(&r.stdout), want, "{}: {}", exe.display(), String::from_utf8_lossy(&r.stderr));
    }
}

/// The compiler, compiled through LLVM, compiles itself to the LLVM module, the C beside it, and
/// the JavaScript the seed makes of it.
#[test]
fn compiles_itself_through_llvm() {
    if !has_llvm() {
        return;
    }
    let dir = out();
    let exe = dir.join("flyc-llvm");
    let main = root().join("selfhost/main.fly");
    // What to compare with is made while the compiler is built.
    let built = std::thread::scope(|s| {
        s.spawn(|| compile(&root().join("selfhost/seed.js"), &main, &dir.join("seed-llvm.ll")));
        Command::new("sh").arg(root().join("selfhost/llvm.sh")).arg(root().join("selfhost/seed.js")).arg(&main).arg(&exe).output().unwrap()
    });
    assert!(built.status.success(), "{}{}", String::from_utf8_lossy(&built.stdout), String::from_utf8_lossy(&built.stderr));
    let seed = root().join("selfhost/seed.js");
    let checks = [("llvm-self.ll", vec![(dir.join("llvm-self.ll"), dir.join("seed-llvm.ll")), (dir.join("llvm-self.c"), dir.join("seed-llvm.c"))]), ("llvm-self.js", vec![(dir.join("llvm-self.js"), seed)])];
    std::thread::scope(|s| {
        for (made, pairs) in checks {
            let (exe, main, dir) = (&exe, &main, &dir);
            s.spawn(move || {
                let r = Command::new(exe).arg(main).arg(dir.join(made)).arg(root()).output().unwrap();
                assert!(r.status.success() && r.stdout.is_empty(), "{}{}", String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
                for (got, want) in pairs {
                    assert!(std::fs::read(&got).unwrap() == std::fs::read(&want).unwrap(), "the compiler built through LLVM makes other than {}", want.display());
                }
            });
        }
    });
}

/// The programs of tests/threads print the same however their tasks interleave: against the
/// simulated world, as JavaScript and as C, and natively on worker threads under the thread
/// sanitizer, through C and through LLVM.
#[test]
fn threaded_programs_run_as_expected() {
    if !has_node() || !has_cc() {
        return;
    }
    let _machine = every_core();
    let mut files: Vec<PathBuf> = std::fs::read_dir(root().join("tests/threads")).unwrap().map(|e| e.unwrap().path()).filter(|f| f.extension().is_some_and(|e| e == "fly")).collect();
    files.sort();
    let mut ways: Vec<&[&str]> = vec![&[], &["--c"], &["--c", "--threads"]];
    if has_llvm() {
        ways.push(&["--llvm", "--threads"]);
    }
    // Each way has fewer programs than there are cores: the ways run at once.
    let reports = on_every_core(&ways, |way| Command::new("sh").arg(root().join("selfhost/corpus.sh")).args(*way).arg(root().join("selfhost/seed.js")).args(&files).output().unwrap());
    for (way, r) in ways.iter().zip(reports) {
        let report = String::from_utf8_lossy(&r.stdout);
        let failed: Vec<&str> = report.lines().filter_map(|l| l.strip_prefix("FAIL ")).collect();
        assert!(failed.is_empty(), "failed ({way:?}):\n{}", failed.join("\n"));
    }
}

/// A server written with web/http.fly, built natively, serves real HTTP on worker threads: each of
/// several connections, kept alive, gets the answer to each of its requests.
#[test]
fn serves_http_on_threads() {
    use std::io::{BufRead, BufReader, Read, Write};
    if !has_node() || !has_cc() {
        return;
    }
    let dir = out();
    let c = dir.join("hello_server.c");
    compile(&root().join("selfhost/seed.js"), &root().join("tests/web/hello_server.fly"), &c);
    let exe = dir.join("hello_server");
    let built = cc().args(["-std=gnu11", "-O1", "-w", "-o"]).arg(&exe).arg(&c).arg("-lm").output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    let mut server = Command::new(&exe).arg("0").env_remove("FLY_WORLD").stdout(std::process::Stdio::piped()).spawn().unwrap();
    let mut first = String::new();
    BufReader::new(server.stdout.as_mut().unwrap()).read_line(&mut first).unwrap();
    let port: u16 = first.trim().strip_prefix("listening on ").and_then(|p| p.parse().ok()).unwrap_or_else(|| panic!("the server said {first:?}"));
    let clients: Vec<_> = (0..8)
        .map(|k| {
            std::thread::spawn(move || {
                let mut s = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
                for i in 0..20 {
                    let close = if i == 19 { "Connection: close\r\n" } else { "" };
                    write!(s, "GET /c{k}/r{i} HTTP/1.1\r\nHost: here\r\n{close}\r\n").unwrap();
                }
                let mut all = String::new();
                s.read_to_string(&mut all).unwrap();
                (k, all)
            })
        })
        .collect();
    for client in clients {
        let (k, all) = client.join().unwrap();
        for i in 0..20 {
            assert!(all.contains(&format!("hello, GET /c{k}/r{i}\n")), "client {k} did not get the answer to request {i}:\n{all}");
        }
        assert_eq!(all.matches("HTTP/1.1 200 OK").count(), 20, "{all}");
    }
    server.kill().unwrap();
    server.wait().unwrap();
}

/// The todo app of examples/todo, built by `web/flynext`: its server routes each address to its
/// page, renders it from its store inside its layout, answers the pages' calls of `Todos`, and
/// serves the pages' program; and, where Playwright is installed (FLY_NODE_PATH, its
/// `node_modules`), the site works in a browser as someone would use it, following links without
/// loading pages.
#[test]
fn todo_site_serves_and_runs() {
    use std::io::{BufRead, BufReader, Read, Write};
    if !has_wasm() || !has_cc() {
        return;
    }
    let dir = out().join("todo");
    let built = Command::new("sh").arg(root().join("web/flynext")).arg("build").arg(root().join("examples/todo/app")).arg(&dir).output().unwrap();
    assert!(built.status.success(), "{}{}", String::from_utf8_lossy(&built.stdout), String::from_utf8_lossy(&built.stderr));
    let start = || {
        let mut server = Command::new(dir.join("server")).arg("0").arg(&dir).env_remove("FLY_WORLD").stdout(std::process::Stdio::piped()).spawn().unwrap();
        let mut first = String::new();
        BufReader::new(server.stdout.as_mut().unwrap()).read_line(&mut first).unwrap();
        let port: u16 = first.trim().strip_prefix("listening on ").and_then(|p| p.parse().ok()).unwrap_or_else(|| panic!("the server said {first:?}"));
        (server, port)
    };
    let ask = |port: u16, request: String| {
        let mut s = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
        s.write_all(request.as_bytes()).unwrap();
        let mut all = Vec::new();
        s.read_to_end(&mut all).unwrap();
        all
    };
    let get = |port: u16, path: &str| ask(port, format!("GET {path} HTTP/1.1\r\nHost: here\r\nConnection: close\r\n\r\n"));
    let (mut server, port) = start();
    let page = String::from_utf8(get(port, "/")).unwrap();
    assert!(page.contains("<a href=\"/todos/1\" class=\"title\">Write the language</a>") && page.contains("<script type=\"text/plain\" id=\"fly-page\">"), "{page}");
    let item = String::from_utf8(get(port, "/todos/2")).unwrap();
    assert!(item.starts_with("HTTP/1.1 200") && item.contains("<h1>Compile it to WebAssembly</h1>"), "{item}");
    // A page's description, a function of its model, in its head for search engines and link previews.
    assert!(item.contains("<meta name=\"description\" content=\"Done: Compile it to WebAssembly\">")
        && item.contains("<meta property=\"og:title\" content=\"Compile it to WebAssembly\">"), "{item}");
    assert!(String::from_utf8(get(port, "/todos/99")).unwrap().starts_with("HTTP/1.1 404"), "an item that is not there is found");
    let failed = String::from_utf8(get(port, "/todos/abc")).unwrap();
    assert!(failed.starts_with("HTTP/1.1 500") && failed.contains("<h1>Something went wrong</h1>"), "a page whose load failed is not the error page: {failed}");
    // A page the same for every request, rendered once, is still rendered whole and as its data.
    let about = String::from_utf8(get(port, "/about")).unwrap();
    assert!(about.starts_with("HTTP/1.1 200") && about.contains("<h1>About</h1>") && about.contains("Open for 0 s."), "{about}");
    // A page in a group, `(info)`, whose address the group is no part of, taking the rest of it.
    let help = String::from_utf8(get(port, "/help/links/following")).unwrap();
    assert!(help.starts_with("HTTP/1.1 200") && help.contains("<p>On links/following:"), "{help}");
    assert!(String::from_utf8(get(port, "/help")).unwrap().contains("<p>Pick a topic:</p>"), "a catch-all that may be empty does not answer its own address");
    // Middleware runs before any route: the list's own address sends a reader home.
    let moved = String::from_utf8(get(port, "/todos")).unwrap();
    assert!(moved.starts_with("HTTP/1.1 303") && moved.contains("\r\nLocation: /\r\n"), "middleware did not redirect: {moved}");
    // Its cookies go with whatever answers, a page rendered once or nothing found, and a value from
    // the request cannot add attributes of its own.
    let shared = String::from_utf8(get(port, "/about?from=news%3B%20Domain%3Devil")).unwrap();
    assert!(shared.starts_with("HTTP/1.1 200") && shared.contains("\r\nSet-Cookie: from=news%3B%20Domain=evil; Path=/;"), "{shared}");
    let lost = String::from_utf8(get(port, "/nowhere?from=x")).unwrap();
    assert!(lost.starts_with("HTTP/1.1 404") && lost.contains("\r\nSet-Cookie: from=x;"), "{lost}");
    let data = String::from_utf8(ask(port, "GET /about HTTP/1.1\r\nHost: here\r\nX-Fly-Data: 1\r\nConnection: close\r\n\r\n".to_string())).unwrap();
    assert!(data.contains("\r\n\r\n(info)/about\n/about\n"), "{data}");
    // A page that exports `revalidate` is rendered once and kept, for a request with cookies too, as
    // its data as well; a change to the list revalidates it. One whose load reads the request is
    // each request's own.
    let progress = String::from_utf8(get(port, "/progress")).unwrap();
    assert!(progress.contains("\r\nX-Fly-Cache: MISS\r\n") && progress.contains("s-maxage=3600") && progress.contains("2 of 3 done."), "{progress}");
    let progress = String::from_utf8(ask(port, "GET /progress HTTP/1.1\r\nHost: here\r\nCookie: a=b\r\nConnection: close\r\n\r\n".to_string())).unwrap();
    assert!(progress.contains("\r\nX-Fly-Cache: HIT\r\n") && progress.contains("2 of 3 done."), "{progress}");
    let progress = String::from_utf8(ask(port, "GET /progress HTTP/1.1\r\nHost: here\r\nX-Fly-Data: 1\r\nConnection: close\r\n\r\n".to_string())).unwrap();
    assert!(progress.contains("\r\nX-Fly-Cache: HIT\r\n") && progress.contains("\r\n\r\nprogress\n/progress\n"), "{progress}");
    for _ in 0..2 {
        let visits = String::from_utf8(ask(port, "GET /visits HTTP/1.1\r\nHost: here\r\nCookie: visits=3\r\nConnection: close\r\n\r\n".to_string())).unwrap();
        assert!(!visits.contains("X-Fly-Cache") && visits.contains("You have opened this page 4 times."), "a page that reads the request was kept: {visits}");
    }
    // A page with `later` is streamed: what `load` made at once, the rest in its place once `later`
    // has made it, in the same answer; to the page's program, its data whole.
    {
        let mut s = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
        s.write_all(b"GET /report HTTP/1.1\r\nHost: here\r\nConnection: close\r\n\r\n").unwrap();
        let mut first = Vec::new();
        let mut buf = [0u8; 65536];
        while !String::from_utf8_lossy(&first).contains("Working out a summary") {
            let n = s.read(&mut buf).unwrap();
            assert!(n > 0, "the page ended before its first part: {}", String::from_utf8_lossy(&first));
            first.extend_from_slice(&buf[..n]);
        }
        let first = String::from_utf8(first).unwrap();
        assert!(first.contains("Transfer-Encoding: chunked") && !first.contains("still to do"), "the first part waited for the rest: {first}");
        let mut rest = Vec::new();
        s.read_to_end(&mut rest).unwrap();
        let rest = String::from_utf8(rest).unwrap();
        assert!(rest.contains("<template id=\"fly-later\">") && rest.contains("1 still to do") && rest.contains("\"summary\":\"1 still to do"), "{rest}");
    }
    let data = String::from_utf8(ask(port, "GET /report HTTP/1.1\r\nHost: here\r\nX-Fly-Data: 1\r\nConnection: close\r\n\r\n".to_string())).unwrap();
    assert!(data.contains("\"summary\":\"1 still to do"), "{data}");
    let body = r#"{"title":"Asked by the test"}"#;
    let answer = String::from_utf8(ask(port, format!("POST /_fly/rpc/Todos.add HTTP/1.1\r\nHost: here\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}", body.len()))).unwrap();
    assert!(answer.starts_with("HTTP/1.1 200") && answer.contains("Asked by the test"), "{answer}");
    assert!(String::from_utf8(get(port, "/")).unwrap().contains("Asked by the test"), "the server did not keep what it was asked to add");
    let progress = String::from_utf8(get(port, "/progress")).unwrap();
    assert!(progress.contains("\r\nX-Fly-Cache: MISS\r\n") && progress.contains("2 of 4 done."), "adding did not revalidate the page: {progress}");
    let wasm = get(port, "/_fly/app.wasm");
    let at = wasm.windows(4).position(|w| w == b"\r\n\r\n").unwrap() + 4;
    assert!(wasm.starts_with(b"HTTP/1.1 200") && wasm[at..].starts_with(b"\0asm"), "the page's program is not served as WebAssembly");
    server.kill().unwrap();
    server.wait().unwrap();
    // In a browser, against a server with its store as it starts.
    let Ok(node_path) = std::env::var("FLY_NODE_PATH") else { return };
    let (mut server, port) = start();
    let r = Command::new("node").arg(root().join("examples/todo/e2e.js")).arg(port.to_string()).env("NODE_PATH", node_path).output().unwrap();
    server.kill().unwrap();
    server.wait().unwrap();
    assert!(r.status.success(), "{}{}", String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
}
