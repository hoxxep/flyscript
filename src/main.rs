use std::process::ExitCode;

use flyscript::syntax::parse_module;

const USAGE: &str = "usage: flyc <parse|ast|check> <file.fly>...\n       flyc run <file.fly> [function] [args...]";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some((command, files)) = args.split_first() else {
        eprintln!("{USAGE}");
        return ExitCode::FAILURE;
    };
    if command == "run" {
        return run(files);
    }
    // Type and effect diagnostics, without the ownership pass: compared with the self-hosted
    // checker's.
    if command == "types" {
        let paths: Vec<std::path::PathBuf> = files.iter().map(std::path::PathBuf::from).collect();
        let mut p = flyscript::check::env::Program::load(&paths);
        let mut fid = 0;
        while fid < p.fns.len() {
            flyscript::check::expr::check_fn(&mut p, fid);
            fid += 1;
        }
        for (m, d) in &p.diags {
            println!("error {m} {}..{}: {}", d.span.start, d.span.end, d.message);
        }
        return ExitCode::SUCCESS;
    }
    // Every declaration as elaborated, one per line: compared with the self-hosted checker's.
    if command == "schemes" {
        let paths: Vec<std::path::PathBuf> = files.iter().map(std::path::PathBuf::from).collect();
        let p = flyscript::check::env::Program::load(&paths);
        for line in flyscript::check::env::describe(&p) {
            println!("{line}");
        }
        return ExitCode::SUCCESS;
    }
    if !matches!(command.as_str(), "parse" | "ast" | "check") || files.is_empty() {
        eprintln!("{USAGE}");
        return ExitCode::FAILURE;
    }
    if command == "check" {
        let paths: Vec<std::path::PathBuf> = files.iter().map(std::path::PathBuf::from).collect();
        let checked = flyscript::check::check_files(&paths);
        for e in checked.render() {
            eprintln!("{e}\n");
        }
        return if checked.errors.is_empty() {
            let modules = checked.program.modules.iter().filter(|m| !m.is_std).count();
            println!("ok: {modules} module(s) checked");
            ExitCode::SUCCESS
        } else {
            eprintln!("{} error(s)", checked.errors.len());
            ExitCode::FAILURE
        };
    }
    let mut ok = true;
    for file in files {
        let source = match std::fs::read_to_string(file) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("{file}: {e}");
                ok = false;
                continue;
            }
        };
        match parse_module(&source) {
            Ok(module) if command == "ast" => println!("{module:#?}"),
            Ok(module) => println!("{file}: ok ({} items)", module.items.len()),
            Err(d) => {
                eprintln!("{}", d.render(file, &source));
                ok = false;
            }
        }
    }
    if ok { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

/// `flyc run file.fly [function] [args...]`: checks the program, then runs `function` (default
/// `main`) with the arguments as its parameters read them (§8.1), printing what it prints and what
/// it returns.
fn run(args: &[String]) -> ExitCode {
    let Some(file) = args.first() else {
        eprintln!("{USAGE}");
        return ExitCode::FAILURE;
    };
    let checked = flyscript::check::check_files(&[std::path::PathBuf::from(file)]);
    if !checked.errors.is_empty() {
        for e in checked.render() {
            eprintln!("{e}\n");
        }
        return ExitCode::FAILURE;
    }
    let name = args.get(1).map_or("main", String::as_str);
    let values = match flyscript::eval::command_line(&checked.program, name, &args[args.len().min(2)..]) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::FAILURE;
        }
    };
    // A program run from the command line sees the real file system.
    let mut world = flyscript::eval::World::default();
    world.real_fs = true;
    let (result, world) = flyscript::eval::run(checked.program, name, values, world);
    for line in &world.out {
        println!("{line}");
    }
    if let Some(code) = world.exit {
        return ExitCode::from(code as u8);
    }
    match result {
        Ok(flyscript::eval::Value::Unit) => ExitCode::SUCCESS,
        Ok(v) => {
            println!("{}", v.show());
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}
