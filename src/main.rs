use std::process::ExitCode;

use flyscript::syntax::parse_module;

const USAGE: &str = "usage: flyc <parse|ast> <file.fly>...";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some((command, files)) = args.split_first() else {
        eprintln!("{USAGE}");
        return ExitCode::FAILURE;
    };
    if !matches!(command.as_str(), "parse" | "ast") || files.is_empty() {
        eprintln!("{USAGE}");
        return ExitCode::FAILURE;
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
