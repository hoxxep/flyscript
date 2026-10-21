//! The type and effect checker (milestone 2).

pub mod env;
pub mod expr;
pub mod impls;
pub mod own;
pub mod subst;
pub mod traits;
pub mod types;

use std::path::PathBuf;

use crate::diag::Diagnostic;
use env::Program;

/// The result of checking: the program, and diagnostics as `(file, source, diagnostic)`.
pub struct Checked {
    pub program: Program,
    pub errors: Vec<(String, Diagnostic)>,
}

impl Checked {
    pub fn render(&self) -> Vec<String> {
        self.errors
            .iter()
            .map(|(file, d)| {
                let source = self.program.modules.iter().find(|m| &m.file == file).map_or("", |m| m.source.as_str());
                d.render(file, source)
            })
            .collect()
    }
}

/// Type- and effect-checks the given files and everything they import.
pub fn check_files(paths: &[PathBuf]) -> Checked {
    let mut program = Program::load(paths);
    for fid in 0..program.fns.len() {
        if !program.modules[program.fns[fid].module].is_std {
            expr::check_fn(&mut program, fid);
        }
    }
    // Ownership needs well-typed bodies.
    if program.diags.is_empty() {
        for fid in 0..program.fns.len() {
            if !program.modules[program.fns[fid].module].is_std {
                own::check_function(&mut program, fid);
            }
        }
    }
    let errors = program
        .diags
        .iter()
        .map(|(m, d)| {
            let file = program.modules.get(*m).map_or_else(|| "<input>".to_string(), |m| m.file.clone());
            (file, d.clone())
        })
        .collect();
    Checked { program, errors }
}
