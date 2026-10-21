//! The evaluator (milestone 4): runs checked programs against a deterministic world.

pub mod builtins;
pub mod coroutine;
pub mod generators;
pub mod interp;
pub mod sched;
pub mod value;
pub mod world;

use std::sync::{Arc, Mutex};

use crate::check::env::{Binding, Program};
use interp::{Ctl, Interp};
pub use value::Value;
pub use world::World;

/// Runs the exported function `name` of the program's first user module with `args`, against
/// `world`. Returns its result, or the panic or uncaught failure that ended it.
pub fn run(program: Program, name: &str, args: Vec<Value>, world: World) -> (Result<Value, String>, World) {
    let entry = program.modules.iter().position(|m| !m.is_std);
    let fid = entry.and_then(|m| match program.lookup(m, name) {
        Some(Binding::Fn(fid)) => Some(fid),
        _ => None,
    });
    let world = Arc::new(Mutex::new(world));
    let result = match fid {
        None => Err(format!("no function `{name}`")),
        Some(fid) => {
            let mut it = Interp::new(Arc::new(program), world.clone());
            match it.call_fn(fid, args) {
                Ok(v) => Ok(v.deref()),
                Err(Ctl::Panic(m)) => Err(format!("panic: {m}")),
                Err(other) => Err(format!("{other:?}")),
            }
        }
    };
    // Generator threads may still hold the world; take its contents.
    let world = std::mem::take(&mut *world.lock().expect("world"));
    (result, world)
}
