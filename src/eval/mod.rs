//! The evaluator (milestone 4): runs checked programs against a deterministic world.

pub mod builtins;
pub mod coroutine;
pub mod drops;
pub mod generators;
pub mod interp;
pub mod sched;
pub mod value;
pub mod world;

use std::sync::{Arc, Mutex};

use crate::check::env::{Binding, Program};
use crate::check::types::Ty;
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

/// The command line as the exported function `name` takes it (§8.1): each parameter the next
/// argument, read as its type reads it, and a last parameter that is a list of strings every
/// argument left.
pub fn command_line(program: &Program, name: &str, args: &[String]) -> Result<Vec<Value>, String> {
    let entry = program.modules.iter().position(|m| !m.is_std);
    let Some(Binding::Fn(fid)) = entry.and_then(|m| program.lookup(m, name)) else {
        return Err(format!("no function `{name}`"));
    };
    let params = &program.fns[fid].scheme.params;
    let mut values = Vec::new();
    for (i, (_, ty)) in params.iter().enumerate() {
        let mut t = ty;
        while let Ty::Borrow(_, inner) = t {
            t = inner;
        }
        let list = matches!(t, Ty::Slice(_));
        if list && i + 1 == params.len() {
            let rest = args.iter().skip(i).map(|a| Value::text(a)).collect();
            values.push(Value::List(Arc::new(rest)));
            break;
        }
        let Some(a) = args.get(i) else { return Err(format!("argument {} is missing", i + 1)) };
        values.push(match t {
            Ty::Prim(p) if p.is_int() => Value::Int(a.parse().map_err(|_| format!("argument {} is not an integer", i + 1))?),
            Ty::Prim(p) if p.is_float() => Value::Float(a.parse().map_err(|_| format!("argument {} is not a number", i + 1))?),
            _ => Value::text(a),
        });
    }
    Ok(values)
}
