//! Programs made at random, well typed by construction, run by every implementation. The checker
//! must accept each; what the reference prints is what the JavaScript, C and LLVM code must print,
//! and native code must run clean under the address, undefined-behavior and leak sanitizers. From
//! each program come mutants that break one rule of ownership or mutability, which the checker
//! must reject: a program it accepts that the sanitizers catch would be a hole in the language.
//!
//! The seeds are fixed, so a failure reproduces. `FLY_FUZZ=n` makes n programs (default 24), and
//! `FLY_FUZZ_SEED=s` starts at seed s. The programs are kept in `target/fuzz/`.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use flyscript::check::check_files;
use flyscript::eval::{World, run};

mod common;
use common::on_every_core;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n.max(1) as u64) as usize
    }
    fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Ty {
    Int,
    Bool,
    Str,
    Vec,
    Opt,
    Shape,
    Bag,
}

impl Ty {
    fn name(self) -> &'static str {
        match self {
            Ty::Int => "i64",
            Ty::Bool => "bool",
            Ty::Str => "String",
            Ty::Vec => "Vec<i64>",
            Ty::Opt => "Option<i64>",
            Ty::Shape => "Shape",
            Ty::Bag => "Bag",
        }
    }
    /// Whether a value of the type is copied rather than moved.
    fn copies(self) -> bool {
        matches!(self, Ty::Int | Ty::Bool | Ty::Opt | Ty::Shape)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Mode {
    Owned,
    Readonly,
    Mut,
}

#[derive(Clone, Debug)]
struct Var {
    name: String,
    ty: Ty,
    /// May be assigned, or changed in place.
    mutable: bool,
    /// Owned here, so it may be moved.
    owned: bool,
    moved: bool,
    /// The loop depth it was declared at: a loop deeper than that may not move it.
    depth: usize,
}

#[derive(Clone)]
struct FnSig {
    name: String,
    params: Vec<(Mode, Ty)>,
    asks: bool,
    fails: bool,
    /// A generator of integers rather than a function giving one.
    yields: bool,
}

/// Where a mutant may be made, and what it inserts there.
#[derive(Clone)]
struct Site {
    line: usize,
    text: String,
    what: &'static str,
    /// Whether `text` replaces the line, rather than following it.
    replace: bool,
}

struct Gen {
    rng: Rng,
    lines: Vec<String>,
    indent: usize,
    scopes: Vec<Vec<Var>>,
    fresh: usize,
    fns: Vec<FnSig>,
    loops: usize,
    /// Vectors being iterated: they may not change.
    iterated: Vec<String>,
    in_main: bool,
    asks: bool,
    fails: bool,
    sites: Vec<Site>,
    budget: usize,
}

impl Gen {
    fn new(seed: u64) -> Gen {
        Gen {
            rng: Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1),
            lines: Vec::new(),
            indent: 0,
            scopes: Vec::new(),
            fresh: 0,
            fns: Vec::new(),
            loops: 0,
            iterated: Vec::new(),
            in_main: false,
            asks: false,
            fails: false,
            sites: Vec::new(),
            budget: 0,
        }
    }

    fn line(&mut self, s: &str) {
        self.lines.push(format!("{}{s}", "  ".repeat(self.indent)));
    }

    fn name(&mut self, base: &str) -> String {
        self.fresh += 1;
        format!("{base}{}", self.fresh)
    }

    fn vars(&self) -> impl Iterator<Item = &Var> {
        self.scopes.iter().flatten().filter(|v| !v.moved)
    }

    fn pick_var(&mut self, test: impl Fn(&Var) -> bool) -> Option<Var> {
        let found: Vec<Var> = self.vars().filter(|v| test(v)).cloned().collect();
        if found.is_empty() { None } else { Some(found[self.rng.below(found.len())].clone()) }
    }

    fn declare(&mut self, name: &str, ty: Ty, mutable: bool, owned: bool) {
        let depth = self.loops;
        self.scopes.last_mut().unwrap().push(Var { name: name.into(), ty, mutable, owned, moved: false, depth });
    }

    fn mark_moved(&mut self, name: &str) {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(v) = scope.iter_mut().find(|v| v.name == name) {
                v.moved = true;
                return;
            }
        }
    }

    // ---- expressions ----

    fn int(&mut self, d: usize) -> String {
        let choice = if d == 0 { self.rng.below(3) } else { self.rng.below(12) };
        match choice {
            0 => format!("{}", self.rng.below(100)),
            1 | 2 => match self.pick_var(|v| v.ty == Ty::Int) {
                Some(v) => v.name,
                None => format!("{}", self.rng.below(50)),
            },
            3 => format!("(({}) + ({})) % 1009", self.int(d - 1), self.int(d - 1)),
            4 => format!("(({}) - ({})) % 1009", self.int(d - 1), self.int(d - 1)),
            5 => format!("(({}) * ({})) % 1009", self.int(d - 1), self.int(d - 1)),
            6 => format!("({}) / (({}) % 7 + 8)", self.int(d - 1), self.int(d - 1)),
            7 => match self.pick_var(|v| matches!(v.ty, Ty::Str | Ty::Vec)) {
                Some(v) => format!("({}.len() as i64)", v.name),
                None => "3".into(),
            },
            8 => match self.pick_var(|v| v.ty == Ty::Vec) {
                Some(v) => {
                    // The index may not lend the vector again while `get` reads it.
                    self.iterated.push(v.name.clone());
                    let i = self.int(d - 1);
                    self.iterated.pop();
                    format!("match ({}.get(((({i}) % 5 + 5) % 5) as usize)) {{ #Some(x) => x + 0, #None => 0 - 1 }}", v.name)
                }
                None => "4".into(),
            },
            9 => match self.pick_var(|v| v.ty == Ty::Shape) {
                Some(v) => format!(
                    "match ({}) {{ #Circle(r) => (r * 3) % 1009, #Rect {{ w, h }} => (w + h) % 1009, #Empty => 0 }}",
                    v.name
                ),
                None => match self.pick_var(|v| v.ty == Ty::Opt) {
                    Some(v) => format!("{}.unwrapOr(7)", v.name),
                    None => "5".into(),
                },
            },
            10 => format!("if ({}) {{ {} }} else {{ {} }}", self.boolean(d - 1), self.int(d - 1), self.int(d - 1)),
            _ => self.call_int(d - 1).unwrap_or_else(|| "6".into()),
        }
    }

    fn boolean(&mut self, d: usize) -> String {
        match self.rng.below(if d == 0 { 2 } else { 6 }) {
            0 => format!("({}) < ({})", self.int(d.saturating_sub(1)), self.int(d.saturating_sub(1))),
            1 => match self.pick_var(|v| v.ty == Ty::Bool) {
                Some(v) => v.name,
                None => "true".into(),
            },
            2 => format!("({}) == ({})", self.int(d - 1), self.int(d - 1)),
            3 => format!("!({})", self.boolean(d - 1)),
            4 => format!("({}) && ({})", self.boolean(d - 1), self.boolean(d - 1)),
            _ => match self.pick_var(|v| v.ty == Ty::Str) {
                Some(v) => format!("{}.includes(\"{}\")", v.name, ["a", "b", "1", "x"][self.rng.below(4)]),
                None => "false".into(),
            },
        }
    }

    /// A new string, owned.
    fn string(&mut self, d: usize) -> String {
        match self.rng.below(4) {
            0 => format!("\"w{}\".toString()", self.rng.below(10)),
            1 => format!("`s${{{}}}a`", self.int(d)),
            2 => match self.pick_var(|v| v.ty == Ty::Str) {
                Some(v) => format!("{}.clone()", v.name),
                None => "\"b\".toString()".into(),
            },
            _ => match self.pick_var(|v| v.ty == Ty::Str) {
                Some(v) => format!("{}.toUpperCase()", v.name),
                None => "\"x1\".toString()".into(),
            },
        }
    }

    fn vector(&mut self, d: usize) -> String {
        match self.rng.below(3) {
            0 => {
                let n = self.rng.below(4);
                let items: Vec<String> = (0..n).map(|_| self.int(d)).collect();
                format!("[{}]", items.join(", "))
            }
            1 => match self.pick_var(|v| v.ty == Ty::Vec) {
                Some(v) => format!("{}.clone()", v.name),
                None => "[1, 2]".into(),
            },
            _ => format!("[{}]", self.int(d)),
        }
    }

    fn option(&mut self, d: usize) -> String {
        if self.rng.chance(70) { format!("#Some({})", self.int(d)) } else { "#None".into() }
    }

    fn shape(&mut self, d: usize) -> String {
        match self.rng.below(3) {
            0 => format!("#Circle({})", self.int(d)),
            1 => format!("#Rect {{ w: {}, h: {} }}", self.int(d), self.int(d)),
            _ => "#Empty".into(),
        }
    }

    fn bag(&mut self, d: usize) -> String {
        format!("Bag {{ name: {}, items: {}, tag: {} }}", self.string(d), self.vector(d), self.option(d))
    }

    fn value(&mut self, ty: Ty, d: usize) -> String {
        match ty {
            Ty::Int => self.int(d),
            Ty::Bool => self.boolean(d),
            Ty::Str => self.string(d),
            Ty::Vec => self.vector(d),
            Ty::Opt => self.option(d),
            Ty::Shape => self.shape(d),
            Ty::Bag => self.bag(d),
        }
    }

    /// The arguments of a call of `f`, if this code may give them; and the variables they move.
    fn args(&mut self, f: &FnSig, d: usize) -> Option<(String, Vec<String>)> {
        let mut out = Vec::new();
        let mut moved = Vec::new();
        let mut used: Vec<String> = Vec::new();
        for &(mode, ty) in &f.params {
            let arg = match mode {
                Mode::Owned if !ty.copies() && self.rng.chance(40) => {
                    // A variable moved in: owned here, declared at this loop depth, used once.
                    let loops = self.loops;
                    let iterated = self.iterated.clone();
                    match self.pick_var(|v| v.ty == ty && v.owned && v.depth == loops && !used.contains(&v.name) && !iterated.contains(&v.name)) {
                        Some(v) => {
                            // Arguments go left to right: what comes after may not use it.
                            used.push(v.name.clone());
                            moved.push(v.name.clone());
                            self.mark_moved(&v.name);
                            v.name
                        }
                        None => self.value(ty, d),
                    }
                }
                Mode::Owned => self.value(ty, d),
                Mode::Readonly => match self.pick_var(|v| v.ty == ty && !used.contains(&v.name)) {
                    Some(v) => {
                        used.push(v.name.clone());
                        v.name
                    }
                    None if ty == Ty::Str => "\"r\".toString()".into(),
                    None => return self.unmove(moved),
                },
                Mode::Mut => {
                    let iterated = self.iterated.clone();
                    let Some(v) = self.pick_var(|v| v.ty == ty && v.mutable && !used.contains(&v.name) && !iterated.contains(&v.name)) else {
                        return self.unmove(moved);
                    };
                    used.push(v.name.clone());
                    format!("mut {}", v.name)
                }
            };
            out.push(arg);
        }
        Some((out.join(", "), moved))
    }

    /// A call abandoned: what its arguments would have moved is still there.
    fn unmove(&mut self, moved: Vec<String>) -> Option<(String, Vec<String>)> {
        for m in moved {
            for scope in self.scopes.iter_mut().rev() {
                if let Some(v) = scope.iter_mut().find(|v| v.name == m) {
                    v.moved = false;
                    break;
                }
            }
        }
        None
    }

    /// A call of a function giving an integer, which this code may perform.
    fn call_int(&mut self, d: usize) -> Option<String> {
        let (asks, fails) = (self.asks, self.fails);
        let candidates: Vec<FnSig> = self.fns.iter().filter(|f| !f.yields && (!f.asks || asks) && (!f.fails || fails)).cloned().collect();
        if candidates.is_empty() {
            return None;
        }
        let f = candidates[self.rng.below(candidates.len())].clone();
        let (args, moved) = self.args(&f, d)?;
        for m in &moved {
            self.mark_moved(m);
        }
        Some(format!("{}({args})", f.name))
    }

    // ---- statements ----

    fn stmt(&mut self, d: usize) {
        if self.in_main && self.rng.chance(30) {
            self.print();
            return;
        }
        if self.in_main && self.rng.chance(6) {
            self.holds();
            return;
        }
        match self.rng.below(18) {
            0..=3 => {
                let ty = [Ty::Int, Ty::Int, Ty::Bool, Ty::Str, Ty::Vec, Ty::Opt, Ty::Shape, Ty::Bag][self.rng.below(8)];
                let name = self.name("v");
                let mutable = self.rng.chance(60);
                let e = self.value(ty, d);
                self.line(&format!("{} {name}: {} = {e};", if mutable { "let" } else { "const" }, ty.name()));
                self.declare(&name, ty, mutable, true);
            }
            4 => {
                if let Some(v) = self.pick_var(|v| v.ty == Ty::Int && v.mutable && v.owned) {
                    let e = self.int(d);
                    self.line(&format!("{} = ({} + {e}) % 1009;", v.name, v.name));
                }
            }
            5 => {
                let iterated = self.iterated.clone();
                if let Some(v) = self.pick_var(|v| v.ty == Ty::Vec && v.mutable && !iterated.contains(&v.name)) {
                    // What is pushed may not lend the vector again, while `push` has it.
                    self.iterated.push(v.name.clone());
                    let e = self.int(d);
                    self.iterated.pop();
                    self.line(&format!("{}.push({e});", v.name));
                } else if let Some(v) = self.pick_var(|v| v.ty == Ty::Bag && v.mutable && v.owned) {
                    let e = self.int(d);
                    self.line(&format!("{}.items.push({e});", v.name));
                }
            }
            6 => {
                if let Some(v) = self.pick_var(|v| v.ty == Ty::Str && v.mutable && v.owned) {
                    let piece = ["q", "z", "12"][self.rng.below(3)];
                    self.line(&format!("{}.push(\"{piece}\");", v.name));
                }
            }
            7 => {
                let c = self.boolean(d);
                self.line(&format!("if ({c}) {{"));
                self.nest(3);
                self.line("} else {");
                self.nest(2);
                self.line("}");
            }
            8 => {
                let i = self.name("i");
                let n = 1 + self.rng.below(3);
                // A mutant moves an outer string in the loop: the second time round it is gone.
                if let Some(v) = self.pick_var(|v| v.ty == Ty::Str && v.owned) {
                    let at = self.lines.len();
                    let pad = "  ".repeat(self.indent + 1);
                    self.sites.push(Site { line: at, text: format!("{pad}const moved_in_loop: String = {};", v.name), what: "a value moved in a loop", replace: false });
                }
                self.line(&format!("for (const {i} of 0..{n}) {{"));
                self.loops += 1;
                self.scopes.push(vec![Var { name: format!("({i} as i64)"), ty: Ty::Int, mutable: false, owned: false, moved: false, depth: self.loops }]);
                self.indent += 1;
                let budget = self.rng.below(3) + 1;
                for _ in 0..budget {
                    if self.budget == 0 {
                        break;
                    }
                    self.budget -= 1;
                    self.stmt(1);
                }
                self.indent -= 1;
                self.scopes.pop();
                self.loops -= 1;
                self.line("}");
            }
            9 => {
                if let Some(v) = self.pick_var(|v| v.ty == Ty::Vec) {
                    let acc = self.name("acc");
                    let x = self.name("x");
                    self.line(&format!("let {acc}: i64 = 0;"));
                    self.line(&format!("for (const {x} of {}) {{", v.name));
                    self.loops += 1;
                    self.iterated.push(v.name.clone());
                    self.scopes.push(vec![Var { name: x.clone(), ty: Ty::Int, mutable: false, owned: false, moved: false, depth: self.loops }]);
                    self.indent += 1;
                    self.line(&format!("{acc} = ({acc} + {x}) % 1009;"));
                    if v.mutable {
                        // A mutant changes the vector while the loop reads it.
                        let at = self.lines.len() - 1;
                        self.sites.push(Site { line: at, text: format!("{}  {}.push(1);", "  ".repeat(self.indent), v.name), what: "a vector changed while iterated", replace: false });
                    }
                    if self.rng.chance(50) && self.budget > 0 {
                        self.budget -= 1;
                        self.stmt(1);
                    }
                    self.indent -= 1;
                    self.scopes.pop();
                    self.iterated.pop();
                    self.loops -= 1;
                    self.line("}");
                    self.declare(&acc, Ty::Int, true, true);
                }
            }
            10 => {
                if let Some(v) = self.pick_var(|v| v.ty == Ty::Shape) {
                    let r = self.name("m");
                    self.line(&format!("let {r}: i64 = 0;"));
                    self.line(&format!("match ({}) {{", v.name));
                    let e1 = self.int(1);
                    let e2 = self.int(1);
                    self.line(&format!("  #Circle(r) => {{ {r} = (r + {e1}) % 1009; }}"));
                    self.line(&format!("  #Rect {{ w, h }} => {{ {r} = (w * h + {e2}) % 1009; }}"));
                    self.line("  #Empty => {}");
                    self.line("}");
                    self.declare(&r, Ty::Int, true, true);
                }
            }
            11 => {
                if let Some(v) = self.pick_var(|v| v.ty == Ty::Vec && v.mutable)
                    && !self.iterated.contains(&v.name)
                {
                    let o = self.name("o");
                    self.line(&format!("const {o}: Option<i64> = {}.pop();", v.name));
                    self.declare(&o, Ty::Opt, false, true);
                }
            }
            12 => {
                // A closure that reads what it captures.
                if let Some(v) = self.pick_var(|v| v.ty == Ty::Int) {
                    let f = self.name("f");
                    let r = self.name("c");
                    let e = self.int(1);
                    self.line(&format!("const {f} = (z: i64) => (z * 2 + {}) % 1009;", v.name));
                    self.line(&format!("const {r}: i64 = {f}({e});"));
                    self.declare(&r, Ty::Int, false, true);
                }
            }
            13 => {
                if let Some(call) = self.call_int(d) {
                    let r = self.name("r");
                    self.line(&format!("const {r}: i64 = {call};"));
                    self.declare(&r, Ty::Int, false, true);
                }
            }
            14 => self.effects(d),
            16 if self.in_main && self.loops == 0 && self.rng.chance(40) => self.tasks(d),
            17 => {
                // A function given a closure, which reads what it captures.
                if let Some(v) = self.pick_var(|v| v.ty == Ty::Int) {
                    let r = self.name("ap");
                    let e = self.int(1);
                    self.line(&format!("const {r}: i64 = twice((z: i64) => (z + {}) % 1009, {e});", v.name));
                    self.declare(&r, Ty::Int, false, true);
                }
            }
            15 => {
                if self.in_main && self.loops == 0 {
                    let n = self.fresh;
                    self.line("{");
                    self.indent += 1;
                    self.line(&format!("defer {{ println(\"cleanup {n}\"); }};"));
                    self.indent -= 1;
                    self.nest(2);
                    self.line("}");
                }
            }
            _ => {
                if self.in_main {
                    self.print();
                }
            }
        }
    }

    /// Code that holds what it was lent, or what an arm took, as long as it may and no longer: each
    /// with a mutant that holds it past that.
    fn holds(&mut self) {
        let pad = "  ".repeat(self.indent);
        let words = ["ab", "four", "seven", "x"];
        let (w1, w2) = (words[self.rng.below(4)], words[self.rng.below(4)]);
        let r = self.name("hd");
        match self.rng.below(3) {
            0 => {
                // An operation's borrowed argument, used before the arm resumes.
                let t = self.name("t");
                let c = self.rng.below(5) + 2;
                let head = format!("const {r}: i64 = handle {{ const {t} = \"{w1}\".toString(); Peek.peek({t}.asStr()) + 1 }} with Peek");
                self.line(&format!("{head} {{ peek(s) resumes k => k((s.len() as i64) * {c}) }};"));
                let at = self.lines.len() - 1;
                self.sites.push(Site {
                    line: at,
                    text: format!("{pad}{head} {{ peek(s) resumes k => {{ discard(k); s.len() as i64 }} }};"),
                    what: "an operation's borrowed argument used after its continuation was given up",
                    replace: true,
                });
            }
            1 => {
                // A value whose type implements `Drop`, its parts only read.
                let g = self.name("gd");
                self.line(&format!("const {g} = Guard {{ a: \"{w1}\".toString(), b: \"{w2}\".toString() }};"));
                self.line(&format!("const {r}: i64 = match ({g}) {{ Guard {{ a, b }} => (a.len() + b.len()) as i64 }};"));
                let at = self.lines.len() - 1;
                self.sites.push(Site {
                    line: at,
                    text: format!("{pad}const {r}: i64 = match ({g}) {{ Guard {{ a, b }} => consume(a) + (b.len() as i64) }};"),
                    what: "a part moved out of a value whose type implements `Drop`",
                    replace: true,
                });
            }
            _ => {
                // An arm that moves a part owns the rest, until it ends.
                let pr = self.name("pr");
                self.line(&format!("const {pr} = #Pair(\"{w1}\".toString(), \"{w2}\".toString());"));
                self.line(&format!("const {r}: i64 = match ({pr}) {{ #Pair(a, b) => consume(a) + (b.len() as i64) }};"));
                let at = self.lines.len() - 1;
                self.sites.push(Site {
                    line: at,
                    text: format!("{pad}const {r}: i64 = {{ const sl: str = match ({pr}) {{ #Pair(a, b) => {{ consume(a); b.asStr() }} }}; sl.len() as i64 }};"),
                    what: "a borrow of what an arm owns, used after the arm",
                    replace: true,
                });
            }
        }
        self.declare(&r, Ty::Int, false, true);
    }

    /// Tasks in a scope, each printing as it goes and giving a result: the seeded scheduler decides
    /// how they interleave, the same way in every implementation.
    fn tasks(&mut self, d: usize) {
        let n = 2 + self.rng.below(3);
        let r = self.name("sc");
        let label = self.name("task");
        self.line(&format!("const {r}: i64 = Io.scope((s) => {{"));
        self.indent += 1;
        let mut joins = Vec::new();
        for k in 0..n {
            let f = self.name("fk");
            let a = self.int(d);
            let b = self.rng.below(4);
            self.line(&format!("const {f} = s.fork(() => {{"));
            self.line(&format!("  println(\"{label} {k} begins\");"));
            self.line(&format!("  Io.sleep(Duration.ms({b}));"));
            self.line(&format!("  println(\"{label} {k} ends\");"));
            self.line(&format!("  ({a} + {k}) % 1009"));
            self.line("});");
            joins.push(format!("{f}.join()"));
        }
        self.line(&format!("({}) % 1009", joins.join(" + ")));
        self.indent -= 1;
        self.line("});");
        self.declare(&r, Ty::Int, false, true);
    }

    fn nest(&mut self, n: usize) {
        self.indent += 1;
        let saved_scope = self.scopes.len();
        self.scopes.push(Vec::new());
        let n = self.rng.below(n) + 1;
        for _ in 0..n {
            if self.budget == 0 {
                break;
            }
            self.budget -= 1;
            self.stmt(1);
        }
        self.scopes.truncate(saved_scope);
        self.indent -= 1;
    }

    /// Calls under handlers: of `Ask`, by arms that resume or not, and of failures, by `catch`.
    fn effects(&mut self, d: usize) {
        let asking: Vec<FnSig> = self.fns.iter().filter(|f| f.asks && !f.yields).cloned().collect();
        let failing: Vec<FnSig> = self.fns.iter().filter(|f| f.fails && !f.asks && !f.yields).cloned().collect();
        let yielding: Vec<FnSig> = self.fns.iter().filter(|f| f.yields).cloned().collect();
        match self.rng.below(3) {
            0 if !asking.is_empty() && !self.fails => {
                let f = asking[self.rng.below(asking.len())].clone();
                let saved = (self.asks, self.fails);
                (self.asks, self.fails) = (true, f.fails);
                let Some((args, moved)) = self.args(&f, d) else {
                    (self.asks, self.fails) = saved;
                    return;
                };
                (self.asks, self.fails) = saved;
                for m in &moved {
                    self.mark_moved(m);
                }
                let r = self.name("h");
                let k = self.rng.below(5) + 2;
                let arm = match self.rng.below(4) {
                    0 | 1 => format!("ask(n) resumes k => k((n * {k}) % 1009)"),
                    // Work after the resumption: the body's frame is the `handle`'s own.
                    2 => format!("ask(n) resumes k => {{ const r = k((n + {k}) % 1009); (r * 2 + 1) % 1009 }}"),
                    _ => format!("ask(n) => (n + {k}) % 1009"),
                };
                let call = format!("handle {{ {}({args}) }} with Ask {{ {arm} }}", f.name);
                if f.fails {
                    self.line(&format!("const {r}: i64 = try {{ {call} }} catch (e) {{ match (e) {{ #TooBig(m) => m % 7 }} }};"));
                } else {
                    self.line(&format!("const {r}: i64 = {call};"));
                }
                self.declare(&r, Ty::Int, false, true);
            }
            1 if !failing.is_empty() => {
                let f = failing[self.rng.below(failing.len())].clone();
                let saved = self.fails;
                self.fails = true;
                let Some((args, moved)) = self.args(&f, d) else {
                    self.fails = saved;
                    return;
                };
                self.fails = saved;
                for m in &moved {
                    self.mark_moved(m);
                }
                let r = self.name("t");
                self.line(&format!("const {r}: i64 = try {{ {}({args}) }} catch (e) {{ match (e) {{ #TooBig(m) => m % 7 }} }};", f.name));
                self.declare(&r, Ty::Int, false, true);
            }
            _ if !yielding.is_empty() => {
                let f = yielding[self.rng.below(yielding.len())].clone();
                let Some((args, moved)) = self.args(&f, d) else { return };
                for m in &moved {
                    self.mark_moved(m);
                }
                let acc = self.name("g");
                let y = self.name("y");
                self.line(&format!("let {acc}: i64 = 0;"));
                self.line(&format!("for (const {y} of {}({args})) {{", f.name));
                self.indent += 1;
                self.line(&format!("{acc} = ({acc} * 3 + {y}) % 1009;"));
                if self.rng.chance(30) {
                    self.line(&format!("if ({acc} > 500) {{ break; }}"));
                }
                self.indent -= 1;
                self.line("}");
                self.declare(&acc, Ty::Int, true, true);
            }
            _ => {}
        }
    }

    fn print(&mut self) {
        let shown: Vec<Var> = self.vars().filter(|v| v.owned || v.ty == Ty::Int).cloned().collect();
        if shown.is_empty() {
            return;
        }
        let v = shown[self.rng.below(shown.len())].clone();
        let label = self.fresh;
        self.fresh += 1;
        let text = match v.ty {
            Ty::Bag => format!("{0}.name}} ${{{0}.items.len()}} ${{{0}.tag", v.name),
            _ => v.name.clone(),
        };
        self.line(&format!("println(`p{label} ${{{text}}}`);"));
    }

    // ---- functions ----

    fn function(&mut self, idx: usize) {
        let yields = idx > 0 && self.rng.chance(20);
        let asks = !yields && self.rng.chance(35);
        let fails = !yields && self.rng.chance(35);
        let nparams = self.rng.below(4);
        let mut params = Vec::new();
        for _ in 0..nparams {
            let (mode, ty) = match self.rng.below(6) {
                0 => (Mode::Owned, Ty::Int),
                1 => (Mode::Readonly, Ty::Str),
                2 => (Mode::Mut, Ty::Vec),
                3 => (Mode::Owned, Ty::Str),
                4 => (Mode::Owned, Ty::Bag),
                _ => (Mode::Owned, Ty::Shape),
            };
            params.push((mode, ty));
        }
        let name = format!("fn{idx}");
        let mut ps = Vec::new();
        self.scopes = vec![Vec::new()];
        for (k, &(mode, ty)) in params.iter().enumerate() {
            let p = format!("a{k}");
            let m = match mode {
                Mode::Owned => "",
                Mode::Readonly => "readonly ",
                Mode::Mut => "mut ",
            };
            ps.push(format!("{p}: {m}{}", ty.name()));
            self.declare(&p, ty, mode == Mode::Mut, mode == Mode::Owned);
            if mode == Mode::Readonly && ty == Ty::Str {
                let at = self.lines.len();
                self.sites.push(Site { line: at, text: format!("  {p}.push(\"no\");"), what: "a readonly parameter changed", replace: false });
            }
        }
        let mut uses = Vec::new();
        if asks {
            uses.push("Ask".to_string());
        }
        if fails {
            uses.push("Fail<#TooBig(i64)>".to_string());
        }
        if yields {
            uses.push("Yield<i64>".to_string());
        }
        let row = if uses.is_empty() { String::new() } else { format!(" uses {}", uses.join(", ")) };
        let ret = if yields { "void" } else { "i64" };
        self.line(&format!("function {name}({}): {ret}{row} {{", ps.join(", ")));
        self.indent += 1;
        (self.asks, self.fails, self.in_main) = (asks, fails, false);
        self.budget = 3 + self.rng.below(6);
        let n = self.budget;
        for _ in 0..n {
            if self.budget == 0 {
                break;
            }
            self.budget -= 1;
            self.stmt(2);
        }
        if asks {
            let e = self.int(1);
            let a = self.name("q");
            self.line(&format!("const {a}: i64 = Ask.ask({e});"));
            self.declare(&a, Ty::Int, false, true);
        }
        if fails {
            let c = self.int(1);
            self.line(&format!("if (({c}) % 5 == 0) {{ throw #TooBig({c}); }}"));
        }
        if yields {
            let n = self.rng.below(5) + 1;
            // In the loop that yields: nothing outside it may be moved.
            self.loops += 1;
            let e = self.int(1);
            self.loops -= 1;
            self.line(&format!("for (const j of 0..{n}) {{ yield ((j as i64) * 7 + {e}) % 1009; }}"));
        } else {
            let e = self.int(2);
            self.line(&e);
        }
        self.indent -= 1;
        self.line("}");
        self.line("");
        self.fns.push(FnSig { name, params, asks, fails, yields });
    }

    fn program(&mut self) -> String {
        self.line("import { println } from \"std/io\";");
        self.line("");
        self.line("type Shape = #Circle(i64) | #Rect { w: i64; h: i64 } | #Empty;");
        self.line("struct Bag { name: String; items: Vec<i64>; tag: Option<i64> }");
        self.line("effect Ask { ask(n: i64): i64; }");
        self.line("effect Peek { peek(s: str): i64; }");
        self.line("type Pair = #Pair(String, String);");
        self.line("struct Guard { a: String; b: String }");
        self.line("impl Drop for Guard { function drop(self: mut Self): void {} }");
        self.line("function consume(s: String): i64 { s.len() as i64 }");
        self.line("function discard<A, B, row E>(k: Cont<A, B, E>): void {}");
        self.line("");
        self.line("function twice(f: (z: i64) => i64, x: i64): i64 { f(f(x)) }");
        self.line("");
        let nfns = 2 + self.rng.below(5);
        for i in 0..nfns {
            self.function(i);
        }
        self.line("export function main(): void uses Io {");
        self.indent += 1;
        (self.asks, self.fails, self.in_main) = (false, false, true);
        self.scopes = vec![Vec::new()];
        self.budget = 18 + self.rng.below(20);
        let mut reported: Vec<String> = Vec::new();
        while self.budget > 0 {
            self.budget -= 1;
            self.stmt(2);
            // A string just moved into a call: a mutant uses it after.
            let moved: Vec<Var> = self.scopes.iter().flatten().filter(|v| v.moved && v.ty == Ty::Str && !reported.contains(&v.name)).cloned().collect();
            if let Some(v) = moved.last() {
                reported.push(v.name.clone());
                let at = self.lines.len() - 1;
                self.sites.push(Site { line: at, text: format!("  println({}.asStr());", v.name), what: "a value used after it moved", replace: false });
            }
        }
        for v in self.scopes[0].clone() {
            if !v.moved && v.ty == Ty::Int {
                self.line(&format!("println(`end {} ${{{}}}`);", v.name, v.name));
            }
        }
        self.indent -= 1;
        self.line("}");
        self.lines.join("\n") + "\n"
    }

    /// The program with the mutation at `site` made.
    fn mutant(&self, site: &Site) -> String {
        let mut lines = self.lines.clone();
        if site.replace {
            lines[site.line] = site.text.clone();
        } else {
            lines.insert(site.line + 1, site.text.clone());
        }
        lines.join("\n") + "\n"
    }
}

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn tool(cmd: &str) -> bool {
    Command::new(cmd).arg("--version").output().is_ok_and(|o| o.status.success())
}

#[test]
fn random_programs_agree_and_mutants_are_rejected() {
    let count: u64 = std::env::var("FLY_FUZZ").ok().and_then(|n| n.parse().ok()).unwrap_or(24);
    let first: u64 = std::env::var("FLY_FUZZ_SEED").ok().and_then(|n| n.parse().ok()).unwrap_or(1);
    let dir = root().join("target/fuzz");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let seeds: Vec<u64> = (first..first + count).collect();
    // Each seed's program, if the checker accepts it, what went wrong, and how many mutants it made.
    let made = on_every_core(&seeds, |&seed| {
        let mut failures = Vec::new();
        let mut g = Gen::new(seed);
        let source = g.program();
        let path = dir.join(format!("p{seed}.fly"));
        std::fs::write(&path, &source).unwrap();
        let checked = check_files(std::slice::from_ref(&path));
        if !checked.errors.is_empty() {
            failures.push(format!("seed {seed}: the checker rejects a well-typed program ({}):\n{}", path.display(), checked.render().join("\n")));
            return (None, failures, 0);
        }
        let (result, world) = run(checked.program, "main", Vec::new(), World::default());
        let mut out: Vec<String> = world.out.iter().flat_map(|s| s.split('\n').map(String::from)).collect();
        if let Err(e) = result {
            out.push(format!("<{e}>"));
        }
        // What the reference printed is what every compiled form must print.
        let mut header = String::new();
        for l in &out {
            let _ = writeln!(header, "// expect: {l}");
        }
        std::fs::write(&path, format!("{header}{source}")).unwrap();
        for (k, site) in g.sites.iter().enumerate() {
            let m = dir.join(format!("m{seed}_{k}.fly"));
            std::fs::write(&m, g.mutant(site)).unwrap();
            let c = check_files(std::slice::from_ref(&m));
            if c.errors.is_empty() {
                failures.push(format!("seed {seed}: the checker accepts {} ({})", site.what, m.display()));
            }
        }
        (Some(path), failures, g.sites.len())
    });
    let mut failures = Vec::new();
    let mut paths: Vec<PathBuf> = Vec::new();
    let mut mutants = 0;
    for (path, failed, n) in made {
        paths.extend(path);
        failures.extend(failed);
        mutants += n;
    }
    eprintln!("{} programs, {mutants} mutants", paths.len());
    if tool("node") && tool("cc") && failures.is_empty() {
        // The committed seed, which is the compiler at its fixpoint: a build left in target/ may be
        // older than the runtime beside it.
        let compiler = root().join("selfhost/seed.js");
        let mut modes: Vec<Vec<&str>> = vec![vec![], vec!["--c", "--leaks"]];
        if Path::new(&format!("{}/bin/llvm-link", String::from_utf8_lossy(&Command::new("brew").args(["--prefix", "llvm"]).output().map(|o| o.stdout).unwrap_or_default()).trim())).exists() {
            modes.push(vec!["--llvm"]);
        }
        // The modes run at once: at the default count, each has fewer programs than there are cores.
        let texts = on_every_core(&modes, |mode| {
            let out = Command::new("sh")
                .arg(root().join("selfhost/corpus.sh"))
                .args(mode)
                .arg(&compiler)
                .args(&paths)
                .current_dir(root())
                .output()
                .unwrap();
            String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr)
        });
        for (mode, text) in modes.iter().zip(texts) {
            if text.contains("FAIL") {
                failures.push(format!("{mode:?}:\n{text}"));
            }
        }
    }
    assert!(failures.is_empty(), "\n{}", failures.join("\n\n"));
}
