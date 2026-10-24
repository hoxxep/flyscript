//! The stack's limit (§5.7): overflowing it is a panic of the task, as it is in compiled code.
//!
//! Each of the evaluator's threads — the program's, and each task's, generator's and
//! coroutine's — has a stack of `SIZE`, reserved rather than committed, and a call checks first
//! that it is above the thread's limit, `MARGIN` above the stack's end. As a panic for an
//! overflow unwinds, half the margin is the cleanups'.

use std::cell::Cell;

pub const SIZE: usize = 256 << 20;
const MARGIN: usize = 8 << 20;

thread_local! {
    static LIMIT: Cell<usize> = const { Cell::new(0) };
}

/// Runs `f` on a thread of its own, with the evaluator's stack.
pub fn spawn<F, T>(f: F) -> std::thread::JoinHandle<T>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    std::thread::Builder::new()
        .stack_size(SIZE)
        .spawn(move || {
            let here = 0u8;
            LIMIT.set((&here as *const u8 as usize).saturating_sub(SIZE) + MARGIN);
            f()
        })
        .expect("a thread for the evaluator")
}

/// Whether there is room for another call. Once there is not, the limit is lowered by half the
/// margin, for the cleanups to run in.
pub fn room() -> bool {
    let here = 0u8;
    let sp = &here as *const u8 as usize;
    let limit = LIMIT.get();
    if limit == 0 || sp >= limit {
        return true;
    }
    LIMIT.set(limit - MARGIN / 2);
    false
}
