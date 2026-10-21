//! A deterministic scheduler for tasks (§6.1, §6.4).
//!
//! Each task runs on its own thread, but only the task holding the baton executes. At each
//! scheduling point — spawning, sending, receiving, joining — the baton passes to a task chosen
//! by a seeded generator, so interleavings are real and a seed reproduces them exactly. A task
//! that would block parks until woken; if no task can run, the program has deadlocked.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Condvar, Mutex};

use super::interp::{Ctl, panic};
use super::value::Value;

#[derive(Clone, Debug, PartialEq)]
pub enum Wait {
    /// A message on channel `id`.
    Channel(u64),
    /// Task `id` finishing.
    Task(u64),
}

struct Inner {
    current: u64,
    ready: Vec<u64>,
    blocked: HashMap<u64, Wait>,
    finished: HashSet<u64>,
    deadlocked: bool,
    rng: u64,
    next: u64,
    channels: HashMap<u64, VecDeque<Value>>,
    /// Channels whose senders are done: a receiver drains them, then sees the end.
    closed: HashSet<u64>,
    /// Tasks whose scope was cancelled: they unwind at their next scheduling point.
    cancelled: HashSet<u64>,
}

pub struct Sched {
    inner: Mutex<Inner>,
    turn: Condvar,
}

impl Sched {
    pub fn new(seed: u64) -> Arc<Sched> {
        Arc::new(Sched {
            inner: Mutex::new(Inner {
                current: 0,
                ready: Vec::new(),
                blocked: HashMap::new(),
                finished: HashSet::new(),
                deadlocked: false,
                rng: seed.max(1),
                next: 1,
                channels: HashMap::new(),
                closed: HashSet::new(),
                cancelled: HashSet::new(),
            }),
            turn: Condvar::new(),
        })
    }

    /// Hands the baton to a ready task, chosen by the seed.
    fn pass(inner: &mut Inner) {
        if inner.ready.is_empty() {
            if !inner.blocked.is_empty() {
                inner.deadlocked = true;
            }
            return;
        }
        inner.rng ^= inner.rng << 13;
        inner.rng ^= inner.rng >> 7;
        inner.rng ^= inner.rng << 17;
        let i = (inner.rng % inner.ready.len() as u64) as usize;
        inner.current = inner.ready.remove(i);
    }

    fn wait_turn(&self, me: u64, mut inner: std::sync::MutexGuard<'_, Inner>) -> Result<(), Ctl> {
        self.turn.notify_all();
        while inner.current != me {
            if inner.deadlocked {
                return Err(panic("deadlock: every task is waiting"));
            }
            inner = self.turn.wait(inner).expect("scheduler");
        }
        if inner.cancelled.contains(&me) {
            return Err(Ctl::Cancelled);
        }
        Ok(())
    }

    /// Cancels task `t`: if it is waiting, it wakes, and at its next scheduling point it unwinds.
    pub fn cancel(&self, t: u64) {
        let mut inner = self.inner.lock().expect("scheduler");
        inner.cancelled.insert(t);
        if inner.blocked.remove(&t).is_some() {
            inner.ready.push(t);
        }
    }

    /// Task `t` has unwound to the scope that cancelled it, and runs on.
    pub fn uncancel(&self, t: u64) {
        self.inner.lock().expect("scheduler").cancelled.remove(&t);
    }

    /// A new task, ready to run when the scheduler picks it.
    pub fn spawn(&self) -> u64 {
        let mut inner = self.inner.lock().expect("scheduler");
        let id = inner.next;
        inner.next += 1;
        inner.ready.push(id);
        id
    }

    /// Blocks the calling thread until task `me` holds the baton (a new task's first step).
    pub fn start(&self, me: u64) -> Result<(), Ctl> {
        let inner = self.inner.lock().expect("scheduler");
        self.wait_turn(me, inner)
    }

    /// A scheduling point: let another ready task run, possibly this one again.
    pub fn yield_now(&self, me: u64) -> Result<(), Ctl> {
        let mut inner = self.inner.lock().expect("scheduler");
        inner.ready.push(me);
        Self::pass(&mut inner);
        self.wait_turn(me, inner)
    }

    /// Parks task `me` until `wait` is satisfied.
    fn block(&self, me: u64, wait: Wait) -> Result<(), Ctl> {
        let mut inner = self.inner.lock().expect("scheduler");
        inner.blocked.insert(me, wait);
        Self::pass(&mut inner);
        // Nothing else can run, so nothing can ever wake this task: a deadlock, reported rather
        // than waited on.
        if inner.deadlocked {
            self.turn.notify_all();
            return Err(panic("deadlock: every task is waiting"));
        }
        self.wait_turn(me, inner)
    }

    fn wake(inner: &mut Inner, wait: &Wait) {
        let woken: Vec<u64> = inner.blocked.iter().filter(|(_, w)| *w == wait).map(|(t, _)| *t).collect();
        for t in woken {
            inner.blocked.remove(&t);
            inner.ready.push(t);
        }
    }

    /// Task `me` has finished: wake its joiners and pass the baton on.
    pub fn finish(&self, me: u64) {
        let mut inner = self.inner.lock().expect("scheduler");
        inner.finished.insert(me);
        Self::wake(&mut inner, &Wait::Task(me));
        Self::pass(&mut inner);
        self.turn.notify_all();
    }

    /// Waits for task `t` to finish.
    pub fn join(&self, me: u64, t: u64) -> Result<(), Ctl> {
        if self.inner.lock().expect("scheduler").finished.contains(&t) {
            return Ok(());
        }
        self.block(me, Wait::Task(t))
    }

    pub fn channel(&self) -> u64 {
        let mut inner = self.inner.lock().expect("scheduler");
        let id = inner.next;
        inner.next += 1;
        inner.channels.insert(id, VecDeque::new());
        id
    }

    pub fn send(&self, me: u64, ch: u64, v: Value) -> Result<(), Ctl> {
        {
            let mut inner = self.inner.lock().expect("scheduler");
            inner.channels.entry(ch).or_default().push_back(v);
            Self::wake(&mut inner, &Wait::Channel(ch));
        }
        self.yield_now(me)
    }

    /// The next message, or `None` once the channel is closed and drained.
    pub fn recv(&self, me: u64, ch: u64) -> Result<Option<Value>, Ctl> {
        loop {
            {
                let mut inner = self.inner.lock().expect("scheduler");
                if let Some(v) = inner.channels.entry(ch).or_default().pop_front() {
                    return Ok(Some(v));
                }
                if inner.closed.contains(&ch) {
                    return Ok(None);
                }
            }
            self.block(me, Wait::Channel(ch))?;
        }
    }

    /// No more messages will be sent on `ch`: its receivers wake to drain it.
    pub fn close(&self, me: u64, ch: u64) -> Result<(), Ctl> {
        {
            let mut inner = self.inner.lock().expect("scheduler");
            inner.closed.insert(ch);
            Self::wake(&mut inner, &Wait::Channel(ch));
        }
        self.yield_now(me)
    }
}
