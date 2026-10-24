//! A deterministic scheduler for tasks (§6.1, §6.4).
//!
//! Each task runs on its own thread, but only the task holding the baton executes. At each
//! scheduling point — spawning, sending, receiving, joining — the baton passes to a task chosen
//! by a seeded generator, so interleavings are real and a seed reproduces them exactly. A task
//! that would block parks until woken, in the order tasks blocked; a sleeping task waits for the
//! virtual clock, which jumps to the earliest wake time when nothing else can run. If no task can
//! run and none sleeps, the program has deadlocked.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Condvar, Mutex};

use super::interp::{Ctl, end_program, panic};
use crate::check::types::Ty;
use super::value::Value;

#[derive(Clone, Debug, PartialEq)]
pub enum Wait {
    /// A message on channel `id`.
    Channel(u64),
    /// Task `id` finishing.
    Task(u64),
    /// The virtual clock reaching this many nanoseconds.
    Until(u64),
}

struct Inner {
    current: u64,
    ready: Vec<u64>,
    /// Waiting tasks, in the order they began to wait.
    blocked: Vec<(u64, Wait)>,
    /// Simulated time in nanoseconds: `Io.now` reads it, and it passes only as tasks sleep.
    clock: u64,
    finished: HashSet<u64>,
    deadlocked: bool,
    rng: u64,
    next: u64,
    channels: HashMap<u64, VecDeque<Value>>,
    /// Channels whose senders are done: a receiver drains them, then sees the end.
    closed: HashSet<u64>,
    /// How many senders each channel has: it ends when the last is gone.
    senders: HashMap<u64, usize>,
    /// Tasks whose scope was cancelled: they unwind at their next scheduling point.
    cancelled: HashSet<u64>,
    /// How deep each task is in cleanup, which runs to its end: a cancellation waits for it.
    cleaning: HashMap<u64, u32>,
    /// Channels whose receiver is gone: what is sent to them is dropped, as a value of this type.
    deaf: HashMap<u64, Ty>,
    /// A panic that ends the program: every task meets it at its next scheduling point, and none
    /// runs its cleanup (§5.7).
    aborted: Option<String>,
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
                blocked: Vec::new(),
                clock: 0,
                finished: HashSet::new(),
                deadlocked: false,
                rng: seed.max(1),
                next: 1,
                channels: HashMap::new(),
                closed: HashSet::new(),
                senders: HashMap::new(),
                cancelled: HashSet::new(),
                cleaning: HashMap::new(),
                deaf: HashMap::new(),
                aborted: None,
            }),
            turn: Condvar::new(),
        })
    }

    /// Hands the baton to a ready task, chosen by the seed. With none ready, time passes to the
    /// earliest sleeper's wake time, waking every task due then.
    fn pass(inner: &mut Inner) {
        if inner.ready.is_empty() {
            let due = inner.blocked.iter().filter_map(|(_, w)| if let Wait::Until(t) = w { Some(*t) } else { None }).min();
            if let Some(t) = due {
                inner.clock = inner.clock.max(t);
                Self::wake(inner, &Wait::Until(t));
            }
        }
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
        loop {
            if let Some(m) = &inner.aborted {
                return Err(panic(m.clone()));
            }
            if inner.current == me {
                break;
            }
            if inner.deadlocked {
                return Err(end_program("deadlock: every task is waiting"));
            }
            inner = self.turn.wait(inner).expect("scheduler");
        }
        if inner.cancelled.contains(&me) && !inner.cleaning.contains_key(&me) {
            return Err(Ctl::Cancelled);
        }
        Ok(())
    }

    /// A task panicked: the program ends, and every task with it, wherever it waits.
    pub fn abort(&self, message: &str) {
        let mut inner = self.inner.lock().expect("scheduler");
        inner.aborted.get_or_insert_with(|| message.to_string());
        self.turn.notify_all();
    }

    /// Cancels task `t`: if it is waiting, it wakes, and at its next scheduling point it unwinds.
    /// One waiting in its cleanup waits on, and unwinds at its first scheduling point after it.
    pub fn cancel(&self, t: u64) {
        let mut inner = self.inner.lock().expect("scheduler");
        inner.cancelled.insert(t);
        if inner.cleaning.contains_key(&t) {
            return;
        }
        if let Some(i) = inner.blocked.iter().position(|(b, _)| *b == t) {
            inner.blocked.remove(i);
            inner.ready.push(t);
        }
    }

    /// Task `t` has unwound to the scope that cancelled it, and runs on.
    pub fn uncancel(&self, t: u64) {
        self.inner.lock().expect("scheduler").cancelled.remove(&t);
    }

    /// Task `me` begins cleanup (§5.6), or ends it: in between, it is not cancelled.
    pub fn cleaning(&self, me: u64, begin: bool) {
        let mut inner = self.inner.lock().expect("scheduler");
        if begin {
            *inner.cleaning.entry(me).or_insert(0) += 1;
        } else if let Some(n) = inner.cleaning.get_mut(&me) {
            *n -= 1;
            if *n == 0 {
                inner.cleaning.remove(&me);
            }
        }
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
        inner.blocked.push((me, wait));
        Self::pass(&mut inner);
        // Nothing else can run, so nothing can ever wake this task: a deadlock, reported rather
        // than waited on.
        if inner.deadlocked {
            self.turn.notify_all();
            return Err(end_program("deadlock: every task is waiting"));
        }
        self.wait_turn(me, inner)
    }

    fn wake(inner: &mut Inner, wait: &Wait) {
        let mut i = 0;
        while i < inner.blocked.len() {
            if inner.blocked[i].1 == *wait {
                let (t, _) = inner.blocked.remove(i);
                inner.ready.push(t);
            } else {
                i += 1;
            }
        }
    }

    /// The virtual clock, in nanoseconds.
    pub fn now(&self) -> u64 {
        self.inner.lock().expect("scheduler").clock
    }

    /// Task `me` sleeps for `nanos` of virtual time: other tasks run meanwhile, and time passes
    /// only when none can.
    pub fn sleep(&self, me: u64, nanos: u64) -> Result<(), Ctl> {
        if nanos == 0 {
            return self.yield_now(me);
        }
        let until = self.inner.lock().expect("scheduler").clock + nanos;
        self.block(me, Wait::Until(until))
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
        inner.senders.insert(id, 1);
        id
    }

    pub fn add_sender(&self, ch: u64) {
        *self.inner.lock().expect("scheduler").senders.entry(ch).or_insert(0) += 1;
    }

    /// Puts `v` in channel `ch`, waking its receiver; sending is that and a scheduling point. If
    /// the receiver is gone, `v` is given back with the type to drop it as.
    pub fn deliver(&self, ch: u64, v: Value) -> Option<(Value, Ty)> {
        let mut inner = self.inner.lock().expect("scheduler");
        if let Some(t) = inner.deaf.get(&ch) {
            return Some((v, t.clone()));
        }
        inner.channels.entry(ch).or_default().push_back(v);
        Self::wake(&mut inner, &Wait::Channel(ch));
        None
    }

    /// The receiving end of `ch` is gone: what is in the channel is given back to be dropped, as
    /// is whatever is sent to it from now on.
    pub fn receiver_gone(&self, ch: u64, elem: Ty) -> Vec<Value> {
        let mut inner = self.inner.lock().expect("scheduler");
        inner.deaf.insert(ch, elem);
        inner.channels.remove(&ch).map(Vec::from).unwrap_or_default()
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
        self.sender_gone(ch);
        self.yield_now(me)
    }

    /// A sender of `ch` is gone, dropped: a destructor does not suspend, so this is no scheduling
    /// point.
    pub fn sender_gone(&self, ch: u64) {
        let mut inner = self.inner.lock().expect("scheduler");
        let left = inner.senders.get_mut(&ch).map(|n| {
            *n = n.saturating_sub(1);
            *n
        });
        if left.unwrap_or(0) == 0 {
            inner.closed.insert(ch);
            Self::wake(&mut inner, &Wait::Channel(ch));
        }
    }
}
