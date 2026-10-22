//! The deterministic world the root `Io` handler runs against (§6.4): in-memory files, sockets
//! carrying scripted requests, a database of profiles and quotas, and captured output. Faults are
//! injected from a seed, so a run is reproducible exactly.

use std::collections::{HashMap, VecDeque};

#[derive(Default, Debug)]
pub struct Socket {
    pub input: Vec<u8>,
    pub pos: usize,
    /// Every status written, with its body.
    pub written: Vec<(u16, String)>,
    /// What was written with `write`, shown when the socket closes.
    pub bytes: Vec<u8>,
    /// The peer the program connected to, if it did.
    pub peer: Option<String>,
}

#[derive(Debug)]
pub struct World {
    pub out: Vec<String>,
    pub files: HashMap<String, String>,
    /// Requests waiting to be accepted, each becoming a socket.
    pub incoming: VecDeque<Vec<u8>>,
    /// The hosts a program may connect to, `host:port`, each with what it sends back.
    pub peers: HashMap<String, Vec<u8>>,
    pub sockets: Vec<Socket>,
    pub profiles: HashMap<String, String>,
    pub quotas: HashMap<String, bool>,
    /// The chance, in percent, that an I/O operation times out.
    pub fault_percent: u64,
    /// The seed, also used by the task scheduler.
    pub seed: u64,
    rng: u64,
    /// Whether files not in `files` are read from, and written to, the real file system: so
    /// for `flyc run`, never for tests, which stay deterministic (§6.4).
    pub real_fs: bool,
}

impl Default for World {
    fn default() -> World {
        World::seeded(0x5eed)
    }
}

impl World {
    pub fn seeded(seed: u64) -> World {
        World {
            out: Vec::new(),
            files: HashMap::new(),
            incoming: VecDeque::new(),
            peers: HashMap::new(),
            sockets: Vec::new(),
            profiles: HashMap::new(),
            quotas: HashMap::new(),
            fault_percent: 0,
            seed,
            rng: seed.max(1),
            real_fs: false,
        }
    }

    /// Whether the next I/O operation fails (xorshift, so a seed gives the same run every time).
    pub fn fault(&mut self) -> bool {
        self.rng ^= self.rng << 13;
        self.rng ^= self.rng >> 7;
        self.rng ^= self.rng << 17;
        self.rng % 100 < self.fault_percent
    }

    pub fn open_socket(&mut self, input: Vec<u8>) -> u64 {
        self.sockets.push(Socket { input, ..Default::default() });
        self.sockets.len() as u64 - 1
    }
}
