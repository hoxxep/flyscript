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

/// A file open on a descriptor: all of it, read from or written to at `pos`, and for a write, put
/// back where it came from as it is written.
#[derive(Default, Debug)]
pub struct OpenFile {
    pub path: String,
    pub data: Vec<u8>,
    pub pos: usize,
    pub writing: bool,
}

#[derive(Debug)]
pub struct World {
    /// Files open on descriptors, by number, and the next number.
    pub fds: HashMap<u32, OpenFile>,
    pub next_fd: u32,
    pub out: Vec<String>,
    pub files: HashMap<String, String>,
    /// The directories made, beside those the files' paths imply.
    pub dirs: std::collections::BTreeSet<String>,
    /// The process's environment.
    pub env: HashMap<String, String>,
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
    /// The generator of `Io.random`'s bytes, from the seed, `0` before the first.
    random_rng: u64,
    /// Whether files not in `files` are read from, and written to, the real file system: so
    /// for `flyc run`, never for tests, which stay deterministic (§6.4).
    pub real_fs: bool,
    /// The status the program asked to end with, by `exit`.
    pub exit: Option<i32>,
}

impl Default for World {
    fn default() -> World {
        World::seeded(0x5eed)
    }
}

/// A value of a world's JSON (§6.4), as `FLY_WORLD` gives it.
enum Json {
    Str(String),
    Num(u64),
    Bool(bool),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
    Null,
}

struct JsonReader<'a> {
    s: &'a [u8],
    at: usize,
}

impl JsonReader<'_> {
    fn space(&mut self) {
        while self.at < self.s.len() && self.s[self.at].is_ascii_whitespace() {
            self.at += 1;
        }
    }

    fn eat(&mut self, c: u8) -> Result<(), String> {
        self.space();
        if self.s.get(self.at) == Some(&c) {
            self.at += 1;
            Ok(())
        } else {
            Err(format!("FLY_WORLD: `{}` expected at byte {}", c as char, self.at))
        }
    }

    fn value(&mut self) -> Result<Json, String> {
        self.space();
        match self.s.get(self.at) {
            Some(b'"') => self.string().map(Json::Str),
            Some(b'[') => {
                self.at += 1;
                let mut items = Vec::new();
                self.space();
                if self.s.get(self.at) == Some(&b']') {
                    self.at += 1;
                    return Ok(Json::Arr(items));
                }
                loop {
                    items.push(self.value()?);
                    self.space();
                    match self.s.get(self.at) {
                        Some(b',') => self.at += 1,
                        _ => break,
                    }
                }
                self.eat(b']')?;
                Ok(Json::Arr(items))
            }
            Some(b'{') => {
                self.at += 1;
                let mut pairs = Vec::new();
                self.space();
                if self.s.get(self.at) == Some(&b'}') {
                    self.at += 1;
                    return Ok(Json::Obj(pairs));
                }
                loop {
                    self.space();
                    let k = self.string()?;
                    self.eat(b':')?;
                    pairs.push((k, self.value()?));
                    self.space();
                    match self.s.get(self.at) {
                        Some(b',') => self.at += 1,
                        _ => break,
                    }
                }
                self.eat(b'}')?;
                Ok(Json::Obj(pairs))
            }
            _ => {
                let start = self.at;
                while self.at < self.s.len() && !matches!(self.s[self.at], b',' | b']' | b'}') && !self.s[self.at].is_ascii_whitespace() {
                    self.at += 1;
                }
                let word = std::str::from_utf8(&self.s[start..self.at]).unwrap_or("");
                match word {
                    "true" => Ok(Json::Bool(true)),
                    "false" => Ok(Json::Bool(false)),
                    "null" => Ok(Json::Null),
                    _ => word.parse().map(Json::Num).map_err(|_| format!("FLY_WORLD: `{word}` is not a value the world reads")),
                }
            }
        }
    }

    fn string(&mut self) -> Result<String, String> {
        self.eat(b'"')?;
        let mut out = String::new();
        let mut chars = std::str::from_utf8(&self.s[self.at..]).map_err(|_| "FLY_WORLD: not UTF-8".to_string())?.char_indices();
        while let Some((i, c)) = chars.next() {
            match c {
                '"' => {
                    self.at += i + 1;
                    return Ok(out);
                }
                '\\' => match chars.next().map(|(_, e)| e) {
                    Some('n') => out.push('\n'),
                    Some('r') => out.push('\r'),
                    Some('t') => out.push('\t'),
                    Some('b') => out.push('\u{8}'),
                    Some('f') => out.push('\u{c}'),
                    Some('u') => {
                        let hex: String = (0..4).filter_map(|_| chars.next().map(|(_, h)| h)).collect();
                        let v = u32::from_str_radix(&hex, 16).map_err(|_| "FLY_WORLD: a bad `\\u` escape".to_string())?;
                        out.push(char::from_u32(v).unwrap_or('\u{fffd}'));
                    }
                    Some(e) => out.push(e),
                    None => break,
                },
                c => out.push(c),
            }
        }
        Err("FLY_WORLD: a string is not closed".to_string())
    }
}

impl World {
    pub fn seeded(seed: u64) -> World {
        World {
            out: Vec::new(),
            fds: HashMap::new(),
            next_fd: 3,
            files: HashMap::new(),
            dirs: std::collections::BTreeSet::new(),
            env: HashMap::new(),
            incoming: VecDeque::new(),
            peers: HashMap::new(),
            sockets: Vec::new(),
            profiles: HashMap::new(),
            quotas: HashMap::new(),
            fault_percent: 0,
            seed,
            rng: seed.max(1),
            random_rng: 0,
            real_fs: false,
            exit: None,
        }
    }

    /// The world `FLY_WORLD` describes (§6.4), as every back end reads it: the requests that
    /// arrive, the peers and what each answers, the profiles and quotas of its database, the
    /// percentage of operations that fail, and the seed, which also chooses who runs next.
    pub fn from_json(text: &str) -> Result<World, String> {
        let mut r = JsonReader { s: text.as_bytes(), at: 0 };
        let Json::Obj(pairs) = r.value()? else { return Err("FLY_WORLD: an object was expected".to_string()) };
        let mut world = World::default();
        let mut faults = 0;
        for (k, v) in pairs {
            match (k.as_str(), v) {
                ("incoming", Json::Arr(items)) => {
                    for item in items {
                        if let Json::Str(s) = item {
                            world.incoming.push_back(s.into_bytes());
                        }
                    }
                }
                ("peers", Json::Obj(ps)) => {
                    for (host, reply) in ps {
                        if let Json::Str(s) = reply {
                            world.peers.insert(host, s.into_bytes());
                        }
                    }
                }
                ("profiles", Json::Obj(ps)) => {
                    for (user, name) in ps {
                        if let Json::Str(s) = name {
                            world.profiles.insert(user, s);
                        }
                    }
                }
                ("quotas", Json::Obj(ps)) => {
                    for (token, allowed) in ps {
                        world.quotas.insert(token, matches!(allowed, Json::Bool(true)));
                    }
                }
                ("faults", Json::Num(n)) => faults = n,
                ("seed", Json::Num(n)) => {
                    world.seed = n;
                    world.rng = n.max(1);
                }
                _ => {}
            }
        }
        world.fault_percent = faults;
        Ok(world)
    }

    /// Whether the next I/O operation fails (xorshift, so a seed gives the same run every time).
    /// `n` bytes of `Io.random`: of the seed, as every back end makes them against a simulated
    /// world, so that a run replays; of the system's generator for `flyc run`.
    pub fn random(&mut self, n: usize) -> Vec<u8> {
        if self.real_fs {
            use std::io::Read;
            let mut b = vec![0; n];
            std::fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut b)).expect("the system's secure random generator");
            return b;
        }
        if self.random_rng == 0 {
            self.random_rng = (self.seed ^ 0x9E37_79B9_7F4A_7C15) | 1;
        }
        let mut out = Vec::with_capacity(n);
        while out.len() < n {
            let mut r = self.random_rng;
            r ^= r << 13;
            r ^= r >> 7;
            r ^= r << 17;
            self.random_rng = r;
            for k in 0..8 {
                if out.len() < n {
                    out.push((r >> (8 * k)) as u8);
                }
            }
        }
        out
    }

    pub fn fault(&mut self) -> bool {
        self.rng ^= self.rng << 13;
        self.rng ^= self.rng >> 7;
        self.rng ^= self.rng << 17;
        self.rng % 100 < self.fault_percent
    }

    /// Whether `path` is a directory of the simulated file system: the working directory, one made,
    /// or one a file's path passes through.
    pub fn is_dir(&self, path: &str) -> bool {
        path.is_empty() || self.dirs.contains(path) || self.files.keys().any(|f| f.starts_with(&format!("{path}/"))) || self.dirs.iter().any(|d| d.starts_with(&format!("{path}/")))
    }

    /// The entries of a directory of the simulated file system, in order.
    pub fn entries(&self, path: &str) -> Vec<String> {
        let prefix = if path.is_empty() { String::new() } else { format!("{path}/") };
        let mut names: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        for p in self.files.keys().chain(self.dirs.iter()) {
            if let Some(rest) = p.strip_prefix(&prefix) {
                if let Some(first) = rest.split('/').next() {
                    if !first.is_empty() {
                        names.insert(first.to_string());
                    }
                }
            }
        }
        names.into_iter().collect()
    }

    pub fn open_socket(&mut self, input: Vec<u8>) -> u64 {
        self.sockets.push(Socket { input, ..Default::default() });
        self.sockets.len() as u64 - 1
    }
}
