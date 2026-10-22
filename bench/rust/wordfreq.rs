// Word frequencies: text built from a vocabulary, split into words, counted in a hash map, and
// the most frequent shown; strings, hashing and sorting.
use std::collections::HashMap;
use std::fmt::Write;
fn main() {
    let n: u32 = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(1000);
    let mut text = String::new();
    let mut seed: u64 = 42;
    for i in 0..n {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        if i > 0 { text.push(' '); }
        write!(text, "w{}", (seed >> 33) % 20000).unwrap();
    }
    let mut counts: HashMap<&str, u32> = HashMap::new();
    for w in text.split_whitespace() { *counts.entry(w).or_insert(0) += 1; }
    println!("{} distinct words", counts.len());
    let mut all: Vec<(&str, u32)> = counts.into_iter().collect();
    all.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
    for (w, c) in &all[..10] { println!("{} {}", w, c); }
}
