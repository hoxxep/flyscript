// A million tasks, each parked on a timer at once: the memory a parked task takes.
use std::time::{Duration, Instant};

#[tokio::main]
async fn main() {
    let n: u64 = 1_000_000;
    let start = Instant::now();
    let mut handles = Vec::with_capacity(n as usize);
    for _ in 0..n {
        handles.push(tokio::spawn(async { tokio::time::sleep(Duration::from_millis(2000)).await; }));
    }
    for h in handles { h.await.unwrap(); }
    println!("{n} tasks parked and woken in {} ms", start.elapsed().as_millis());
}
