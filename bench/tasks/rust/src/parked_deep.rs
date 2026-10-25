// A million tasks, each parked two calls deep: a handler, and the helper it waits in.
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

async fn pause(ms: u64, tag: u64) -> u64 {
    let before = tag * 7;
    tokio::time::sleep(Duration::from_millis(ms)).await;
    before + tag
}

async fn serve(id: u64) -> u64 {
    let a = id * 3;
    let got = pause(2000, id).await;
    a + got
}

#[tokio::main]
async fn main() {
    let n: u64 = 1_000_000;
    let start = Instant::now();
    let total = Arc::new(AtomicI64::new(0));
    let mut hs = Vec::with_capacity(n as usize);
    for i in 0..n {
        let t = total.clone();
        hs.push(tokio::spawn(async move { t.fetch_add(serve(i).await as i64, Ordering::SeqCst); }));
    }
    for h in hs { h.await.unwrap(); }
    println!("{n} tasks parked and woken in {} ms, {}", start.elapsed().as_millis(), total.load(Ordering::SeqCst));
}
