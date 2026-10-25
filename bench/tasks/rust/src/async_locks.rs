// Twenty million locks of tokio's `Mutex` no other task contends: a lock that is an `.await`
// point, as `Mutex.lock` is a scheduling point.
use std::sync::Arc;
use std::time::Instant;
use tokio::sync::Mutex;

#[tokio::main]
async fn main() {
    let n: u64 = 20_000_000;
    let m = Arc::new(Mutex::new(0u64));
    let start = Instant::now();
    let m2 = m.clone();
    tokio::spawn(async move {
        for _ in 0..n { *m2.lock().await += 1; }
    }).await.unwrap();
    println!("{} locks in {} ms", *m.lock().await, start.elapsed().as_millis());
}
