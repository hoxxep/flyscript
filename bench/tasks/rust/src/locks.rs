// Twenty million `Mutex` locks no other task contends: what taking a lock and giving it back costs.
use std::sync::{Arc, Mutex};
use std::time::Instant;

#[tokio::main]
async fn main() {
    let n: u64 = 20_000_000;
    let m = Arc::new(Mutex::new(0u64));
    let start = Instant::now();
    let m2 = m.clone();
    tokio::spawn(async move {
        for _ in 0..n { *m2.lock().unwrap() += 1; }
    }).await.unwrap();
    println!("{} locks in {} ms", *m.lock().unwrap(), start.elapsed().as_millis());
}
