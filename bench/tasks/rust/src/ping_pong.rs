// Two tasks answering each other over channels, half a million round trips: what a message costs
// when the task it wakes is waiting for it.
use std::time::Instant;
use tokio::sync::mpsc::unbounded_channel;

#[tokio::main]
async fn main() {
    let n: u64 = 500_000;
    let (atx, mut arx) = unbounded_channel::<u64>();
    let (btx, mut brx) = unbounded_channel::<u64>();
    let start = Instant::now();
    // Both sides are tasks on the runtime's workers: the body of `main` runs on a thread of its own.
    let total = tokio::spawn(async move {
        let echo = tokio::spawn(async move {
            while let Some(v) = arx.recv().await { btx.send(v).unwrap(); }
        });
        let mut total: u64 = 0;
        for i in 0..n {
            atx.send(i).unwrap();
            if let Some(v) = brx.recv().await { total += v; }
        }
        drop(atx);
        echo.await.unwrap();
        total
    }).await.unwrap();
    println!("{n} round trips in {} ms ({total})", start.elapsed().as_millis());
}
