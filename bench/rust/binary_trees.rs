// binary-trees, single-threaded: allocation and freeing of many small trees.
struct Node { kids: Option<(Box<Node>, Box<Node>)> }
fn make(d: u32) -> Box<Node> { Box::new(Node { kids: if d > 0 { Some((make(d - 1), make(d - 1))) } else { None } }) }
fn check(n: &Node) -> u32 { 1 + match &n.kids { Some((l, r)) => check(l) + check(r), None => 0 } }
fn main() {
    let n: u32 = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(10);
    let max = n.max(6);
    let s = make(max + 1); println!("stretch tree of depth {}\t check: {}", max + 1, check(&s)); drop(s);
    let long_lived = make(max);
    let mut d = 4;
    while d <= max {
        let iters = 1u32 << (max - d + 4); let mut sum = 0;
        for _ in 0..iters { let t = make(d); sum += check(&t); }
        println!("{}\t trees of depth {}\t check: {}", iters, d, sum);
        d += 2;
    }
    println!("long lived tree of depth {}\t check: {}", max, check(&long_lived));
}
