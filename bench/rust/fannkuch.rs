// fannkuch-redux: permutations of small arrays, flipped; integer work over arrays.
fn main() {
    let n: usize = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(7);
    let mut perm = [0i32; 16]; let mut perm1 = [0i32; 16]; let mut count = [0i32; 16];
    let (mut max_flips, mut checksum, mut r, mut perm_count) = (0i32, 0i32, n, 0i32);
    for i in 0..n { perm1[i] = i as i32; }
    loop {
        while r != 1 { count[r - 1] = r as i32; r -= 1; }
        perm[..n].copy_from_slice(&perm1[..n]);
        let mut flips = 0;
        loop { let k = perm[0] as usize; if k == 0 { break; } perm[..=k].reverse(); flips += 1; }
        max_flips = max_flips.max(flips);
        checksum += if perm_count % 2 == 0 { flips } else { -flips };
        loop {
            if r == n { println!("{}\nPfannkuchen({}) = {}", checksum, n, max_flips); return; }
            let p0 = perm1[0];
            for i in 0..r { perm1[i] = perm1[i + 1]; }
            perm1[r] = p0;
            count[r] -= 1;
            if count[r] > 0 { break; }
            r += 1;
        }
        perm_count += 1;
    }
}
