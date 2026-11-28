//! Rebuild the two finite minimax bounds used in the FR-9018 wheel.
//! Compile with `rustc --edition=2021 -O replay_partitioned_wheel.rs`.
//! Run with `./replay_partitioned_wheel parent.txt parent` or
//! `./replay_partitioned_wheel even.txt even`. Each output row gives the
//! bucket number, its prime count, and its signed surviving lower bound.
//! The printed independent bound charges the largest fiber for each prime
//! separately. The paired bound charges the largest two-fiber union.
use std::fs;
use std::io::{self, Write};

struct Wheel {
    bound: u32,
    split: [u32; 7],
    cutoff: u32,
    paired_through: u32,
}
const PARENT: Wheel = Wheel {
    bound: 1_926_574_681,
    split: [7, 11, 13, 17, 19, 23, 29],
    cutoff: 7643,
    paired_through: 113,
};
const EVEN: Wheel = Wheel {
    bound: 100_000_000,
    split: [3, 5, 7, 11, 13, 17, 19],
    cutoff: 1721,
    paired_through: 19,
};

fn small_primes() -> Vec<u32> {
    let mut p = Vec::new();
    for n in 2u32..=44_000 {
        if p.iter().take_while(|&&d| d * d <= n).all(|&d| n % d != 0) {
            p.push(n);
        }
    }
    p
}

fn tables(small: &[u32], wheel: &Wheel) -> Vec<Vec<u32>> {
    // Sequential segments of odd numbers. No table or prime list is read.
    let mut rows: Vec<Vec<u32>> = (0..128).map(|_| Vec::new()).collect();
    let mut lo = 3u64;
    let odd_limit = (wheel.bound - ((wheel.bound + 1) % 2)) as u64;
    while lo <= odd_limit {
        let hi = (lo + 2_000_000 - 2).min(odd_limit);
        let mut prime = vec![true; ((hi - lo) / 2 + 1) as usize];
        for &q32 in &small[1..] {
            let q = q32 as u64;
            if q * q > hi {
                break;
            }
            let mut start = (lo.div_ceil(q) * q).max(q * q);
            if start % 2 == 0 {
                start += q;
            }
            let mut pos = ((start - lo) / 2) as usize;
            while pos < prime.len() {
                prime[pos] = false;
                pos += q as usize;
            }
        }
        for (i, ok) in prime.into_iter().enumerate() {
            if !ok {
                continue;
            }
            let p = (lo + 2 * i as u64) as u32;
            if p <= wheel.split[6] {
                continue;
            }
            let bucket = wheel
                .split
                .iter()
                .rev()
                .fold(0usize, |id, &q| 2 * id + ((2 * (p % q) > q) as usize));
            rows[bucket].push(p);
        }
        lo = hi + 2;
    }
    rows
}

fn maximum_pair(row: &[u32], q: u32, r: u32) -> (u32, u32) {
    let (a, b) = (q as usize, r as usize);
    let mut joint = vec![0u32; a * b];
    for &p in row {
        joint[(p % q) as usize * b + (p % r) as usize] += 1;
    }
    let mut right = vec![0u32; b];
    for line in joint.chunks_exact(b) {
        for (j, &n) in line.iter().enumerate() {
            right[j] += n;
        }
    }
    let mut first_max = 0;
    let paired = joint
        .chunks_exact(b)
        .map(|line| {
            let first_loss: u32 = line.iter().sum();
            first_max = first_max.max(first_loss);
            let second_loss = (0..b).map(|j| right[j] - line[j]).max().unwrap();
            first_loss + second_loss
        })
        .max()
        .unwrap();
    (paired, first_max + right.into_iter().max().unwrap())
}

fn lower(row: &[u32], primes: &[u32], wheel: &Wheel) -> (i64, i64) {
    let early: Vec<u32> = primes
        .iter()
        .copied()
        .filter(|&q| wheel.split[6] < q && q <= wheel.paired_through)
        .collect();
    let mut pairing = early.chunks_exact(2);
    let (mut charged, mut separate) = (0u32, 0u32);
    for pair in pairing.by_ref() {
        let (joint, ordinary) = maximum_pair(row, pair[0], pair[1]);
        charged += joint;
        separate += ordinary;
    }
    let mut rest = pairing.remainder().to_vec();
    rest.extend(
        primes
            .iter()
            .copied()
            .filter(|&q| wheel.paired_through < q && q < wheel.cutoff),
    );
    let mut remaining = row.len() as i64 - charged as i64;
    for q in rest.into_iter().rev() {
        let mut hist = vec![0u32; q as usize];
        for &p in row {
            hist[(p % q) as usize] += 1;
        }
        remaining -= hist.into_iter().max().unwrap() as i64;
    }
    (remaining, remaining - (separate - charged) as i64)
}

fn main() {
    let small = small_primes();
    let cut = std::env::args()
        .nth(1)
        .expect("supply the output filename, optionally followed by even");
    let wheel = match std::env::args().nth(2).as_deref() {
        Some("even") => &EVEN,
        None | Some("parent") => &PARENT,
        _ => panic!("mode must be parent or even"),
    };
    let rows = tables(&small, wheel);
    let cores = 3;
    let mut results = vec![(0i64, 0i64); rows.len()];
    std::thread::scope(|scope| {
        for (batch, target) in rows
            .chunks(rows.len().div_ceil(cores))
            .zip(results.chunks_mut(rows.len().div_ceil(cores)))
        {
            let s = &small;
            scope.spawn(move || {
                for (r, out) in batch.iter().zip(target) {
                    *out = lower(r, s, wheel);
                }
            });
        }
    });
    let mut text = String::new();
    for (i, &(v, _)) in results.iter().enumerate() {
        text.push_str(&format!("{} {} {}\n", i, rows[i].len(), v));
    }
    let min = results.iter().map(|r| r.0).min().unwrap();
    let independent = results.iter().map(|r| r.1).min().unwrap();
    text.push_str(&format!("minimum {}\n", min));
    fs::write(cut, text).unwrap();
    writeln!(
        io::stdout(),
        "{} tables, {} primes above {}, independent minimum {}, paired minimum {}",
        rows.len(),
        rows.iter().map(Vec::len).sum::<usize>(),
        wheel.split[6],
        independent,
        min
    )
    .unwrap();
}
