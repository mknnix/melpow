use std::time::Instant;

use melpow::{HashFunction, SVec};

struct Hasher;

impl HashFunction for Hasher {
    fn hash(&self, b: &[u8], k: &[u8]) -> SVec<u8> {
        let mut res = blake3::keyed_hash(blake3::hash(k).as_bytes(), b);
        for _ in 0..100 {
            res = blake3::hash(res.as_bytes());
        }
        SVec::from_slice(res.as_bytes())
    }
}

fn main() {
    for difficulty in 10..25 {
        let start = Instant::now();
        let p = melpow::Proof::generate_with_progress(b"hello", difficulty, |_| {}, Hasher);
        eprintln!(
            "difficulty = {}\tlength = {}\tspeed = {:.2} H/s",
            difficulty,
            p.to_bytes().len(),
            2.0f64.powi(difficulty as _) / start.elapsed().as_secs_f64()
        );
        let start = Instant::now();
        let _ = p.verify(b"hello", difficulty, Hasher);
        eprintln!("verify cost = {:?}", start.elapsed());
    }
}
