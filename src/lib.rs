//! `melpow` is the crate that implements MelPoW, Themelio's version of non-interactive proofs of sequential work, which are just "Interactive Proofs of Sequential Work" by Cohen and Pietrzak subjected to a Fiat-Shamir transformation. MelPoW is used as the core mechanism behind Melmint, the algorithmic monetary policy system that stabilizes the mel.
//!
//! `Proof` is the main interface to MelPoW. It represents a proof that a certain amount of sequential work, represented by a **difficulty**, has been done starting from a **puzzle**. The difficulty is exponential: a difficulty of N represents that `O(2^N)` work has been done.

mod hash;
mod node;
pub use crate::node::{Node, SVec};
pub use hash::HashFunction;

use std::{convert::TryInto, sync::Arc, time::{Duration, Instant}};
use rustc_hash::FxHashMap;

use smol;
//use smol::prelude::*;

use bincode;
use serde::{Serialize, Deserialize};
use anyhow;

const PROOF_CERTAINTY: usize = 200;

type ProofMap = FxHashMap<Node, SVec<u8>>;
type ArcProofMap = Arc<ProofMap>;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
/// A MelPoW proof with an opaque representation that is guaranteed to be stable. It can be cloned relatively cheaply because it's internally reference counted.
pub struct Proof(ArcProofMap);

#[allow(non_snake_case)]
#[derive(Clone, Debug, Serialize, Deserialize)]
/// Represents a proof generating in progress, it will return a Proof if the work has completed
pub struct ProofUnderProgress {
    proof_map: ArcProofMap,
    chi: SVec<u8>,
    //gammas: Vec<node::Node>,

    total_count: f64,
    current_count: f64,

    puzzle: Vec<u8>,
    difficulty: usize,

    nd: node::Node,

    TICK_SECS: u64, // const in the lifetime of a instance, do not modify it once constructed.
    tick_secs_override: Option<u64>,

    progressing: bool,
    finish: bool,
    proof: Option<Proof>,

}

impl ProofUnderProgress {
    /// initial a blank progress for new proof. but without hash function set, you need to give it for each call to self.next
    pub fn init(puzzle: &[u8], difficulty: usize) -> Self {
        let mut proof_map = Arc::new(FxHashMap::default());
        let chi = hash::bts_key(puzzle, b"chi");

        let gammas = gen_gammas(puzzle, difficulty);
        gammas.into_iter().for_each(|gamma| {
            gamma_to_path(gamma).into_iter().for_each(|pn| {
                proof_map.insert(pn, SVec::new());
            });

            proof_map.insert(gamma, SVec::new());
        });

        let total_count = 2.0f64.powi(difficulty as _);
        let current_count = 0.0;

        Self {
            proof_map,
            chi,
            //gammas,

            total_count,
            current_count,

            puzzle: puzzle.to_vec(),
            difficulty,

            nd: node::Node::new_zero(),

            TICK_SECS: Self::default_tick(),
            tick_secs_override: None,

            progressing: false,
            finish: false,
            proof: None,
        }
    }

    /// save the snapshot of generating status into a byte array.
    pub fn save(&self) -> anyhow::Result<Vec<u8>> {
        Ok( bincode::serialize(self)? )
    }
    /// recovering the snapshot from a byte array. (Notice: this operation will return a new instance with the state)
    pub fn recovery_from(data: &[u8]) -> anyhow::Result<Self> {
        let mut s: Self = bincode::deserialize(data)?;
        s.progressing = false;
        return Ok(s);
    }

    /// get the percentage of current progress...
    pub fn current_percentage(&self) -> Option<f64> {
        Some( 100.0 * self.current_radio()? )
    }
    pub fn current_radio(&self) -> Option<f64> {
        if self.current_count <= 0.0 || self.total_count <= 0.0 {
            return None;
        }

        Some(self.current_count / self.total_count)
    }

    // getters for .total_count / .current_count
    pub fn total_count(&self) -> f64 { self.total_count }
    pub fn current_count(&self) -> f64 { self.current_count }

    /// the core handle function for the progress of generating proof.
    /// if the progress callback given, call for give the clone of current status.
    /// ** make sure the .finish and .current_count field only modified by this function **
    pub async fn do_progressing<H: HashFunction>(&mut self, saving: smol::channel::Sender<Self>, h: H) {
        if self.finish { return; }

        // assert only one do_progressing exists.
        assert!(self.progressing == false);
        self.progressing = true;

        let chi = self.chi.clone();

        let mut time = Instant::now();
        let tick = self.get_tick();
        //let tick = Duration::from_secs(tick);

        let map_ch = smol::channel::bounded(1);
        let info_ch = smol::channel::bounded(1);

        let (map_send, map_recv) = map_ch;
        let (info_send, info_recv) = info_ch;

        let calcing = node::calc_labels_helper(
            &chi,
            self.difficulty,
            self.nd,
            info_send,
            map_recv,
            &h,
        );

        smol::future::race(calcing, async {
            let mut proof_map = Arc::make_mut(&'async_recursion mut self.proof_map);

            loop {
                map_send.send(proof_map).await;

                {
                    let (nd, lab) = info_recv.recv().await.unwrap();

                    if nd.len == self.difficulty {
                        self.current_count += 1.0;
                        //on_progress(current_count / total_count);
                    }
                    if proof_map.get(&nd).is_some() || nd.len == 0 {
                        proof_map.insert(nd, lab);
                    }

                    if let Some(radio) = self.current_radio() {
                        if radio >= 1.0 {
                            self.finish = true;
                        }
                    }
                }

                if time.elapsed().as_secs() >= tick {
                    time = Instant::now();
                    saving.send(self.clone()).await;
                }
            }
        }).await;
    }
    /// generate the proof. this method should be call with The Final State, otherwise it will got you an unwanted result
    pub fn generate_proof(&mut self) -> Proof {
        if ! self.finish {
            panic!("do not call this with still in progressing...");
        }
        if let Some(proof) = &self.proof {
            return proof.clone();
        }

        let proof = Proof( self.proof_map.clone() );

        self.proof = Some(proof);
        self.generate_proof()
    }

    /// default tick value is read-only for everyone (don't modify unless you have a good idea)
    pub fn default_tick() -> u64 { 30 }

    /// get the interval size, return the default value if no any override
    pub fn get_tick(&self) -> u64 {
        if let Some(tick) = self.tick_secs_override {
            return tick;
        }

        self.TICK_SECS
    }
    /// specify a tick value to replace the default... returns True if success
    pub fn override_tick(&mut self, tick: u64) -> bool {
        // refused to override again
        if let Some(_) = self.tick_secs_override {
            return false;
        }
        // refused to override if in progressing
        if self.progressing {
            return false;
        }

        // cannot accept too small interval
        //assert!(tick >= 5);

        self.tick_secs_override = Some(tick);
        return true;
    }
}

impl Proof {
    /// un-comment next line if scheduled to deprecating this not interrupt-recoverable public interface...
    //#[deprecated(since="0.3.0", note="recommended use `ProofUnderProgress` instead")]
    pub fn generate<H: HashFunction>(puzzle: &[u8], difficulty: usize, h: H) -> Self {
        Self::generate_with_progress(puzzle, difficulty, |_| (), h)
    }

    /// un-comment next line if scheduled to deprecating this not interrupt-recoverable public interface...
    //#[deprecated(since="0.3.0", note="recommended use `ProofUnderProgress` instead")]
    pub fn generate_with_progress<H: HashFunction>(
        puzzle: &[u8],
        difficulty: usize,
        on_progress: impl Fn(f64),
        h: H,
    ) -> Self {
        let mut proof_map = FxHashMap::default();
        let chi = hash::bts_key(puzzle, b"chi");
        let gammas = gen_gammas(puzzle, difficulty);

        gammas.into_iter().for_each(|gamma| {
            gamma_to_path(gamma).into_iter().for_each(|pn| {
                proof_map.insert(pn, SVec::new());
            });

            proof_map.insert(gamma, SVec::new());
        });

        let total_count = 2.0f64.powi(difficulty as _);
        let mut current_count = 0.0;
        node::calc_labels(
            &chi,
            difficulty,
            &mut |nd, lab| {
                if nd.len == difficulty {
                    current_count += 1.0;
                    on_progress(current_count / total_count);
                }
                if proof_map.get(&nd).is_some() || nd.len == 0 {
                    proof_map.insert(nd, SVec::from_slice(lab));
                }
            },
            h,
        );

        Proof(proof_map.into())
    }
}
impl Proof {
    /// Verifies a MelPoW proof.
    #[must_use]
    pub fn verify<H: HashFunction>(&self, puzzle: &[u8], difficulty: usize, h: H) -> bool {
        let mut output: bool = true;

        if difficulty > 100 {
            output = false;
        } else {
            let chi = hash::bts_key(puzzle, b"chi");
            let gammas = gen_gammas(puzzle, difficulty);
            let phi = self.0[&node::Node::new_zero()].clone();
            let mut temp_map = self.0.clone();
            let temp_map = Arc::make_mut(&mut temp_map);

            for gamma in gammas {
                match self.0.get(&gamma) {
                    None => {
                        output = false;
                    }
                    Some(label) => {
                        // verify that the label is correctly calculated from parents
                        let mut hasher = hash::Accumulator::new(&chi, &h);
                        hasher.add(&gamma.to_bytes());
                        for parent in gamma.get_parents(difficulty) {
                            match self.0.get(&parent) {
                                None => return false,
                                Some(parlab) => {
                                    hasher.add(parlab);
                                }
                            }
                        }
                        if hasher.hash() != *label {
                            output = false;
                        }

                        // check "merkle-like" commitment
                        (0..difficulty).rev().for_each(|index| {
                            let mut h = hash::Accumulator::new(&chi, &h);
                            h.add(&gamma.take(index).to_bytes());
                            let g_l_0 = gamma.take(index).append(0);
                            let g_l_1 = gamma.take(index).append(1);
                            let g_l = gamma.take(index);
                            let h = h.add(&temp_map[&g_l_0]).add(&temp_map[&g_l_1]).hash();
                            temp_map.insert(g_l, h);
                        });

                        if phi != self.0[&node::Node::new_zero()].clone() {
                            output = false;
                        }
                    }
                }
            }
        }

        output
    }

    /// Serializes the proof to a byte vector.
    pub fn to_bytes(&self) -> Vec<u8> {
        let unit_size = 8 + 32;
        let mut output = Vec::with_capacity(unit_size * self.0.len());

        self.0.iter().for_each(|(key, value)| {
            assert_eq!(value.len(), 32);
            output.extend_from_slice(&key.to_bytes());
            output.extend_from_slice(value);
        });

        output
    }
    /// Deserializes a proof from a byte vector.
    pub fn from_bytes(mut bts: &[u8]) -> Option<Self> {
        let unit_size = 8 + 32;

        if bts.len() % unit_size != 0 {
            None
        } else {
            let mut omap = FxHashMap::default();
            while !bts.is_empty() {
                let nd = node::Node::from_bytes(&bts[0..8])?;
                let lab = SVec::from_slice(&bts[8..32 + 8]);
                omap.insert(nd, lab);
                bts = &bts[unit_size..]
            }

            Some(Proof(omap.into()))
        }
    }
}

fn gen_gammas(puzzle: &[u8], difficulty: usize) -> Vec<node::Node> {
    (0..PROOF_CERTAINTY)
        .map(|index| {
            let g_seed = hash::bts_key(puzzle, format!("gamma-{}", index).as_bytes());
            let g_int = u64::from_le_bytes(g_seed[0..8].try_into().unwrap());
            let shift = 64 - difficulty;
            let g_int = (g_int >> shift) << shift;
            let g_int = g_int.reverse_bits();
            node::Node::new(g_int, difficulty)
        })
        .collect::<Vec<node::Node>>()
}

fn gamma_to_path(gamma: node::Node) -> Vec<node::Node> {
    let n = gamma.len;
    (0..n)
        .map(|index| gamma.take(index).append(1 - gamma.get_bit(index) as usize))
        .collect::<Vec<node::Node>>()
}

#[cfg(test)]
mod tests {
    use crate::{HashFunction, Proof, ProofUnderProgress, SVec};

    struct Hasher;

    impl HashFunction for Hasher {
        fn hash(&self, b: &[u8], k: &[u8]) -> SVec<u8> {
            //println!("hasher called");
            let res = blake3::keyed_hash(blake3::hash(k).as_bytes(), b);
            SVec::from_slice(res.as_bytes())
        }
    }

    #[test]
    fn test_simple() {
        let difficulty = 16;
        let puzzle = vec![];
        let proof = Proof::generate(&puzzle, difficulty, Hasher);
        assert!(proof.verify(&puzzle, difficulty, Hasher));
        assert!(!proof.verify(&puzzle, difficulty + 1, Hasher));
        assert!(!proof.verify(b"hello", difficulty, Hasher));
        assert_eq!(Proof::from_bytes(&proof.to_bytes()).unwrap(), proof);
        println!("[SIMPLE] proof length is {}", proof.to_bytes().len())
    }

    // RUST_BACKTRACE=full cargo test -v -- --nocapture
    #[test]
    fn test_interruptable() {
        let difficulty = 17;
        let puzzle = b"demopuzfortestonly".to_vec();
        println!("diff: {}, puz: {:?}", difficulty, puzzle);

        let mut pup = ProofUnderProgress::init(&puzzle, difficulty);
        assert!(pup.override_tick(5));

        pup.do_progressing(&mut |state: ProofUnderProgress|{
            println!("2nd PUP: tick={:?}|%={:?}", state.get_tick(), state.current_percentage());
            println!("2nd PUP dumps: {:?}", state);
        }, Hasher);
        println!("2nd PUP proof completed");
        let proof_2nd = pup.generate_proof();

        let proof_orig = Proof::generate_with_progress(&puzzle, difficulty, |p|{println!("generate: {:?}", p);}, Hasher);
        assert_eq!(proof_orig, proof_2nd);

        for proof in vec![proof_orig.clone(), proof_2nd.clone()] {
            println!("proof length is {}", proof.to_bytes().len());
            assert!(proof.verify(&puzzle, difficulty, Hasher));
            assert!(!proof.verify(&puzzle, difficulty + 1, Hasher));
            assert!(!proof.verify(b"hello", difficulty, Hasher));
            assert_eq!(Proof::from_bytes(&proof.to_bytes()).unwrap(), proof);

        }

        assert_eq!(proof_2nd, proof_orig);
    }

    //#[test]
    fn test_recovery() {
        let difficulty = 18;
        let puzzle = b"recovery".to_vec();

        let mut pup = ProofUnderProgress::init(&puzzle, difficulty);
        assert!(pup.override_tick(1));

        let mut rec = None;
        pup.do_progressing(&mut |state: ProofUnderProgress|{
            if let None = rec {
                rec = Some(state.save().unwrap());
            }

        }, Hasher);

        let p1 = pup.generate_proof();

        // ===================================

        let mut pup_rec = ProofUnderProgress::recovery_from(&rec.unwrap()).unwrap();
        pup_rec.do_progressing(&mut |state: ProofUnderProgress|{
            println!("recovered PUP: tick={:?}|%={:?}", state.get_tick(), state.current_percentage());
            //println!("recovered PUP dumps: {:?}", state);
        }, Hasher);

        let p2 = pup_rec.generate_proof();

        assert_eq!(p1, p2);

        for proof in vec![p1.clone(), p2.clone()] {
            println!("proof length is {}", proof.to_bytes().len());
            assert!(proof.verify(&puzzle, difficulty, Hasher));
            assert!(!proof.verify(&puzzle, difficulty + 1, Hasher));
            assert!(!proof.verify(b"hello", difficulty, Hasher));
            assert_eq!(Proof::from_bytes(&proof.to_bytes()).unwrap(), proof);

        }
    }
}
