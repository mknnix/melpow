//! `melpow` is the crate that implements MelPoW, Themelio's version of non-interactive proofs of sequential work, which are just "Interactive Proofs of Sequential Work" by Cohen and Pietrzak subjected to a Fiat-Shamir transformation. MelPoW is used as the core mechanism behind Melmint, the algorithmic monetary policy system that stabilizes the mel.
//!
//! `Proof` is the main interface to MelPoW. It represents a proof that a certain amount of sequential work, represented by a **difficulty**, has been done starting from a **puzzle**. The difficulty is exponential: a difficulty of N represents that `O(2^N)` work has been done.

mod hash;
mod node;
pub use crate::node::SVec;
pub use hash::HashFunction;

use std::{convert::TryInto, sync::Arc, time::Instant};
use rustc_hash::FxHashMap;

use bincode;
use serde::{Serialize, Deserialize};
use anyhow;

const PROOF_CERTAINTY: usize = 200;

type ProofMap = Arc<FxHashMap< node::Node, SVec<u8> >>;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
/// A MelPoW proof with an opaque representation that is guaranteed to be stable. It can be cloned relatively cheaply because it's internally reference counted.
pub struct Proof(ProofMap);

#[allow(non_snake_case)]
#[derive(Serialize, Deserialize)]
/// Represents a proof generating in progress, it will return a Proof if the work has completed
pub struct ProofUnderProgress {
    proof_map: ProofMap,
    chi: SVec<u8>,
    gammas: Vec<node::Node>,

    total_count: f64,
    current_count: f64,

    nd: node::Node,
    n: usize,
    lab: SVec<u8>,

    l0: SVec<u8>, l1: SVec<u8>,
    nd0: node::Node, nd1: node::Node,

    puzzle: Vec<u8>,
    difficulty: usize,

    TICK_SECS: u64, // const in the lifetime of a instance, do not modify it once constructed.
    tick_secs_override: Option<u64>,
    ticks: u64, // a tick counter

    finish: bool,
    proof: Option<Proof>,

    /*#[serde(default = "None")]
    #[default = "None"]
    h: Option<Box<dyn HashFunction>>
    */
}

impl ProofUnderProgress {
    /// initial a blank progress for new proof. but without hash function set, you need to give it for each call to self.next
    pub fn init(puzzle: &[u8], difficulty: usize) -> Self {
        let mut proof_map = Arc::new(FxHashMap::default());
        let chi = hash::bts_key(puzzle, b"chi");

        let gammas = gen_gammas(puzzle, difficulty);
        let proof_map_mut = Arc::make_mut(&mut proof_map);
        for gamma in gammas.clone() {
            for pn in gamma_to_path(gamma) {
                proof_map_mut.insert(pn, SVec::new());
            }

            proof_map_mut.insert(gamma, SVec::new());
        }

        let total_count = 2.0f64.powi(difficulty as _);
        let current_count = 0.0;

        let ndz = node::Node::new_zero();
        let svecz = SVec::new();

        Self {
            proof_map,
            chi,
            gammas,

            total_count,
            current_count,

            nd: ndz,
            n: 0,
            lab: svecz.clone(),

            l0: svecz.clone(), l1: svecz.clone(),
            nd0: ndz, nd1: ndz,

            puzzle: puzzle.to_vec(),
            difficulty,

            TICK_SECS: Self::default_tick(),
            tick_secs_override: None,
            ticks: 0,

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
        return Ok( bincode::deserialize(data)? );
        /*
        let mut snapshot = bincode::deserialize(data)?;
        snapshot.h = Some(Box::new(h));
        Ok(snapshot)
        */
    }

    /// to execute next generating until $tick seconds later.
    /// if finish, return a Proof object, or None
    /// ** make sure the .ticks field only add by this function **
    pub fn next(&mut self, h: impl HashFunction) -> Option<Proof> {
        let start = Instant::now();
        let tick = self.get_tick();

        while ! self.finish {
            if start.elapsed().as_secs() > tick {
                return None;
            }

            self.do_progressing(&h);
            self.ticks += 1;
        }

        Some( self.generate_proof() )
    }
    /// read(only) the current tick number, the tick-number is add one for each tick.
    pub fn current_tick(&self) -> u64 { self.ticks }
    /// read(only) the current elapsed seconds, This result may be inaccurate if the tick interval has changed in the middle
    pub fn elapsed_secs(&self) -> u64 { self.ticks * self.get_tick() }

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

    /// the core handle function for the progress of generating proof. do not pub it unless you expect others to violate the tick interval.
    /// the number of executes is fixed to 10,000 hashes (unless it will be returned earlier when the progress completed)
    /// ** make sure the .finish and .current_count field only modified by this function **
    fn do_progressing(&mut self, h: impl HashFunction) {
        if self.finish { return; }

        const OPS: usize = 10_000;

        let chi = &self.chi;
        let ell = Arc::make_mut(&mut self.proof_map);

        for _ in 0..OPS {
            if self.finish { return; }

            if self.nd.len == self.n {
                self.lab = {
                    let mut lab_gen = hash::Accumulator::new(chi, &h);
                    lab_gen.add(&self.nd.to_bytes());
                    self.nd.foreach_parent(self.n, |parent| {
                        lab_gen.add(&ell[&parent]);
                    });
                    lab_gen.hash()
                };

                // completing the progress... (possible mis-understanding?)
                self.finish = true;
            } else {
                // left tree
                self.l0 = {
                    let mut lab_gen = hash::Accumulator::new(chi, &h);
                    lab_gen.add(&self.nd.append(0).to_bytes());
                    self.nd.foreach_parent(self.n, |parent| {
                        lab_gen.add(&ell[&parent]);
                    });
                    lab_gen.hash()
                };
                ell.insert(self.nd.append(0), self.l0.clone());

                // right tree
                self.l1 = {
                    let mut lab_gen = hash::Accumulator::new(chi, &h);
                    lab_gen.add(&self.nd.append(1).to_bytes());
                    self.nd.foreach_parent(self.n, |parent| {
                        lab_gen.add(&ell[&parent]);
                    });
                    lab_gen.hash()
                };
                ell.remove(&self.nd.append(0));

                // calculate label
                self.lab = hash::Accumulator::new(chi, &h)
                    .add(&self.nd.to_bytes())
                    .add(&self.l0)
                    .add(&self.l1)
                    .hash();
            }

            self.current_count += 1.0;
        }
    }
    /// generate the proof. this method should be call with The Final State, otherwise it will got you an unwanted result
    pub fn generate_proof(&mut self) -> Proof {
        if ! self.finish {
            panic!("do not call this with still in progressing...");
        }
        if let Some(proof) = &self.proof {
            return proof.clone();
        }

        let proof = Proof( self.proof_map.clone().into() );

        self.proof = Some(proof);
        self.generate_proof()
    }

    /// default tick value is read-only for everyone (don't modify unless you have a good idea)
    pub fn default_tick() -> u64 { 30 }

    /// get the time-split interval, return the default value if no any override
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
        if self.ticks > 0 {
            return false;
        }

        self.tick_secs_override = Some(tick);
        return true;
    }
}

impl Proof {
    /// Generates a MelPoW proof with respect to the given starting puzzle and a difficulty.
    pub fn generate<H: HashFunction>(puzzle: &[u8], difficulty: usize, h: H) -> Self {
        Self::generate_with_progress(puzzle, difficulty, |_| (), h)
    }
    /// Generate with progress. The callback is called every time progress is made with a floating point number from 0 to 1.
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
    use crate::{HashFunction, Proof, SVec};

    struct Hasher;

    impl HashFunction for Hasher {
        fn hash(&self, b: &[u8], k: &[u8]) -> SVec<u8> {
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
        println!("proof length is {}", proof.to_bytes().len())
    }
}
