use std::ops::Deref;

use crate::node::SVec;

/// A raw hash function. For convenience, this trait is implemented also for closures.
pub trait HashFunction {
    /// Hashes a bunch of bytes, with a given key.
    fn hash(&self, b: &[u8], k: &[u8]) -> SVec<u8>;
}

// impl<F: Fn(&[u8]) -> SVec<u8>> HashFunction for F {
//     fn hash(&self, b: &[u8]) -> SVec<u8> {
//         (self)(b)
//     }
// }

impl<H: HashFunction> HashFunction for &H {
    fn hash(&self, b: &[u8], k: &[u8]) -> SVec<u8> {
        self.deref().hash(b, k)
    }
}

pub fn bts_key(bts: &[u8], key: &[u8]) -> SVec<u8> {
    SVec::from_slice(&tmelcrypt::hash_keyed(key, bts))
}

#[derive(Default)]
pub struct Accumulator<H: HashFunction> {
    accum: SVec<u8>,
    hasher: H,
    key: SVec<u8>,
}

impl<H: HashFunction> Accumulator<H> {
    pub fn new(key: &[u8], hasher: H) -> Self {
        Accumulator {
            accum: SVec::new(),
            hasher,
            key: SVec::from_slice(key),
        }
    }

    #[inline]
    pub fn add(&mut self, bts: &[u8]) -> &mut Self {
        self.accum.extend_from_slice(bts);
        self
    }

    #[inline]
    pub fn hash(&self) -> SVec<u8> {
        self.hasher.hash(&self.accum, &self.key)
    }
}
