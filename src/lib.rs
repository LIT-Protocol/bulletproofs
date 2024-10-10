#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "docs", feature(external_doc))]
#![cfg_attr(feature = "docs", deny(missing_docs))]
#![cfg_attr(feature = "docs", doc(include = "../README.md"))]
#![cfg_attr(
    feature = "docs",
    doc(html_root_url = "https://docs.rs/bulletproofs/4.0.0")
)]

extern crate alloc;
extern crate core;

mod util;

#[cfg_attr(feature = "docs", doc(include = "../docs/notes-intro.md"))]
mod notes {
    #[cfg_attr(feature = "docs", doc(include = "../docs/notes-ipp.md"))]
    mod inner_product_proof {}
    #[cfg_attr(feature = "docs", doc(include = "../docs/notes-rp.md"))]
    mod range_proof {}
    #[cfg_attr(feature = "docs", doc(include = "../docs/notes-r1cs.md"))]
    mod r1cs_proof {}
}

mod errors;
mod generators;
mod inner_product_proof;
mod linear_proof;
mod range_proof;
mod transcript;
mod types;

use subtle::Choice;

pub use crate::errors::ProofError;
pub use crate::generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use crate::linear_proof::LinearProof;
pub use crate::range_proof::RangeProof;
pub use transcript::TranscriptProtocol;
#[cfg(any(feature = "curve25519", test))]
pub use types::curve25519_impls::Curve25519;
pub use types::{
    BulletproofCurveArithmetic, FromWideBytes, HashToPoint, HashToScalar, PippengerScalar,
    ScalarBatchInvert,
};
pub use group;
pub use merlin;

#[cfg(feature = "curve25519")]
pub use vsss_rs;
#[cfg(feature = "k256")]
pub use k256;
#[cfg(feature = "p256")]
pub use p256;
#[cfg(feature = "bls12_381")]
pub use bls12_381_plus;
#[cfg(feature = "bls12_381_std")]
pub use blstrs_plus;
#[cfg(feature = "ed448")]
pub use ed448_goldilocks_plus as ed448;

trait CtOptionOps<T> {
    fn ok_or<E>(self, err: E) -> Result<T, E>;
}

impl<T> CtOptionOps<T> for subtle::CtOption<T> {
    fn ok_or<E>(self, err: E) -> Result<T, E> {
        if self.is_some().unwrap_u8() == 1u8 {
            Ok(self.unwrap())
        } else {
            Err(err)
        }
    }
}

impl CtOptionOps<()> for Choice {
    fn ok_or<E>(self, err: E) -> Result<(), E> {
        if self.unwrap_u8() == 1u8 {
            Ok(())
        } else {
            Err(err)
        }
    }
}

#[cfg_attr(feature = "docs", doc(include = "../docs/aggregation-api.md"))]
pub mod range_proof_mpc {
    pub use crate::errors::MPCError;
    pub use crate::range_proof::dealer;
    pub use crate::range_proof::messages;
    pub use crate::range_proof::party;
}

#[cfg(feature = "yoloproofs")]
#[cfg(feature = "std")]
pub mod r1cs;
mod serdes;
