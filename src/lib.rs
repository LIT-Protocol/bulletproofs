#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "docs", feature(external_doc))]
#![cfg_attr(feature = "docs", deny(missing_docs))]
#![cfg_attr(feature = "docs", doc(include = "../README.md"))]
#![cfg_attr(
    feature = "docs",
    doc(html_root_url = "https://docs.rs/bulletproofs/4.0.0")
)]

extern crate alloc;

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
pub use merlin;
pub use transcript::TranscriptProtocol;
#[cfg(feature = "decaf377")]
pub use types::decaf377_impls::Decaf377;
#[cfg(feature = "ed25519")]
pub use types::ed25519_impls::Ed25519;
#[cfg(feature = "jubjub")]
pub use types::jubjub_impls::JubJub;
#[cfg(feature = "ristretto25519")]
pub use types::ristretto25519_impls::Ristretto25519;
pub use types::{
    BulletproofCurveArithmetic, FromWideBytes, HashToPoint, HashToScalar, PippengerScalar,
    ScalarBatchInvert,
};

pub use lit_rust_crypto;

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
