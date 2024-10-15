#![allow(non_snake_case)]
#![cfg_attr(feature = "docs", doc(include = "../../docs/range-proof-protocol.md"))]

extern crate alloc;
#[cfg(feature = "std")]
extern crate rand;

use super::CtOptionOps;

#[cfg(feature = "std")]
use self::rand::thread_rng;
use alloc::vec::Vec;

use core::iter;

use group::ff::Field;
use group::Group;
use merlin::Transcript;

use crate::errors::ProofError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::InnerProductProof;
use crate::serdes::*;
use crate::transcript::TranscriptProtocol;
use crate::types::*;
use crate::util;

use rand_core::{CryptoRng, RngCore};
use serde::{self, Deserialize, Serialize};

// Modules for MPC protocol

pub mod dealer;
pub mod messages;
pub mod party;

/// The `RangeProof` struct represents a proof that one or more values
/// are in a range.
///
/// The `RangeProof` struct contains functions for creating and
/// verifying aggregated range proofs.  The single-value case is
/// implemented as a special case of aggregated range proofs.
///
/// The bitsize of the range, as well as the list of commitments to
/// the values, are not included in the proof, and must be known to
/// the verifier.
///
/// This implementation requires that both the bitsize `n` and the
/// aggregation size `m` be powers of two, so that `n = 8, 16, 32, 64`
/// and `m = 1, 2, 4, 8, 16, ...`.  Note that the aggregation size is
/// not given as an explicit parameter, but is determined by the
/// number of values or commitments passed to the prover or verifier.
///
/// # Note
///
/// For proving, these functions run the multiparty aggregation
/// protocol locally.  That API is exposed in the [`aggregation`](::range_proof_mpc)
/// module and can be used to perform online aggregation between
/// parties without revealing secret values to each other.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RangeProof<C: BulletproofCurveArithmetic> {
    #[serde(with = "CurvePoint::<C>")]
    /// Commitment to the bits of the value
    A: C::Point,
    #[serde(with = "CurvePoint::<C>")]
    /// Commitment to the blinding factors
    S: C::Point,
    #[serde(with = "CurvePoint::<C>")]
    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    T_1: C::Point,
    #[serde(with = "CurvePoint::<C>")]
    /// Commitment to the \\(t_2\\) coefficient of \\( t(x) \\)
    T_2: C::Point,
    #[serde(with = "CurveScalar::<C>")]
    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    t_x: C::Scalar,
    #[serde(with = "CurveScalar::<C>")]
    /// Blinding factor for the synthetic commitment to \\(t(x)\\)
    t_x_blinding: C::Scalar,
    #[serde(with = "CurveScalar::<C>")]
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    e_blinding: C::Scalar,
    #[serde(bound(serialize = "InnerProductProof<C>: Serialize"))]
    #[serde(bound(deserialize = "InnerProductProof<C>: Deserialize<'de>"))]
    /// Proof data for the inner-product argument.
    ipp_proof: InnerProductProof<C>,
}

impl<C: BulletproofCurveArithmetic> RangeProof<C> {
    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    /// This is a convenience wrapper around [`RangeProof::prove_multiple`].
    ///
    /// # Example
    /// ```
    /// use rand::thread_rng;
    /// use group::ff::Field;
    /// use merlin::Transcript;
    /// use bulletproofs::{BulletproofGens, PedersenGens, RangeProof, Curve25519};
    ///
    /// fn main() {
    /// // Generators for Pedersen commitments.  These can be selected
    /// // independently of the Bulletproofs generators.
    /// use bulletproofs::BulletproofCurveArithmetic;
    /// let pc_gens = PedersenGens::<Curve25519>::default();
    ///
    /// // Generators for Bulletproofs, valid for proofs up to bitsize 64
    /// // and aggregation size up to 1.
    /// let bp_gens = BulletproofGens::<Curve25519>::new(64, 1);
    ///
    /// // A secret value we want to prove lies in the range [0, 2^32)
    /// let secret_value = 1037578891u64;
    ///
    /// // The API takes a blinding factor for the commitment.
    /// let blinding = <Curve25519 as BulletproofCurveArithmetic>::Scalar::random(&mut thread_rng());
    ///
    /// // The proof can be chained to an existing transcript.
    /// // Here we create a transcript with a doctest domain separator.
    /// let mut prover_transcript = Transcript::new(b"doctest example");
    ///
    /// // Create a 32-bit rangeproof.
    /// let (proof, committed_value) = RangeProof::<Curve25519>::prove_single(
    ///     &bp_gens,
    ///     &pc_gens,
    ///     &mut prover_transcript,
    ///     secret_value,
    ///     &blinding,
    ///     32,
    /// ).expect("A real program could handle errors");
    ///
    /// // Verification requires a transcript with identical initial state:
    /// let mut verifier_transcript = Transcript::new(b"doctest example");
    /// assert!(
    ///     proof
    ///         .verify_single(&bp_gens, &pc_gens, &mut verifier_transcript, &committed_value, 32)
    ///         .is_ok()
    /// );
    /// # }
    /// ```
    pub fn prove_single_with_rng<T: RngCore + CryptoRng>(
        bp_gens: &BulletproofGens<C>,
        pc_gens: &PedersenGens<C>,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &C::Scalar,
        n: usize,
        rng: &mut T,
    ) -> Result<(RangeProof<C>, C::Point), ProofError> {
        let (p, Vs) = RangeProof::<C>::prove_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            &[v],
            &[*v_blinding],
            n,
            rng,
        )?;
        Ok((p, Vs[0]))
    }

    /// Create a rangeproof for a given pair of value `v` and
    /// blinding scalar `v_blinding`.
    /// This is a convenience wrapper around [`RangeProof::prove_single_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn prove_single(
        bp_gens: &BulletproofGens<C>,
        pc_gens: &PedersenGens<C>,
        transcript: &mut Transcript,
        v: u64,
        v_blinding: &C::Scalar,
        n: usize,
    ) -> Result<(RangeProof<C>, C::Point), ProofError> {
        RangeProof::prove_single_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            v,
            v_blinding,
            n,
            &mut thread_rng(),
        )
    }

    /// Create a rangeproof for a set of values.
    ///
    /// # Example
    /// ```
    /// use rand::thread_rng;
    /// use group::ff::Field;
    /// use merlin::Transcript;
    /// use bulletproofs::{BulletproofGens, Curve25519, PedersenGens, RangeProof};
    ///
    /// # fn main() {
    /// // Generators for Pedersen commitments.  These can be selected
    /// // independently of the Bulletproofs generators.
    /// use bulletproofs::BulletproofCurveArithmetic;
    /// let pc_gens = PedersenGens::<Curve25519>::default();
    ///
    /// // Generators for Bulletproofs, valid for proofs up to bitsize 64
    /// // and aggregation size up to 16.
    /// let bp_gens = BulletproofGens::<Curve25519>::new(64, 16);
    ///
    /// // Four secret values we want to prove lie in the range [0, 2^32)
    /// let secrets = [4242344947u64, 3718732727u64, 2255562556u64, 2526146994u64];
    ///
    /// // The API takes blinding factors for the commitments.
    /// let blindings: Vec<_> = (0..4).map(|_| <Curve25519 as BulletproofCurveArithmetic>::Scalar::random(&mut thread_rng())).collect();
    ///
    /// // The proof can be chained to an existing transcript.
    /// // Here we create a transcript with a doctest domain separator.
    /// let mut prover_transcript = Transcript::new(b"doctest example");
    ///
    /// // Create an aggregated 32-bit rangeproof and corresponding commitments.
    /// let (proof, commitments) = RangeProof::prove_multiple(
    ///     &bp_gens,
    ///     &pc_gens,
    ///     &mut prover_transcript,
    ///     &secrets,
    ///     &blindings,
    ///     32,
    /// ).expect("A real program could handle errors");
    ///
    /// // Verification requires a transcript with identical initial state:
    /// let mut verifier_transcript = Transcript::new(b"doctest example");
    /// assert!(
    ///     proof
    ///         .verify_multiple(&bp_gens, &pc_gens, &mut verifier_transcript, &commitments, 32)
    ///         .is_ok()
    /// );
    /// # }
    /// ```
    pub fn prove_multiple_with_rng(
        bp_gens: &BulletproofGens<C>,
        pc_gens: &PedersenGens<C>,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[C::Scalar],
        n: usize,
        mut rng: impl RngCore + CryptoRng,
    ) -> Result<(RangeProof<C>, Vec<C::Point>), ProofError> {
        use self::dealer::*;
        use self::party::*;

        if values.len() != blindings.len() {
            return Err(ProofError::WrongNumBlindingFactors);
        }

        let dealer = Dealer::new(bp_gens, pc_gens, transcript, n, values.len())?;

        let parties: Vec<_> = values
            .iter()
            .zip(blindings.iter())
            .map(|(&v, &v_blinding)| Party::new(bp_gens, pc_gens, v, v_blinding, n))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let (parties, bit_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .enumerate()
            .map(|(j, p)| {
                p.assign_position_with_rng(j, &mut rng)
                    .expect("We already checked the parameters, so this should never happen")
            })
            .unzip();

        let value_commitments: Vec<_> = bit_commitments.iter().map(|c| c.V_j).collect();

        let (dealer, bit_challenge) = dealer.receive_bit_commitments(bit_commitments)?;

        let (parties, poly_commitments): (Vec<_>, Vec<_>) = parties
            .into_iter()
            .map(|p| p.apply_challenge_with_rng(&bit_challenge, &mut rng))
            .unzip();

        let (dealer, poly_challenge) = dealer.receive_poly_commitments(poly_commitments)?;

        let proof_shares: Vec<_> = parties
            .into_iter()
            .map(|p| p.apply_challenge(&poly_challenge))
            // Collect the iterator of Results into a Result<Vec>, then unwrap it
            .collect::<Result<Vec<_>, _>>()?;

        let proof = dealer.receive_trusted_shares(&proof_shares)?;

        Ok((proof, value_commitments))
    }

    /// Create a rangeproof for a set of values.
    /// This is a convenience wrapper around [`RangeProof::prove_multiple_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn prove_multiple(
        bp_gens: &BulletproofGens<C>,
        pc_gens: &PedersenGens<C>,
        transcript: &mut Transcript,
        values: &[u64],
        blindings: &[C::Scalar],
        n: usize,
    ) -> Result<(RangeProof<C>, Vec<C::Point>), ProofError> {
        RangeProof::prove_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            values,
            blindings,
            n,
            thread_rng(),
        )
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around `verify_multiple` for the `m=1` case.
    pub fn verify_single_with_rng<T: RngCore + CryptoRng>(
        &self,
        bp_gens: &BulletproofGens<C>,
        pc_gens: &PedersenGens<C>,
        transcript: &mut Transcript,
        V: &C::Point,
        n: usize,
        rng: &mut T,
    ) -> Result<(), ProofError> {
        self.verify_multiple_with_rng(bp_gens, pc_gens, transcript, &[*V], n, rng)
    }

    /// Verifies a rangeproof for a given value commitment \\(V\\).
    ///
    /// This is a convenience wrapper around [`RangeProof::verify_single_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn verify_single(
        &self,
        bp_gens: &BulletproofGens<C>,
        pc_gens: &PedersenGens<C>,
        transcript: &mut Transcript,
        V: &C::Point,
        n: usize,
    ) -> Result<(), ProofError> {
        self.verify_single_with_rng(bp_gens, pc_gens, transcript, V, n, &mut thread_rng())
    }

    /// Verifies an aggregated rangeproof for the given value commitments.
    pub fn verify_multiple_with_rng<T: RngCore + CryptoRng>(
        &self,
        bp_gens: &BulletproofGens<C>,
        pc_gens: &PedersenGens<C>,
        transcript: &mut Transcript,
        value_commitments: &[C::Point],
        n: usize,
        rng: &mut T,
    ) -> Result<(), ProofError> {
        let m = value_commitments.len();

        // First, replay the "interactive" protocol using the proof
        // data to recompute all challenges.
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(ProofError::InvalidBitsize);
        }
        if bp_gens.gens_capacity < n {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        if bp_gens.party_capacity < m {
            return Err(ProofError::InvalidGeneratorsLength);
        }

        transcript.rangeproof_domain_sep(n as u64, m as u64);

        for V in value_commitments.iter() {
            // Allow the commitments to be zero (0 value, 0 blinding)
            // See https://github.com/dalek-cryptography/bulletproofs/pull/248#discussion_r255167177
            transcript.append_point::<C>(b"V", V);
        }

        transcript.validate_and_append_point::<C>(b"A", &self.A)?;
        transcript.validate_and_append_point::<C>(b"S", &self.S)?;

        let y: C::Scalar = transcript.challenge_scalar::<C>(b"y");
        let z: C::Scalar = transcript.challenge_scalar::<C>(b"z");
        let zz = z * z;
        let minus_z = -z;

        transcript.validate_and_append_point::<C>(b"T_1", &self.T_1)?;
        transcript.validate_and_append_point::<C>(b"T_2", &self.T_2)?;

        let x = transcript.challenge_scalar::<C>(b"x");

        transcript.append_scalar::<C>(b"t_x", &self.t_x);
        transcript.append_scalar::<C>(b"t_x_blinding", &self.t_x_blinding);
        transcript.append_scalar::<C>(b"e_blinding", &self.e_blinding);

        let w: C::Scalar = transcript.challenge_scalar::<C>(b"w");

        // Challenge value for batching statements to be verified
        let c = C::Scalar::random(rng);

        let (x_sq, x_inv_sq, s) = self.ipp_proof.verification_scalars(n * m, transcript)?;
        let s_inv = s.iter().rev();

        let a = self.ipp_proof.a;
        let b = self.ipp_proof.b;

        // Construct concat_z_and_2, an iterator of the values of
        // z^0 * \vec(2)^n || z^1 * \vec(2)^n || ... || z^(m-1) * \vec(2)^n
        let powers_of_2: Vec<C::Scalar> =
            util::exp_iter::<C>(C::Scalar::from(2u64)).take(n).collect();
        let concat_z_and_2: Vec<C::Scalar> = util::exp_iter::<C>(z)
            .take(m)
            .flat_map(|exp_z| powers_of_2.iter().map(move |exp_2| *exp_2 * exp_z))
            .collect();

        let g = s.iter().map(|s_i| minus_z - a * s_i);
        let h = s_inv
            .zip(util::exp_iter::<C>(y.invert().unwrap()))
            .zip(concat_z_and_2.iter())
            .map(|((s_i_inv, exp_y_inv), z_and_2)| z + exp_y_inv * (zz * z_and_2 - b * s_i_inv));

        let value_commitment_scalars = util::exp_iter::<C>(z).take(m).map(|z_exp| c * zz * z_exp);
        let basepoint_scalar: C::Scalar =
            w * (self.t_x - a * b) + c * (delta::<C>(n, m, &y, &z) - self.t_x);

        let mega_points: Vec<C::Point> = iter::once(self.A)
            .chain(iter::once(self.S))
            .chain(iter::once(self.T_1))
            .chain(iter::once(self.T_2))
            .chain(self.ipp_proof.L_vec.clone())
            .chain(self.ipp_proof.R_vec.clone())
            .chain(iter::once(pc_gens.B_blinding))
            .chain(iter::once(pc_gens.B))
            .chain(bp_gens.G(n, m).copied())
            .chain(bp_gens.H(n, m).copied())
            .chain(value_commitments.iter().copied())
            .collect();
        let mega_scalars: Vec<C::Scalar> = iter::once(C::Scalar::ONE)
            .chain(iter::once(x))
            .chain(iter::once(c * x))
            .chain(iter::once(c * x * x))
            .chain(x_sq.iter().cloned())
            .chain(x_inv_sq.iter().cloned())
            .chain(iter::once(-self.e_blinding - c * self.t_x_blinding))
            .chain(iter::once(basepoint_scalar))
            .chain(g)
            .chain(h)
            .chain(value_commitment_scalars)
            .collect();
        let mega_check = C::pippenger_sum_of_products(&mega_points, &mega_scalars);

        mega_check
            .is_identity()
            .ok_or(ProofError::VerificationError)
    }

    /// Verifies an aggregated range proof for the given value commitments.
    /// This is a convenience wrapper around [`RangeProof::verify_multiple_with_rng`],
    /// passing in a threadsafe RNG.
    #[cfg(feature = "std")]
    pub fn verify_multiple(
        &self,
        bp_gens: &BulletproofGens<C>,
        pc_gens: &PedersenGens<C>,
        transcript: &mut Transcript,
        value_commitments: &[C::Point],
        n: usize,
    ) -> Result<(), ProofError> {
        self.verify_multiple_with_rng(
            bp_gens,
            pc_gens,
            transcript,
            value_commitments,
            n,
            &mut thread_rng(),
        )
    }

    /// Serializes the proof into a byte array of \\(2 \lg n + 9\\)
    /// 32-byte elements, where \\(n\\) is the number of secret bits.
    ///
    /// # Layout
    ///
    /// The layout of the range proof encoding is:
    ///
    /// * four compressed Ristretto points \\(A,S,T_1,T_2\\),
    /// * three scalars \\(t_x, \tilde{t}_x, \tilde{e}\\),
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0,R_0\dots,L_{n-1},R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        // 7 elements: points A, S, T1, T2, scalars tx, tx_bl, e_bl.
        let mut buf = Vec::with_capacity(
            4 * C::POINT_BYTES + 3 * C::SCALAR_BYTES + self.ipp_proof.serialized_size(),
        );
        buf.append(&mut C::serialize_point(&self.A));
        buf.append(&mut C::serialize_point(&self.S));
        buf.append(&mut C::serialize_point(&self.T_1));
        buf.append(&mut C::serialize_point(&self.T_2));
        buf.append(&mut C::serialize_scalar(&self.t_x));
        buf.append(&mut C::serialize_scalar(&self.t_x_blinding));
        buf.append(&mut C::serialize_scalar(&self.e_blinding));
        buf.append(&mut self.ipp_proof.to_bytes());
        buf
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `RangeProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<Self, ProofError> {
        if slice.len() < 4 * C::POINT_BYTES + 5 * C::SCALAR_BYTES {
            return Err(ProofError::FormatError);
        }

        let mut pos = 0;

        let A = C::deserialize_point(&slice[pos..pos + C::POINT_BYTES])
            .map_err(|_| ProofError::FormatError)?;
        pos += C::POINT_BYTES;
        let S = C::deserialize_point(&slice[pos..pos + C::POINT_BYTES])
            .map_err(|_| ProofError::FormatError)?;
        pos += C::POINT_BYTES;
        let T_1 = C::deserialize_point(&slice[pos..pos + C::POINT_BYTES])
            .map_err(|_| ProofError::FormatError)?;
        pos += C::POINT_BYTES;
        let T_2 = C::deserialize_point(&slice[pos..pos + C::POINT_BYTES])
            .map_err(|_| ProofError::FormatError)?;
        pos += C::POINT_BYTES;

        let t_x = C::deserialize_scalar(&slice[pos..pos + C::SCALAR_BYTES])
            .map_err(|_| ProofError::FormatError)?;
        pos += C::SCALAR_BYTES;
        let t_x_blinding = C::deserialize_scalar(&slice[pos..pos + C::SCALAR_BYTES])
            .map_err(|_| ProofError::FormatError)?;
        pos += C::SCALAR_BYTES;
        let e_blinding = C::deserialize_scalar(&slice[pos..pos + C::SCALAR_BYTES])
            .map_err(|_| ProofError::FormatError)?;
        pos += C::SCALAR_BYTES;

        let ipp_proof = InnerProductProof::from_bytes(&slice[pos..])?;

        Ok(RangeProof {
            A,
            S,
            T_1,
            T_2,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }
}

// impl<C: BulletproofCurveArithmetic> Serialize for RangeProof<C> {
//     fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
//     where
//         S: Serializer,
//     {
//         serializer.serialize_bytes(&self.to_bytes()[..])
//     }
// }
//
// impl<'de, C: BulletproofCurveArithmetic> Deserialize<'de> for RangeProof<C> {
//     fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
//     where
//         D: Deserializer<'de>,
//     {
//         struct RangeProofVisitor<C: BulletproofCurveArithmetic> {
//             _marker: core::marker::PhantomData<C>,
//         }
//
//         impl<'de, C: BulletproofCurveArithmetic> Visitor<'de> for RangeProofVisitor<C> {
//             type Value = RangeProof<C>;
//
//             fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
//                 formatter.write_str("a valid RangeProof")
//             }
//
//             fn visit_bytes<E>(self, v: &[u8]) -> Result<RangeProof<C>, E>
//             where
//                 E: serde::de::Error,
//             {
//                 // Using Error::custom requires T: Display, which our error
//                 // type only implements when it implements std::error::Error.
//                 #[cfg(feature = "std")]
//                 return RangeProof::from_bytes(v).map_err(serde::de::Error::custom);
//                 // In no-std contexts, drop the error message.
//                 #[cfg(not(feature = "std"))]
//                 return RangeProof::from_bytes(v)
//                     .map_err(|_| serde::de::Error::custom("deserialization error"));
//             }
//         }
//
//         deserializer.deserialize_bytes(RangeProofVisitor {
//             _marker: core::marker::PhantomData,
//         })
//     }
// }
//
/// Compute
/// \\[
/// \delta(y,z) = (z - z^{2}) \langle \mathbf{1}, {\mathbf{y}}^{n \cdot m} \rangle - \sum_{j=0}^{m-1} z^{j+3} \cdot \langle \mathbf{1}, {\mathbf{2}}^{n \cdot m} \rangle
/// \\]
fn delta<C: BulletproofCurveArithmetic>(
    n: usize,
    m: usize,
    y: &C::Scalar,
    z: &C::Scalar,
) -> C::Scalar {
    let sum_y = util::sum_of_powers::<C>(y, n * m);
    let sum_2 = util::sum_of_powers::<C>(&C::Scalar::from(2u64), n);
    let sum_z = util::sum_of_powers::<C>(z, m);

    (*z - *z * *z) * sum_y - *z * *z * *z * sum_2 * sum_z
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::generators::PedersenGens;

    #[cfg(feature = "curve25519")]
    #[test]
    fn test_delta_curve25519() {
        test_delta::<crate::Curve25519>();
    }

    #[cfg(feature = "k256")]
    #[test]
    fn test_delta_k256() {
        test_delta::<k256::Secp256k1>();
    }

    #[cfg(feature = "p256")]
    #[test]
    fn test_delta_p256() {
        test_delta::<p256::NistP256>();
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn test_delta_bls12_381() {
        test_delta::<bls12_381_plus::Bls12381G1>();
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn test_delta_bls12_381_std() {
        test_delta::<blstrs_plus::Bls12381G1>();
    }

    fn test_delta<C: BulletproofCurveArithmetic>() {
        let mut rng = thread_rng();
        let y = C::Scalar::random(&mut rng);
        let z = C::Scalar::random(&mut rng);

        // Choose n = 256 to ensure we overflow the group order during
        // the computation, to check that that's done correctly
        let n = 256;

        // code copied from previous implementation
        let z2 = z * z;
        let z3 = z2 * z;
        let mut power_g = C::Scalar::ZERO;
        let mut exp_y = C::Scalar::ONE; // start at y^0 = 1
        let mut exp_2 = C::Scalar::ONE; // start at 2^0 = 1
        for _ in 0..n {
            power_g += (z - z2) * exp_y - z3 * exp_2;

            exp_y = exp_y * y; // y^i -> y^(i+1)
            exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)
        }

        assert_eq!(power_g, delta::<C>(n, 1, &y, &z),);
    }

    /// Given a bitsize `n`, test the following:
    ///
    /// 1. Generate `m` random values and create a proof they are all in range;
    /// 2. Serialize to wire format;
    /// 3. Deserialize from wire format;
    /// 4. Verify the proof.
    fn singleparty_create_and_verify_helper<C: BulletproofCurveArithmetic>(n: usize, m: usize) {
        // Split the test into two scopes, so that it's explicit what
        // data is shared between the prover and the verifier.

        // Use bincode for serialization
        //use bincode; // already present in lib.rs

        // Both prover and verifier have access to the generators and the proof
        let max_bitsize = 64;
        let max_parties = 8;
        let pc_gens = PedersenGens::<C>::default();
        let bp_gens = BulletproofGens::<C>::new(max_bitsize, max_parties);

        // Prover's scope
        let (proof_bytes, value_commitments) = {
            use self::rand::Rng;
            let mut rng = thread_rng();

            // 0. Create witness data
            let (min, max) = (0u64, ((1u128 << n) - 1) as u64);
            let values: Vec<u64> = (0..m).map(|_| rng.gen_range(min..max)).collect();
            let blindings: Vec<C::Scalar> = (0..m).map(|_| C::Scalar::random(&mut rng)).collect();

            // 1. Create the proof
            let mut transcript = Transcript::new(b"AggregatedRangeProofTest");
            let (proof, value_commitments) = RangeProof::<C>::prove_multiple(
                &bp_gens,
                &pc_gens,
                &mut transcript,
                &values,
                &blindings,
                n,
            )
            .unwrap();

            // 2. Return serialized proof and value commitments
            (bincode::serialize(&proof).unwrap(), value_commitments)
        };

        // Verifier's scope
        {
            // 3. Deserialize
            let proof: RangeProof<C> = bincode::deserialize(&proof_bytes).unwrap();

            // 4. Verify with the same customization label as above
            let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

            assert!(proof
                .verify_multiple(&bp_gens, &pc_gens, &mut transcript, &value_commitments, n)
                .is_ok());
        }
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn create_and_verify_n_32_m_1_curve25519() {
        singleparty_create_and_verify_helper::<crate::Curve25519>(32, 1);
    }

    #[cfg(feature = "k256")]
    #[test]
    fn create_and_verify_n_32_m_1_k256() {
        singleparty_create_and_verify_helper::<k256::Secp256k1>(32, 1);
    }

    #[cfg(feature = "p256")]
    #[test]
    fn create_and_verify_n_32_m_1_p256() {
        singleparty_create_and_verify_helper::<p256::NistP256>(32, 1);
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn create_and_verify_n_32_m_1_bls12_381() {
        singleparty_create_and_verify_helper::<bls12_381_plus::Bls12381G1>(32, 1);
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn create_and_verify_n_32_m_1_bls12_381_std() {
        singleparty_create_and_verify_helper::<blstrs_plus::Bls12381G1>(32, 1);
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn create_and_verify_n_32_m_2_curve25519() {
        singleparty_create_and_verify_helper::<crate::Curve25519>(32, 2);
    }

    #[cfg(feature = "k256")]
    #[test]
    fn create_and_verify_n_32_m_2_k256() {
        singleparty_create_and_verify_helper::<k256::Secp256k1>(32, 2);
    }

    #[cfg(feature = "p256")]
    #[test]
    fn create_and_verify_n_32_m_2_p256() {
        singleparty_create_and_verify_helper::<p256::NistP256>(32, 2);
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn create_and_verify_n_32_m_2_bls12_381() {
        singleparty_create_and_verify_helper::<bls12_381_plus::Bls12381G1>(32, 2);
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn create_and_verify_n_32_m_2_bls12_381_std() {
        singleparty_create_and_verify_helper::<blstrs_plus::Bls12381G1>(32, 2);
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn create_and_verify_n_32_m_4_curve25519() {
        singleparty_create_and_verify_helper::<crate::Curve25519>(32, 4);
    }

    #[cfg(feature = "k256")]
    #[test]
    fn create_and_verify_n_32_m_4_k256() {
        singleparty_create_and_verify_helper::<k256::Secp256k1>(32, 4);
    }

    #[cfg(feature = "p256")]
    #[test]
    fn create_and_verify_n_32_m_4_p256() {
        singleparty_create_and_verify_helper::<p256::NistP256>(32, 4);
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn create_and_verify_n_32_m_4_bls12_381() {
        singleparty_create_and_verify_helper::<bls12_381_plus::Bls12381G1>(32, 4);
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn create_and_verify_n_32_m_4_bls12_381_std() {
        singleparty_create_and_verify_helper::<blstrs_plus::Bls12381G1>(32, 4);
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn create_and_verify_n_32_m_8_curve25519() {
        singleparty_create_and_verify_helper::<crate::Curve25519>(32, 8);
    }

    #[cfg(feature = "k256")]
    #[test]
    fn create_and_verify_n_32_m_8_k256() {
        singleparty_create_and_verify_helper::<k256::Secp256k1>(32, 8);
    }

    #[cfg(feature = "p256")]
    #[test]
    fn create_and_verify_n_32_m_8_p256() {
        singleparty_create_and_verify_helper::<p256::NistP256>(32, 8);
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn create_and_verify_n_32_m_8_bls12_381() {
        singleparty_create_and_verify_helper::<bls12_381_plus::Bls12381G1>(32, 8);
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn create_and_verify_n_32_m_8_bls12_381_std() {
        singleparty_create_and_verify_helper::<blstrs_plus::Bls12381G1>(32, 8);
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn create_and_verify_n_64_m_1_curve25519() {
        singleparty_create_and_verify_helper::<crate::Curve25519>(64, 1);
    }

    #[cfg(feature = "k256")]
    #[test]
    fn create_and_verify_n_64_m_1_k256() {
        singleparty_create_and_verify_helper::<k256::Secp256k1>(64, 1);
    }

    #[cfg(feature = "p256")]
    #[test]
    fn create_and_verify_n_64_m_1_p256() {
        singleparty_create_and_verify_helper::<p256::NistP256>(64, 1);
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn create_and_verify_n_64_m_1_bls12_381() {
        singleparty_create_and_verify_helper::<bls12_381_plus::Bls12381G1>(64, 1);
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn create_and_verify_n_64_m_1_bls12_381_std() {
        singleparty_create_and_verify_helper::<blstrs_plus::Bls12381G1>(64, 1);
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn create_and_verify_n_64_m_2_curve25519() {
        singleparty_create_and_verify_helper::<crate::Curve25519>(64, 2);
    }

    #[cfg(feature = "k256")]
    #[test]
    fn create_and_verify_n_64_m_2_k256() {
        singleparty_create_and_verify_helper::<k256::Secp256k1>(64, 2);
    }

    #[cfg(feature = "p256")]
    #[test]
    fn create_and_verify_n_64_m_2_p256() {
        singleparty_create_and_verify_helper::<p256::NistP256>(64, 2);
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn create_and_verify_n_64_m_2_bls12_381() {
        singleparty_create_and_verify_helper::<bls12_381_plus::Bls12381G1>(64, 2);
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn create_and_verify_n_64_m_2_bls12_381_std() {
        singleparty_create_and_verify_helper::<blstrs_plus::Bls12381G1>(64, 2);
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn create_and_verify_n_64_m_4_curve25519() {
        singleparty_create_and_verify_helper::<crate::Curve25519>(64, 4);
    }

    #[cfg(feature = "k256")]
    #[test]
    fn create_and_verify_n_64_m_4_k256() {
        singleparty_create_and_verify_helper::<k256::Secp256k1>(64, 4);
    }

    #[cfg(feature = "p256")]
    #[test]
    fn create_and_verify_n_64_m_4_p256() {
        singleparty_create_and_verify_helper::<p256::NistP256>(64, 4);
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn create_and_verify_n_64_m_4_bls12_381() {
        singleparty_create_and_verify_helper::<bls12_381_plus::Bls12381G1>(64, 4);
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn create_and_verify_n_64_m_4_bls12_381_std() {
        singleparty_create_and_verify_helper::<blstrs_plus::Bls12381G1>(64, 4);
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn create_and_verify_n_64_m_8_curve25519() {
        singleparty_create_and_verify_helper::<crate::Curve25519>(64, 8);
    }

    #[cfg(feature = "k256")]
    #[test]
    fn create_and_verify_n_64_m_8_k256() {
        singleparty_create_and_verify_helper::<k256::Secp256k1>(64, 8);
    }

    #[cfg(feature = "p256")]
    #[test]
    fn create_and_verify_n_64_m_8_p256() {
        singleparty_create_and_verify_helper::<p256::NistP256>(64, 8);
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn create_and_verify_n_64_m_8_bls12_381() {
        singleparty_create_and_verify_helper::<bls12_381_plus::Bls12381G1>(64, 8);
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn create_and_verify_n_64_m_8_bls12_381_std() {
        singleparty_create_and_verify_helper::<blstrs_plus::Bls12381G1>(64, 8);
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn detect_dishonest_party_during_aggregation_curve25519() {
        detect_dishonest_party_during_aggregation::<crate::Curve25519>();
    }

    #[cfg(feature = "k256")]
    #[test]
    fn detect_dishonest_party_during_aggregation_k256() {
        detect_dishonest_party_during_aggregation::<k256::Secp256k1>();
    }

    #[cfg(feature = "p256")]
    #[test]
    fn detect_dishonest_party_during_aggregation_p256() {
        detect_dishonest_party_during_aggregation::<p256::NistP256>();
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn detect_dishonest_party_during_aggregation_bls12_381() {
        detect_dishonest_party_during_aggregation::<bls12_381_plus::Bls12381G1>();
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn detect_dishonest_party_during_aggregation_bls12_381_std() {
        detect_dishonest_party_during_aggregation::<blstrs_plus::Bls12381G1>();
    }

    fn detect_dishonest_party_during_aggregation<C: BulletproofCurveArithmetic>() {
        use self::dealer::*;
        use self::party::*;

        use crate::errors::MPCError;

        // Simulate four parties, two of which will be dishonest and use a 64-bit value.
        let m = 4;
        let n = 32;

        let pc_gens = PedersenGens::<C>::default();
        let bp_gens = BulletproofGens::<C>::new(n, m);

        use self::rand::Rng;
        let mut rng = thread_rng();
        let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

        // Parties 0, 2 are honest and use a 32-bit value
        let v0 = rng.gen::<u32>() as u64;
        let v0_blinding = C::Scalar::random(&mut rng);
        let party0 = Party::new(&bp_gens, &pc_gens, v0, v0_blinding, n).unwrap();

        let v2 = rng.gen::<u32>() as u64;
        let v2_blinding = C::Scalar::random(&mut rng);
        let party2 = Party::new(&bp_gens, &pc_gens, v2, v2_blinding, n).unwrap();

        // Parties 1, 3 are dishonest and use a 64-bit value
        let v1 = rng.gen::<u64>();
        let v1_blinding = C::Scalar::random(&mut rng);
        let party1 = Party::new(&bp_gens, &pc_gens, v1, v1_blinding, n).unwrap();

        let v3 = rng.gen::<u64>();
        let v3_blinding = C::Scalar::random(&mut rng);
        let party3 = Party::new(&bp_gens, &pc_gens, v3, v3_blinding, n).unwrap();

        let dealer = Dealer::new(&bp_gens, &pc_gens, &mut transcript, n, m).unwrap();

        let (party0, bit_com0) = party0.assign_position(0).unwrap();
        let (party1, bit_com1) = party1.assign_position(1).unwrap();
        let (party2, bit_com2) = party2.assign_position(2).unwrap();
        let (party3, bit_com3) = party3.assign_position(3).unwrap();

        let (dealer, bit_challenge) = dealer
            .receive_bit_commitments(vec![bit_com0, bit_com1, bit_com2, bit_com3])
            .unwrap();

        let (party0, poly_com0) = party0.apply_challenge(&bit_challenge);
        let (party1, poly_com1) = party1.apply_challenge(&bit_challenge);
        let (party2, poly_com2) = party2.apply_challenge(&bit_challenge);
        let (party3, poly_com3) = party3.apply_challenge(&bit_challenge);

        let (dealer, poly_challenge) = dealer
            .receive_poly_commitments(vec![poly_com0, poly_com1, poly_com2, poly_com3])
            .unwrap();

        let share0 = party0.apply_challenge(&poly_challenge).unwrap();
        let share1 = party1.apply_challenge(&poly_challenge).unwrap();
        let share2 = party2.apply_challenge(&poly_challenge).unwrap();
        let share3 = party3.apply_challenge(&poly_challenge).unwrap();

        match dealer.receive_shares(&[share0, share1, share2, share3]) {
            Err(MPCError::MalformedProofShares { bad_shares }) => {
                assert_eq!(bad_shares, vec![1, 3]);
            }
            Err(_) => {
                panic!("Got wrong error type from malformed shares");
            }
            Ok(_) => {
                panic!("The proof was malformed, but it was not detected");
            }
        }
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn detect_dishonest_dealer_during_aggregation_curve25519() {
        detect_dishonest_dealer_during_aggregation::<crate::Curve25519>();
    }

    #[cfg(feature = "k256")]
    #[test]
    fn detect_dishonest_dealer_during_aggregation_k256() {
        detect_dishonest_dealer_during_aggregation::<k256::Secp256k1>();
    }

    #[cfg(feature = "p256")]
    #[test]
    fn detect_dishonest_dealer_during_aggregation_p256() {
        detect_dishonest_dealer_during_aggregation::<p256::NistP256>();
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn detect_dishonest_dealer_during_aggregation_bls12_381() {
        detect_dishonest_dealer_during_aggregation::<bls12_381_plus::Bls12381G1>();
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn detect_dishonest_dealer_during_aggregation_bls12_381_std() {
        detect_dishonest_dealer_during_aggregation::<blstrs_plus::Bls12381G1>();
    }

    fn detect_dishonest_dealer_during_aggregation<C: BulletproofCurveArithmetic>() {
        use self::dealer::*;
        use self::party::*;
        use crate::errors::MPCError;

        // Simulate one party
        let m = 1;
        let n = 32;

        let pc_gens = PedersenGens::<C>::default();
        let bp_gens = BulletproofGens::<C>::new(n, m);

        use self::rand::Rng;
        let mut rng = rand::thread_rng();
        let mut transcript = Transcript::new(b"AggregatedRangeProofTest");

        let v0 = rng.gen::<u32>() as u64;
        let v0_blinding = C::Scalar::random(&mut rng);
        let party0 = Party::new(&bp_gens, &pc_gens, v0, v0_blinding, n).unwrap();

        let dealer = Dealer::new(&bp_gens, &pc_gens, &mut transcript, n, m).unwrap();

        // Now do the protocol flow as normal....

        let (party0, bit_com0) = party0.assign_position(0).unwrap();

        let (dealer, bit_challenge) = dealer.receive_bit_commitments(vec![bit_com0]).unwrap();

        let (party0, poly_com0) = party0.apply_challenge(&bit_challenge);

        let (_dealer, mut poly_challenge) =
            dealer.receive_poly_commitments(vec![poly_com0]).unwrap();

        // But now simulate a malicious dealer choosing x = 0
        poly_challenge.x = C::Scalar::ZERO;

        let maybe_share0 = party0.apply_challenge(&poly_challenge);

        assert_eq!(maybe_share0.unwrap_err(), MPCError::MaliciousDealer);
    }
}
