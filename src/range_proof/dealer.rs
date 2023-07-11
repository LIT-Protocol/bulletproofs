//! The `dealer` module contains the API for the dealer state while the dealer is
//! engaging in an aggregated multiparty computation protocol.
//!
//! For more explanation of how the `dealer`, `party`, and `messages` modules orchestrate the protocol execution, see
//! [the API for the aggregated multiparty computation protocol](../aggregation/index.html#api-for-the-aggregated-multiparty-computation-protocol).

use core::iter;

extern crate alloc;

use alloc::vec::Vec;
use core::marker::PhantomData;
use group::ff::Field;
use merlin::Transcript;

use crate::errors::MPCError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof;
use crate::range_proof::RangeProof;
use crate::transcript::TranscriptProtocol;

use rand_core::{CryptoRng, RngCore};

use crate::types::*;
use crate::util;

#[cfg(feature = "std")]
use rand::thread_rng;

use super::messages::*;

/// Used to construct a dealer for the aggregated rangeproof MPC protocol.
pub struct Dealer<C: BulletproofCurveArithmetic> {
    _marker: PhantomData<C>,
}

impl<C: BulletproofCurveArithmetic> Dealer<C> {
    /// Creates a new dealer coordinating `m` parties proving `n`-bit ranges.
    pub fn new<'a, 'b>(
        bp_gens: &'b BulletproofGens<C>,
        pc_gens: &'b PedersenGens<C>,
        transcript: &'a mut Transcript,
        n: usize,
        m: usize,
    ) -> Result<DealerAwaitingBitCommitments<'a, 'b, C>, MPCError> {
        if !(n == 8 || n == 16 || n == 32 || n == 64) {
            return Err(MPCError::InvalidBitsize);
        }
        if !m.is_power_of_two() {
            return Err(MPCError::InvalidAggregation);
        }
        if bp_gens.gens_capacity < n {
            return Err(MPCError::InvalidGeneratorsLength);
        }
        if bp_gens.party_capacity < m {
            return Err(MPCError::InvalidGeneratorsLength);
        }

        // At the end of the protocol, the dealer will attempt to
        // verify the proof, and if it fails, determine which party's
        // shares were invalid.
        //
        // However, verifying the proof requires either knowledge of
        // all of the challenges, or a copy of the initial transcript
        // state.
        //
        // The dealer has all of the challenges, but using them for
        // verification would require duplicating the verification
        // logic.  Instead, we keep a copy of the initial transcript
        // state.
        let initial_transcript = transcript.clone();

        transcript.rangeproof_domain_sep(n as u64, m as u64);

        Ok(DealerAwaitingBitCommitments {
            bp_gens,
            pc_gens,
            transcript,
            initial_transcript,
            n,
            m,
        })
    }
}

/// A dealer waiting for the parties to send their [`BitCommitment`]s.
pub struct DealerAwaitingBitCommitments<'a, 'b, C: BulletproofCurveArithmetic> {
    bp_gens: &'b BulletproofGens<C>,
    pc_gens: &'b PedersenGens<C>,
    transcript: &'a mut Transcript,
    /// The dealer keeps a copy of the initial transcript state, so
    /// that it can attempt to verify the aggregated proof at the end.
    initial_transcript: Transcript,
    n: usize,
    m: usize,
}

impl<'a, 'b, C: BulletproofCurveArithmetic> DealerAwaitingBitCommitments<'a, 'b, C> {
    /// Receive each party's [`BitCommitment`]s and compute the [`BitChallenge`].
    pub fn receive_bit_commitments(
        self,
        bit_commitments: Vec<BitCommitment<C>>,
    ) -> Result<(DealerAwaitingPolyCommitments<'a, 'b, C>, BitChallenge<C>), MPCError> {
        if self.m != bit_commitments.len() {
            return Err(MPCError::WrongNumBitCommitments);
        }

        // Commit each V_j individually
        for vc in bit_commitments.iter() {
            self.transcript.append_point::<C>(b"V", &vc.V_j);
        }

        // Commit aggregated A_j, S_j
        let A: C::Point = bit_commitments.iter().map(|vc| vc.A_j).sum();
        self.transcript.append_point::<C>(b"A", &A);

        let S: C::Point = bit_commitments.iter().map(|vc| vc.S_j).sum();
        self.transcript.append_point::<C>(b"S", &S);

        let y = self.transcript.challenge_scalar::<C>(b"y");
        let z = self.transcript.challenge_scalar::<C>(b"z");
        let bit_challenge = BitChallenge { y, z };

        Ok((
            DealerAwaitingPolyCommitments {
                n: self.n,
                m: self.m,
                transcript: self.transcript,
                initial_transcript: self.initial_transcript,
                bp_gens: self.bp_gens,
                pc_gens: self.pc_gens,
                bit_challenge,
                bit_commitments,
                A,
                S,
            },
            bit_challenge,
        ))
    }
}

/// A dealer which has sent the [`BitChallenge`] to the parties and
/// is waiting for their [`PolyCommitment`]s.
pub struct DealerAwaitingPolyCommitments<'a, 'b, C: BulletproofCurveArithmetic> {
    n: usize,
    m: usize,
    transcript: &'a mut Transcript,
    initial_transcript: Transcript,
    bp_gens: &'b BulletproofGens<C>,
    pc_gens: &'b PedersenGens<C>,
    bit_challenge: BitChallenge<C>,
    bit_commitments: Vec<BitCommitment<C>>,
    /// Aggregated commitment to the parties' bits
    A: C::Point,
    /// Aggregated commitment to the parties' bit blindings
    S: C::Point,
}

impl<'a, 'b, C: BulletproofCurveArithmetic> DealerAwaitingPolyCommitments<'a, 'b, C> {
    /// Receive [`PolyCommitment`]s from the parties and compute the
    /// [`PolyChallenge`].
    pub fn receive_poly_commitments(
        self,
        poly_commitments: Vec<PolyCommitment<C>>,
    ) -> Result<(DealerAwaitingProofShares<'a, 'b, C>, PolyChallenge<C>), MPCError> {
        if self.m != poly_commitments.len() {
            return Err(MPCError::WrongNumPolyCommitments);
        }

        // Commit sums of T_1_j's and T_2_j's
        let T_1: C::Point = poly_commitments.iter().map(|pc| pc.T_1_j).sum();
        let T_2: C::Point = poly_commitments.iter().map(|pc| pc.T_2_j).sum();

        self.transcript.append_point::<C>(b"T_1", &T_1);
        self.transcript.append_point::<C>(b"T_2", &T_2);

        let x = self.transcript.challenge_scalar::<C>(b"x");
        let poly_challenge = PolyChallenge { x };

        Ok((
            DealerAwaitingProofShares {
                n: self.n,
                m: self.m,
                transcript: self.transcript,
                initial_transcript: self.initial_transcript,
                bp_gens: self.bp_gens,
                pc_gens: self.pc_gens,
                bit_challenge: self.bit_challenge,
                bit_commitments: self.bit_commitments,
                A: self.A,
                S: self.S,
                poly_challenge,
                poly_commitments,
                T_1,
                T_2,
            },
            poly_challenge,
        ))
    }
}

/// A dealer which has sent the [`PolyChallenge`] to the parties and
/// is waiting to aggregate their [`ProofShare`]s into a
/// [`RangeProof`].
pub struct DealerAwaitingProofShares<'a, 'b, C: BulletproofCurveArithmetic> {
    n: usize,
    m: usize,
    transcript: &'a mut Transcript,
    initial_transcript: Transcript,
    bp_gens: &'b BulletproofGens<C>,
    pc_gens: &'b PedersenGens<C>,
    bit_challenge: BitChallenge<C>,
    bit_commitments: Vec<BitCommitment<C>>,
    poly_challenge: PolyChallenge<C>,
    poly_commitments: Vec<PolyCommitment<C>>,
    A: C::Point,
    S: C::Point,
    T_1: C::Point,
    T_2: C::Point,
}

impl<'a, 'b, C: BulletproofCurveArithmetic> DealerAwaitingProofShares<'a, 'b, C> {
    /// Assembles proof shares into an `RangeProof`.
    ///
    /// Used as a helper function by `receive_trusted_shares` (which
    /// just hands back the result) and `receive_shares` (which
    /// validates the proof shares.
    fn assemble_shares(
        &mut self,
        proof_shares: &[ProofShare<C>],
    ) -> Result<RangeProof<C>, MPCError> {
        if self.m != proof_shares.len() {
            return Err(MPCError::WrongNumProofShares);
        }

        // Validate lengths for each share
        let mut bad_shares = Vec::<usize>::new(); // no allocations until we append
        for (j, share) in proof_shares.iter().enumerate() {
            share
                .check_size(self.n, self.bp_gens, j)
                .unwrap_or_else(|_| {
                    bad_shares.push(j);
                });
        }

        if !bad_shares.is_empty() {
            return Err(MPCError::MalformedProofShares { bad_shares });
        }

        let t_x: C::Scalar = proof_shares.iter().map(|ps| ps.t_x).sum();
        let t_x_blinding: C::Scalar = proof_shares.iter().map(|ps| ps.t_x_blinding).sum();
        let e_blinding: C::Scalar = proof_shares.iter().map(|ps| ps.e_blinding).sum();

        self.transcript.append_scalar::<C>(b"t_x", &t_x);
        self.transcript
            .append_scalar::<C>(b"t_x_blinding", &t_x_blinding);
        self.transcript
            .append_scalar::<C>(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = self.transcript.challenge_scalar::<C>(b"w");
        let Q = self.pc_gens.B * w;

        let G_factors: Vec<C::Scalar> =
            iter::repeat(C::Scalar::ONE).take(self.n * self.m).collect();
        let H_factors: Vec<C::Scalar> = util::exp_iter::<C>(self.bit_challenge.y.invert().unwrap())
            .take(self.n * self.m)
            .collect();

        let l_vec: Vec<C::Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.l_vec.clone().into_iter())
            .collect();
        let r_vec: Vec<C::Scalar> = proof_shares
            .iter()
            .flat_map(|ps| ps.r_vec.clone().into_iter())
            .collect();

        let ipp_proof = inner_product_proof::InnerProductProof::<C>::create(
            self.transcript,
            &Q,
            &G_factors,
            &H_factors,
            self.bp_gens.G(self.n, self.m).cloned().collect(),
            self.bp_gens.H(self.n, self.m).cloned().collect(),
            l_vec,
            r_vec,
        );

        Ok(RangeProof {
            A: self.A,
            S: self.S,
            T_1: self.T_1,
            T_2: self.T_2,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        })
    }

    /// Assemble the final aggregated [`RangeProof`] from the given
    /// `proof_shares`, then validate the proof to ensure that all
    /// `ProofShare`s were well-formed.
    ///
    /// This is a convenience wrapper around receive_shares_with_rng
    ///
    #[cfg(feature = "std")]
    pub fn receive_shares(self, proof_shares: &[ProofShare<C>]) -> Result<RangeProof<C>, MPCError> {
        self.receive_shares_with_rng(proof_shares, &mut thread_rng())
    }

    /// Assemble the final aggregated [`RangeProof`] from the given
    /// `proof_shares`, then validate the proof to ensure that all
    /// `ProofShare`s were well-formed.
    ///
    /// If the aggregated proof fails to validate, this function
    /// audits the submitted shares to determine which shares were
    /// invalid.  This information is returned as part of the
    /// [`MPCError`].
    ///
    /// If the proof shares are known to be trusted, for instance when
    /// performing local aggregation,
    /// [`receive_trusted_shares`](DealerAwaitingProofShares::receive_trusted_shares)
    /// saves time by skipping verification of the aggregated proof.
    pub fn receive_shares_with_rng<T: RngCore + CryptoRng>(
        mut self,
        proof_shares: &[ProofShare<C>],
        rng: &mut T,
    ) -> Result<RangeProof<C>, MPCError> {
        let proof = self.assemble_shares(proof_shares)?;

        let Vs: Vec<_> = self.bit_commitments.iter().map(|vc| vc.V_j).collect();

        // See comment in `Dealer::new` for why we use `initial_transcript`
        let transcript = &mut self.initial_transcript;
        if proof
            .verify_multiple_with_rng(self.bp_gens, self.pc_gens, transcript, &Vs, self.n, rng)
            .is_ok()
        {
            Ok(proof)
        } else {
            // Proof verification failed. Now audit the parties:
            let mut bad_shares = Vec::new();
            for j in 0..self.m {
                match proof_shares[j].audit_share(
                    self.bp_gens,
                    self.pc_gens,
                    j,
                    &self.bit_commitments[j],
                    &self.bit_challenge,
                    &self.poly_commitments[j],
                    &self.poly_challenge,
                ) {
                    Ok(_) => {}
                    Err(_) => bad_shares.push(j),
                }
            }
            Err(MPCError::MalformedProofShares { bad_shares })
        }
    }

    /// Assemble the final aggregated [`RangeProof`] from the given
    /// `proof_shares`, but skip validation of the proof.
    ///
    /// ## WARNING
    ///
    /// This function does **NOT** validate the proof shares.  It is
    /// suitable for creating aggregated proofs when all parties are
    /// known by the dealer to be honest (for instance, when there's
    /// only one party playing all roles).
    ///
    /// Otherwise, use
    /// [`receive_shares`](DealerAwaitingProofShares::receive_shares),
    /// which validates that all shares are well-formed, or else
    /// detects which party(ies) submitted malformed shares.
    pub fn receive_trusted_shares(
        mut self,
        proof_shares: &[ProofShare<C>],
    ) -> Result<RangeProof<C>, MPCError> {
        self.assemble_shares(proof_shares)
    }
}
