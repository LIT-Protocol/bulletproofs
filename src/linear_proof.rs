#![allow(non_snake_case)]

extern crate alloc;

use super::CtOptionOps;
use alloc::vec::Vec;

use bls12_381_plus::{G1Affine, G1Projective, Scalar};
use core::iter;
use group::{ff::Field, Curve};
use merlin::Transcript;
use rand_core::{CryptoRng, RngCore};

use crate::errors::ProofError;
use crate::inner_product_proof::inner_product;
use crate::transcript::TranscriptProtocol;
use crate::util::ScalarBatchInvert;

/// A linear proof, which is an "lightweight" version of a Bulletproofs inner-product proof
/// Protocol: Section E.3 of [GHL'21](https://eprint.iacr.org/2021/1397.pdf)
///
/// Prove that <a, b> = c where a is secret and b is public.
#[derive(Clone, Debug)]
pub struct LinearProof {
    pub(crate) L_vec: Vec<G1Projective>,
    pub(crate) R_vec: Vec<G1Projective>,
    /// A commitment to the base case elements
    pub(crate) S: G1Projective,
    /// a_star, corresponding to the base case `a`
    pub(crate) a: Scalar,
    /// r_star, corresponding to the base case `r`
    pub(crate) r: Scalar,
}

impl LinearProof {
    /// Create a linear proof, a lightweight variant of a Bulletproofs inner-product proof.
    /// This proves that <a, b> = c where a is secret and b is public.
    ///
    /// The lengths of the vectors must all be the same, and must all be either 0 or a power of 2.
    /// The proof is created with respect to the bases \\(G\\).
    pub fn create(
        transcript: &mut Transcript,
        mut rng: impl RngCore + CryptoRng,
        // Commitment to witness
        C: &G1Projective,
        // Blinding factor for C
        mut r: Scalar,
        // Secret scalar vector a
        mut a_vec: Vec<Scalar>,
        // Public scalar vector b
        mut b_vec: Vec<Scalar>,
        // Generator vector
        mut G_vec: Vec<G1Projective>,
        // Pedersen generator F, for committing to the secret value
        F: &G1Projective,
        // Pedersen generator B, for committing to the blinding value
        B: &RistrettoPoint,
    ) -> Result<LinearProof, ProofError> {
        let mut n = b_vec.len();
        // All of the input vectors must have the same length.
        if G_vec.len() != n {
            return Err(ProofError::InvalidGeneratorsLength);
        }
        if a_vec.len() != n {
            return Err(ProofError::InvalidInputLength);
        }
        // All of the input vectors must have a length that is a power of two.
        if !n.is_power_of_two() {
            return Err(ProofError::InvalidInputLength);
        }

        // Append all public data to the transcript
        transcript.innerproduct_domain_sep(n as u64);
        transcript.append_point(b"C", &C);
        for b_i in &b_vec {
            transcript.append_scalar(b"b_i", b_i);
        }
        for G_i in &G_vec {
            transcript.append_point(b"G_i", &G_i.compress());
        }
        transcript.append_point(b"F", &F.compress());
        transcript.append_point(b"B", &B.compress());

        // Create slices G, H, a, b backed by their respective
        // vectors. This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        transcript.innerproduct_domain_sep(n as u64);
        transcript.append_point(b"C", C);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        while n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);

            let c_L = inner_product(a_L, b_R);
            let c_R = inner_product(a_R, b_L);

            let s_j = Scalar::random(&mut rng);
            let t_j = Scalar::random(&mut rng);

            // L = a_L * G_R + s_j * B + c_L * F
            let L_points: Vec<G1Projective> = G_R
                .iter()
                .copied()
                .chain(iter::once(*B))
                .chain(iter::once(*F))
                .collect();
            let L_scalars: Vec<Scalar> = a_L
                .iter()
                .copied()
                .chain(iter::once(s_j))
                .chain(iter::once(c_L))
                .collect();
            let L = G1Projective::sum_of_products(&L_points, &L_scalars);

            // R = a_R * G_L + t_j * B + c_R * F
            let R_points: Vec<G1Projective> = G_L
                .iter()
                .copied()
                .chain(iter::once(*B))
                .chain(iter::once(*F))
                .collect();
            let R_scalars: Vec<Scalar> = a_R
                .iter()
                .copied()
                .chain(iter::once(t_j))
                .chain(iter::once(c_R))
                .collect();
            let R = G1Projective::sum_of_products(&R_points, &R_scalars);

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let x_j = transcript.challenge_scalar(b"x_j");
            let x_j_inv = x_j.invert().unwrap();

            for i in 0..n {
                // a_L = a_L + x_j^{-1} * a_R
                a_L[i] += x_j_inv * a_R[i];
                // b_L = b_L + x_j * b_R
                b_L[i] += x_j * b_R[i];
                // G_L = G_L + x_j * G_R
                G_L[i] = G1Projective::sum_of_products(&[G_L[i], G_R[i]], &[Scalar::one(), x_j]);
            }
            a = a_L;
            b = b_L;
            G = G_L;
            r = r + x_j * s_j + x_j_inv * t_j;
        }

        let s_star = Scalar::random(&mut rng);
        let t_star = Scalar::random(&mut rng);
        let S = B * t_star + F * s_star * b[0] + G[0] * s_star;
        transcript.append_point(b"S", &S);

        let x_star = transcript.challenge_scalar(b"x_star");
        let a_star = s_star + x_star * a[0];
        let r_star = t_star + x_star * r;

        Ok(LinearProof {
            L_vec,
            R_vec,
            S,
            a: a_star,
            r: r_star,
        })
    }

    pub fn verify(
        &self,
        transcript: &mut Transcript,
        // Commitment to witness
        C: &G1Projective,
        // Generator vector
        G: &[G1Projective],
        // Pedersen generator F, for committing to the secret value
        F: &G1Projective,
        // Pedersen generator B, for committing to the blinding value
        B: &G1Projective,
        // Public scalar vector b
        b_vec: Vec<Scalar>,
    ) -> Result<(), ProofError> {
        let n = b_vec.len();
        if G.len() != n {
            return Err(ProofError::InvalidGeneratorsLength);
        }

        // Append all public data to the transcript
        transcript.innerproduct_domain_sep(n as u64);
        transcript.append_point(b"C", &C);
        for b_i in &b_vec {
            transcript.append_scalar(b"b_i", b_i);
        }
        for G_i in G {
            transcript.append_point(b"G_i", &G_i.compress());
        }
        transcript.append_point(b"F", &F.compress());
        transcript.append_point(b"B", &B.compress());

        let (x_vec, x_inv_vec, b_0) = self.verification_scalars(n, transcript, b_vec)?;
        transcript.append_point(b"S", &self.S);
        let x_star = transcript.challenge_scalar(b"x_star");

        // L_R_factors = sum_{j=0}^{l-1} (x_j * L_j + x_j^{-1} * R_j)
        //
        // Note: in GHL'21 the verification equation is incorrect (as of 05/03/22), with x_j and x_j^{-1} reversed.
        // (Incorrect paper equation: sum_{j=0}^{l-1} (x_j^{-1} * L_j + x_j * R_j) )
        let L_R_points: Vec<G1Projective> = self
            .L_vec
            .iter()
            .copied()
            .chain(self.R_vec.iter().copied())
            .collect();
        let L_R_scalars: Vec<Scalar> = x_vec.iter().copied().chain(x_inv_vec.into_iter()).collect();
        let L_R_factors = G1Projective::sum_of_products(&L_R_points, &L_R_scalars);

        // This is an optimized way to compute the base case G (G_0 in the paper):
        // G_0 = sum_{i=0}^{2^{l-1}} (x<i> * G_i)
        let s = self.subset_product(n, x_vec);
        let G_0 = G1Projective::sum_of_products(G, &s);

        // This matches the verification equation:
        // S == r_star * B + a_star * b_0 * F
        //      - x_star * (C + sum_{j=0}^{l-1} (x_j * L_j + x_j^{-1} * R_j))
        //      + a_star * sum_{i=0}^{2^{l-1}} (x<i> * G_i)
        //
        // Where L_R_factors = sum_{j=0}^{l-1} (x_j * L_j + x_j^{-1} * R_j)
        // and G_0 = sum_{i=0}^{2^{l-1}} (x<i> * G_i)
        let expect_S = B * self.r + F * self.a * b_0 - (C + L_R_factors) * x_star + G_0 * self.a;

        if expect_S == self.S {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    /// Computes the vector of challenge scalars \\([x\_{i}]\\), and its inverse \\([x\_{i}^{-1}]\\)
    /// for combined multiscalar multiplication in a parent protocol.
    /// Also computes \\(b_0\\) which is the base case for public vector \\(b\\).
    ///
    /// The verifier must provide the input length \\(n\\) explicitly to avoid unbounded allocation.
    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
        mut b_vec: Vec<Scalar>,
    ) -> Result<(Vec<Scalar>, Vec<Scalar>, Scalar), ProofError> {
        let lg_n = self.L_vec.len();
        if lg_n >= 48 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<lg_n below.
            return Err(ProofError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        // 1. Recompute x_k,...,x_1 based on the proof transcript
        // 2. Generate b_0 from the public vector b
        let mut n_mut = n;
        let mut b = &mut b_vec[..];
        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            let x_j = transcript.challenge_scalar(b"x_j");
            challenges.push(x_j);
            n_mut /= 2;
            let (b_L, b_R) = b.split_at_mut(n_mut);
            for i in 0..n_mut {
                b_L[i] += x_j * b_R[i];
            }
            b = b_L;
        }

        // 3. Compute the challenge inverses: 1/x_k, ..., 1/x_1
        let mut challenges_inv = challenges.clone();
        Scalar::batch_invert(&mut challenges_inv);

        Ok((challenges, challenges_inv, b[0]))
    }

    /// Compute the subset-products of \\(x_j\\) inductively:
    /// for i = 1..n, \\(s_i = product_(j=1^{log_2(n)}) x_j ^ b(i,j)\\)
    /// where \\(b(i,j)\\) = 1 if the jth bit of (i-1) is 1, and 0 otherwise.
    /// In GHL'21 this is referred to as the subset-product \\(x<i>\\).
    ///
    /// Note that this is different from the Bulletproofs \\(s_i\\) generation,
    /// where \\(b(i, j)\\) = 1 if the jth bit of (i-1) is 1, and -1 otherwise.
    fn subset_product(&self, n: usize, challenges: Vec<Scalar>) -> Vec<Scalar> {
        let lg_n = self.L_vec.len();

        let mut s = Vec::with_capacity(n);
        s.push(Scalar::one());
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [x_k,...,x_1],
            // so x_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let x_lg_i = challenges[(lg_n - 1) - lg_i];
            s.push(s[i - k] * x_lg_i);
        }

        s
    }

    /// Returns the size in bytes required to serialize the linear proof.
    ///
    /// For vectors of length `n` the proof size is
    /// \\(32 \cdot (2\lg n+3)\\) bytes.
    pub fn serialized_size(&self) -> usize {
        (self.L_vec.len() * 2 + 1) * 48 + 64
    }

    /// Serializes the proof into a byte array of \\(2n+3\\) 32-byte elements.
    /// The layout of the linear proof is:
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * one compressed Ristretto point \\(S\\),
    /// * two scalars \\(a, r\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        buf.extend_from_slice(&self.a.to_bytes());
        buf.extend_from_slice(&self.r.to_bytes());
        buf.extend_from_slice(&self.S.to_affine().to_compressed());
        for (l, r) in self.L_vec.iter().zip(self.R_vec.iter()) {
            buf.extend_from_slice(&l.to_affine().to_compressed());
            buf.extend_from_slice(&r.to_affine().to_compressed());
        }
        buf
    }

    /// Converts the proof into a byte iterator over serialized view of the proof.
    /// The layout of the inner product proof is:
    /// * \\(n\\) pairs of compressed Ristretto points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * one compressed Ristretto point \\(S\\),
    /// * two scalars \\(a, r\\).
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn to_bytes_iter(&self) -> impl Iterator<Item = u8> + '_ {
        self.a
            .to_bytes()
            .into_iter()
            .chain(self.r.to_bytes().into_iter())
            .chain(self.S.to_affine().to_compressed().into_iter())
            .chain(self.L_vec.iter().zip(self.R_vec.iter()).flat_map(|(l, r)| {
                l.to_affine()
                    .to_compressed()
                    .into_iter()
                    .chain(r.to_affine().to_compressed().into_iter())
            }))
    }

    /// Deserializes the proof from a byte slice.
    /// Returns an error in the following cases:
    /// * the slice does not have \\(2n+3\\) 32-byte elements,
    /// * \\(n\\) is larger or equal to 32 (proof is too big),
    /// * any of \\(2n + 1\\) points are not valid compressed Ristretto points,
    /// * any of 2 scalars are not canonical scalars modulo Ristretto group order.
    pub fn from_bytes(slice: &[u8]) -> Result<LinearProof, ProofError> {
        let b = slice.len() - 64;
        if b % 48 != 0 {
            return Err(ProofError::FormatError);
        }
        let num_elements = b / 48 + 2;
        if num_elements < 3 {
            return Err(ProofError::FormatError);
        }
        if (num_elements - 3) % 2 != 0 {
            return Err(ProofError::FormatError);
        }
        let lg_n = (num_elements - 3) / 2;
        if lg_n >= 48 {
            return Err(ProofError::FormatError);
        }

        use crate::util::{read32, read48};

        let a = Scalar::from_bytes(&read32(slice)).ok_or(ProofError::FormatError)?;
        let r = Scalar::from_bytes(&read32(&slice[32..])).ok_or(ProofError::FormatError)?;
        let S = G1Affine::from_compressed(&read48(&slice[64..]))
            .map(G1Projective::from)
            .ok_or(ProofError::FormatError)?;

        let mut L_vec: Vec<G1Projective> = Vec::with_capacity(lg_n);
        let mut R_vec: Vec<G1Projective> = Vec::with_capacity(lg_n);
        for i in 0..lg_n {
            let pos = 112 + i * 96;
            L_vec.push(
                G1Affine::from_compressed(&read48(&slice[pos..]))
                    .map(G1Projective::from)
                    .ok_or(ProofError::FormatError)?,
            );
            R_vec.push(
                G1Affine::from_compressed(&read48(&slice[pos + 48..]))
                    .map(G1Projective::from)
                    .ok_or(ProofError::FormatError)?,
            );
        }

        Ok(LinearProof {
            L_vec,
            R_vec,
            S,
            a,
            r,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_helper(n: usize) {
        let mut rng = rand::thread_rng();

        use crate::generators::{BulletproofGens, PedersenGens};
        let bp_gens = BulletproofGens::new(n, 1);
        let G: Vec<G1Projective> = bp_gens.share(0).G(n).cloned().collect();

        let pedersen_gens = PedersenGens::default();
        let F = pedersen_gens.B;
        let B = pedersen_gens.B_blinding;

        // a and b are the vectors for which we want to prove c = <a,b>
        // a is a private vector, b is a public vector
        let a: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();

        let mut prover_transcript = Transcript::new(b"linearprooftest");

        // C = <a, G> + r * B + <a, b> * F
        let r = Scalar::random(&mut rng);
        let c = inner_product(&a, &b);
        let C_points: Vec<G1Projective> = G
            .iter()
            .map(|&p| p)
            .chain(iter::once(B))
            .chain(iter::once(F))
            .collect();
        let C_scalars: Vec<Scalar> = a
            .iter()
            .map(|&s| s)
            .chain(iter::once(r))
            .chain(iter::once(c))
            .collect();
        let C = G1Projective::sum_of_products(&C_points, &C_scalars);

        let proof = LinearProof::create(
            &mut prover_transcript,
            &mut rng,
            &C,
            r,
            a,
            b.clone(),
            G.clone(),
            &F,
            &B,
        )
        .unwrap();

        let mut verifier_transcript = Transcript::new(b"linearprooftest");
        assert!(proof
            .verify(&mut verifier_transcript, &C, &G, &F, &B, b.clone())
            .is_ok());

        // Test serialization and deserialization
        let serialized_proof = proof.to_bytes();
        assert_eq!(proof.serialized_size(), serialized_proof.len());

        let deserialized_proof = LinearProof::from_bytes(&serialized_proof).unwrap();
        let mut serde_verifier_transcript = Transcript::new(b"linearprooftest");
        assert!(deserialized_proof
            .verify(&mut serde_verifier_transcript, &C, &G, &F, &B, b)
            .is_ok());
    }

    #[test]
    fn test_linear_proof_base() {
        test_helper(1);
    }

    #[test]
    fn test_linear_proof_16() {
        test_helper(16);
    }

    #[test]
    fn test_linear_proof_32() {
        test_helper(32);
    }

    #[test]
    fn test_linear_proof_64() {
        test_helper(64);
    }
}
