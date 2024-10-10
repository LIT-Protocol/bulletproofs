#![allow(non_snake_case)]
#![cfg_attr(feature = "docs", doc(include = "../docs/inner-product-protocol.md"))]

extern crate alloc;

use super::CtOptionOps;
use alloc::borrow::Borrow;
use alloc::vec::Vec;

use core::iter;
use group::ff::Field;
use merlin::Transcript;
use serde::{Deserialize, Serialize};
use subtle::ConstantTimeEq;

use crate::errors::ProofError;
use crate::serdes::*;
use crate::transcript::TranscriptProtocol;
use crate::types::*;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct InnerProductProof<C: BulletproofCurveArithmetic> {
    #[serde(with = "CurvePointVec::<C>")]
    pub(crate) L_vec: Vec<C::Point>,
    #[serde(with = "CurvePointVec::<C>")]
    pub(crate) R_vec: Vec<C::Point>,
    #[serde(with = "CurveScalar::<C>")]
    pub(crate) a: C::Scalar,
    #[serde(with = "CurveScalar::<C>")]
    pub(crate) b: C::Scalar,
}

impl<C: BulletproofCurveArithmetic> InnerProductProof<C> {
    /// Create an inner-product proof.
    ///
    /// The proof is created with respect to the bases \\(G\\), \\(H'\\),
    /// where \\(H'\_i = H\_i \cdot \texttt{Hprime\\_factors}\_i\\).
    ///
    /// The `verifier` is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    ///
    /// The lengths of the vectors must all be the same, and must all be
    /// either 0 or a power of 2.
    pub fn create(
        transcript: &mut Transcript,
        Q: &C::Point,
        G_factors: &[C::Scalar],
        H_factors: &[C::Scalar],
        mut G_vec: Vec<C::Point>,
        mut H_vec: Vec<C::Point>,
        mut a_vec: Vec<C::Scalar>,
        mut b_vec: Vec<C::Scalar>,
    ) -> Self {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert_eq!(G_factors.len(), n);
        assert_eq!(H_factors.len(), n);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        transcript.innerproduct_domain_sep(n as u64);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        // If it's the first iteration, unroll the Hprime = H*y_inv scalar mults
        // into multiscalar muls, for performance.
        if n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product::<C>(a_L, b_R);
            let c_R = inner_product::<C>(a_R, b_L);

            let L_scalars: Vec<C::Scalar> = a_L
                .iter()
                .zip(G_factors[n..2 * n].iter())
                .map(|(a_L_i, g)| *a_L_i * *g)
                .chain(
                    b_R.iter()
                        .zip(H_factors[0..n].iter())
                        .map(|(b_R_i, h)| *b_R_i * *h),
                )
                .chain(iter::once(c_L))
                .collect();
            let L_points: Vec<C::Point> = G_R
                .iter()
                .copied()
                .chain(H_L.iter().copied())
                .chain(iter::once(*Q))
                .collect();
            let L = C::pippenger_sum_of_products(&L_points, &L_scalars);

            let R_scalars: Vec<C::Scalar> = a_R
                .iter()
                .zip(G_factors[0..n].iter())
                .map(|(a_R_i, g)| *a_R_i * *g)
                .chain(
                    b_L.iter()
                        .zip(H_factors[n..2 * n].iter())
                        .map(|(b_L_i, h)| *b_L_i * *h),
                )
                .chain(iter::once(c_R))
                .collect();
            let R_points: Vec<C::Point> = G_L
                .iter()
                .copied()
                .chain(H_R.iter().copied())
                .chain(iter::once(*Q))
                .collect();
            let R = C::pippenger_sum_of_products(&R_points, &R_scalars);

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point::<C>(b"L", &L);
            transcript.append_point::<C>(b"R", &R);

            let u: C::Scalar = transcript.challenge_scalar::<C>(b"u");
            let u_inv = u.invert().unwrap();

            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = C::pippenger_sum_of_products(
                    &[G_L[i], G_R[i]],
                    &[u_inv * G_factors[i], u * G_factors[n + i]],
                );
                H_L[i] = C::pippenger_sum_of_products(
                    &[H_L[i], H_R[i]],
                    &[u * H_factors[i], u_inv * H_factors[n + i]],
                );
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        while n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product::<C>(a_L, b_R);
            let c_R = inner_product::<C>(a_R, b_L);

            let L_points: Vec<C::Point> = G_R
                .iter()
                .copied()
                .chain(H_L.iter().copied())
                .chain(iter::once(*Q))
                .collect();
            let L_scalars: Vec<C::Scalar> = a_L
                .iter()
                .copied()
                .chain(b_R.iter().copied())
                .chain(iter::once(c_L))
                .collect();
            let L = C::pippenger_sum_of_products(&L_points, &L_scalars);

            let R_points: Vec<C::Point> = G_L
                .iter()
                .copied()
                .chain(H_R.iter().copied())
                .chain(iter::once(*Q))
                .collect();
            let R_scalars: Vec<C::Scalar> = a_R
                .iter()
                .copied()
                .chain(b_L.iter().copied())
                .chain(iter::once(c_R))
                .collect();
            let R = C::pippenger_sum_of_products(&R_points, &R_scalars);

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point::<C>(b"L", &L);
            transcript.append_point::<C>(b"R", &R);

            let u: C::Scalar = transcript.challenge_scalar::<C>(b"u");
            let u_inv = u.invert().unwrap();

            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = C::pippenger_sum_of_products(&[G_L[i], G_R[i]], &[u_inv, u]);
                H_L[i] = C::pippenger_sum_of_products(&[H_L[i], H_R[i]], &[u, u_inv]);
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        InnerProductProof {
            L_vec,
            R_vec,
            a: a[0],
            b: b[0],
        }
    }

    /// Computes three vectors of verification scalars \\([u\_{i}^{2}]\\), \\([u\_{i}^{-2}]\\) and \\([s\_{i}]\\) for combined multiscalar multiplication
    /// in a parent protocol. See [inner product protocol notes](index.html#verification-equation) for details.
    /// The verifier must provide the input length \\(n\\) explicitly to avoid unbounded allocation within the inner product proof.
    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut Transcript,
    ) -> Result<(Vec<C::Scalar>, Vec<C::Scalar>, Vec<C::Scalar>), ProofError> {
        let lg_n = self.L_vec.len();
        if lg_n >= 32 {
            // 4 billion multiplications should be enough for anyone
            // and this check prevents overflow in 1<<lg_n below.
            return Err(ProofError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);

        // 1. Recompute x_k,...,x_1 based on the proof transcript

        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.validate_and_append_point::<C>(b"L", L)?;
            transcript.validate_and_append_point::<C>(b"R", R)?;
            challenges.push(transcript.challenge_scalar::<C>(b"u"));
        }

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1

        let mut challenges_inv = challenges.clone();
        let allinv = C::Scalar::batch_invert(&mut challenges_inv);

        // 3. Compute u_i^2 and (1/u_i)^2

        for i in 0..lg_n {
            // XXX missing square fn upstream
            challenges[i] = challenges[i] * challenges[i];
            challenges_inv[i] = challenges_inv[i] * challenges_inv[i];
        }
        let challenges_sq = challenges;
        let challenges_inv_sq = challenges_inv;

        // 4. Compute s values inductively.

        let mut s = Vec::with_capacity(n);
        s.push(allinv);
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [u_k,...,u_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
            s.push(s[i - k] * u_lg_i_sq);
        }

        Ok((challenges_sq, challenges_inv_sq, s))
    }

    /// This method is for testing that proof generation work,
    /// but for efficiency the actual protocols would use `verification_scalars`
    /// method to combine inner product verification with other checks
    /// in a single multiscalar multiplication.
    #[allow(dead_code)]
    pub fn verify<IG, IH>(
        &self,
        n: usize,
        transcript: &mut Transcript,
        G_factors: IG,
        H_factors: IH,
        P: &C::Point,
        Q: &C::Point,
        G: &[C::Point],
        H: &[C::Point],
    ) -> Result<(), ProofError>
    where
        IG: IntoIterator,
        IG::Item: Borrow<C::Scalar>,
        IH: IntoIterator,
        IH::Item: Borrow<C::Scalar>,
    {
        let (u_sq, u_inv_sq, s) = self.verification_scalars(n, transcript)?;

        let g_times_a_times_s = G_factors
            .into_iter()
            .zip(s.iter())
            .map(|(g_i, s_i)| (self.a * s_i) * g_i.borrow())
            .take(G.len());

        // 1/s[i] is s[!i], and !i runs from n-1 to 0 as i runs from 0 to n-1
        let inv_s = s.iter().rev();

        let h_times_b_div_s = H_factors
            .into_iter()
            .zip(inv_s)
            .map(|(h_i, s_i_inv)| (self.b * s_i_inv) * h_i.borrow());

        let neg_u_sq = u_sq.iter().map(|ui| -*ui);
        let neg_u_inv_sq = u_inv_sq.iter().map(|ui| -*ui);

        let P_points: Vec<C::Point> = iter::once(*Q)
            .chain(G.iter().copied())
            .chain(H.iter().copied())
            .chain(self.L_vec.iter().copied())
            .chain(self.R_vec.iter().copied())
            .collect();
        let P_scalars: Vec<C::Scalar> = iter::once(self.a * self.b)
            .chain(g_times_a_times_s)
            .chain(h_times_b_div_s)
            .chain(neg_u_sq)
            .chain(neg_u_inv_sq)
            .collect();
        let expect_P = C::pippenger_sum_of_products(P_points.as_slice(), P_scalars.as_slice());

        expect_P.ct_eq(P).ok_or(ProofError::VerificationError)
    }

    /// Returns the size in bytes required to serialize the inner
    /// product proof.
    ///
    /// For vectors of length `n` the proof size is
    /// \\(POINT_BYTES \cdot (2\lg n+2)\\) bytes.
    pub fn serialized_size(&self) -> usize {
        (self.L_vec.len() * 2) * C::POINT_BYTES + 2 * C::SCALAR_BYTES
    }

    /// Serializes the proof into a byte array of \\(2n+2\\) POINT_SIZE-byte elements.
    /// The layout of the inner product proof is:
    /// * \\(n\\) pairs of compressed Projective points \\(L_0, R_0 \dots, L_{n-1}, R_{n-1}\\),
    /// * two scalars \\(a, b\\).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        buf.append(&mut C::serialize_scalar(&self.a));
        buf.append(&mut C::serialize_scalar(&self.b));
        for (l, r) in self.L_vec.iter().zip(self.R_vec.iter()) {
            buf.append(&mut C::serialize_point(&l));
            buf.append(&mut C::serialize_point(&r));
        }
        buf
    }

    /// Deserializes the proof from a byte slice.
    /// Returns an error in the following cases:
    /// * the slice does not have \\(2n+2\\) 32-byte elements,
    /// * \\(n\\) is larger or equal to 32 (proof is too big),
    /// * any of \\(2n\\) points are not valid compressed G1Projective points,
    /// * any of 2 scalars are not canonical scalars modulo G1Projective group order.
    pub fn from_bytes(slice: &[u8]) -> Result<Self, ProofError> {
        let b = slice.len() - C::SCALAR_BYTES * 2;
        if b % C::POINT_BYTES != 0 {
            return Err(ProofError::FormatError);
        }
        let num_elements = b / C::POINT_BYTES + 2;
        if num_elements < 2 {
            return Err(ProofError::FormatError);
        }
        if (num_elements - 2) % 2 != 0 {
            return Err(ProofError::FormatError);
        }
        let lg_n = (num_elements - 2) / 2;
        if lg_n >= C::POINT_BYTES {
            return Err(ProofError::FormatError);
        }

        let a = C::deserialize_scalar(&slice[..C::SCALAR_BYTES])
            .map_err(|_| ProofError::FormatError)?;
        let b = C::deserialize_scalar(&slice[C::SCALAR_BYTES..C::SCALAR_BYTES * 2])
            .map_err(|_| ProofError::FormatError)?;

        let mut L_vec: Vec<C::Point> = Vec::with_capacity(lg_n);
        let mut R_vec: Vec<C::Point> = Vec::with_capacity(lg_n);
        for i in 0..lg_n {
            let pos = C::SCALAR_BYTES * 2 + i * (C::POINT_BYTES * 2);
            let l = C::deserialize_point(&slice[pos..pos + C::POINT_BYTES])
                .map_err(|_| ProofError::FormatError)?;
            let r = C::deserialize_point(&slice[pos + C::POINT_BYTES..pos + C::POINT_BYTES * 2])
                .map_err(|_| ProofError::FormatError)?;
            L_vec.push(l);
            R_vec.push(r);
        }

        Ok(InnerProductProof { L_vec, R_vec, a, b })
    }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product<C: BulletproofCurveArithmetic>(a: &[C::Scalar], b: &[C::Scalar]) -> C::Scalar {
    let mut out = C::Scalar::ZERO;
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::util;
    use group::ff::Field;

    fn test_helper_create<C: BulletproofCurveArithmetic>(n: usize) {
        let mut rng = rand::thread_rng();

        use crate::generators::BulletproofGens;
        let bp_gens = BulletproofGens::<C>::new(n, 1);
        let G: Vec<C::Point> = bp_gens.share(0).G(n).cloned().collect();
        let H: Vec<C::Point> = bp_gens.share(0).H(n).cloned().collect();

        // Q would be determined upstream in the protocol, so we pick a random one.
        let Q = C::Point::hash_to_point(b"test point");

        // a and b are the vectors for which we want to prove c = <a,b>
        let a: Vec<_> = (0..n).map(|_| C::Scalar::random(&mut rng)).collect();
        let b: Vec<_> = (0..n).map(|_| C::Scalar::random(&mut rng)).collect();
        let c = inner_product::<C>(&a, &b);

        let G_factors: Vec<C::Scalar> = iter::repeat(C::Scalar::ONE).take(n).collect();

        // y_inv is (the inverse of) a random challenge
        let y_inv = C::Scalar::random(&mut rng);
        let H_factors: Vec<C::Scalar> = util::exp_iter::<C>(y_inv).take(n).collect();

        // P would be determined upstream, but we need a correct P to check the proof.
        //
        // To generate P = <a,G> + <b,H'> + <a,b> Q, compute
        //             P = <a,G> + <b',H> + <a,b> Q,
        // where b' = b \circ y^(-n)
        let b_prime = b
            .iter()
            .zip(util::exp_iter::<C>(y_inv))
            .map(|(bi, yi)| *bi * yi);
        // a.iter() has Item=&Scalar, need Item=Scalar to chain with b_prime
        let a_prime = a.iter().cloned();

        let P_points: Vec<C::Point> = G
            .iter()
            .map(|&p| p)
            .chain(H.iter().map(|&p| p))
            .chain(iter::once(Q))
            .collect();
        let P_scalars: Vec<C::Scalar> = a_prime.chain(b_prime).chain(iter::once(c)).collect();
        let P = C::pippenger_sum_of_products(&P_points, &P_scalars);

        let mut verifier = Transcript::new(b"innerproducttest");
        let proof = InnerProductProof::<C>::create(
            &mut verifier,
            &Q,
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a.clone(),
            b.clone(),
        );

        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
            .verify::<iter::Take<iter::Repeat<C::Scalar>>, iter::Take<util::ScalarExp<C>>>(
                n,
                &mut verifier,
                iter::repeat(C::Scalar::ONE).take(n),
                util::exp_iter(y_inv).take(n),
                &P,
                &Q,
                &G,
                &H
            )
            .is_ok());

        let proof = InnerProductProof::<C>::from_bytes(proof.to_bytes().as_slice()).unwrap();
        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
            .verify::<iter::Take<iter::Repeat<C::Scalar>>, iter::Take<util::ScalarExp<C>>>(
                n,
                &mut verifier,
                iter::repeat(C::Scalar::ONE).take(n),
                util::exp_iter(y_inv).take(n),
                &P,
                &Q,
                &G,
                &H
            )
            .is_ok());
    }

    #[test]
    fn make_ipp_1() {
        #[cfg(feature = "curve25519")]
        test_helper_create::<crate::Curve25519>(1);
        #[cfg(feature = "k256")]
        test_helper_create::<k256::Secp256k1>(1);
        #[cfg(feature = "p256")]
        test_helper_create::<p256::NistP256>(1);
        #[cfg(feature = "bls12_381")]
        test_helper_create::<bls12_381_plus::Bls12381G1>(1);
        #[cfg(feature = "bls12_381_std")]
        test_helper_create::<blstrs_plus::Bls12381G1>(1);
    }

    #[test]
    fn make_ipp_2() {
        #[cfg(feature = "curve25519")]
        test_helper_create::<crate::Curve25519>(2);
        #[cfg(feature = "k256")]
        test_helper_create::<k256::Secp256k1>(2);
        #[cfg(feature = "p256")]
        test_helper_create::<p256::NistP256>(2);
        #[cfg(feature = "bls12_381")]
        test_helper_create::<bls12_381_plus::Bls12381G1>(2);
        #[cfg(feature = "bls12_381_std")]
        test_helper_create::<blstrs_plus::Bls12381G1>(2);
    }

    #[test]
    fn make_ipp_4() {
        #[cfg(feature = "curve25519")]
        test_helper_create::<crate::Curve25519>(4);
        #[cfg(feature = "k256")]
        test_helper_create::<k256::Secp256k1>(4);
        #[cfg(feature = "p256")]
        test_helper_create::<p256::NistP256>(4);
        #[cfg(feature = "bls12_381")]
        test_helper_create::<bls12_381_plus::Bls12381G1>(4);
        #[cfg(feature = "bls12_381_std")]
        test_helper_create::<blstrs_plus::Bls12381G1>(4);
    }

    #[test]
    fn make_ipp_32() {
        #[cfg(feature = "curve25519")]
        test_helper_create::<crate::Curve25519>(32);
        #[cfg(feature = "k256")]
        test_helper_create::<k256::Secp256k1>(32);
        #[cfg(feature = "p256")]
        test_helper_create::<p256::NistP256>(32);
        #[cfg(feature = "bls12_381")]
        test_helper_create::<bls12_381_plus::Bls12381G1>(32);
        #[cfg(feature = "bls12_381_std")]
        test_helper_create::<blstrs_plus::Bls12381G1>(32);
    }

    #[test]
    fn make_ipp_64() {
        #[cfg(feature = "curve25519")]
        test_helper_create::<crate::Curve25519>(64);
        #[cfg(feature = "k256")]
        test_helper_create::<k256::Secp256k1>(64);
        #[cfg(feature = "p256")]
        test_helper_create::<p256::NistP256>(64);
        #[cfg(feature = "bls12_381")]
        test_helper_create::<bls12_381_plus::Bls12381G1>(64);
        #[cfg(feature = "bls12_381_std")]
        test_helper_create::<blstrs_plus::Bls12381G1>(64);
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn test_inner_product_curve25519() {
        test_inner_product::<crate::Curve25519>();
    }

    #[cfg(feature = "k256")]
    #[test]
    fn test_inner_product_k256() {
        test_inner_product::<k256::Secp256k1>();
    }

    #[cfg(feature = "p256")]
    #[test]
    fn test_inner_product_p256() {
        test_inner_product::<p256::NistP256>();
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn test_inner_product_bls12_381() {
        test_inner_product::<bls12_381_plus::Bls12381G1>();
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn test_inner_product_bls12_381_std() {
        test_inner_product::<blstrs_plus::Bls12381G1>();
    }

    fn test_inner_product<C: BulletproofCurveArithmetic>() {
        let a = vec![
            C::Scalar::from(1u64),
            C::Scalar::from(2u64),
            C::Scalar::from(3u64),
            C::Scalar::from(4u64),
        ];
        let b = vec![
            C::Scalar::from(2u64),
            C::Scalar::from(3u64),
            C::Scalar::from(4u64),
            C::Scalar::from(5u64),
        ];
        assert_eq!(C::Scalar::from(40u64), inner_product::<C>(&a, &b));
    }
}
