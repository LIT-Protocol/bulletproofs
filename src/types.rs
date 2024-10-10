use core::fmt::Debug;
use group::{ff::PrimeField, Group, GroupEncoding};
use subtle::{ConditionallySelectable, ConstantTimeEq};
use zeroize::Zeroize;

/// A trait for types that can be converted to a `Scalar` usable by pippenger's algorithm.
pub trait PippengerScalar: PrimeField + Zeroize {
    /// Convert the scalar to a 4-limb representation in canonical form.
    fn as_pippenger_scalar(&self) -> [u64; 4];
}

/// The hash to curve point methods
pub trait HashToPoint {
    /// The output point type
    type Point: Group + GroupEncoding + Default + ConditionallySelectable;

    /// Compute the output from a hash method
    fn hash_to_point(m: &[u8]) -> Self::Point;
}

/// The hash to scalar methods
pub trait HashToScalar {
    /// The output scalar type
    type Scalar: PrimeField;

    /// Compute the hash of the message `m` with domain separator `dst` and return the result as a scalar.
    fn hash_to_scalar(m: &[u8]) -> Self::Scalar;
}

pub trait ScalarBatchInvert: PrimeField + Zeroize {
    fn batch_invert(scalars: &mut [Self]) -> Self {
        let n = scalars.len();

        let mut acc = Self::ONE;
        let mut scratch = vec![Self::ONE; n];

        for (s, sc) in scalars.iter().zip(scratch.iter_mut()) {
            *sc = acc;
            acc *= s;
        }

        debug_assert!(acc.is_zero().unwrap_u8() == 0);

        acc = acc.invert().unwrap();
        let ret = acc;

        for (s, sc) in scalars.iter_mut().zip(scratch.iter()).rev() {
            let tv = *s * acc;
            *s = *sc * acc;
            acc = tv;
        }

        ret
    }
}

pub trait FromWideBytes: PrimeField {
    fn from_wide_bytes(bytes: &[u8]) -> Self;
}

pub trait BulletproofCurveArithmetic: Copy + Clone + Debug {
    const SCALAR_BYTES: usize;
    const POINT_BYTES: usize;

    type Scalar: HashToScalar<Scalar = Self::Scalar> + ScalarBatchInvert + FromWideBytes;
    type Point: Group<Scalar = Self::Scalar>
        + GroupEncoding
        + Default
        + ConditionallySelectable
        + ConstantTimeEq
        + HashToPoint<Point = Self::Point>;

    fn serialize_point(p: &Self::Point) -> Vec<u8>;
    fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()>;
    fn serialize_scalar(s: &Self::Scalar) -> Vec<u8>;
    fn deserialize_scalar(bytes: &[u8]) -> Result<Self::Scalar, ()>;
    fn pippenger_sum_of_products(points: &[Self::Point], scalars: &[Self::Scalar]) -> Self::Point;
}

#[cfg(feature = "k256")]
mod k256_impls {
    use super::*;
    use k256::elliptic_curve::ScalarPrimitive;
    use k256::{
        elliptic_curve::{
            bigint::U512,
            hash2curve::{ExpandMsgXmd, GroupDigest},
            ops::Reduce,
            sec1::FromEncodedPoint,
        },
        ProjectivePoint, Scalar, Secp256k1,
    };

    const DST: &[u8] = b"secp256k1_XMD:SHA-256_SSWU_RO_";

    impl HashToScalar for Scalar {
        type Scalar = Scalar;

        fn hash_to_scalar(m: &[u8]) -> Self::Scalar {
            Secp256k1::hash_to_scalar::<ExpandMsgXmd<sha2::Sha256>>(&[m], &[DST]).unwrap()
        }
    }

    impl HashToPoint for ProjectivePoint {
        type Point = ProjectivePoint;

        fn hash_to_point(m: &[u8]) -> Self::Point {
            Secp256k1::hash_from_bytes::<ExpandMsgXmd<sha2::Sha256>>(&[m], &[DST]).unwrap()
        }
    }

    impl FromWideBytes for Scalar {
        fn from_wide_bytes(bytes: &[u8]) -> Self {
            let mut repr = k256::WideBytes::clone_from_slice(bytes);
            repr.copy_from_slice(bytes);
            <Scalar as Reduce<U512>>::reduce_bytes(&repr)
        }
    }

    impl PippengerScalar for Scalar {
        fn as_pippenger_scalar(&self) -> [u64; 4] {
            let s: ScalarPrimitive<Secp256k1> = (*self).into();
            let mut out = [0u64; 4];
            out.copy_from_slice(
                s.as_limbs()
                    .iter()
                    .map(|l| l.0 as u64)
                    .collect::<Vec<_>>()
                    .as_slice(),
            );
            out
        }
    }

    impl ScalarBatchInvert for Scalar {}

    impl BulletproofCurveArithmetic for Secp256k1 {
        const SCALAR_BYTES: usize = 32;
        const POINT_BYTES: usize = 33;

        type Scalar = Scalar;
        type Point = ProjectivePoint;

        fn serialize_point(p: &Self::Point) -> Vec<u8> {
            p.to_affine().to_bytes().to_vec()
        }

        fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()> {
            let encoded_point = k256::EncodedPoint::from_bytes(bytes).map_err(|_| ())?;
            Option::<ProjectivePoint>::from(ProjectivePoint::from_encoded_point(&encoded_point))
                .ok_or(())
        }

        fn serialize_scalar(s: &Self::Scalar) -> Vec<u8> {
            s.to_bytes().to_vec()
        }

        fn deserialize_scalar(bytes: &[u8]) -> Result<Self::Scalar, ()> {
            let repr = <Scalar as PrimeField>::Repr::clone_from_slice(bytes);
            Option::<Scalar>::from(Scalar::from_repr(repr)).ok_or(())
        }

        fn pippenger_sum_of_products(
            points: &[Self::Point],
            scalars: &[Self::Scalar],
        ) -> Self::Point {
            sum_of_products_pippenger(points, scalars)
        }
    }
}

#[cfg(feature = "p256")]
mod p256_impls {
    use super::*;
    use p256::elliptic_curve::ops::Reduce;
    use p256::elliptic_curve::sec1::FromEncodedPoint;
    use p256::elliptic_curve::ScalarPrimitive;
    use p256::{
        elliptic_curve::{
            bigint::U256,
            hash2curve::{ExpandMsgXmd, GroupDigest},
        },
        NistP256, ProjectivePoint, Scalar,
    };

    const DST: &[u8] = b"P256_XMD:SHA-256_SSWU_RO_";

    impl HashToScalar for Scalar {
        type Scalar = Scalar;

        fn hash_to_scalar(m: &[u8]) -> Self::Scalar {
            NistP256::hash_to_scalar::<ExpandMsgXmd<sha2::Sha256>>(&[m], &[DST]).unwrap()
        }
    }

    impl HashToPoint for ProjectivePoint {
        type Point = ProjectivePoint;

        fn hash_to_point(m: &[u8]) -> Self::Point {
            NistP256::hash_from_bytes::<ExpandMsgXmd<sha2::Sha256>>(&[m], &[DST]).unwrap()
        }
    }

    impl FromWideBytes for Scalar {
        fn from_wide_bytes(bytes: &[u8]) -> Self {
            let hi = p256::FieldBytes::from_slice(&bytes[..32]);
            let lo = p256::FieldBytes::from_slice(&bytes[32..]);

            let mut s0 = <Scalar as Reduce<U256>>::reduce_bytes(&hi);
            let s1 = <Scalar as Reduce<U256>>::reduce_bytes(&lo);
            for _ in 1..=256 {
                s0 = s0.double();
            }
            s0 + s1
        }
    }

    impl PippengerScalar for Scalar {
        fn as_pippenger_scalar(&self) -> [u64; 4] {
            let s: ScalarPrimitive<NistP256> = (*self).into();
            let mut out = [0u64; 4];
            out.copy_from_slice(
                s.as_limbs()
                    .iter()
                    .map(|l| l.0 as u64)
                    .collect::<Vec<_>>()
                    .as_slice(),
            );
            out
        }
    }

    impl ScalarBatchInvert for Scalar {}

    impl BulletproofCurveArithmetic for NistP256 {
        const SCALAR_BYTES: usize = 32;
        const POINT_BYTES: usize = 33;

        type Scalar = Scalar;
        type Point = ProjectivePoint;

        fn serialize_point(p: &Self::Point) -> Vec<u8> {
            p.to_affine().to_bytes().to_vec()
        }

        fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()> {
            let encoded_point = p256::EncodedPoint::from_bytes(bytes).map_err(|_| ())?;
            Option::<ProjectivePoint>::from(ProjectivePoint::from_encoded_point(&encoded_point))
                .ok_or(())
        }

        fn serialize_scalar(s: &Self::Scalar) -> Vec<u8> {
            s.to_bytes().to_vec()
        }

        fn deserialize_scalar(bytes: &[u8]) -> Result<Self::Scalar, ()> {
            let repr = <Scalar as PrimeField>::Repr::clone_from_slice(bytes);
            Option::<Scalar>::from(Scalar::from_repr(repr)).ok_or(())
        }

        fn pippenger_sum_of_products(
            points: &[Self::Point],
            scalars: &[Self::Scalar],
        ) -> Self::Point {
            sum_of_products_pippenger(points, scalars)
        }
    }
}

#[cfg(feature = "bls12_381")]
mod bls12_381_impls {
    use super::*;
    use crate::util::{read32, read48};
    use bls12_381_plus::elliptic_curve::hash2curve::ExpandMsgXmd;
    use bls12_381_plus::{Bls12381G1, G1Affine, G1Projective, Scalar};

    const DST: &[u8] = b"BLS12381G1_XMD:SHA-256_SSWU_RO_";

    impl HashToScalar for Scalar {
        type Scalar = Self;

        fn hash_to_scalar(m: &[u8]) -> Self::Scalar {
            Scalar::hash::<ExpandMsgXmd<sha2::Sha256>>(m, DST)
        }
    }

    impl HashToPoint for G1Projective {
        type Point = Self;

        fn hash_to_point(m: &[u8]) -> Self::Point {
            G1Projective::hash::<ExpandMsgXmd<sha2::Sha256>>(m, DST)
        }
    }

    impl FromWideBytes for Scalar {
        fn from_wide_bytes(bytes: &[u8]) -> Self {
            Scalar::from_bytes_wide(&<[u8; 64]>::try_from(bytes).unwrap())
        }
    }

    impl PippengerScalar for Scalar {
        fn as_pippenger_scalar(&self) -> [u64; 4] {
            self.to_raw()
        }
    }

    impl ScalarBatchInvert for Scalar {}

    impl BulletproofCurveArithmetic for Bls12381G1 {
        const SCALAR_BYTES: usize = 32;
        const POINT_BYTES: usize = 48;

        type Scalar = Scalar;
        type Point = G1Projective;

        fn serialize_point(p: &Self::Point) -> Vec<u8> {
            p.to_bytes().as_ref().to_vec()
        }

        fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()> {
            Option::<G1Projective>::from(
                G1Affine::from_compressed(&read48(bytes)).map(G1Projective::from),
            )
            .ok_or(())
        }

        fn serialize_scalar(s: &Self::Scalar) -> Vec<u8> {
            s.to_be_bytes().to_vec()
        }

        fn deserialize_scalar(bytes: &[u8]) -> Result<Self::Scalar, ()> {
            Option::<Scalar>::from(Scalar::from_be_bytes(&read32(bytes))).ok_or(())
        }

        fn pippenger_sum_of_products(
            points: &[Self::Point],
            scalars: &[Self::Scalar],
        ) -> Self::Point {
            G1Projective::sum_of_products(&points, &scalars)
        }
    }
}

#[cfg(feature = "bls12_381_std")]
mod bls12_381_std_impls {
    use super::*;
    use crate::util::{read32, read48};
    use blstrs_plus::elliptic_curve::hash2curve::ExpandMsgXmd;
    use blstrs_plus::{Bls12381G1, G1Affine, G1Projective, Scalar};

    const DST: &[u8] = b"BLS12381G1_XMD:SHA-256_SSWU_RO_";

    impl HashToScalar for Scalar {
        type Scalar = Self;

        fn hash_to_scalar(m: &[u8]) -> Self::Scalar {
            Scalar::hash::<ExpandMsgXmd<sha2::Sha256>>(m, DST)
        }
    }

    impl HashToPoint for G1Projective {
        type Point = Self;

        fn hash_to_point(m: &[u8]) -> Self::Point {
            G1Projective::hash::<ExpandMsgXmd<sha2::Sha256>>(m, DST)
        }
    }

    impl FromWideBytes for Scalar {
        fn from_wide_bytes(bytes: &[u8]) -> Self {
            Scalar::from_bytes_wide(&<[u8; 64]>::try_from(bytes).unwrap())
        }
    }

    impl PippengerScalar for Scalar {
        fn as_pippenger_scalar(&self) -> [u64; 4] {
            self.to_raw()
        }
    }

    impl ScalarBatchInvert for Scalar {}

    impl BulletproofCurveArithmetic for Bls12381G1 {
        const SCALAR_BYTES: usize = 32;
        const POINT_BYTES: usize = 48;

        type Scalar = Scalar;
        type Point = G1Projective;

        fn serialize_point(p: &Self::Point) -> Vec<u8> {
            p.to_bytes().as_ref().to_vec()
        }

        fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()> {
            Option::<G1Projective>::from(
                G1Affine::from_compressed(&read48(bytes)).map(G1Projective::from),
            )
            .ok_or(())
        }

        fn serialize_scalar(s: &Self::Scalar) -> Vec<u8> {
            s.to_be_bytes().to_vec()
        }

        fn deserialize_scalar(bytes: &[u8]) -> Result<Self::Scalar, ()> {
            Option::<Scalar>::from(Scalar::from_be_bytes(&read32(bytes))).ok_or(())
        }

        fn pippenger_sum_of_products(
            points: &[Self::Point],
            scalars: &[Self::Scalar],
        ) -> Self::Point {
            G1Projective::sum_of_products(&points, &scalars)
        }
    }
}

#[cfg(any(feature = "curve25519", test))]
pub mod curve25519_impls {
    use super::*;
    use crate::util::read32;
    use vsss_rs::{
        curve25519::{WrappedRistretto, WrappedScalar},
        curve25519_dalek::{traits::MultiscalarMul, RistrettoPoint, Scalar},
    };

    impl HashToScalar for WrappedScalar {
        type Scalar = WrappedScalar;

        fn hash_to_scalar(m: &[u8]) -> Self::Scalar {
            Scalar::hash_from_bytes::<sha2::Sha512>(m).into()
        }
    }

    impl HashToPoint for WrappedRistretto {
        type Point = WrappedRistretto;

        fn hash_to_point(m: &[u8]) -> Self::Point {
            RistrettoPoint::hash_from_bytes::<sha2::Sha512>(m).into()
        }
    }

    impl FromWideBytes for WrappedScalar {
        fn from_wide_bytes(bytes: &[u8]) -> Self {
            Scalar::from_bytes_mod_order_wide(&<[u8; 64]>::try_from(bytes).unwrap()).into()
        }
    }

    impl PippengerScalar for WrappedScalar {
        fn as_pippenger_scalar(&self) -> [u64; 4] {
            todo!()
        }
    }

    impl ScalarBatchInvert for WrappedScalar {}

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
    pub struct Curve25519;

    impl BulletproofCurveArithmetic for Curve25519 {
        const SCALAR_BYTES: usize = 32;
        const POINT_BYTES: usize = 32;

        type Scalar = WrappedScalar;
        type Point = WrappedRistretto;

        fn serialize_point(p: &Self::Point) -> Vec<u8> {
            p.to_bytes().to_vec()
        }

        fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()> {
            Option::<WrappedRistretto>::from(WrappedRistretto::from_bytes(&read32(bytes))).ok_or(())
        }

        fn serialize_scalar(s: &Self::Scalar) -> Vec<u8> {
            s.0.to_bytes().to_vec()
        }

        fn deserialize_scalar(bytes: &[u8]) -> Result<Self::Scalar, ()> {
            Option::<WrappedScalar>::from(WrappedScalar::from_repr(read32(bytes))).ok_or(())
        }

        fn pippenger_sum_of_products(
            points: &[Self::Point],
            scalars: &[Self::Scalar],
        ) -> Self::Point {
            let scalars = scalars.iter().map(|s| s.0).collect::<Vec<_>>();
            let points = points.iter().map(|p| p.0).collect::<Vec<_>>();
            RistrettoPoint::multiscalar_mul(scalars.iter(), points.iter()).into()
        }
    }
}

#[cfg(feature = "ed448")]
pub mod ed448_impls {
    use super::*;
    use ed448_goldilocks_plus::{
        elliptic_curve::hash2curve::ExpandMsgXof,
        Scalar, EdwardsPoint, Ed448, ScalarBytes, WideScalarBytes,
    };

    const SCALAR_DST: &[u8] = b"curve448_XOF:SHAKE256_RO_";
    const EDWARDS_DST: &[u8] = b"edwards448_XOF:SHAKE256_ELL2_RO_";

    impl HashToScalar for Scalar {
       type Scalar = Scalar;

       fn hash_to_scalar(m: &[u8]) -> Self::Scalar {
           Scalar::hash::<ExpandMsgXof<sha3::Shake256>>(m, SCALAR_DST)
       }
   }

    impl HashToPoint for EdwardsPoint {
        type Point = EdwardsPoint;

        fn hash_to_point(m: &[u8]) -> Self::Point {
            EdwardsPoint::hash::<ExpandMsgXof<sha3::Shake256>>(m, EDWARDS_DST)
        }
    }

    impl FromWideBytes for Scalar {
        fn from_wide_bytes(bytes: &[u8]) -> Self {
            Scalar::from_bytes_mod_order_wide(WideScalarBytes::from_slice(bytes))
        }
    }

    impl ScalarBatchInvert for Scalar {}

    impl BulletproofCurveArithmetic for Ed448 {
        const SCALAR_BYTES: usize = 57;
        const POINT_BYTES: usize = 57;
        type Scalar = Scalar;
        type Point = EdwardsPoint;

        fn serialize_point(p: &Self::Point) -> Vec<u8> {
            p.to_bytes().to_vec()
        }

        fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()> {
            Option::<EdwardsPoint>::from(EdwardsPoint::from_bytes(<EdwardsPoint as GroupEncoding>::Repr::from_slice(bytes))).ok_or(())
        }

        fn serialize_scalar(s: &Self::Scalar) -> Vec<u8> {
            s.to_bytes_rfc_8032().to_vec()
        }

        fn deserialize_scalar(bytes: &[u8]) -> Result<Self::Scalar, ()> {
            Option::<Scalar>::from(Scalar::from_canonical_bytes(ScalarBytes::from_slice(bytes))).ok_or(())
        }

        fn pippenger_sum_of_products(points: &[Self::Point], scalars: &[Self::Scalar]) -> Self::Point {
            EdwardsPoint::sum_of_products_pippenger(points, scalars)
        }
    }
}

#[cfg(any(feature = "k256", feature = "p256"))]
fn sum_of_products_pippenger<P, S>(points: &[P], scalars: &[S]) -> P
where
    P: Group<Scalar = S> + GroupEncoding + Default + ConditionallySelectable,
    S: PippengerScalar,
{
    const WINDOW: usize = 4;
    const NUM_BUCKETS: usize = 1 << WINDOW;
    const EDGE: usize = WINDOW - 1;
    const MASK: u64 = (NUM_BUCKETS - 1) as u64;

    let scalars = scalars
        .iter()
        .map(|s| s.as_pippenger_scalar())
        .collect::<Vec<_>>();
    let num_components = core::cmp::min(points.len(), scalars.len());
    let mut buckets = [P::identity(); NUM_BUCKETS];
    let mut res = P::identity();
    let mut num_doubles = 0;
    let mut bit_sequence_index = 255usize;

    loop {
        for _ in 0..num_doubles {
            res = res.double();
        }

        let mut max_bucket = 0;
        let word_index = bit_sequence_index >> 6;
        let bit_index = bit_sequence_index & 63;

        if bit_index < EDGE {
            // we are on the edge of a word; have to look at the previous word, if it exists
            if word_index == 0 {
                // there is no word before
                let smaller_mask = ((1 << (bit_index + 1)) - 1) as u64;
                for i in 0..num_components {
                    let bucket_index: usize = (scalars[i][word_index] & smaller_mask) as usize;
                    if bucket_index > 0 {
                        buckets[bucket_index] += points[i];
                        if bucket_index > max_bucket {
                            max_bucket = bucket_index;
                        }
                    }
                }
            } else {
                // there is a word before
                let high_order_mask = ((1 << (bit_index + 1)) - 1) as u64;
                let high_order_shift = EDGE - bit_index;
                let low_order_mask = ((1 << high_order_shift) - 1) as u64;
                let low_order_shift = 64 - high_order_shift;
                let prev_word_index = word_index - 1;
                for i in 0..num_components {
                    let mut bucket_index =
                        ((scalars[i][word_index] & high_order_mask) << high_order_shift) as usize;
                    bucket_index |= ((scalars[i][prev_word_index] >> low_order_shift)
                        & low_order_mask) as usize;
                    if bucket_index > 0 {
                        buckets[bucket_index] += points[i];
                        if bucket_index > max_bucket {
                            max_bucket = bucket_index;
                        }
                    }
                }
            }
        } else {
            let shift = bit_index - EDGE;
            for i in 0..num_components {
                let bucket_index: usize = ((scalars[i][word_index] >> shift) & MASK) as usize;
                if bucket_index > 0 {
                    buckets[bucket_index] += points[i];
                    if bucket_index > max_bucket {
                        max_bucket = bucket_index;
                    }
                }
            }
        }
        res += &buckets[max_bucket];
        for i in (1..max_bucket).rev() {
            buckets[i] += buckets[i + 1];
            res += buckets[i];
            buckets[i + 1] = P::identity();
        }
        buckets[1] = P::identity();
        if bit_sequence_index < WINDOW {
            break;
        }
        bit_sequence_index -= WINDOW;
        num_doubles = {
            if bit_sequence_index < EDGE {
                bit_sequence_index + 1
            } else {
                WINDOW
            }
        };
    }
    res
}
