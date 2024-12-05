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
        type Point = ProjectivePoint;
        type Scalar = Scalar;

        const POINT_BYTES: usize = 33;
        const SCALAR_BYTES: usize = 32;

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
    use p256::elliptic_curve::sec1::FromEncodedPoint;
    use p256::elliptic_curve::ScalarPrimitive;
    use p256::{
        elliptic_curve::{
            bigint::{NonZero, U512},
            hash2curve::{ExpandMsgXmd, GroupDigest},
            scalar::FromUintUnchecked,
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
            const WIDE_MODULUS: NonZero<U512> = NonZero::from_uint(U512::from_be_hex("0000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"));
            let mut num = U512::from_be_slice(bytes);
            num %= WIDE_MODULUS;

            let (_, lo) = num.split();
            Scalar::from_uint_unchecked(lo)
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
        type Point = ProjectivePoint;
        type Scalar = Scalar;

        const POINT_BYTES: usize = 33;
        const SCALAR_BYTES: usize = 32;

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
        type Point = G1Projective;
        type Scalar = Scalar;

        const POINT_BYTES: usize = 48;
        const SCALAR_BYTES: usize = 32;

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
        type Point = G1Projective;
        type Scalar = Scalar;

        const POINT_BYTES: usize = 48;
        const SCALAR_BYTES: usize = 32;

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

#[cfg(any(feature = "ristretto25519", test))]
pub mod ristretto25519_impls {
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
    pub struct Ristretto25519;

    impl BulletproofCurveArithmetic for Ristretto25519 {
        type Point = WrappedRistretto;
        type Scalar = WrappedScalar;

        const POINT_BYTES: usize = 32;
        const SCALAR_BYTES: usize = 32;

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

#[cfg(any(feature = "ed25519", test))]
pub mod ed25519_impls {
    use super::*;
    use crate::util::read32;
    use curve25519_dalek_ml::EdwardsPoint;
    use vsss_rs::curve25519::WrappedEdwards;
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

    impl HashToPoint for WrappedEdwards {
        type Point = WrappedEdwards;

        fn hash_to_point(m: &[u8]) -> Self::Point {
            const DST: &[u8] = b"edwards25519_XMD:SHA-512_ELL2_RO_";
            let pt = EdwardsPoint::hash_to_curve(m, DST);
            let pt = unsafe { std::mem::transmute(pt) };
            WrappedEdwards(pt)
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
    pub struct Ed25519;

    impl BulletproofCurveArithmetic for Ed25519 {
        type Point = WrappedEdwards;
        type Scalar = WrappedScalar;

        const POINT_BYTES: usize = 32;
        const SCALAR_BYTES: usize = 32;

        fn serialize_point(p: &Self::Point) -> Vec<u8> {
            p.to_bytes().to_vec()
        }

        fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()> {
            Option::<WrappedEdwards>::from(WrappedEdwards::from_bytes(&read32(bytes))).ok_or(())
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
            vsss_rs::curve25519_dalek::EdwardsPoint::multiscalar_mul(scalars.iter(), points.iter())
                .into()
        }
    }
}

#[cfg(feature = "p384")]
mod p384_impls {
    use super::*;

    use elliptic_curve_tools::SumOfProducts;
    use p384::{
        elliptic_curve::{
            bigint::{NonZero, U768},
            hash2curve::{ExpandMsgXmd, GroupDigest},
            scalar::FromUintUnchecked,
            sec1::FromEncodedPoint,
        },
        NistP384, ProjectivePoint, Scalar,
    };

    const DST: &[u8] = b"P384_XMD:SHA-256_SSWU_RO_";

    impl HashToScalar for Scalar {
        type Scalar = Scalar;

        fn hash_to_scalar(m: &[u8]) -> Self::Scalar {
            NistP384::hash_to_scalar::<ExpandMsgXmd<sha2::Sha256>>(&[m], &[DST]).unwrap()
        }
    }

    impl HashToPoint for ProjectivePoint {
        type Point = ProjectivePoint;

        fn hash_to_point(m: &[u8]) -> Self::Point {
            NistP384::hash_from_bytes::<ExpandMsgXmd<sha2::Sha256>>(&[m], &[DST]).unwrap()
        }
    }

    impl FromWideBytes for Scalar {
        fn from_wide_bytes(bytes: &[u8]) -> Self {
            const WIDE_MODULUS: NonZero<U768> = NonZero::from_uint(U768::from_be_hex("000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973"));
            let mut num = U768::from_be_slice(bytes);
            num %= WIDE_MODULUS;

            let (_, lo) = num.split();
            Scalar::from_uint_unchecked(lo)
        }
    }

    impl ScalarBatchInvert for Scalar {}

    impl BulletproofCurveArithmetic for NistP384 {
        type Point = ProjectivePoint;
        type Scalar = Scalar;

        const POINT_BYTES: usize = 49;
        const SCALAR_BYTES: usize = 48;

        fn serialize_point(p: &Self::Point) -> Vec<u8> {
            p.to_affine().to_bytes().to_vec()
        }

        fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()> {
            let encoded_point = p384::EncodedPoint::from_bytes(bytes).map_err(|_| ())?;
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
            let grouped = scalars
                .iter()
                .zip(points.iter())
                .map(|(s, p)| (*s, *p))
                .collect::<Vec<(Scalar, ProjectivePoint)>>();
            ProjectivePoint::sum_of_products(&grouped)
        }
    }
}

#[cfg(feature = "ed448")]
mod ed448_impls {
    use super::*;
    use ed448_goldilocks_plus::{
        elliptic_curve::hash2curve::ExpandMsgXof, Ed448, EdwardsPoint, Scalar, ScalarBytes,
        WideScalarBytes,
    };
    use elliptic_curve_tools::SumOfProducts;

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
        type Point = EdwardsPoint;
        type Scalar = Scalar;

        const POINT_BYTES: usize = 57;
        const SCALAR_BYTES: usize = 57;

        fn serialize_point(p: &Self::Point) -> Vec<u8> {
            p.to_bytes().to_vec()
        }

        fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()> {
            Option::<EdwardsPoint>::from(EdwardsPoint::from_bytes(
                <EdwardsPoint as GroupEncoding>::Repr::from_slice(bytes),
            ))
            .ok_or(())
        }

        fn serialize_scalar(s: &Self::Scalar) -> Vec<u8> {
            s.to_bytes_rfc_8032().to_vec()
        }

        fn deserialize_scalar(bytes: &[u8]) -> Result<Self::Scalar, ()> {
            Option::<Scalar>::from(Scalar::from_canonical_bytes(ScalarBytes::from_slice(bytes)))
                .ok_or(())
        }

        fn pippenger_sum_of_products(
            points: &[Self::Point],
            scalars: &[Self::Scalar],
        ) -> Self::Point {
            let grouped = scalars
                .iter()
                .zip(points.iter())
                .map(|(s, p)| (*s, *p))
                .collect::<Vec<(Scalar, EdwardsPoint)>>();
            EdwardsPoint::sum_of_products(&grouped)
        }
    }
}

#[cfg(feature = "decaf377")]
pub mod decaf377_impls {
    use super::*;
    use blake2::{Blake2b512, Digest};
    use decaf377::{Element as ProjectivePoint, Fq, Fr as Scalar};
    use elliptic_curve::{
        group::GroupEncoding,
        hash2curve::{ExpandMsg, ExpandMsgXmd, Expander},
    };

    impl HashToScalar for Scalar {
        type Scalar = Scalar;

        fn hash_to_scalar(m: &[u8]) -> Self::Scalar {
            let output = Blake2b512::digest(m);
            Scalar::from_le_bytes_mod_order(&output[..])
        }
    }

    impl HashToPoint for ProjectivePoint {
        type Point = ProjectivePoint;

        fn hash_to_point(m: &[u8]) -> Self::Point {
            const DST: &'static [u8] = b"DECAF377_XMD:BLAKE2B-512_ELL_RO_";

            let mut expander = ExpandMsgXmd::<Blake2b512>::expand_message(&[m], &[DST], 96)
                .expect("expander creation to succeed");
            let mut uniform_bytes = [0u8; 48];
            expander.fill_bytes(&mut uniform_bytes);
            let one = Fq::from_le_bytes_mod_order(&uniform_bytes);
            expander.fill_bytes(&mut uniform_bytes);
            let two = Fq::from_le_bytes_mod_order(&uniform_bytes);

            Self::hash_to_curve(&one, &two)
        }
    }

    impl FromWideBytes for Scalar {
        fn from_wide_bytes(bytes: &[u8]) -> Self {
            Scalar::from_le_bytes_mod_order(bytes)
        }
    }

    impl ScalarBatchInvert for Scalar {}

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
    pub struct Decaf377;

    impl BulletproofCurveArithmetic for Decaf377 {
        type Point = ProjectivePoint;
        type Scalar = Scalar;

        const POINT_BYTES: usize = 32;
        const SCALAR_BYTES: usize = 32;

        fn serialize_point(p: &Self::Point) -> Vec<u8> {
            p.to_bytes().to_vec()
        }

        fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()> {
            let mut repr = <ProjectivePoint as GroupEncoding>::Repr::default();
            repr.copy_from_slice(bytes);
            Option::<ProjectivePoint>::from(ProjectivePoint::from_bytes(&repr)).ok_or(())
        }

        fn serialize_scalar(s: &Self::Scalar) -> Vec<u8> {
            s.to_bytes().to_vec()
        }

        fn deserialize_scalar(bytes: &[u8]) -> Result<Self::Scalar, ()> {
            let repr: [u8; 32] = bytes.try_into().map_err(|_| ())?;
            Scalar::from_bytes_checked(&repr).map_err(|_| ())
        }

        fn pippenger_sum_of_products(
            points: &[Self::Point],
            scalars: &[Self::Scalar],
        ) -> Self::Point {
            ProjectivePoint::vartime_multiscalar_mul(scalars, points)
        }
    }
}

#[cfg(feature = "jubjub")]
pub mod jubjub_impls {
    use super::*;
    use elliptic_curve::{group::GroupEncoding, hash2curve::ExpandMsgXmd};
    use elliptic_curve_tools::SumOfProducts;
    use jubjub_plus::{ExtendedPoint, Scalar, SubgroupPoint};

    impl HashToScalar for Scalar {
        type Scalar = Scalar;

        fn hash_to_scalar(m: &[u8]) -> Self::Scalar {
            const DST: &'static [u8] = b"JubJub_XMD:BLAKE2b-512";
            Scalar::hash::<ExpandMsgXmd<blake2::Blake2b512>>(m, &DST)
        }
    }

    impl HashToPoint for SubgroupPoint {
        type Point = SubgroupPoint;

        fn hash_to_point(m: &[u8]) -> Self::Point {
            const DST: &'static [u8] = b"JubJub_XMD:BLAKE2b-512_RO_";
            ExtendedPoint::hash::<ExpandMsgXmd<blake2::Blake2b512>>(m, &DST).into()
        }
    }

    impl FromWideBytes for Scalar {
        fn from_wide_bytes(bytes: &[u8]) -> Self {
            let repr = bytes.try_into().expect("64 bytes");
            Scalar::from_bytes_wide(&repr)
        }
    }

    impl ScalarBatchInvert for Scalar {}

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
    pub struct JubJub;

    impl BulletproofCurveArithmetic for JubJub {
        type Point = SubgroupPoint;
        type Scalar = Scalar;

        const POINT_BYTES: usize = 32;
        const SCALAR_BYTES: usize = 32;

        fn serialize_point(p: &Self::Point) -> Vec<u8> {
            p.to_bytes().to_vec()
        }

        fn deserialize_point(bytes: &[u8]) -> Result<Self::Point, ()> {
            let mut repr = <SubgroupPoint as GroupEncoding>::Repr::default();
            repr.copy_from_slice(bytes);
            Option::<SubgroupPoint>::from(SubgroupPoint::from_bytes(&repr)).ok_or(())
        }

        fn serialize_scalar(s: &Self::Scalar) -> Vec<u8> {
            s.to_bytes().to_vec()
        }

        fn deserialize_scalar(bytes: &[u8]) -> Result<Self::Scalar, ()> {
            let repr: [u8; 32] = bytes.try_into().map_err(|_| ())?;
            Option::<Scalar>::from(Scalar::from_bytes(&repr)).ok_or(())
        }

        fn pippenger_sum_of_products(
            points: &[Self::Point],
            scalars: &[Self::Scalar],
        ) -> Self::Point {
            let grouped = scalars
                .iter()
                .zip(points.iter())
                .map(|(s, p)| (*s, *p))
                .collect::<Vec<(Scalar, SubgroupPoint)>>();
            SubgroupPoint::sum_of_products(&grouped)
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
