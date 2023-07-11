#![deny(missing_docs)]
#![allow(non_snake_case)]

extern crate alloc;

use crate::BulletproofCurveArithmetic;
use alloc::vec;
use alloc::vec::Vec;
use group::ff::Field;
use zeroize::Zeroize;

use crate::inner_product_proof::inner_product;

/// Represents a degree-1 vector polynomial \\(\mathbf{a} + \mathbf{b} \cdot x\\).
pub struct VecPoly1<C: BulletproofCurveArithmetic>(pub Vec<C::Scalar>, pub Vec<C::Scalar>);

/// Represents a degree-3 vector polynomial
/// \\(\mathbf{a} + \mathbf{b} \cdot x + \mathbf{c} \cdot x^2 + \mathbf{d} \cdot x^3 \\).
#[cfg(feature = "yoloproofs")]
pub struct VecPoly3<C: BulletproofCurveArithmetic>(
    pub Vec<C::Scalar>,
    pub Vec<C::Scalar>,
    pub Vec<C::Scalar>,
    pub Vec<C::Scalar>,
);

/// Represents a degree-2 scalar polynomial \\(a + b \cdot x + c \cdot x^2\\)
pub struct Poly2<C: BulletproofCurveArithmetic>(pub C::Scalar, pub C::Scalar, pub C::Scalar);

/// Represents a degree-6 scalar polynomial, without the zeroth degree
/// \\(a \cdot x + b \cdot x^2 + c \cdot x^3 + d \cdot x^4 + e \cdot x^5 + f \cdot x^6\\)
#[cfg(feature = "yoloproofs")]
pub struct Poly6<C: BulletproofCurveArithmetic> {
    pub t1: C::Scalar,
    pub t2: C::Scalar,
    pub t3: C::Scalar,
    pub t4: C::Scalar,
    pub t5: C::Scalar,
    pub t6: C::Scalar,
}

/// Provides an iterator over the powers of a `Scalar`.
///
/// This struct is created by the `exp_iter` function.
pub struct ScalarExp<C: BulletproofCurveArithmetic> {
    x: C::Scalar,
    next_exp_x: C::Scalar,
}

impl<C: BulletproofCurveArithmetic> Iterator for ScalarExp<C> {
    type Item = C::Scalar;

    fn next(&mut self) -> Option<C::Scalar> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter<C: BulletproofCurveArithmetic>(x: C::Scalar) -> ScalarExp<C> {
    let next_exp_x = C::Scalar::ONE;
    ScalarExp { x, next_exp_x }
}

pub fn add_vec<C: BulletproofCurveArithmetic>(a: &[C::Scalar], b: &[C::Scalar]) -> Vec<C::Scalar> {
    if a.len() != b.len() {
        // throw some error
        //println!("lengths of vectors don't match for vector addition");
    }
    let mut out = vec![C::Scalar::ZERO; b.len()];
    for i in 0..a.len() {
        out[i] = a[i] + b[i];
    }
    out
}

impl<C: BulletproofCurveArithmetic> VecPoly1<C> {
    pub fn zero(n: usize) -> Self {
        VecPoly1(vec![C::Scalar::ZERO; n], vec![C::Scalar::ZERO; n])
    }

    pub fn inner_product(&self, rhs: &VecPoly1<C>) -> Poly2<C> {
        // Uses Karatsuba's method
        let l = self;
        let r = rhs;

        let t0 = inner_product::<C>(&l.0, &r.0);
        let t2 = inner_product::<C>(&l.1, &r.1);

        let l0_plus_l1 = add_vec::<C>(&l.0, &l.1);
        let r0_plus_r1 = add_vec::<C>(&r.0, &r.1);

        let t1 = inner_product::<C>(&l0_plus_l1, &r0_plus_r1) - t0 - t2;

        Poly2(t0, t1, t2)
    }

    pub fn eval(&self, x: C::Scalar) -> Vec<C::Scalar> {
        let n = self.0.len();
        let mut out = vec![C::Scalar::ZERO; n];
        for i in 0..n {
            out[i] = self.0[i] + self.1[i] * x;
        }
        out
    }
}

#[cfg(feature = "yoloproofs")]
impl<C: BulletproofCurveArithmetic> VecPoly3<C>
where
    S: PippengerScalar,
{
    pub fn zero(n: usize) -> Self {
        VecPoly3(
            vec![C::Scalar::ZERO; n],
            vec![C::Scalar::ZERO; n],
            vec![C::Scalar::ZERO; n],
            vec![C::Scalar::ZERO; n],
        )
    }

    /// Compute an inner product of `lhs`, `rhs` which have the property that:
    /// - `lhs.0` is zero;
    /// - `rhs.2` is zero;
    /// This is the case in the constraint system proof.
    pub fn special_inner_product(lhs: &Self, rhs: &Self) -> Poly6<C::Scalar> {
        // TODO: make checks that l_poly.0 and r_poly.2 are zero.

        let t1 = inner_product(&lhs.1, &rhs.0);
        let t2 = inner_product(&lhs.1, &rhs.1) + inner_product(&lhs.2, &rhs.0);
        let t3 = inner_product(&lhs.2, &rhs.1) + inner_product(&lhs.3, &rhs.0);
        let t4 = inner_product(&lhs.1, &rhs.3) + inner_product(&lhs.3, &rhs.1);
        let t5 = inner_product(&lhs.2, &rhs.3);
        let t6 = inner_product(&lhs.3, &rhs.3);

        Poly6 {
            t1,
            t2,
            t3,
            t4,
            t5,
            t6,
        }
    }

    pub fn eval(&self, x: C::Scalar) -> Vec<C::Scalar> {
        let n = self.0.len();
        let mut out = vec![C::Scalar::ZERO; n];
        for i in 0..n {
            out[i] = self.0[i] + x * (self.1[i] + x * (self.2[i] + x * self.3[i]));
        }
        out
    }
}

impl<C: BulletproofCurveArithmetic> Poly2<C> {
    pub fn eval(&self, x: C::Scalar) -> C::Scalar {
        self.0 + x * (self.1 + x * self.2)
    }
}

#[cfg(feature = "yoloproofs")]
impl<C: BulletproofCurveArithmetic> Poly6<C> {
    pub fn eval(&self, x: C::Scalar) -> C::Scalar {
        x * (self.t1 + x * (self.t2 + x * (self.t3 + x * (self.t4 + x * (self.t5 + x * self.t6)))))
    }
}

impl<C: BulletproofCurveArithmetic> Drop for VecPoly1<C> {
    fn drop(&mut self) {
        for e in self.0.iter_mut() {
            e.zeroize();
        }
        for e in self.1.iter_mut() {
            e.zeroize();
        }
    }
}

impl<C: BulletproofCurveArithmetic> Drop for Poly2<C> {
    fn drop(&mut self) {
        self.0.zeroize();
        self.1.zeroize();
        self.2.zeroize();
    }
}

#[cfg(feature = "yoloproofs")]
impl<C: BulletproofCurveArithmetic> Drop for VecPoly3<C> {
    fn drop(&mut self) {
        for e in self.0.iter_mut() {
            e.zeroize();
        }
        for e in self.1.iter_mut() {
            e.zeroize();
        }
        for e in self.2.iter_mut() {
            e.zeroize();
        }
        for e in self.3.iter_mut() {
            e.zeroize();
        }
    }
}

#[cfg(feature = "yoloproofs")]
impl<C: BulletproofCurveArithmetic> Drop for Poly6<C> {
    fn drop(&mut self) {
        self.t1.zeroize();
        self.t2.zeroize();
        self.t3.zeroize();
        self.t4.zeroize();
        self.t5.zeroize();
        self.t6.zeroize();
    }
}

/// Raises `x` to the power `n` using binary exponentiation,
/// with (1 to 2)*lg(n) scalar multiplications.
/// TODO: a consttime version of this would be awfully similar to a Montgomery ladder.
pub fn scalar_exp_vartime<C: BulletproofCurveArithmetic>(x: &C::Scalar, mut n: u64) -> C::Scalar {
    let mut result = C::Scalar::ONE;
    let mut aux = *x; // x, x^2, x^4, x^8, ...
    while n > 0 {
        let bit = n & 1;
        if bit == 1 {
            result *= aux;
        }
        n >>= 1;
        aux = aux * aux; // FIXME: one unnecessary mult at the last step here!
    }
    result
}

/// Takes the sum of all the powers of `x`, up to `n`
/// If `n` is a power of 2, it uses the efficient algorithm with `2*lg n` multiplications and additions.
/// If `n` is not a power of 2, it uses the slow algorithm with `n` multiplications and additions.
/// In the Bulletproofs case, all calls to `sum_of_powers` should have `n` as a power of 2.
pub fn sum_of_powers<C: BulletproofCurveArithmetic>(x: &C::Scalar, n: usize) -> C::Scalar {
    if !n.is_power_of_two() {
        return sum_of_powers_slow::<C>(x, n);
    }
    if n == 0 || n == 1 {
        return C::Scalar::from(n as u64);
    }
    let mut m = n;
    let mut result = C::Scalar::ONE + x;
    let mut factor = *x;
    while m > 2 {
        factor = factor * factor;
        result = result + factor * result;
        m /= 2;
    }
    result
}

// takes the sum of all of the powers of x, up to n
fn sum_of_powers_slow<C: BulletproofCurveArithmetic>(x: &C::Scalar, n: usize) -> C::Scalar {
    exp_iter::<C>(*x).take(n).sum()
}

#[cfg(any(
    feature = "bls12_381",
    feature = "bls12_381_std",
    feature = "curve25519",
    test
))]
/// Given `data` with `len >= 32`, return the first 32 bytes.
pub fn read32(data: &[u8]) -> [u8; 32] {
    let mut buf32 = [0u8; 32];
    buf32[..].copy_from_slice(&data[..32]);
    buf32
}

#[cfg(any(feature = "bls12_381", feature = "bls12_381_std"))]
pub fn read48(data: &[u8]) -> [u8; 48] {
    let mut buf48 = [0u8; 48];
    buf48.copy_from_slice(&data[..48]);
    buf48
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::*;

    #[cfg(feature = "curve25519")]
    #[test]
    fn exp_2_is_powers_of_2_curve25519() {
        exp_2_is_powers_of_2::<crate::Curve25519>()
    }

    #[cfg(feature = "k256")]
    #[test]
    fn exp_2_is_powers_of_2_k256() {
        exp_2_is_powers_of_2::<k256::Secp256k1>()
    }

    #[cfg(feature = "p256")]
    #[test]
    fn exp_2_is_powers_of_2_p256() {
        exp_2_is_powers_of_2::<p256::NistP256>()
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn exp_2_is_powers_of_2_bls12_381() {
        exp_2_is_powers_of_2::<bls12_381_plus::Bls12381G1>()
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn exp_2_is_powers_of_2_blstrs() {
        exp_2_is_powers_of_2::<blstrs_plus::Bls12381G1>()
    }

    fn exp_2_is_powers_of_2<C: BulletproofCurveArithmetic>() {
        let exp_2: Vec<_> = exp_iter::<C>(C::Scalar::from(2u64)).take(4).collect();

        assert_eq!(exp_2[0], C::Scalar::from(1u64));
        assert_eq!(exp_2[1], C::Scalar::from(2u64));
        assert_eq!(exp_2[2], C::Scalar::from(4u64));
        assert_eq!(exp_2[3], C::Scalar::from(8u64));
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn test_inner_product_curve25519() {
        test_inner_product::<crate::Curve25519>()
    }

    #[cfg(feature = "k256")]
    #[test]
    fn test_inner_product_k256() {
        test_inner_product::<k256::Secp256k1>()
    }

    #[cfg(feature = "p256")]
    #[test]
    fn test_inner_product_p256() {
        test_inner_product::<p256::NistP256>()
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn test_inner_product_bls12_381_plus() {
        test_inner_product::<bls12_381_plus::Bls12381G1>()
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn test_inner_product_blstrs() {
        test_inner_product::<blstrs_plus::Bls12381G1>()
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

    /// Raises `x` to the power `n`.
    fn scalar_exp_vartime_slow<C: BulletproofCurveArithmetic>(x: &C::Scalar, n: u64) -> C::Scalar {
        let mut result = C::Scalar::ONE;
        for _ in 0..n {
            result = result * x;
        }
        result
    }

    fn test_sum_of_powers<C: BulletproofCurveArithmetic>() {
        let x = C::Scalar::from(10u64);
        assert_eq!(sum_of_powers_slow::<C>(&x, 0), sum_of_powers::<C>(&x, 0));
        assert_eq!(sum_of_powers_slow::<C>(&x, 1), sum_of_powers::<C>(&x, 1));
        assert_eq!(sum_of_powers_slow::<C>(&x, 2), sum_of_powers::<C>(&x, 2));
        assert_eq!(sum_of_powers_slow::<C>(&x, 4), sum_of_powers::<C>(&x, 4));
        assert_eq!(sum_of_powers_slow::<C>(&x, 8), sum_of_powers::<C>(&x, 8));
        assert_eq!(sum_of_powers_slow::<C>(&x, 16), sum_of_powers::<C>(&x, 16));
        assert_eq!(sum_of_powers_slow::<C>(&x, 32), sum_of_powers::<C>(&x, 32));
        assert_eq!(sum_of_powers_slow::<C>(&x, 64), sum_of_powers::<C>(&x, 64));
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn test_sum_of_powers_slow_curve25519() {
        test_sum_of_powers_slow::<crate::Curve25519>()
    }

    #[cfg(feature = "k256")]
    #[test]
    fn test_sum_of_powers_slow_k256() {
        test_sum_of_powers_slow::<k256::Secp256k1>()
    }

    #[cfg(feature = "p256")]
    #[test]
    fn test_sum_of_powers_slow_p256() {
        test_sum_of_powers_slow::<p256::NistP256>()
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn test_sum_of_powers_slow_bls12_381() {
        test_sum_of_powers_slow::<bls12_381_plus::Bls12381G1>()
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn test_sum_of_powers_slow_bls12_381_std() {
        test_sum_of_powers_slow::<blstrs_plus::Bls12381G1>()
    }

    fn test_sum_of_powers_slow<C: BulletproofCurveArithmetic>() {
        let x = C::Scalar::from(10u64);
        assert_eq!(sum_of_powers_slow::<C>(&x, 0), C::Scalar::ZERO);
        assert_eq!(sum_of_powers_slow::<C>(&x, 1), C::Scalar::ONE);
        assert_eq!(sum_of_powers_slow::<C>(&x, 2), C::Scalar::from(11u64));
        assert_eq!(sum_of_powers_slow::<C>(&x, 3), C::Scalar::from(111u64));
        assert_eq!(sum_of_powers_slow::<C>(&x, 4), C::Scalar::from(1111u64));
        assert_eq!(sum_of_powers_slow::<C>(&x, 5), C::Scalar::from(11111u64));
        assert_eq!(sum_of_powers_slow::<C>(&x, 6), C::Scalar::from(111111u64));
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn vec_of_scalars_clear_on_drop_curve25519() {
        vec_of_scalars_clear_on_drop::<crate::Curve25519>()
    }

    #[cfg(feature = "k256")]
    #[test]
    fn vec_of_scalars_clear_on_drop_k256() {
        vec_of_scalars_clear_on_drop::<k256::Secp256k1>()
    }

    #[cfg(feature = "p256")]
    #[test]
    fn vec_of_scalars_clear_on_drop_p256() {
        vec_of_scalars_clear_on_drop::<p256::NistP256>()
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn vec_of_scalars_clear_on_drop_bls12_381() {
        vec_of_scalars_clear_on_drop::<bls12_381_plus::Bls12381G1>()
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn vec_of_scalars_clear_on_drop_bls12_381_std() {
        vec_of_scalars_clear_on_drop::<blstrs_plus::Bls12381G1>()
    }

    fn vec_of_scalars_clear_on_drop<C: BulletproofCurveArithmetic>() {
        let mut v = vec![C::Scalar::from(24u64), C::Scalar::from(42u64)];

        for e in v.iter_mut() {
            e.zeroize();
        }

        fn flat_slice<T>(x: &[T]) -> &[u8] {
            use core::mem;
            use core::slice;

            unsafe { slice::from_raw_parts(x.as_ptr() as *const u8, mem::size_of_val(x)) }
        }

        assert_eq!(flat_slice(&v.as_slice()), &[0u8; 64][..]);
        assert_eq!(v[0], C::Scalar::ZERO);
        assert_eq!(v[1], C::Scalar::ZERO);
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn tuple_of_scalars_clear_on_drop_curve25519() {
        tuple_of_scalars_clear_on_drop::<crate::Curve25519>()
    }

    #[cfg(feature = "k256")]
    #[test]
    fn tuple_of_scalars_clear_on_drop_k256() {
        tuple_of_scalars_clear_on_drop::<k256::Secp256k1>()
    }

    #[cfg(feature = "p256")]
    #[test]
    fn tuple_of_scalars_clear_on_drop_p256() {
        tuple_of_scalars_clear_on_drop::<p256::NistP256>()
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn tuple_of_scalars_clear_on_drop_bls12_381() {
        tuple_of_scalars_clear_on_drop::<bls12_381_plus::Bls12381G1>()
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn tuple_of_scalars_clear_on_drop_bls12_381_std() {
        tuple_of_scalars_clear_on_drop::<blstrs_plus::Bls12381G1>()
    }

    fn tuple_of_scalars_clear_on_drop<C: BulletproofCurveArithmetic>() {
        let mut v = Poly2::<C>(
            C::Scalar::from(24u64),
            C::Scalar::from(42u64),
            C::Scalar::from(255u64),
        );

        v.0.zeroize();
        v.1.zeroize();
        v.2.zeroize();

        fn as_bytes<T>(x: &T) -> &[u8] {
            use core::mem;
            use core::slice;

            unsafe { slice::from_raw_parts(x as *const T as *const u8, mem::size_of_val(x)) }
        }

        assert_eq!(as_bytes(&v), &[0u8; 96][..]);
        assert_eq!(v.0, C::Scalar::ZERO);
        assert_eq!(v.1, C::Scalar::ZERO);
        assert_eq!(v.2, C::Scalar::ZERO);
    }

    #[cfg(feature = "curve25519")]
    #[test]
    fn batch_invert_curve25519() {
        batch_invert::<crate::Curve25519>()
    }

    #[cfg(feature = "k256")]
    #[test]
    fn batch_invert_k256() {
        batch_invert::<k256::Secp256k1>()
    }

    #[cfg(feature = "p256")]
    #[test]
    fn batch_invert_p256() {
        batch_invert::<p256::NistP256>()
    }

    #[cfg(feature = "bls12_381")]
    #[test]
    fn batch_invert_bls12_381() {
        batch_invert::<bls12_381_plus::Bls12381G1>()
    }

    #[cfg(feature = "bls12_381_std")]
    #[test]
    fn batch_invert_bls12_381_std() {
        batch_invert::<blstrs_plus::Bls12381G1>()
    }

    fn batch_invert<C: BulletproofCurveArithmetic>() {
        let mut scalars = [
            C::Scalar::from(3u64),
            C::Scalar::from(5u64),
            C::Scalar::from(7u64),
            C::Scalar::from(11u64),
        ];

        let allinv = C::Scalar::batch_invert(&mut scalars);

        assert_eq!(allinv, C::Scalar::from(3 * 5 * 7 * 11u64).invert().unwrap());
        assert_eq!(scalars[0], C::Scalar::from(3u64).invert().unwrap());
        assert_eq!(scalars[1], C::Scalar::from(5u64).invert().unwrap());
        assert_eq!(scalars[2], C::Scalar::from(7u64).invert().unwrap());
        assert_eq!(scalars[3], C::Scalar::from(11u64).invert().unwrap());
    }
}
