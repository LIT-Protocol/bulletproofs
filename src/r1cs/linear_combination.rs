//! Definition of linear combinations.

use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::{Add, Mul, Neg, Sub};
use group::ff::Field;
use crate::types::*;

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum Variable<C: BulletproofCurveArithmetic> {
    /// Represents an external input specified by a commitment.
    Committed(usize),
    /// Represents the left input of a multiplication gate.
    MultiplierLeft(usize),
    /// Represents the right input of a multiplication gate.
    MultiplierRight(usize),
    /// Represents the output of a multiplication gate.
    MultiplierOutput(usize),
    /// Represents the constant 1.
    One(),
    /// See <https://github.com/rust-lang/rust/issues/32739>
    _Unreachable(PhantomData<C>),
}

impl<C: BulletproofCurveArithmetic> From<Variable<C>> for LinearCombination<C> {
    fn from(v: Variable<C>) -> LinearCombination<C> {
        LinearCombination {
            terms: vec![(v, C::Scalar::ONE)],
        }
    }
}

impl<C: BulletproofCurveArithmetic, S: Into<C::Scalar>> From<S> for LinearCombination<C> {
    fn from(s: S) -> LinearCombination<C> {
        LinearCombination {
            terms: vec![(Variable::One(), s.into())],
        }
    }
}

// Arithmetic on variables produces linear combinations

impl<C: BulletproofCurveArithmetic> Neg for Variable<C> {
    type Output = LinearCombination<C>;

    fn neg(self) -> Self::Output {
        -LinearCombination::from(self)
    }
}

impl<C: BulletproofCurveArithmetic, L: Into<LinearCombination<C>>> Add<L> for Variable<C> {
    type Output = LinearCombination<C>;

    fn add(self, other: L) -> Self::Output {
        LinearCombination::from(self) + other.into()
    }
}

impl<C: BulletproofCurveArithmetic, L: Into<LinearCombination<C>>> Sub<L> for Variable<C> {
    type Output = LinearCombination<C>;

    fn sub(self, other: L) -> Self::Output {
        LinearCombination::from(self) - other.into()
    }
}

impl<C: BulletproofCurveArithmetic, S: Into<C::Scalar>> Mul<S> for Variable<C> {
    type Output = LinearCombination<C>;

    fn mul(self, other: S) -> Self::Output {
        LinearCombination {
            terms: vec![(self, other.into())],
        }
    }
}

// Arithmetic on scalars with variables produces linear combinations

impl<C: BulletproofCurveArithmetic> Add<Variable<C>> for C::Scalar {
    type Output = LinearCombination<C>;

    fn add(self, other: Variable<C>) -> Self::Output {
        LinearCombination {
            terms: vec![(Variable::One(), self), (other, C::Scalar::ONE)],
        }
    }
}

impl<C: BulletproofCurveArithmetic> Sub<Variable<C>> for C::Scalar {
    type Output = LinearCombination<C>;

    fn sub(self, other: Variable<C>) -> Self::Output {
        LinearCombination {
            terms: vec![(Variable::One(), self), (other, -C::Scalar::ONE)],
        }
    }
}

impl<C: BulletproofCurveArithmetic> Mul<Variable<C>> for C::Scalar {
    type Output = LinearCombination<C>;

    fn mul(self, other: Variable<C>) -> Self::Output {
        LinearCombination {
            terms: vec![(other, self)],
        }
    }
}

/// Represents a linear combination of
/// [`Variables`](::r1cs::Variable).  Each term is represented by a
/// `(Variable, Scalar)` pair.
#[derive(Clone, Debug, PartialEq)]
pub struct LinearCombination<C: BulletproofCurveArithmetic> {
    pub(super) terms: Vec<(Variable<C>, C::Scalar)>,
}

impl<C: BulletproofCurveArithmetic> Default for LinearCombination<C> {
    fn default() -> Self {
        LinearCombination { terms: Vec::new() }
    }
}

impl<C: BulletproofCurveArithmetic> FromIterator<(Variable<C>, C::Scalar)> for LinearCombination<C> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Variable<C>, C::Scalar)>,
    {
        LinearCombination {
            terms: iter.into_iter().collect(),
        }
    }
}

impl<'a, C: BulletproofCurveArithmetic> FromIterator<&'a (Variable<C>, C::Scalar)> for LinearCombination<C> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = &'a (Variable<C>, C::Scalar)>,
    {
        LinearCombination {
            terms: iter.into_iter().cloned().collect(),
        }
    }
}

// Arithmetic on linear combinations

impl<C: BulletproofCurveArithmetic, L: Into<LinearCombination<C>>> Add<L> for LinearCombination<C> {
    type Output = Self;

    fn add(mut self, rhs: L) -> Self::Output {
        self.terms.extend(rhs.into().terms.iter().cloned());
        LinearCombination { terms: self.terms }
    }
}

impl<C: BulletproofCurveArithmetic, L: Into<LinearCombination<C>>> Sub<L> for LinearCombination<C> {
    type Output = Self;

    fn sub(mut self, rhs: L) -> Self::Output {
        self.terms
            .extend(rhs.into().terms.iter().map(|(var, coeff)| (*var, -coeff)));
        LinearCombination { terms: self.terms }
    }
}

impl<C: BulletproofCurveArithmetic> Mul<LinearCombination<C>> for C::Scalar {
    type Output = LinearCombination<C>;

    fn mul(self, other: LinearCombination<C>) -> Self::Output {
        let out_terms = other
            .terms
            .into_iter()
            .map(|(var, scalar)| (var, scalar * self))
            .collect();
        LinearCombination { terms: out_terms }
    }
}

impl<C: BulletproofCurveArithmetic> Neg for LinearCombination<C> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for (_, s) in self.terms.iter_mut() {
            *s = -*s
        }
        self
    }
}

impl<C: BulletproofCurveArithmetic, S: Into<C::Scalar>> Mul<S> for LinearCombination<C> {
    type Output = Self;

    fn mul(mut self, other: S) -> Self::Output {
        let other = other.into();
        for (_, s) in self.terms.iter_mut() {
            *s *= other
        }
        self
    }
}
