//! Defines a `TranscriptProtocol` trait for using a Merlin transcript.

use crate::types::{BulletproofCurveArithmetic, FromWideBytes};
use group::ff::PrimeField;
use group::Group;
use merlin::Transcript;

use crate::errors::ProofError;

pub trait TranscriptProtocol {
    /// Append a domain separator for an `n`-bit, `m`-party range proof.
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64);

    /// Append a domain separator for a length-`n` inner product proof.
    fn innerproduct_domain_sep(&mut self, n: u64);

    /// Append a domain separator for a constraint system.
    fn r1cs_domain_sep(&mut self);

    /// Commit a domain separator for a CS without randomized constraints.
    fn r1cs_1phase_domain_sep(&mut self);

    /// Commit a domain separator for a CS with randomized constraints.
    fn r1cs_2phase_domain_sep(&mut self);

    /// Append a `scalar` with the given `label`.
    fn append_scalar<C: BulletproofCurveArithmetic>(
        &mut self,
        label: &'static [u8],
        scalar: &C::Scalar,
    );

    /// Append a `point` with the given `label`.
    fn append_point<C: BulletproofCurveArithmetic>(
        &mut self,
        label: &'static [u8],
        point: &C::Point,
    );

    /// Check that a point is not the identity, then append it to the
    /// transcript.  Otherwise, return an error.
    fn validate_and_append_point<C: BulletproofCurveArithmetic>(
        &mut self,
        label: &'static [u8],
        point: &C::Point,
    ) -> Result<(), ProofError>;

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar<C: BulletproofCurveArithmetic>(
        &mut self,
        label: &'static [u8],
    ) -> C::Scalar;
}

impl TranscriptProtocol for Transcript {
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64) {
        self.append_message(b"dom-sep", b"rangeproof v1");
        self.append_u64(b"n", n);
        self.append_u64(b"m", m);
    }

    fn innerproduct_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", b"ipp v1");
        self.append_u64(b"n", n);
    }

    fn r1cs_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs v1");
    }

    fn r1cs_1phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs-1phase");
    }

    fn r1cs_2phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs-2phase");
    }

    fn append_scalar<C: BulletproofCurveArithmetic>(
        &mut self,
        label: &'static [u8],
        scalar: &C::Scalar,
    ) {
        self.append_message(label, &C::serialize_scalar(scalar));
    }

    fn append_point<C: BulletproofCurveArithmetic>(
        &mut self,
        label: &'static [u8],
        point: &C::Point,
    ) {
        self.append_message(label, &C::serialize_point(point));
    }

    fn validate_and_append_point<C: BulletproofCurveArithmetic>(
        &mut self,
        label: &'static [u8],
        point: &C::Point,
    ) -> Result<(), ProofError> {
        if point.is_identity().unwrap_u8() == 1u8 {
            Err(ProofError::VerificationError)
        } else {
            self.append_message(label, &C::serialize_point(point));
            Ok(())
        }
    }

    fn challenge_scalar<C: BulletproofCurveArithmetic>(
        &mut self,
        label: &'static [u8],
    ) -> C::Scalar {
        let repr = <C::Scalar as PrimeField>::Repr::default();
        let mut buf = vec![0u8; repr.as_ref().len() * 2];
        self.challenge_bytes(label, &mut buf);

        C::Scalar::from_wide_bytes(&buf)
    }
}
