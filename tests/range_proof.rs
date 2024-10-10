use rand_core::SeedableRng;

use rand_chacha::ChaChaRng;

use group::ff::Field;

use merlin::Transcript;

use bulletproofs::{BulletproofCurveArithmetic, BulletproofGens, PedersenGens, RangeProof};

use hex;

#[cfg(feature = "curve25519")]
// #[test]
fn generate_test_vectors_curve25519() {
    generate_test_vectors::<bulletproofs::Curve25519>();
}

#[cfg(feature = "k256")]
// #[test]
fn generate_test_vectors_k256() {
    generate_test_vectors::<k256::Secp256k1>();
}

#[cfg(feature = "p256")]
// #[test]
fn generate_test_vectors_p256() {
    generate_test_vectors::<p256::NistP256>();
}

#[cfg(feature = "bls12_381")]
// #[test]
fn generate_test_vectors_bls12_381() {
    generate_test_vectors::<bls12_381_plus::Bls12381G1>();
}

#[cfg(feature = "bls12_381_std")]
// #[test]
fn generate_test_vectors_bls12_381_std() {
    generate_test_vectors::<blstrs_plus::Bls12381G1>();
}

#[cfg(feature = "ed448")]
// #[test]
fn generate_test_vectors_ed448() {
    generate_test_vectors::<ed448_goldilocks_plus::Ed448>()
}

// This function generates test vectors and dumps them to stdout.
// It can be run by uncommenting the #[test] annotation.
// We allow(dead_code) to ensure that it continues to compile.
#[allow(dead_code)]
fn generate_test_vectors<C: BulletproofCurveArithmetic>() {
    let pc_gens = PedersenGens::<C>::default();
    let bp_gens = BulletproofGens::<C>::new(64, 8);

    // Use a deterministic RNG for proving, so the test vectors can be
    // generated reproducibly.
    let mut test_rng = ChaChaRng::from_seed([24u8; 32]);

    let values = vec![0u64, 1, 2, 3, 4, 5, 6, 7];
    let blindings = (0..8)
        .map(|_| C::Scalar::random(&mut test_rng))
        .collect::<Vec<_>>();

    for n in &[8, 16, 32, 64] {
        for m in &[1, 2, 4, 8] {
            let mut transcript = Transcript::new(b"Deserialize-And-Verify Test");
            let (proof, value_commitments) = RangeProof::<C>::prove_multiple(
                &bp_gens,
                &pc_gens,
                &mut transcript,
                &values[0..*m],
                &blindings[0..*m],
                *n,
            )
            .unwrap();

            println!("n,m = {}, {}", n, m);
            println!("proof = \"{}\"", hex::encode(proof.to_bytes()));
            println!("vc = [");
            for com in &value_commitments {
                println!("    \"{}\"", hex::encode(C::serialize_point(&com)));
            }
            println!("]\n");
        }
    }

    panic!();
}
