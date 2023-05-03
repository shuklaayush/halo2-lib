#![allow(non_snake_case)]
use crate::ed25519::{FpChip, FqChip};
use crate::fields::FpStrategy;
use crate::halo2_proofs::{
    arithmetic::CurveAffine,
    dev::MockProver,
    halo2curves::bn256::{Bn256, Fr as Fs, G1Affine},
    halo2curves::ed25519::{Ed25519Affine, Fq, Fr},
    plonk::*,
    poly::commitment::ParamsProver,
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use crate::halo2_proofs::{
    poly::kzg::{
        commitment::KZGCommitmentScheme,
        multiopen::{ProverSHPLONK, VerifierSHPLONK},
        strategy::SingleStrategy,
    },
    transcript::{TranscriptReadBuffer, TranscriptWriterBuffer},
};
use crate::{
    ecc::{
        eddsa::eddsa_verify,
        edwards::{EccChip, Ed25519Point},
    },
    fields::{FieldChip, PrimeField},
};
use ark_std::{end_timer, start_timer};
use halo2_base::gates::builder::{
    CircuitBuilderStage, GateThreadBuilder, MultiPhaseThreadBreakPoints, RangeCircuitBuilder,
};
use halo2_base::gates::RangeChip;
use halo2_base::utils::fs::gen_srs;
use halo2_base::utils::{biguint_to_fe, fe_to_biguint, modulus};
use halo2_base::Context;
use rand::RngCore;
use rand_core::OsRng;
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::io::BufReader;
use std::io::Write;
use std::{fs, io::BufRead};

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
struct CircuitParams {
    strategy: FpStrategy,
    degree: u32,
    num_advice: usize,
    num_lookup_advice: usize,
    num_fixed: usize,
    lookup_bits: usize,
    limb_bits: usize,
    num_limbs: usize,
}

fn eddsa_test<F: PrimeField>(
    ctx: &mut Context<F>,
    params: CircuitParams,
    R: Ed25519Affine,
    s: Fr,
    msghash: Fr,
    pk: Ed25519Affine,
) {
    std::env::set_var("LOOKUP_BITS", params.lookup_bits.to_string());
    let range = RangeChip::<F>::default(params.lookup_bits);
    let fp_chip = FpChip::<F>::new(&range, params.limb_bits, params.num_limbs);
    let fq_chip = FqChip::<F>::new(&range, params.limb_bits, params.num_limbs);

    let [m, s] = [msghash, s].map(|x| fq_chip.load_private(ctx, FqChip::<F>::fe_to_witness(&x)));
    let [Rx, Ry] = [R.x, R.y].map(|x| fq_chip.load_private(ctx, FpChip::<F>::fe_to_witness(&x)));
    let R = Ed25519Point::construct(Rx, Ry);

    let ecc_chip = EccChip::<F, FpChip<F>>::new(&fp_chip);
    let pk = ecc_chip.load_private(ctx, (pk.x, pk.y));
    // test EdDSA
    let res = eddsa_verify::<F, Fq, Fr, Ed25519Affine>(&fp_chip, ctx, &pk, &R, &s, &m, 4, 4);
    assert_eq!(res.value(), &F::one());
}

fn random_eddsa_circuit(
    params: CircuitParams,
    stage: CircuitBuilderStage,
    break_points: Option<MultiPhaseThreadBreakPoints>,
) -> RangeCircuitBuilder<Fs> {
    // TODO: generate eddsa sig and verify in circuit
    use sha2::{Digest, Sha512};

    fn hash_to_fr(hash: Sha512) -> Fr {
        let mut output = [0u8; 64];
        output.copy_from_slice(hash.finalize().as_slice());

        Fr::from_bytes_wide(&output)
    }

    fn seed_to_key(seed: [u8; 32]) -> (Fr, [u8; 32], [u8; 32]) {
        // Expand the seed to a 64-byte array with SHA512.
        let h = Sha512::digest(&seed[..]);

        // Convert the low half to a scalar with Ed25519 "clamping"
        let s = {
            let mut scalar_bytes = [0u8; 32];
            scalar_bytes[..].copy_from_slice(&h.as_slice()[0..32]);
            // Clear the lowest three bits to make the scalar a multiple of 8
            scalar_bytes[0] &= 248;
            // Clear highest bit
            scalar_bytes[31] &= 127;
            // Set second highest bit to 1
            scalar_bytes[31] |= 64;

            let mut scalar_bytes_wide = [0u8; 64];
            scalar_bytes_wide[0..32].copy_from_slice(&scalar_bytes);

            Fr::from_bytes_wide(&scalar_bytes_wide)
        };

        // Extract and cache the high half.
        let prefix = {
            let mut prefix = [0u8; 32];
            prefix[..].copy_from_slice(&h.as_slice()[32..64]);
            prefix
        };

        // Compute the public key as A = [s]B.
        let A = Ed25519Affine::from(Ed25519Affine::generator() * &s);

        let A_bytes = A.to_bytes();

        (s, prefix, A_bytes)
    }

    fn sign(s: Fr, prefix: [u8; 32], A_bytes: [u8; 32], msg: &[u8]) -> ([u8; 32], [u8; 32]) {
        let r = hash_to_fr(Sha512::default().chain(&prefix[..]).chain(msg));

        let R_bytes = Ed25519Affine::from(Ed25519Affine::generator() * &r).to_bytes();

        let k = hash_to_fr(Sha512::default().chain(&R_bytes[..]).chain(&A_bytes[..]).chain(msg));

        let s_bytes = (r + s * k).to_bytes();

        (R_bytes, s_bytes)
    }

    let mut rng = OsRng;

    let mut builder = match stage {
        CircuitBuilderStage::Mock => GateThreadBuilder::mock(),
        CircuitBuilderStage::Prover => GateThreadBuilder::prover(),
        CircuitBuilderStage::Keygen => GateThreadBuilder::keygen(),
    };

    // Generate a key pair
    let mut seed = [0u8; 32];
    rng.fill_bytes(&mut seed[..]);

    let (s, prefix, A_bytes) = seed_to_key(seed);

    // Generate a valid signature
    let msg = b"test message";
    let (R_bytes, s_bytes) = sign(s, prefix, A_bytes, msg);

    // TODO: Rename
    let msg_hash = hash_to_fr(Sha512::default().chain(&R_bytes[..]).chain(&A_bytes[..]).chain(msg));

    let R = Ed25519Affine::from_bytes(R_bytes).unwrap();
    let s = Fr::from_bytes(&s_bytes).unwrap();
    let A = Ed25519Affine::from_bytes(A_bytes).unwrap();

    let start0 = start_timer!(|| format!("Witness generation for circuit in {stage:?} stage"));
    eddsa_test(builder.main(0), params, R, s, msg_hash, A);

    let circuit = match stage {
        CircuitBuilderStage::Mock => {
            builder.config(params.degree as usize, Some(20));
            RangeCircuitBuilder::mock(builder)
        }
        CircuitBuilderStage::Keygen => {
            builder.config(params.degree as usize, Some(20));
            RangeCircuitBuilder::keygen(builder)
        }
        CircuitBuilderStage::Prover => RangeCircuitBuilder::prover(builder, break_points.unwrap()),
    };
    end_timer!(start0);
    circuit
}

#[test]
fn test_ed25519_eddsa() {
    let path = "configs/ed25519/eddsa_circuit.config";
    let params: CircuitParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();

    let circuit = random_eddsa_circuit(params, CircuitBuilderStage::Mock, None);
    MockProver::run(params.degree, &circuit, vec![]).unwrap().assert_satisfied();
}
