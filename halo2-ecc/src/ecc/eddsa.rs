use crate::bigint::{big_less_than, CRTInteger};
use crate::fields::{fp::FpChip, FieldChip, PrimeField};
use halo2_base::{
    gates::{GateInstructions, RangeInstructions},
    utils::{biguint_to_fe, power_of_two, CurveAffineExt},
    AssignedValue, Context,
};
use num_bigint::BigUint;

use super::edwards::{ec_sub, fixed_base_scalar_multiply, scalar_multiply, Ed25519Point};

// CF is the coordinate field of GA
// SF is the scalar field of GA
// p = coordinate field modulus
// n = scalar field modulus
pub fn eddsa_verify<F: PrimeField, CF: PrimeField, SF: PrimeField, GA>(
    base_chip: &FpChip<F, CF>,
    ctx: &mut Context<F>,
    pubkey: &Ed25519Point<F, <FpChip<F, CF> as FieldChip<F>>::FieldPoint>, // A
    R: &Ed25519Point<F, <FpChip<F, CF> as FieldChip<F>>::FieldPoint>,
    s: &CRTInteger<F>,
    msghash: &CRTInteger<F>,
    var_window_bits: usize,
    fixed_window_bits: usize,
) -> AssignedValue<F>
where
    GA: CurveAffineExt<Base = CF, ScalarExt = SF>,
{
    let scalar_chip =
        FpChip::<F, SF>::new(base_chip.range, base_chip.limb_bits, base_chip.num_limbs);

    // Check s < L
    scalar_chip.enforce_less_than_p(ctx, s);

    // Compute h = H(R || A || M)
    let k = msghash;

    // Compute sB
    let sB = fixed_base_scalar_multiply::<F, _, _>(
        base_chip,
        ctx,
        &GA::generator(),
        s.truncation.limbs.clone(),
        base_chip.limb_bits,
        fixed_window_bits,
    );
    // Compute kA
    let kA = scalar_multiply::<F, FpChip<F, CF>, GA>(
        base_chip,
        ctx,
        pubkey,
        k.truncation.limbs.clone(),
        base_chip.limb_bits,
        var_window_bits,
    );

    // Compute R' = sB - kA
    let R_prime = ec_sub::<F, FpChip<F, CF>, GA>(base_chip, ctx, &sB, &kA);

    let sub = ec_sub::<F, FpChip<F, CF>, GA>(base_chip, ctx, &R, &R_prime);
    let cofactor = scalar_chip
        .load_constant(ctx, FpChip::<F, CF>::fe_to_constant(biguint_to_fe(&(BigUint::from(8u32)))));

    let sub_mul_cofactor = scalar_multiply::<F, FpChip<F, CF>, GA>(
        base_chip,
        ctx,
        &sub,
        cofactor.truncation.limbs.clone(),
        base_chip.limb_bits,
        var_window_bits,
    );

    // Check if 8(R - R') = O
    base_chip.is_zero(ctx, &sub_mul_cofactor.x)
}

// TODO: Decode R, s inside circuit
//       Don't prehash