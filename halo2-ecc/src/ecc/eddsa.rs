use crate::bigint::{big_less_than, CRTInteger};
use crate::fields::{fp::FpChip, FieldChip, PrimeField};
use halo2_base::{
    gates::{GateInstructions, RangeInstructions},
    utils::CurveAffineExt,
    AssignedValue, Context,
};

use super::edwards::{is_equal, scalar_multiply, EcPoint};
use super::fixed_base;

// CF is the coordinate field of GA
// SF is the scalar field of GA
// p = coordinate field modulus
// n = scalar field modulus
pub fn eddsa_verify<F: PrimeField, CF: PrimeField, SF: PrimeField, GA>(
    base_chip: &FpChip<F, CF>,
    ctx: &mut Context<F>,
    pubkey: &EcPoint<F, <FpChip<F, CF> as FieldChip<F>>::FieldPoint>,
    R: &EcPoint<F, <FpChip<F, CF> as FieldChip<F>>::FieldPoint>,
    s: &CRTInteger<F>,
    msghash: &CRTInteger<F>,
    var_window_bits: usize,
    fixed_window_bits: usize,
) -> AssignedValue<F>
where
    GA: CurveAffineExt<Base = CF, ScalarExt = SF>,
{
    // Check s < L
    let s_less_than_l = scalar_chip.enforce_less_than_p(ctx, s);

    let A = pubkey;
    // Compute h = H(R || A || M)
    let k = msghash;

    // Compute sB
    let sB = fixed_base::scalar_multiply::<F, _, _>(
        base_chip,
        ctx,
        &GA::generator(),
        s.limbs.clone(),
        base_chip.limb_bits,
        fixed_window_bits,
    );
    // Compute kA
    let kA =
        scalar_multiply::<F, _>(base_chip, ctx, pubkey, &k, base_chip.limb_bits, var_window_bits);

    // Compute R' = sB - kA
    let R_prime = ec_sub(base_chip, ctx, &sB, &kA, false);

    let sub = ec_sub(base_chip, ctx, &R, &R_prime, false);
    let sub_mul_cofactor =
        multiply_by_cofactor::<F, _>(base_chip, ctx, &sub, base_chip.limb_bits, var_window_bits);

    // Check if 8(R - R') = O
    // where O is the identity point (0, 1)
    let identity_check = is_equal(base_chip, ctx, &sub_mul_cofactor, &GA::identity(), false);

    let result = base_chip.gate().and(ctx, s_less_than_l, equal_check);
    result
}

// TODO: Decode R, s inside circuit
//       Don't prehash
