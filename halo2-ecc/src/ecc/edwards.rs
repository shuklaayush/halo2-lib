#![allow(non_snake_case)]
use crate::bigint::CRTInteger;
use crate::fields::{fp::FpChip, FieldChip, PrimeField, PrimeFieldChip, Selectable};
use crate::halo2_proofs::arithmetic::CurveAffine;

use group::{Curve, Group};
use halo2_base::gates::builder::GateThreadBuilder;

use crate::bigint::FixedCRTInteger;
use halo2_base::{
    gates::{GateInstructions, RangeInstructions},
    utils::{fe_to_biguint, modulus, CurveAffineExt},
    AssignedValue, Context,
};
use itertools::Itertools;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::cmp::min;
use std::marker::PhantomData;

// Ed25519Point and EccChip take in a generic `FieldChip` to implement generic elliptic curve operations on arbitrary field extensions (provided chip exists) for twisted Edwards curves
// i.e. a.x^2 + y^2 = 1 + d.x^2.y^2
#[derive(Debug)]
pub struct Ed25519Point<F: PrimeField, FieldPoint> {
    pub x: FieldPoint,
    pub y: FieldPoint,
    _marker: PhantomData<F>,
}

impl<F: PrimeField, FieldPoint: Clone> Clone for Ed25519Point<F, FieldPoint> {
    fn clone(&self) -> Self {
        Self { x: self.x.clone(), y: self.y.clone(), _marker: PhantomData }
    }
}

impl<F: PrimeField, FieldPoint> Ed25519Point<F, FieldPoint> {
    pub fn construct(x: FieldPoint, y: FieldPoint) -> Self {
        Self { x, y, _marker: PhantomData }
    }

    pub fn x(&self) -> &FieldPoint {
        &self.x
    }

    pub fn y(&self) -> &FieldPoint {
        &self.y
    }
}

// Implements:
//  Given P = (x_1, y_1) and Q = (x_2, y_2), ecc points over the twisted Edwards curve (Ed25519) in the field F_p
//  Find ec addition P + Q = (x_3, y_3)
// By solving:
//  x_3 = (x_1 * y_2 + y_1 * x_2) / (1 + d * x_1 * x_2 * y_1 * y_2)
//  y_3 = (y_1 * y_2 + x_1 * x_2) / (1 - d * x_1 * x_2 * y_1 * y_2)
// Where d is a constant specific to the twisted Edwards curve (Ed25519)
pub fn ec_add<F, FC, C>(
    chip: &FC,
    ctx: &mut Context<F>,
    P: &Ed25519Point<F, FC::FieldPoint>,
    Q: &Ed25519Point<F, FC::FieldPoint>,
) -> Ed25519Point<F, FC::FieldPoint>
where
    F: PrimeField,
    FC: FieldChip<F>,
    C: CurveAffine<Base = FC::FieldType>,
{
    let d = chip.load_constant(ctx, FC::fe_to_constant(C::b()));
    let one = chip.load_constant(ctx, FC::fe_to_constant(FC::FieldType::one()));

    // x3 = (x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2)
    let x1_y2 = chip.mul(ctx, &P.x, &Q.y);
    let y1_x2 = chip.mul(ctx, &P.y, &Q.x);
    let x1_x2_y1_y2 = chip.mul(ctx, &x1_y2, &y1_x2);
    let d_x1_x2_y1_y2 = chip.mul(ctx, &d, &x1_x2_y1_y2);

    let denominator_x = chip.add_no_carry(ctx, &one, &d_x1_x2_y1_y2);
    let numerator_x = chip.add_no_carry(ctx, &x1_y2, &y1_x2);

    let x_3 = chip.divide(ctx, &numerator_x, &denominator_x);

    // y3 = (y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)
    let y1_y2 = chip.mul(ctx, &P.y, &Q.y);
    let x1_x2 = chip.mul(ctx, &P.x, &Q.x);

    let numerator_y = chip.add_no_carry(ctx, &y1_y2, &x1_x2);
    let denominator_y = chip.sub_no_carry(ctx, &one, &d_x1_x2_y1_y2);

    let y_3 = chip.divide(ctx, &numerator_y, &denominator_y);

    Ed25519Point::construct(x_3, y_3)
}

pub fn ec_double<F, FC, C>(
    chip: &FC,
    ctx: &mut Context<F>,
    P: &Ed25519Point<F, FC::FieldPoint>,
) -> Ed25519Point<F, FC::FieldPoint>
where
    F: PrimeField,
    FC: FieldChip<F>,
    C: CurveAffine<Base = FC::FieldType>,
{
    let d = chip.load_constant(ctx, FC::fe_to_constant(C::b()));
    let one = chip.load_constant(ctx, FC::fe_to_constant(FC::FieldType::one()));

    // x2 = (2 * x1 * y1) / (1 + d * x1^2 * y1^2)
    let x1_y1 = chip.mul(ctx, &P.x, &P.y);
    let x1_y1_2 = chip.mul(ctx, &x1_y1, &x1_y1);
    let d_x1_y1_2 = chip.mul(ctx, &d, &x1_y1_2);

    let denominator_x = chip.add_no_carry(ctx, &one, &d_x1_y1_2);
    let numerator_x = chip.scalar_mul_no_carry(ctx, &x1_y1, 2);

    let x_3 = chip.divide(ctx, &numerator_x, &denominator_x);

    // y2 = (y1^2 + x1^2) / (1 - d * x1^2 * y1^2)
    let x1_2 = chip.mul(ctx, &P.x, &P.x);
    let y1_2 = chip.mul(ctx, &P.y, &P.y);

    let numerator_y = chip.add_no_carry(ctx, &y1_2, &x1_2);
    let denominator_y = chip.sub_no_carry(ctx, &one, &d_x1_y1_2);

    let y_3 = chip.divide(ctx, &numerator_y, &denominator_y);

    Ed25519Point::construct(x_3, y_3)
}

// Implements:
//  Given P = (x_1, y_1) and Q = (x_2, y_2), ecc points over the twisted Edwards curve (Ed25519) in the field F_p
//  Find ec addition P - Q = (x_3, y_3)
// By solving:
//  x_3 = (x_1 * y_2 - y_1 * x_2) / (1 - d * x_1 * x_2 * y_1 * y_2)
//  y_3 = (y_1 * y_2 - x_1 * x_2) / (1 + d * x_1 * x_2 * y_1 * y_2)
// Where d is a constant specific to the twisted Edwards curve (Ed25519)
pub fn ec_sub<F, FC, C>(
    chip: &FC,
    ctx: &mut Context<F>,
    P: &Ed25519Point<F, FC::FieldPoint>,
    Q: &Ed25519Point<F, FC::FieldPoint>,
) -> Ed25519Point<F, FC::FieldPoint>
where
    F: PrimeField,
    FC: FieldChip<F>,
    C: CurveAffine<Base = FC::FieldType>,
{
    let d = chip.load_constant(ctx, FC::fe_to_constant(C::b()));
    let one = chip.load_constant(ctx, FC::fe_to_constant(FC::FieldType::one()));

    // x3 = (x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2)
    let x1_y2 = chip.mul(ctx, &P.x, &Q.y);
    let y1_x2 = chip.mul(ctx, &P.y, &Q.x);
    let x1_x2_y1_y2 = chip.mul(ctx, &x1_y2, &y1_x2);
    let d_x1_x2_y1_y2 = chip.mul(ctx, &d, &x1_x2_y1_y2);

    let denominator_x = chip.sub_no_carry(ctx, &one, &d_x1_x2_y1_y2);
    let numerator_x = chip.sub_no_carry(ctx, &x1_y2, &y1_x2);

    let x_3 = chip.divide(ctx, &numerator_x, &denominator_x);

    // y3 = (y1 * y2 + x1 * x2) / (1 - d * x1 * x2 * y1 * y2)
    let y1_y2 = chip.mul(ctx, &P.y, &Q.y);
    let x1_x2 = chip.mul(ctx, &P.x, &Q.x);

    let numerator_y = chip.sub_no_carry(ctx, &y1_y2, &x1_x2);
    let denominator_y = chip.add_no_carry(ctx, &one, &d_x1_x2_y1_y2);

    let y_3 = chip.divide(ctx, &numerator_y, &denominator_y);

    Ed25519Point::construct(x_3, y_3)
}

pub fn ec_select<F: PrimeField, FC>(
    chip: &FC,
    ctx: &mut Context<F>,
    P: &Ed25519Point<F, FC::FieldPoint>,
    Q: &Ed25519Point<F, FC::FieldPoint>,
    sel: AssignedValue<F>,
) -> Ed25519Point<F, FC::FieldPoint>
where
    FC: FieldChip<F> + Selectable<F, Point = FC::FieldPoint>,
{
    let Rx = chip.select(ctx, &P.x, &Q.x, sel);
    let Ry = chip.select(ctx, &P.y, &Q.y, sel);
    Ed25519Point::construct(Rx, Ry)
}

// takes the dot product of points with sel, where each is intepreted as
// a _vector_
pub fn ec_select_by_indicator<F: PrimeField, FC>(
    chip: &FC,
    ctx: &mut Context<F>,
    points: &[Ed25519Point<F, FC::FieldPoint>],
    coeffs: &[AssignedValue<F>],
) -> Ed25519Point<F, FC::FieldPoint>
where
    FC: FieldChip<F> + Selectable<F, Point = FC::FieldPoint>,
{
    let x_coords = points.iter().map(|P| P.x.clone()).collect::<Vec<_>>();
    let y_coords = points.iter().map(|P| P.y.clone()).collect::<Vec<_>>();
    let Rx = chip.select_by_indicator(ctx, &x_coords, coeffs);
    let Ry = chip.select_by_indicator(ctx, &y_coords, coeffs);
    Ed25519Point::construct(Rx, Ry)
}

// `sel` is little-endian binary
pub fn ec_select_from_bits<F: PrimeField, FC>(
    chip: &FC,
    ctx: &mut Context<F>,
    points: &[Ed25519Point<F, FC::FieldPoint>],
    sel: &[AssignedValue<F>],
) -> Ed25519Point<F, FC::FieldPoint>
where
    FC: FieldChip<F> + Selectable<F, Point = FC::FieldPoint>,
{
    let w = sel.len();
    let num_points = points.len();
    assert_eq!(1 << w, num_points);
    let coeffs = chip.range().gate().bits_to_indicator(ctx, sel);
    ec_select_by_indicator(chip, ctx, points, &coeffs)
}

// computes [scalar] * P on twisted Edwards curve (Ed25519)
// - `scalar` is represented as a reference array of `AssignedCell`s
// - `scalar = sum_i scalar_i * 2^{max_bits * i}`
// - an array of length > 1 is needed when `scalar` exceeds the modulus of scalar field `F`
// assumes:
// - `scalar_i < 2^{max_bits} for all i` (constrained by num_to_bits)
// - `max_bits <= modulus::<F>.bits()`
//   * P has order given by the scalar field modulus
pub fn scalar_multiply<F: PrimeField, FC, C>(
    chip: &FC,
    ctx: &mut Context<F>,
    P: &Ed25519Point<F, FC::FieldPoint>,
    scalar: Vec<AssignedValue<F>>,
    max_bits: usize,
    window_bits: usize,
) -> Ed25519Point<F, FC::FieldPoint>
where
    FC: FieldChip<F> + Selectable<F, Point = FC::FieldPoint>,
    C: CurveAffine<Base = FC::FieldType>,
{
    assert!(!scalar.is_empty());
    assert!((max_bits as u64) <= modulus::<F>().bits());

    let total_bits = max_bits * scalar.len();
    let num_windows = (total_bits + window_bits - 1) / window_bits;
    let rounded_bitlen = num_windows * window_bits;

    let mut bits = Vec::with_capacity(rounded_bitlen);
    for x in scalar {
        let mut new_bits = chip.gate().num_to_bits(ctx, x, max_bits);
        bits.append(&mut new_bits);
    }
    let mut rounded_bits = bits;
    let zero_cell = ctx.load_zero();
    rounded_bits.resize(rounded_bitlen, zero_cell);

    // is_started[idx] holds whether there is a 1 in bits with index at least (rounded_bitlen - idx)
    let mut is_started = Vec::with_capacity(rounded_bitlen);
    is_started.resize(rounded_bitlen - total_bits + 1, zero_cell);
    for idx in 1..total_bits {
        let or = chip.gate().or(ctx, *is_started.last().unwrap(), rounded_bits[total_bits - idx]);
        is_started.push(or);
    }

    // is_zero_window[idx] is 0/1 depending on whether bits [rounded_bitlen - window_bits * (idx + 1), rounded_bitlen - window_bits * idx) are all 0
    let mut is_zero_window = Vec::with_capacity(num_windows);
    for idx in 0..num_windows {
        let temp_bits = rounded_bits
            [rounded_bitlen - window_bits * (idx + 1)..rounded_bitlen - window_bits * idx]
            .iter()
            .copied();
        let bit_sum = chip.gate().sum(ctx, temp_bits);
        let is_zero = chip.gate().is_zero(ctx, bit_sum);
        is_zero_window.push(is_zero);
    }

    // cached_points[idx] stores idx * P, with cached_points[0] = P
    let cache_size = 1usize << window_bits;
    let mut cached_points = Vec::with_capacity(cache_size);
    cached_points.push(P.clone());
    cached_points.push(P.clone());
    for idx in 2..cache_size {
        if idx == 2 {
            let double = ec_double::<F, FC, C>(chip, ctx, P /*, b*/);
            cached_points.push(double);
        } else {
            let new_point = ec_add::<F, FC, C>(chip, ctx, &cached_points[idx - 1], P);
            cached_points.push(new_point);
        }
    }

    // if all the starting window bits are 0, get start_point = P
    let mut curr_point = ec_select_from_bits::<F, FC>(
        chip,
        ctx,
        &cached_points,
        &rounded_bits[rounded_bitlen - window_bits..rounded_bitlen],
    );

    for idx in 1..num_windows {
        let mut mult_point = curr_point.clone();
        for _ in 0..window_bits {
            mult_point = ec_double::<F, FC, C>(chip, ctx, &mult_point);
        }
        let add_point = ec_select_from_bits::<F, FC>(
            chip,
            ctx,
            &cached_points,
            &rounded_bits
                [rounded_bitlen - window_bits * (idx + 1)..rounded_bitlen - window_bits * idx],
        );
        let mult_and_add = ec_add::<F, FC, C>(chip, ctx, &mult_point, &add_point);
        let is_started_point =
            ec_select(chip, ctx, &mult_point, &mult_and_add, is_zero_window[idx]);

        curr_point =
            ec_select(chip, ctx, &is_started_point, &add_point, is_started[window_bits * idx]);
    }
    curr_point
}

// this only works for curves GA with base field of prime order
#[derive(Clone, Debug)]
pub struct FixedEd25519Point<F: PrimeField, C: CurveAffine> {
    pub x: FixedCRTInteger<F>, // limbs in `F` and value in `BigUint`
    pub y: FixedCRTInteger<F>,
    _marker: PhantomData<C>,
}

impl<F: PrimeField, C: CurveAffineExt> FixedEd25519Point<F, C>
where
    C::Base: PrimeField,
{
    pub fn construct(x: FixedCRTInteger<F>, y: FixedCRTInteger<F>) -> Self {
        Self { x, y, _marker: PhantomData }
    }

    pub fn from_curve(point: C, num_limbs: usize, limb_bits: usize) -> Self {
        let (x, y) = point.into_coordinates();
        let x = FixedCRTInteger::from_native(fe_to_biguint(&x), num_limbs, limb_bits);
        let y = FixedCRTInteger::from_native(fe_to_biguint(&y), num_limbs, limb_bits);
        Self::construct(x, y)
    }

    pub fn assign<FC>(self, chip: &FC, ctx: &mut Context<F>) -> Ed25519Point<F, FC::FieldPoint>
    where
        FC: PrimeFieldChip<F, FieldType = C::Base, FieldPoint = CRTInteger<F>>,
    {
        let assigned_x = self.x.assign(ctx, chip.limb_bits(), chip.native_modulus());
        let assigned_y = self.y.assign(ctx, chip.limb_bits(), chip.native_modulus());
        Ed25519Point::construct(assigned_x, assigned_y)
    }
}

// computes `[scalar] * P` on y^2 = x^3 + b where `P` is fixed (constant)
// - `scalar` is represented as a reference array of `AssignedCell`s
// - `scalar = sum_i scalar_i * 2^{max_bits * i}`
// - an array of length > 1 is needed when `scalar` exceeds the modulus of scalar field `F`
// assumes:
// - `scalar_i < 2^{max_bits} for all i` (constrained by num_to_bits)
// - `max_bits <= modulus::<F>.bits()`
pub fn fixed_base_scalar_multiply<F, FC, C>(
    chip: &FC,
    ctx: &mut Context<F>,
    point: &C,
    scalar: Vec<AssignedValue<F>>,
    max_bits: usize,
    window_bits: usize,
) -> Ed25519Point<F, FC::FieldPoint>
where
    F: PrimeField,
    C: CurveAffineExt,
    C::Base: PrimeField,
    FC: PrimeFieldChip<F, FieldType = C::Base, FieldPoint = CRTInteger<F>>
        + Selectable<F, Point = FC::FieldPoint>,
{
    if point.is_identity().into() {
        let point = FixedEd25519Point::from_curve(*point, chip.num_limbs(), chip.limb_bits());
        return FixedEd25519Point::assign(point, chip, ctx);
    }
    debug_assert!(!scalar.is_empty());
    debug_assert!((max_bits as u32) <= F::NUM_BITS);

    let total_bits = max_bits * scalar.len();
    let num_windows = (total_bits + window_bits - 1) / window_bits;

    // Jacobian coordinate
    let base_pt = point.to_curve();
    // cached_points[i * 2^w + j] holds `[j * 2^(i * w)] * point` for j in {0, ..., 2^w - 1}

    // first we compute all cached points in Jacobian coordinates since it's fastest
    let mut increment = base_pt;
    let cached_points_jacobian = (0..num_windows)
        .flat_map(|i| {
            let mut curr = increment;
            // start with increment at index 0 instead of identity just as a dummy value to avoid divide by 0 issues
            let cache_vec = std::iter::once(increment)
                .chain((1..(1usize << min(window_bits, total_bits - i * window_bits))).map(|_| {
                    let prev = curr;
                    curr += increment;
                    prev
                }))
                .collect::<Vec<_>>();
            increment = curr;
            cache_vec
        })
        .collect::<Vec<_>>();
    // for use in circuits we need affine coordinates, so we do a batch normalize: this is much more efficient than calling `to_affine` one by one since field inversion is very expensive
    // initialize to all 0s
    let mut cached_points_affine = vec![C::default(); cached_points_jacobian.len()];
    C::Curve::batch_normalize(&cached_points_jacobian, &mut cached_points_affine);

    // TODO: do not assign and use select_from_bits on Constant(_) QuantumCells
    let cached_points = cached_points_affine
        .into_iter()
        .map(|point| {
            let point = FixedEd25519Point::from_curve(point, chip.num_limbs(), chip.limb_bits());
            FixedEd25519Point::assign(point, chip, ctx)
        })
        .collect_vec();

    let bits = scalar
        .into_iter()
        .flat_map(|scalar_chunk| chip.gate().num_to_bits(ctx, scalar_chunk, max_bits))
        .collect::<Vec<_>>();

    let cached_point_window_rev = cached_points.chunks(1usize << window_bits).rev();
    let bit_window_rev = bits.chunks(window_bits).rev();
    let mut curr_point = None;
    // `is_started` is just a way to deal with if `curr_point` is actually identity
    let mut is_started = ctx.load_zero();
    for (cached_point_window, bit_window) in cached_point_window_rev.zip(bit_window_rev) {
        let bit_sum = chip.gate().sum(ctx, bit_window.iter().copied());
        // are we just adding a window of all 0s? if so, skip
        let is_zero_window = chip.gate().is_zero(ctx, bit_sum);
        let add_point = ec_select_from_bits::<F, _>(chip, ctx, cached_point_window, bit_window);
        curr_point = if let Some(curr_point) = curr_point {
            let sum = ec_add::<F, FC, C>(chip, ctx, &curr_point, &add_point);
            let zero_sum = ec_select(chip, ctx, &curr_point, &sum, is_zero_window);
            Some(ec_select(chip, ctx, &zero_sum, &add_point, is_started))
        } else {
            Some(add_point)
        };
        is_started = {
            // is_started || !is_zero_window
            // (a || !b) = (1-b) + a*b
            let not_zero_window = chip.gate().not(ctx, is_zero_window);
            chip.gate().mul_add(ctx, is_started, is_zero_window, not_zero_window)
        };
    }
    curr_point.unwrap()
}
/*
pub fn is_on_curve<F, FC>(chip: &FC, ctx: &mut Context<F>, P: &Ed25519Point<F, FC::FieldPoint>)
where
    F: PrimeField,
    FC: FieldChip<F>,
{
    let a = F::from_str("486662").unwrap(); // The a constant of the Ed25519 curve
    let d = F::from_str(
        "37095705934669439343138083508754565189542113879843219016388785533085940283555",
    )
    .unwrap(); // The d constant of the Ed25519 curve

    // Calculate ax^2
    let ax_sq = chip.mul_no_carry(ctx, &a, &P.x);
    let x_sq = chip.mul_no_carry(ctx, &ax_sq, &P.x);

    // Calculate y^2
    let y_sq = chip.mul_no_carry(ctx, &P.y, &P.y);

    // Calculate d * x^2 * y^2
    let dx_sq_y_sq = chip.mul_no_carry(ctx, &x_sq, &y_sq);
    let d_dx_sq_y_sq = chip.mul_no_carry(ctx, &d, &dx_sq_y_sq);

    // Calculate lhs = ax^2 + y^2
    let lhs = chip.add_no_carry(ctx, &x_sq, &y_sq);

    // Calculate rhs = 1 + d * x^2 * y^2
    let one_fp = chip.constant(ctx, F::one());
    let rhs = chip.add_no_carry(ctx, &one_fp, &d_dx_sq_y_sq);

    // Check if lhs and rhs are equal
    let diff = chip.sub_no_carry(ctx, &lhs, &rhs);
    chip.check_carry_mod_to_zero(ctx, &diff)
}

pub fn load_random_point<F, FC, C>(
    chip: &FC,
    ctx: &mut Context<F>,
) -> Ed25519Point<F, FC::FieldPoint>
where
    F: PrimeField,
    FC: FieldChip<F>,
    C: CurveAffineExt<Base = FC::FieldType>,
{
    let base_point: C = C::CurveExt::random(ChaCha20Rng::from_entropy()).to_affine();
    let (x, y) = base_point.into_coordinates();
    let pt_x = FC::fe_to_witness(&x);
    let pt_y = FC::fe_to_witness(&y);
    let base = {
        let x_overflow = chip.load_private(ctx, pt_x);
        let y_overflow = chip.load_private(ctx, pt_y);
        Ed25519Point::construct(x_overflow, y_overflow)
    };
    // for above reason we still need to constrain that the witness is on the curve
    is_on_curve::<F, FC, C>(chip, ctx, &base);
    base
}
*/

pub type BaseFieldEccChip<'chip, C> = EccChip<
    'chip,
    <C as CurveAffine>::ScalarExt,
    FpChip<'chip, <C as CurveAffine>::ScalarExt, <C as CurveAffine>::Base>,
>;

#[derive(Clone, Debug)]
pub struct EccChip<'chip, F: PrimeField, FC: FieldChip<F>> {
    pub field_chip: &'chip FC,
    _marker: PhantomData<F>,
}

impl<'chip, F: PrimeField, FC: FieldChip<F>> EccChip<'chip, F, FC> {
    pub fn new(field_chip: &'chip FC) -> Self {
        Self { field_chip, _marker: PhantomData }
    }

    pub fn field_chip(&self) -> &FC {
        self.field_chip
    }

    pub fn load_private(
        &self,
        ctx: &mut Context<F>,
        point: (FC::FieldType, FC::FieldType),
    ) -> Ed25519Point<F, FC::FieldPoint> {
        let (x, y) = (FC::fe_to_witness(&point.0), FC::fe_to_witness(&point.1));

        let x_assigned = self.field_chip.load_private(ctx, x);
        let y_assigned = self.field_chip.load_private(ctx, y);

        Ed25519Point::construct(x_assigned, y_assigned)
    }

    pub fn add<C>(
        &self,
        ctx: &mut Context<F>,
        P: &Ed25519Point<F, FC::FieldPoint>,
        Q: &Ed25519Point<F, FC::FieldPoint>,
    ) -> Ed25519Point<F, FC::FieldPoint>
    where
        C: CurveAffineExt<Base = FC::FieldType>,
    {
        ec_add::<F, FC, C>(self.field_chip, ctx, P, Q)
    }

    pub fn double<C>(
        &self,
        ctx: &mut Context<F>,
        P: &Ed25519Point<F, FC::FieldPoint>,
    ) -> Ed25519Point<F, FC::FieldPoint>
    where
        C: CurveAffineExt<Base = FC::FieldType>,
    {
        ec_double::<F, FC, C>(self.field_chip, ctx, P)
    }

    pub fn is_equal(
        &self,
        ctx: &mut Context<F>,
        P: &Ed25519Point<F, FC::FieldPoint>,
        Q: &Ed25519Point<F, FC::FieldPoint>,
    ) -> AssignedValue<F> {
        // TODO: optimize
        let x_is_equal = self.field_chip.is_equal(ctx, &P.x, &Q.x);
        let y_is_equal = self.field_chip.is_equal(ctx, &P.y, &Q.y);
        self.field_chip.range().gate().and(ctx, x_is_equal, y_is_equal)
    }

    /*
    /// Does not constrain witness to lie on curve
    pub fn assign_point<C>(&self, ctx: &mut Context<F>, g: C) -> Ed25519Point<F, FC::FieldPoint>
    where
        C: CurveAffineExt<Base = FC::FieldType>,
    {
        let (x, y) = g.into_coordinates();
        self.load_private(ctx, (x, y))
    }

    pub fn assign_constant_point<C>(
        &self,
        ctx: &mut Context<F>,
        g: C,
    ) -> Ed25519Point<F, FC::FieldPoint>
    where
        C: CurveAffineExt<Base = FC::FieldType>,
    {
        let (x, y) = g.into_coordinates();
        let [x, y] = [x, y].map(FC::fe_to_constant);
        let x = self.field_chip.load_constant(ctx, x);
        let y = self.field_chip.load_constant(ctx, y);

        Ed25519Point::construct(x, y)
    }

    pub fn load_random_point<C>(&self, ctx: &mut Context<F>) -> Ed25519Point<F, FC::FieldPoint>
    where
        C: CurveAffineExt<Base = FC::FieldType>,
    {
        load_random_point::<F, FC, C>(self.field_chip(), ctx)
    }

    pub fn assert_is_on_curve<C>(&self, ctx: &mut Context<F>, P: &Ed25519Point<F, FC::FieldPoint>)
    where
        C: CurveAffine<Base = FC::FieldType>,
    {
        is_on_curve::<F, FC, C>(self.field_chip, ctx, P)
    }

    pub fn is_on_curve_or_infinity<C>(
        &self,
        ctx: &mut Context<F>,
        P: &Ed25519Point<F, FC::FieldPoint>,
    ) -> AssignedValue<F>
    where
        C: CurveAffine<Base = FC::FieldType>,
        C::Base: ff::PrimeField,
    {
        let lhs = self.field_chip.mul_no_carry(ctx, &P.y, &P.y);
        let mut rhs = self.field_chip.mul(ctx, &P.x, &P.x);
        rhs = self.field_chip.mul_no_carry(ctx, &rhs, &P.x);

        let b = FC::fe_to_constant(C::b());
        rhs = self.field_chip.add_constant_no_carry(ctx, &rhs, b);
        let mut diff = self.field_chip.sub_no_carry(ctx, &lhs, &rhs);
        diff = self.field_chip.carry_mod(ctx, &diff);

        let is_on_curve = self.field_chip.is_zero(ctx, &diff);

        let x_is_zero = self.field_chip.is_zero(ctx, &P.x);
        let y_is_zero = self.field_chip.is_zero(ctx, &P.y);

        self.field_chip.range().gate().or_and(ctx, is_on_curve, x_is_zero, y_is_zero)
    }

    pub fn negate(
        &self,
        ctx: &mut Context<F>,
        P: &Ed25519Point<F, FC::FieldPoint>,
    ) -> Ed25519Point<F, FC::FieldPoint> {
        Ed25519Point::construct(P.x.clone(), self.field_chip.negate(ctx, &P.y))
    }

    /// Assumes that P.x != Q.x
    /// Otherwise will panic
    pub fn sub_unequal(
        &self,
        ctx: &mut Context<F>,
        P: &Ed25519Point<F, FC::FieldPoint>,
        Q: &Ed25519Point<F, FC::FieldPoint>,
        is_strict: bool,
    ) -> Ed25519Point<F, FC::FieldPoint> {
        ec_sub_unequal(self.field_chip, ctx, P, Q, is_strict)
    }

    pub fn assert_equal(
        &self,
        ctx: &mut Context<F>,
        P: &Ed25519Point<F, FC::FieldPoint>,
        Q: &Ed25519Point<F, FC::FieldPoint>,
    ) {
        self.field_chip.assert_equal(ctx, &P.x, &Q.x);
        self.field_chip.assert_equal(ctx, &P.y, &Q.y);
    }

    pub fn sum<'b, 'v: 'b, C>(
        &self,
        ctx: &mut Context<F>,
        points: impl Iterator<Item = &'b Ed25519Point<F, FC::FieldPoint>>,
    ) -> Ed25519Point<F, FC::FieldPoint>
    where
        C: CurveAffineExt<Base = FC::FieldType>,
        FC::FieldPoint: 'b,
    {
        let rand_point = self.load_random_point::<C>(ctx);
        self.field_chip.enforce_less_than(ctx, rand_point.x());
        let mut acc = rand_point.clone();
        for point in points {
            self.field_chip.enforce_less_than(ctx, point.x());
            acc = self.add_unequal(ctx, &acc, point, true);
            self.field_chip.enforce_less_than(ctx, acc.x());
        }
        self.sub_unequal(ctx, &acc, &rand_point, true)
    }
    */
}

/*
impl<'chip, F: PrimeField, FC: FieldChip<F>> EccChip<'chip, F, FC>
where
    FC: Selectable<F, Point = FC::FieldPoint>,
{
    pub fn select(
        &self,
        ctx: &mut Context<F>,
        P: &Ed25519Point<F, FC::FieldPoint>,
        Q: &Ed25519Point<F, FC::FieldPoint>,
        condition: AssignedValue<F>,
    ) -> Ed25519Point<F, FC::FieldPoint> {
        ec_select(self.field_chip, ctx, P, Q, condition)
    }

    pub fn scalar_mult(
        &self,
        ctx: &mut Context<F>,
        P: &Ed25519Point<F, FC::FieldPoint>,
        scalar: Vec<AssignedValue<F>>,
        max_bits: usize,
        window_bits: usize,
    ) -> Ed25519Point<F, FC::FieldPoint> {
        scalar_multiply::<F, FC>(self.field_chip, ctx, P, scalar, max_bits, window_bits)
    }

    // default for most purposes
    pub fn variable_base_msm<C>(
        &self,
        thread_pool: &mut GateThreadBuilder<F>,
        P: &[Ed25519Point<F, FC::FieldPoint>],
        scalars: Vec<Vec<AssignedValue<F>>>,
        max_bits: usize,
    ) -> Ed25519Point<F, FC::FieldPoint>
    where
        C: CurveAffineExt<Base = FC::FieldType>,
        C::Base: ff::PrimeField,
    {
        // window_bits = 4 is optimal from empirical observations
        self.variable_base_msm_in::<C>(thread_pool, P, scalars, max_bits, 4, 0)
    }

    // TODO: put a check in place that scalar is < modulus of C::Scalar
    pub fn variable_base_msm_in<C>(
        &self,
        builder: &mut GateThreadBuilder<F>,
        P: &[Ed25519Point<F, FC::FieldPoint>],
        scalars: Vec<Vec<AssignedValue<F>>>,
        max_bits: usize,
        window_bits: usize,
        phase: usize,
    ) -> Ed25519Point<F, FC::FieldPoint>
    where
        C: CurveAffineExt<Base = FC::FieldType>,
        C::Base: ff::PrimeField,
    {
        #[cfg(feature = "display")]
        println!("computing length {} MSM", P.len());

        if P.len() <= 25 {
            multi_scalar_multiply::<F, FC, C>(
                self.field_chip,
                builder.main(phase),
                P,
                scalars,
                max_bits,
                window_bits,
            )
        } else {
            /*let mut radix = (f64::from((max_bits * scalars[0].len()) as u32)
                / f64::from(P.len() as u32))
            .sqrt()
            .floor() as usize;
            if radix == 0 {
                radix = 1;
            }*/
            // guessing that is is always better to use parallelism for >25 points
            pippenger::multi_exp_par::<F, FC, C>(
                self.field_chip,
                builder,
                P,
                scalars,
                max_bits,
                window_bits, // clump_factor := window_bits
                phase,
            )
        }
    }
}

impl<'chip, F: PrimeField, FC: PrimeFieldChip<F>> EccChip<'chip, F, FC>
where
    FC::FieldType: PrimeField,
{
    // TODO: put a check in place that scalar is < modulus of C::Scalar
    pub fn fixed_base_scalar_mult<C>(
        &self,
        ctx: &mut Context<F>,
        point: &C,
        scalar: Vec<AssignedValue<F>>,
        max_bits: usize,
        window_bits: usize,
    ) -> Ed25519Point<F, FC::FieldPoint>
    where
        C: CurveAffineExt,
        FC: PrimeFieldChip<F, FieldType = C::Base, FieldPoint = CRTInteger<F>>
            + Selectable<F, Point = FC::FieldPoint>,
    {
        fixed_base::scalar_multiply::<F, _, _>(
            self.field_chip,
            ctx,
            point,
            scalar,
            max_bits,
            window_bits,
        )
    }

    // default for most purposes
    pub fn fixed_base_msm<C>(
        &self,
        builder: &mut GateThreadBuilder<F>,
        points: &[C],
        scalars: Vec<Vec<AssignedValue<F>>>,
        max_scalar_bits_per_cell: usize,
    ) -> Ed25519Point<F, FC::FieldPoint>
    where
        C: CurveAffineExt,
        FC: PrimeFieldChip<F, FieldType = C::Base, FieldPoint = CRTInteger<F>>
            + Selectable<F, Point = FC::FieldPoint>,
    {
        self.fixed_base_msm_in::<C>(builder, points, scalars, max_scalar_bits_per_cell, 4, 0)
    }

    // `radix = 0` means auto-calculate
    //
    /// `clump_factor = 0` means auto-calculate
    ///
    /// The user should filter out base points that are identity beforehand; we do not separately do this here
    pub fn fixed_base_msm_in<C>(
        &self,
        builder: &mut GateThreadBuilder<F>,
        points: &[C],
        scalars: Vec<Vec<AssignedValue<F>>>,
        max_scalar_bits_per_cell: usize,
        clump_factor: usize,
        phase: usize,
    ) -> Ed25519Point<F, FC::FieldPoint>
    where
        C: CurveAffineExt,
        FC: PrimeFieldChip<F, FieldType = C::Base, FieldPoint = CRTInteger<F>>
            + Selectable<F, Point = FC::FieldPoint>,
    {
        debug_assert_eq!(points.len(), scalars.len());
        #[cfg(feature = "display")]
        println!("computing length {} fixed base msm", points.len());

        // heuristic to decide when to use parallelism
        if points.len() < 25 {
            let ctx = builder.main(phase);
            fixed_base::msm(self, ctx, points, scalars, max_scalar_bits_per_cell, clump_factor)
        } else {
            fixed_base::msm_par(
                self,
                builder,
                points,
                scalars,
                max_scalar_bits_per_cell,
                clump_factor,
                phase,
            )
        }

        // Empirically does not seem like pippenger is any better for fixed base msm right now, because of the cost of `select_by_indicator`
        // Cell usage becomes around comparable when `points.len() > 100`, and `clump_factor` should always be 4
        /*
        let radix = if radix == 0 {
            // auto calculate
            (f64::from(FC::FieldType::NUM_BITS) / f64::from(points.len() as u32)).sqrt().ceil()
                as usize
        } else {
            radix
        };
        assert!(radix > 0);

        fixed_base_pippenger::multi_exp::<F, FC, C>(
            self.field_chip,
            ctx,
            points,
            scalars,
            max_scalar_bits_per_cell,
            radix,
            clump_factor,
        )
        */
    }
}
*/

use crate::halo2_proofs::{
    dev::MockProver,
    halo2curves::ed25519::{Ed25519Affine, Fq, Fr},
};
use halo2_base::gates::builder::RangeCircuitBuilder;
use halo2_base::gates::RangeChip;
use halo2_base::utils::bigint_to_fe;
#[cfg(test)]
use rand_core::OsRng;

#[cfg(test)]
fn basic_tests<F: PrimeField>(
    ctx: &mut Context<F>,
    lookup_bits: usize,
    limb_bits: usize,
    num_limbs: usize,
    P: Ed25519Affine,
    Q: Ed25519Affine,
) {
    std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());
    let range = RangeChip::<F>::default(lookup_bits);
    let fp_chip = FpChip::<F, Fq>::new(&range, limb_bits, num_limbs);
    let chip = EccChip::new(&fp_chip);

    let P_assigned = chip.load_private(ctx, (P.x, P.y));
    let Q_assigned = chip.load_private(ctx, (Q.x, Q.y));

    // test add_unequal
    chip.field_chip.enforce_less_than(ctx, P_assigned.x());
    chip.field_chip.enforce_less_than(ctx, Q_assigned.x());
    let sum = chip.add::<Ed25519Affine>(ctx, &P_assigned, &Q_assigned);
    assert_eq!(sum.x.truncation.to_bigint(limb_bits), sum.x.value);
    assert_eq!(sum.y.truncation.to_bigint(limb_bits), sum.y.value);
    {
        let actual_sum = Ed25519Affine::from(P + Q);
        assert_eq!(bigint_to_fe::<Fq>(&sum.x.value), actual_sum.x);
        assert_eq!(bigint_to_fe::<Fq>(&sum.y.value), actual_sum.y);
    }
    println!("add unequal witness OK");

    // test double
    let doub = chip.double::<Ed25519Affine>(ctx, &P_assigned);
    assert_eq!(doub.x.truncation.to_bigint(limb_bits), doub.x.value);
    assert_eq!(doub.y.truncation.to_bigint(limb_bits), doub.y.value);
    {
        let actual_doub = Ed25519Affine::from(P * Fr::from(2u64));
        assert_eq!(bigint_to_fe::<Fq>(&doub.x.value), actual_doub.x);
        assert_eq!(bigint_to_fe::<Fq>(&doub.y.value), actual_doub.y);
    }
    println!("double witness OK");
}

#[test]
fn test_ecc() {
    let k = 23;
    let P = Ed25519Affine::random(OsRng);
    let Q = Ed25519Affine::random(OsRng);

    let mut builder = GateThreadBuilder::<Fr>::mock();
    basic_tests(builder.main(0), k - 1, 88, 3, P, Q);

    builder.config(k, Some(20));
    let circuit = RangeCircuitBuilder::mock(builder);

    MockProver::run(k as u32, &circuit, vec![]).unwrap().assert_satisfied();
}
