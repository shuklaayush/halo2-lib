use crate::halo2_proofs::halo2curves::ed25519::{Fq, Fr};

use crate::ecc;
use crate::fields::fp;

pub type FpChip<'range, F> = fp::FpChip<'range, F, Fq>;
pub type FqChip<'range, F> = fp::FpChip<'range, F, Fr>;
pub type Ed25519Chip<'chip, F> = ecc::EccChip<'chip, F, FpChip<'chip, F>>;

#[cfg(test)]
mod tests;
