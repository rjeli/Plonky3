//! This crate contains a framework for low-degree tests (LDTs).

// #![no_std]

mod ldt_based_pcs;
mod quotient;

use alloc::vec;
use alloc::vec::Vec;

use itertools::{izip, Itertools};
pub use ldt_based_pcs::*;
use p3_challenger::FieldChallenger;
use p3_commit::Mmcs;
use p3_field::{
    batch_multiplicative_inverse, extension::HasFrobenuis, AbstractField, ExtensionField, Field,
    PackedField, TwoAdicField,
};
use p3_matrix::{
    dense::{RowMajorMatrix, RowMajorMatrixView},
    Dimensions, Matrix, MatrixRowSlices,
};
use p3_util::log2_strict_usize;
pub use quotient::*;

extern crate alloc;

/// A batch low-degree test (LDT).
pub trait Ldt<Val, Domain, M, Challenger>
where
    Val: Field,
    Domain: ExtensionField<Val>,
    M: Mmcs<Domain>,
    Challenger: FieldChallenger<Val>,
{
    type Proof;
    type Error;

    fn log_blowup(&self) -> usize;

    fn blowup(&self) -> usize {
        1 << self.log_blowup()
    }

    /// Prove that each column of each matrix in `codewords` is a codeword.
    fn prove(
        &self,
        input_mmcs: &[M],
        input_data: &[&M::ProverData],
        challenger: &mut Challenger,
    ) -> Self::Proof;

    fn verify(
        &self,
        input_mmcs: &[M],
        input_dims: &[Vec<Dimensions>],
        input_commits: &[M::Commitment],
        proof: &Self::Proof,
        challenger: &mut Challenger,
    ) -> Result<(), Self::Error>;
}

fn galois<F: Field, EF: HasFrobenuis<F>>(x: EF) -> [EF; 4] {
    let mut xs = [x; 4];
    for i in 1..4 {
        xs[i] = xs[i - 1].frobenius();
    }
    xs
}

// idk naive lagrange? i got this from gpt4...
fn lagrange<F: Field, const D: usize>(xs: [F; D], ys: [F; D]) -> [F; D] {
    let mut poly = [F::zero(); D];

    let mut den = [F::one(); D];
    for i in 0..D {
        for j in 0..D {
            if i != j {
                den[i] *= xs[i] - xs[j];
            }
        }
    }
    batch_multiplicative_inverse(&mut den);

    // welcome to malloc city
    for i in 0..D {
        let mut term_poly = vec![ys[i] * den[i]];
        for j in 0..D {
            if j != i {
                let mut new_term_poly = vec![F::zero(); term_poly.len() + 1];
                for k in 0..term_poly.len() {
                    new_term_poly[k] -= xs[j] * term_poly[k];
                    new_term_poly[k + 1] += term_poly[k];
                }
                term_poly = new_term_poly;
            }
        }
        for j in 0..term_poly.len() {
            poly[j] += term_poly[j];
        }
    }

    poly
}

fn polymul<F: Field>(p1: &[F], p2: &[F]) -> Vec<F> {
    let mut res = vec![F::zero(); p1.len() + p2.len() - 1];
    for (i, c1) in p1.iter().enumerate() {
        for (j, c2) in p2.iter().enumerate() {
            res[i + j] += *c1 * *c2;
        }
    }
    res
}

fn minpoly<F: Field, EF: HasFrobenuis<F>>(mut alpha: EF) -> Vec<F> {
    let mut poly = vec![EF::one()];
    for _ in 0..EF::D {
        poly = polymul(&poly, &[-alpha, EF::one()]);
        alpha = alpha.frobenius();
    }
    let mut poly = poly
        .into_iter()
        .map(|coeff| {
            assert!(coeff.is_in_basefield());
            coeff.as_base_slice()[0]
        })
        .collect_vec();
    assert!(poly[(EF::D + 1)..].iter().all(|x| x.is_zero()));
    assert_eq!(poly[EF::D], F::one());
    poly.resize(EF::D + 1, F::zero());
    poly
}

// returns (poly - r) / m
pub fn minpoly_quotient<F, EF, M>(
    inner: &M,
    data: &M::ProverData,
    alpha: EF,
    values: &[EF],
) -> RowMajorMatrix<F>
where
    F: Field + TwoAdicField,
    EF: ExtensionField<F> + HasFrobenuis<F>,
    for<'a> M: Mmcs<<F as PackedField>::Scalar, Mat<'a> = RowMajorMatrixView<'a, F>> + 'static,
{
    let mat = &inner.get_matrices(&data)[0];
    let height = mat.height();
    let log_height = log2_strict_usize(height);

    let alpha_frobs = galois(alpha);

    // calculate r for each poly
    let mut rs = vec![];
    for &val in values {
        let p_a_frobs = galois(val);
        let r: [F; 4] = lagrange(alpha_frobs, p_a_frobs).map(|coeff| {
            assert!(<EF as ExtensionField<F>>::is_in_basefield(&coeff));
            coeff.as_base_slice()[0]
        });
        rs.push(r);
    }

    // calculate m
    let m = minpoly(alpha);
    let xs = F::two_adic_generator(log_height)
        .shifted_powers(F::generator())
        .take(height);
    let mut m_invs: Vec<F> = xs
        .map(|x| m.iter().zip(x.powers()).map(|(a, b)| *a * b).sum())
        .collect();
    batch_multiplicative_inverse(&mut m_invs);

    let mut qp = RowMajorMatrix::new(vec![F::zero(); mat.width() * mat.height()], mat.width());
    let xs = F::two_adic_generator(log_height).shifted_powers(F::generator());
    for (row, qp_row, x, m_inv) in izip!(mat.rows(), qp.rows_mut(), xs, m_invs) {
        let x_pows: [F; 4] = (0..4)
            .map(|i| x.exp_u64(i))
            .collect_vec()
            .try_into()
            .unwrap();
        for (y, qp_y, r) in izip!(row, qp_row, &rs) {
            *qp_y = (*y - F::dot_product(&x_pows, &r)) * m_inv;
        }
    }

    qp
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::extension::BinomialExtensionField;
    use rand::{thread_rng, Rng};

    use super::*;

    #[test]
    fn test_minpoly() {
        type F = BabyBear;
        type EF = BinomialExtensionField<F, 4>;
        for _ in 0..1000 {
            let alpha: EF = thread_rng().gen();
            let m = minpoly(alpha);
            let sum: EF = alpha.powers().zip(m).map(|(x, c)| x * c).sum();
            assert_eq!(sum, EF::zero());
        }
    }
}
