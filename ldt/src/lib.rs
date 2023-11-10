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
    add_vecs, batch_multiplicative_inverse, cyclic_subgroup_coset_known_order,
    extension::HasFrobenuis, scale_vec, sum_vecs, AbstractField, ExtensionField, Field,
    PackedField, TwoAdicField,
};
use p3_matrix::{
    dense::{RowMajorMatrix, RowMajorMatrixView},
    Dimensions, Matrix, MatrixRowSlices, MatrixRowSlicesMut,
};
use p3_util::log2_strict_usize;
pub use quotient::*;
use tracing::{debug_span, instrument};

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

// expands a product of binomials (x - xs[0])(x - xs[1]).. into coeffs
fn binomial_expand<F: Field>(xs: &[F]) -> Vec<F> {
    let mut coeffs = vec![F::zero(); xs.len() + 1];
    coeffs[0] = F::one();
    for (i, &x) in xs.iter().enumerate() {
        for j in (1..i + 2).rev() {
            coeffs[j] = coeffs[j - 1] - x * coeffs[j];
        }
        coeffs[0] *= -x;
    }
    coeffs
}

fn galois_lagrange_basis<F: Field, EF: HasFrobenuis<F>>(alpha: EF) -> Vec<EF> {
    let xs = galois(alpha);
    let w_alpha = xs[1..]
        .iter()
        .map(|&xi| xs[0] - xi)
        .product::<EF>()
        .inverse();
    binomial_expand(&xs[1..])
        .into_iter()
        .map(|c| c * w_alpha)
        .collect()
}

#[instrument(skip_all, level = "debug")]
fn remainder_polys<F: Field, EF: HasFrobenuis<F>>(alpha: EF, values: &[EF]) -> Vec<[F; 4]> {
    let mut rs: Vec<[F; 4]> = vec![];
    // precompute basis for alpha, Frob alpha, Frob^2 alpha, ..
    let l_alpha = galois_lagrange_basis(alpha);
    assert_eq!(l_alpha.len(), EF::D);
    for &p_alpha in values {
        let mut l_alpha_frob = scale_vec(p_alpha, l_alpha.clone());
        let mut r = l_alpha_frob.clone();
        for _ in 1..EF::D {
            l_alpha_frob.iter_mut().for_each(|c| *c = c.frobenius());
            r = add_vecs(r, l_alpha_frob.clone());
        }
        rs.push(
            r.into_iter()
                .map(|c| {
                    assert!(<EF as ExtensionField<F>>::is_in_basefield(&c));
                    c.as_base_slice()[0]
                })
                .collect_vec()
                .try_into()
                .unwrap(),
        );
    }
    rs
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

#[instrument(skip_all, level = "debug")]
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
#[instrument(skip_all, level = "debug")]
pub fn minpoly_quotient<F, EF, M>(
    inner: &M,
    data: &M::ProverData,
    alpha: EF,
    values: &[EF],
    shift: F,
) -> RowMajorMatrix<F>
where
    F: Field + TwoAdicField,
    EF: ExtensionField<F> + HasFrobenuis<F>,
    for<'a> M: Mmcs<<F as PackedField>::Scalar, Mat<'a> = RowMajorMatrixView<'a, F>> + 'static,
{
    let mat = &inner.get_matrices(&data)[0];
    let height = mat.height();
    let log_height = log2_strict_usize(height);

    // calculate r for each poly
    let rs = remainder_polys(alpha, values);
    // convert [(a,b,c,d), (e,f,g,h), ..]
    // into [[(a,e,..), (b,f,..)]]
    let mut rs_transposed: Vec<[F::Packing; 4]> = vec![];
    for ch in rs.chunks_exact(4) {
        let ch: [[F; 4]; 4] = ch.into_iter().copied().collect_vec().try_into().unwrap();
        rs_transposed.push(
            (0..4)
                .map(|i| *F::Packing::from_slice(&ch.map(|coeffs| coeffs[i])))
                .collect_vec()
                .try_into()
                .unwrap(),
        );
    }

    let xs = cyclic_subgroup_coset_known_order(F::two_adic_generator(log_height), shift, height)
        .collect_vec();

    // calculate m
    let m_invs: Vec<F> = debug_span!("m_invs").in_scope(|| {
        let m = minpoly(alpha);
        batch_multiplicative_inverse(
            &xs.iter()
                .map(|&x| m.iter().zip(x.powers()).map(|(a, b)| *a * b).sum())
                .collect_vec(),
        )
    });

    // very optimistic
    // assumes your extension degree is 4, your packing width is 4,
    // and your trace width is a multiple of 4.
    let mut qp = RowMajorMatrix::new(vec![F::zero(); mat.width() * mat.height()], mat.width());
    debug_span!("fill qp").in_scope(|| {
        let rs_at_x_span = debug_span!("eval r(x) at x");
        let quotient_span = debug_span!("eval qp");
        for i in 0..height {
            // reduce rs horizontally
            /*
            let x_pows = F::Packing::from_fn(|j| xs[i].exp_u64(j as u64));
            let rs_at_x: Vec<F> = rs_at_x_span.in_scope(|| {
                rs.iter()
                    .map(|r| {
                        let packed_r = *F::Packing::from_slice(r);
                        // fall back to scalar code to horizontally sum BB4 -> BB
                        (packed_r * x_pows).as_slice().iter().copied().sum()
                    })
                    .collect_vec()
            });
            */

            // [(1,1,1,1),(x,x,x,x),(x^2,x^2,x^2,x^2),(x3,x^3,x^3,x^3)]
            let x_pows: [F::Packing; 4] = (0..4)
                .map(|j| F::Packing::from(xs[i].exp_u64(j)))
                .collect_vec()
                .try_into()
                .unwrap();

            let p_row = F::Packing::pack_slice(mat.row_slice(i));
            let p_qp_row = F::Packing::pack_slice_mut(qp.row_slice_mut(i));
            // let p_r_at_x = F::Packing::pack_slice(&rs_at_x);
            let p_m_inv = F::Packing::from(m_invs[i]);

            for (y, qp_y, r) in izip!(p_row, p_qp_row, &rs_transposed) {
                let mut sum = F::Packing::zero();
                for (ch, x_pow) in r.iter().zip(x_pows) {
                    sum += *ch * x_pow;
                }
                *qp_y = (*y - sum) * p_m_inv;
            }
        }
    });

    qp
}

#[cfg(test)]
mod tests {
    use std::println;

    use p3_baby_bear::BabyBear;
    use p3_commit::DirectMmcs;
    use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
    use p3_field::extension::BinomialExtensionField;
    use p3_field::AbstractExtensionField;
    use p3_interpolation::{interpolate_coset, interpolate_subgroup};
    use p3_matrix::{MatrixRowSlicesMut, MatrixRows};
    use p3_mds::coset_mds::CosetMds;
    use p3_merkle_tree::FieldMerkleTreeMmcs;
    use p3_poseidon2::{DiffusionMatrixBabybear, Poseidon2};
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use rand::{thread_rng, Rng};
    use tracing::info_span;
    use tracing_forest::ForestLayer;
    use tracing_subscriber::layer::SubscriberExt;
    use tracing_subscriber::util::SubscriberInitExt;
    use tracing_subscriber::{EnvFilter, Registry};

    use super::*;

    type F = BabyBear;
    type EF = BinomialExtensionField<F, 4>;

    type Val = BabyBear;
    type Challenge = BinomialExtensionField<BabyBear, 4>;
    type MyMds = CosetMds<Val, 16>;
    type Perm = Poseidon2<Val, MyMds, DiffusionMatrixBabybear, 16, 5>;
    type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
    type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
    type ValMmcs = FieldMerkleTreeMmcs<<Val as Field>::Packing, MyHash, MyCompress, 8>;

    #[test]
    fn test_minpoly() {
        for _ in 0..1000 {
            let alpha: EF = thread_rng().gen();
            let m = minpoly(alpha);
            let sum: EF = alpha.powers().zip(m).map(|(x, c)| x * c).sum();
            assert_eq!(sum, EF::zero());
        }

        info_span!("bar").in_scope(|| println!("hi"));
    }

    #[test]
    fn test_binomial_expand() {
        // (x - 1)(x - 2) = x^2 - 3x + 2
        assert_eq!(
            binomial_expand(&[F::one(), F::two()]),
            vec![F::two(), -F::from_canonical_usize(3), F::one()]
        );
    }

    fn reduce<F: Field>(coeffs: &[F], x: F) -> F {
        coeffs
            .iter()
            .zip(x.powers())
            .map(|(c, x_pow)| *c * x_pow)
            .sum()
    }

    #[test]
    fn test_remainder_poly() {
        let mut rng = thread_rng();
        let log_height = 5;
        let trace: RowMajorMatrix<Val> = RowMajorMatrix::rand(&mut rng, 1 << log_height, 10);
        let point: EF = rng.gen();
        let values = interpolate_subgroup(&trace, point);
        let rs = remainder_polys(point, &values);
        for (r, y) in rs.into_iter().zip(values) {
            // r(alpha) == p(alpha)
            assert_eq!(
                reduce(
                    &r.into_iter().map(|x| EF::from_base(x)).collect_vec(),
                    point
                ),
                y
            );
        }
    }

    fn max_deg<F: TwoAdicField>(m: &RowMajorMatrix<F>) -> usize {
        let coeffs = Radix2Dit.idft_batch(m.clone());
        coeffs.height()
            - (0..coeffs.height())
                .rev()
                .take_while(|&r| coeffs.row(r).all(|x| x.is_zero()))
                .count()
    }

    #[test]
    fn test_minpoly_quotient() {
        Registry::default()
            .with(EnvFilter::from_default_env())
            .with(ForestLayer::default())
            .init();

        let mut rng = thread_rng();
        let shift = Val::generator();

        let mds = MyMds::default();
        let perm = Perm::new_from_rng(8, 22, mds, DiffusionMatrixBabybear, &mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm.clone());
        let inner = ValMmcs::new(hash, compress);

        let width = 1024;
        let log_height = 14;

        let trace: RowMajorMatrix<Val> = RowMajorMatrix::rand(&mut rng, 1 << log_height, width);
        let lde = Radix2Dit.coset_lde_batch(trace, 1, shift);
        assert_eq!(max_deg(&lde), 1 << log_height);

        let (_comm, data) = inner.commit_matrix(lde.clone());
        let point: Challenge = rng.gen();
        let mut values = interpolate_coset(&lde, shift, point);

        let qp = minpoly_quotient(&inner, &data, point, &values, shift);
        // passes ldt when opening valid
        assert!(max_deg(&qp) <= (1 << log_height) - 4);

        // invalidate the opening
        values[100] = rng.gen();
        let qp = minpoly_quotient(&inner, &data, point, &values, shift);
        // now degree should be too high
        assert!(max_deg(&qp) > (1 << log_height) - 4);
    }
}
