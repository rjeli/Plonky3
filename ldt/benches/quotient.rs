use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use itertools::{izip, Itertools};
use p3_commit::{DirectMmcs, Mmcs};
use p3_interpolation::interpolate_coset;
use p3_ldt::{minpoly_quotient, Opening, QuotientMmcs};
use p3_matrix::{dense::RowMajorMatrix, Matrix, MatrixRows};
use p3_util::log2_strict_usize;
use rand::{thread_rng, Rng};

use p3_baby_bear::BabyBear;
use p3_field::{
    extension::{BinomialExtensionField, HasFrobenuis},
    AbstractExtensionField, AbstractField, ExtensionField, Field, TwoAdicField,
};
use p3_mds::coset_mds::CosetMds;
use p3_merkle_tree::FieldMerkleTreeMmcs;
use p3_poseidon2::{DiffusionMatrixBabybear, Poseidon2};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};

type Val = BabyBear;
type Challenge = BinomialExtensionField<BabyBear, 4>;
type MyMds = CosetMds<Val, 16>;
type Perm = Poseidon2<Val, MyMds, DiffusionMatrixBabybear, 16, 5>;
type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
type ValMmcs = FieldMerkleTreeMmcs<<Val as Field>::Packing, MyHash, MyCompress, 8>;

fn inner_mmcs() -> ValMmcs {
    let mds = MyMds::default();
    let perm = Perm::new_from_rng(8, 22, mds, DiffusionMatrixBabybear, &mut thread_rng());
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    ValMmcs::new(hash, compress)
}

fn bench_quotient(c: &mut Criterion) {
    let mut rng = thread_rng();
    let coset_shift = Val::generator();
    let inner = inner_mmcs();
    for width in [128, 1024] {
        for log_height in [10, 12, 14] {
            let mut group = c.benchmark_group("quotient");
            group.sample_size(10);

            let trace: RowMajorMatrix<Val> = RowMajorMatrix::rand(&mut rng, 1 << log_height, width);
            let (comm, data) = inner.commit_matrix(trace.clone());
            let point: Challenge = rng.gen();
            let values = interpolate_coset(&trace, coset_shift, point);

            let mmcs = QuotientMmcs {
                inner: inner.clone(),
                openings: vec![vec![Opening {
                    point,
                    values: values.clone(),
                }]],
                coset_shift,
            };

            group.bench_with_input(
                BenchmarkId::new("ext_quotient", format!("{}x{}", width, 1 << log_height)),
                &data,
                |b, data| {
                    b.iter(|| {
                        let mat = &mmcs.get_matrices(&data)[0];
                        for r in 0..mat.height() {
                            for val in mat.row(r) {
                                black_box(val);
                            }
                        }
                    });
                },
            );

            group.bench_with_input(
                BenchmarkId::new("minpoly", format!("{}x{}", width, 1 << log_height)),
                &(&inner, &data, point, &values),
                |b, (inner, data, point, values)| {
                    b.iter(|| black_box(minpoly_quotient(*inner, data, *point, values)));
                },
            );
        }
    }
}

criterion_group!(benches, bench_quotient);
criterion_main!(benches);
