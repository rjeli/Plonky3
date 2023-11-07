use alloc::vec;
use alloc::vec::Vec;
use itertools::{izip, Itertools};
use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger};
use p3_commit::Mmcs;
use p3_dft::{reverse_bits, reverse_bits_len};
use p3_field::{AbstractField, TwoAdicField};
use p3_matrix::Dimensions;
use p3_util::rotate_bits_right;

use crate::{FriConfig, FriProof, QueryProof};

pub(crate) fn verify<FC: FriConfig>(
    config: &FC,
    input_mmcs: &[FC::InputMmcs],
    input_commits: &[<FC::InputMmcs as Mmcs<FC::Challenge>>::Commitment],
    proof: &FriProof<FC>,
    challenger: &mut FC::Challenger,
) -> Result<(), ()> {
    println!("verifying fri");

    let alpha: FC::Challenge = challenger.sample_ext_element();
    dbg!(alpha);

    let mut betas: Vec<FC::Challenge> = vec![];
    for comm in &proof.commit_phase_commits {
        challenger.observe(comm.clone());
        betas.push(challenger.sample_ext_element());
    }
    dbg!(&betas);

    if proof.query_proofs.len() != config.num_queries() {
        return Err(());
    }

    // let qp = &proof.query_proofs[0];

    // TODO: check proof shape
    let log_max_height = proof.commit_phase_commits.len() + config.log_blowup();
    let query_indices = (0..config.num_queries())
        .map(|_| challenger.sample_bits(log_max_height))
        .collect_vec();

    for (index, query_proof) in query_indices.into_iter().zip(&proof.query_proofs) {
        verify_query(
            config,
            input_mmcs,
            input_commits,
            index,
            query_proof,
            &proof.commit_phase_commits,
            log_max_height,
            alpha,
            &betas,
        )?;
    }

    println!("verified fri");

    Ok(())
}

fn verify_query<FC: FriConfig>(
    config: &FC,
    input_mmcs: &[FC::InputMmcs],
    input_commits: &[<FC::InputMmcs as Mmcs<FC::Challenge>>::Commitment],
    index: usize,
    proof: &QueryProof<FC>,
    commit_phase_commits: &[<FC::CommitPhaseMmcs as Mmcs<FC::Challenge>>::Commitment],
    log_max_height: usize,
    alpha: FC::Challenge,
    betas: &[FC::Challenge],
) -> Result<(), ()> {
    let mut old_eval = FC::Challenge::zero();

    // Verify input commitment
    for (mmcs, commit, input_opening) in izip!(input_mmcs, input_commits, &proof.input_openings) {
        // TODO: this assumes all matrices are max height
        let dims = input_opening
            .opened_values
            .iter()
            .map(|vals| Dimensions {
                width: vals.len(),
                height: 1 << log_max_height,
            })
            .collect_vec();
        mmcs.verify_batch(
            commit,
            &dims,
            index,
            &input_opening.opened_values,
            &input_opening.opening_proof,
        )
        // TODO
        .map_err(|_| ())?;

        for vals in &input_opening.opened_values {
            for v in vals {
                old_eval *= alpha;
                old_eval += *v;
            }
        }
    }

    dbg!(index, old_eval, log_max_height);
    dbg!(commit_phase_commits.len());
    dbg!(proof.commit_phase_openings.len());

    let mut x = FC::Challenge::generator()
        * FC::Challenge::two_adic_generator(log_max_height).exp_u64(index as u64);

    // let index = reverse_bits_len(index, log_max_height);
    // let index = rotate_bits_right(index, log_max_height);
    // dbg!(index);

    // TODO: check proof shape
    for (i, (commit, step, &beta)) in
        izip!(commit_phase_commits, &proof.commit_phase_openings, betas).enumerate()
    {
        let index_i = rotate_bits_right(index >> i, log_max_height - i);
        let index_i_sibling = index_i ^ 1;
        let index_pair = index_i >> 1;

        let dims = &[Dimensions {
            width: 2,
            height: (1 << (log_max_height - i - 1)),
        }];
        let mut evals = vec![old_eval; 2];
        evals[index_i_sibling % 2] = step.sibling_value;

        println!("verifying commit step");

        dbg!(
            index_i,
            index_i_sibling,
            index_pair,
            &evals,
            old_eval,
            step.sibling_value
        );

        config
            .commit_phase_mmcs()
            .verify_batch(
                commit,
                dims,
                index_pair,
                &[evals.clone()],
                &step.opening_proof,
            )
            .map_err(|e| dbg!("verify error"));

        let mut xs = [x; 2];
        xs[index_i % 2] *= FC::Challenge::two_adic_generator(1);
        old_eval = evals[0] + (beta - xs[0]) * (evals[1] - evals[0]) / (xs[1] - xs[0]);

        x = x.square();

        println!("verified commit step");

        // todo
        /*
        config
            .commit_phase_mmcs()
            .verify_batch(commit, dimensions, index, opened_values, proof)
            .map_err(|_| ())?;
            */
    }

    Ok(())
}
