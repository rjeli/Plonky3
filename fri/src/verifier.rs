use alloc::vec;
use alloc::vec::Vec;
use itertools::{izip, Itertools};
use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger};
use p3_commit::Mmcs;
use p3_field::AbstractField;
use p3_matrix::Dimensions;

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

    // TODO: does this need to be asserted valid?
    let log_max_height = proof.commit_phase_commits.len() + config.log_blowup();
    let query_indices = (0..config.num_queries())
        .map(|_| challenger.sample_bits(log_max_height))
        .collect_vec();

    for (index, proof) in query_indices.into_iter().zip(&proof.query_proofs) {
        verify_query(
            config,
            input_mmcs,
            input_commits,
            index,
            proof,
            log_max_height,
            alpha,
        )?;
    }

    println!("verified fri");

    Ok(())
}

fn verify_query<FC: FriConfig>(
    _config: &FC,
    input_mmcs: &[FC::InputMmcs],
    input_commits: &[<FC::InputMmcs as Mmcs<FC::Challenge>>::Commitment],
    index: usize,
    proof: &QueryProof<FC>,
    log_max_height: usize,
    alpha: FC::Challenge,
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

    dbg!(index, old_eval);

    for step in &proof.commit_phase_openings {
        // todo
    }

    Ok(())
}
