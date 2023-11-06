use alloc::vec;
use alloc::vec::Vec;
use itertools::{izip, Itertools};
use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger};
use p3_commit::Mmcs;
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

    let mut betas: Vec<FC::Challenge> = vec![];
    for com in &proof.commit_phase_commits {
        challenger.observe(com.clone());
        betas.push(challenger.sample_ext_element());
    }
    dbg!(&betas);

    if proof.query_proofs.len() != config.num_queries() {
        return Err(());
    }

    let log_max_height = 7; // TODO
    let query_indices = (0..config.num_queries()).map(|_| challenger.sample_bits(log_max_height));

    for (index, proof) in query_indices.zip(&proof.query_proofs) {
        verify_query(config, input_mmcs, input_commits, index, proof)?;
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
) -> Result<(), ()> {
    // input_mmcs.iter().
    // println!("verifying query at {index}");
    /*
    dbg!(
        input_mmcs.len(),
        proof.input_openings.len(),
        input_commits.len(),
        index
    );
    */
    for (i, (mmcs, commit, input_opening)) in
        izip!(input_mmcs, input_commits, &proof.input_openings).enumerate()
    {
        let dims = match i {
            0 => Dimensions {
                width: 60,
                height: 128,
            },
            1 => Dimensions {
                width: 2,
                height: 128,
            },
            _ => panic!(),
        };
        // dbg!(input_opening.opened_values.len());
        mmcs.verify_batch(
            commit,
            &[dims],
            index,
            &input_opening.opened_values,
            &input_opening.opening_proof,
        )
        .map_err(|_| ())?;
    }

    // TODO
    Ok(())
}
