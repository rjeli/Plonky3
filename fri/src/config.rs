use core::marker::PhantomData;

use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{DirectMmcs, Mmcs};
use p3_field::{ExtensionField, PrimeField64, TwoAdicField};

pub trait FriConfig {
    type Val: PrimeField64;
    type Domain: ExtensionField<Self::Val> + TwoAdicField;
    type Challenge: ExtensionField<Self::Val> + ExtensionField<Self::Domain> + TwoAdicField;

    type InputMmcs: Mmcs<Self::Challenge>;
    type CommitPhaseMmcs: DirectMmcs<Self::Challenge>;

    type Challenger: FieldChallenger<Self::Val>
        + CanObserve<<Self::CommitPhaseMmcs as Mmcs<Self::Challenge>>::Commitment>;

    fn commit_phase_mmcs(&self) -> &Self::CommitPhaseMmcs;

    fn num_queries(&self) -> usize;

    fn log_blowup(&self) -> usize;

    fn blowup(&self) -> usize {
        1 << self.log_blowup()
    }

    // TODO: grinding bits
}

pub struct FriConfigImpl<Val, Domain, Challenge, InputMmcs, CommitPhaseMmcs, Challenger> {
    num_queries: usize,
    commit_phase_mmcs: CommitPhaseMmcs,
    _phantom: PhantomData<(Val, Domain, Challenge, InputMmcs, Challenger)>,
}

impl<Val, Domain, Challenge, InputMmcs, CommitPhaseMmcs, Challenger>
    FriConfigImpl<Val, Domain, Challenge, InputMmcs, CommitPhaseMmcs, Challenger>
{
    pub fn new(num_queries: usize, commit_phase_mmcs: CommitPhaseMmcs) -> Self {
        Self {
            num_queries,
            commit_phase_mmcs,
            _phantom: PhantomData,
        }
    }
}

impl<Val, Domain, Challenge, InputMmcs, CommitPhaseMmcs, Challenger> FriConfig
    for FriConfigImpl<Val, Domain, Challenge, InputMmcs, CommitPhaseMmcs, Challenger>
where
    Val: PrimeField64,
    Domain: ExtensionField<Val> + TwoAdicField,
    Challenge: ExtensionField<Val> + ExtensionField<Domain> + TwoAdicField,
    InputMmcs: Mmcs<Challenge>,
    CommitPhaseMmcs: DirectMmcs<Challenge>,
    Challenger: FieldChallenger<Val> + CanObserve<<CommitPhaseMmcs as Mmcs<Challenge>>::Commitment>,
{
    type Val = Val;
    type Domain = Domain;
    type Challenge = Challenge;
    type InputMmcs = InputMmcs;
    type CommitPhaseMmcs = CommitPhaseMmcs;
    type Challenger = Challenger;

    fn commit_phase_mmcs(&self) -> &CommitPhaseMmcs {
        &self.commit_phase_mmcs
    }

    fn num_queries(&self) -> usize {
        self.num_queries
    }

    fn log_blowup(&self) -> usize {
        1 // TODO: 2x blowup for now, but should make it configurable
    }
}
