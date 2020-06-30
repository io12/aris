use aris::expression::Expr;
use aris::proofs::pooledproof::PooledProof;
use aris::proofs::PJRef;
use aris::proofs::Proof;

use std::collections::HashMap;

use frunk::Coproduct;
use frunk::Hlist;

// yew doesn't seem to allow Components to be generic over <P: Proof>, so fix a proof type P at the module level
pub type P = PooledProof<Hlist![Expr]>;

/// Create a unique ID that is different each call
pub fn uid() -> usize {
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;
    static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
    NEXT_ID.fetch_add(1, Ordering::Relaxed)
}

pub fn calculate_lineinfo<P: Proof>(
    output: &mut HashMap<PJRef<P>, (usize, usize)>,
    prf: &<P as Proof>::Subproof,
    line: &mut usize,
    depth: &mut usize,
) {
    for prem in prf.premises() {
        output.insert(Coproduct::inject(prem.clone()), (*line, *depth));
        *line += 1;
    }
    for lineref in prf.lines() {
        use frunk::Coproduct::{Inl, Inr};
        match lineref {
            Inl(r) => {
                output.insert(Coproduct::inject(r), (*line, *depth));
                *line += 1;
            }
            Inr(Inl(sr)) => {
                *depth += 1;
                calculate_lineinfo::<P>(output, &prf.lookup_subproof(&sr).unwrap(), line, depth);
                *depth -= 1;
            }
            Inr(Inr(void)) => match void {},
        }
    }
}
