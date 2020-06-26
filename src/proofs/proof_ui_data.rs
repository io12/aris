use crate::proofs::js_to_pjs;
use crate::PJRef;
use crate::Proof;

use std::collections::HashMap;

use frunk::Coproduct;

pub struct ProofUiData<P: Proof> {
    pub ref_to_line_depth: HashMap<PJRef<P>, (usize, usize)>,
    pub ref_to_input: HashMap<PJRef<P>, String>,
}

impl<P: Proof> ProofUiData<P> {
    pub fn new() -> Self {
        Self {
            ref_to_line_depth: HashMap::new(),
            ref_to_input: HashMap::new(),
        }
    }

    pub fn from_proof(proof: &P) -> Self {
        ProofUiData {
            ref_to_line_depth: calculate_lineinfo::<P>(proof.top_level_proof()),
            ref_to_input: initialize_inputs(proof),
        }
    }
}

pub fn calculate_lineinfo<P: Proof>(
    proof: &<P as Proof>::Subproof,
) -> HashMap<PJRef<P>, (usize, usize)> {
    let mut ret = HashMap::new();
    calculate_lineinfo_helper::<P>(&mut ret, proof.top_level_proof(), &mut 1, &mut 0);
    ret
}

fn calculate_lineinfo_helper<P: Proof>(
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
                calculate_lineinfo_helper::<P>(
                    output,
                    &prf.lookup_subproof(&sr).unwrap(),
                    line,
                    depth,
                );
                *depth -= 1;
            }
            Inr(Inr(void)) => match void {},
        }
    }
}

pub fn initialize_inputs<P: Proof>(prf: &P) -> HashMap<PJRef<P>, String> {
    fn aux<P: Proof>(p: &<P as Proof>::Subproof, out: &mut HashMap<PJRef<P>, String>) {
        use frunk::Coproduct::{Inl, Inr};
        for line in p
            .premises()
            .into_iter()
            .map(Coproduct::inject)
            .chain(p.lines().into_iter().map(js_to_pjs::<P>))
        {
            match line {
                Inl(pr) => {
                    if let Some(e) = p.lookup_expr(&Coproduct::inject(pr.clone())) {
                        out.insert(Coproduct::inject(pr.clone()), format!("{}", e));
                    }
                }
                Inr(Inl(jr)) => {
                    if let Some(e) = p.lookup_expr(&Coproduct::inject(jr.clone())) {
                        out.insert(Coproduct::inject(jr.clone()), format!("{}", e));
                    }
                }
                Inr(Inr(Inl(sr))) => aux::<P>(&p.lookup_subproof(&sr).unwrap(), out),
                Inr(Inr(Inr(void))) => match void {},
            }
        }
    }

    let mut out = HashMap::new();
    aux::<P>(prf.top_level_proof(), &mut out);
    out
}
