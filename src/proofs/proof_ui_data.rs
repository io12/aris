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

    pub fn from_proof(prf: &P) -> Self {
        let mut ref_to_line_depth = HashMap::new();
        calculate_lineinfo::<P>(
            &mut ref_to_line_depth,
            prf.top_level_proof(),
            &mut 1,
            &mut 0,
        );
        ProofUiData {
            ref_to_line_depth,
            ref_to_input: initialize_inputs(prf),
        }
    }
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
