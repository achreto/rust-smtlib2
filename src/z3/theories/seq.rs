use crate::{SortedVar, Term};

fn seq_prefix(name: &str) -> String {
    format!("seq.{name}")
}

pub fn unit(elem: Term) -> Term {
    Term::fn_apply(seq_prefix("unit"), vec![elem])
}

pub fn empty(sort: String) -> Term {
    Term::QualifiedIdentifier(SortedVar::new(seq_prefix("empty"), sort))
}

pub fn concat(seqs: Vec<Term>) -> Term {
    Term::fn_apply(seq_prefix("++"), seqs)
}

pub fn len(seq: Term) -> Term {
    Term::fn_apply(seq_prefix("len"), vec![seq])
}

pub fn extract(seq: Term, offset: Term, length: Term) -> Term {
    Term::fn_apply(seq_prefix("extract"), vec![seq, offset, length])
}

pub fn indexof(seq: Term, subseq: Term, offset: Option<Term>) -> Term {
    let mut args = vec![seq, subseq];
    if let Some(start_idx) = offset {
        args.push(start_idx);
    }
    Term::fn_apply(seq_prefix("indexof"), args)
}

pub fn at(seq: Term, offset: Term) -> Term {
    Term::fn_apply(seq_prefix("at"), vec![seq, offset])
}

pub fn nth(seq: Term, offset: Term) -> Term {
    Term::fn_apply(seq_prefix("nth"), vec![seq, offset])
}

pub fn contains(seq: Term, subseq: Term) -> Term {
    Term::fn_apply(seq_prefix("contains"), vec![seq, subseq])
}

pub fn prefixof(pre: Term, seq: Term) -> Term {
    Term::fn_apply(seq_prefix("prefixof"), vec![pre, seq])
}

pub fn suffixof(suf: Term, seq: Term) -> Term {
    Term::fn_apply(seq_prefix("suffixof"), vec![suf, seq])
}

pub fn replace(seq: Term, src: Term, dst: Term) -> Term {
    Term::fn_apply(seq_prefix("replace"), vec![seq, src, dst])
}

pub fn map(fun: Term, seq: Term) -> Term {
    Term::fn_apply(seq_prefix("map"), vec![fun, seq])
}

pub fn mapi(fun: Term, offset: Term, seq: Term) -> Term {
    Term::fn_apply(seq_prefix("mapi"), vec![fun, offset, seq])
}

pub fn foldl(fun: Term, initial: Term, seq: Term) -> Term {
    Term::fn_apply(seq_prefix("foldl"), vec![fun, initial, seq])
}

pub fn foldli(fun: Term, offset: Term, initial: Term, seq: Term) -> Term {
    Term::fn_apply(seq_prefix("foldli"), vec![fun, offset, initial, seq])
}
