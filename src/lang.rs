//! E-graph language, analysis, and hand-coded rewrite rules.

use crate::stack::LocalIdx;
use egg::{rewrite as rw, *};

define_language! {
    pub enum WasmLang {
        I32Const(i32),
        "i32.add"   = I32Add([Id; 2]),
        "i32.mul"   = I32Mul([Id; 2]),
        "i32.div_u" = I32DivU([Id; 2]),
        "i32.div_s" = I32DivS([Id; 2]),
        "i32.shl"   = I32Shl([Id; 2]),
        Symbol(Symbol),
        LocalIdx(LocalIdx),
        "init" = Init,
        "state_seq" = StateSeq([Id; 2]),
        "drop" = Drop([Id; 2]),
        "local.get" = LocalGet([Id; 2]),
        "local.set" = LocalSet([Id; 3]),
        "i32.store" = I32Store([Id; 3]),
        "i32.load"  = I32Load([Id; 2]),
        "call" = Call([Id; 2]),
    }
}

pub type EGraph = egg::EGraph<WasmLang, ConstantFolding>;

#[derive(Default)]
pub struct ConstantFolding;

impl Analysis<WasmLang> for ConstantFolding {
    type Data = Option<i32>;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        egg::merge_max(to, from)
    }

    fn make(egraph: &mut EGraph, enode: &WasmLang, _id: Id) -> Self::Data {
        let x = |i: &Id| egraph[*i].data;
        match enode {
            WasmLang::I32Const(c) => Some(*c),
            WasmLang::I32Add([a, b]) => Some(x(a)? + x(b)?),
            WasmLang::I32Mul([a, b]) => Some(x(a)? * x(b)?),
            WasmLang::I32DivU([a, b]) => {
                let divisor = x(b)?;
                if divisor == 0 {
                    None
                } else {
                    Some((x(a)? as u32 / divisor as u32) as i32)
                }
            }
            WasmLang::I32DivS([a, b]) => {
                let divisor = x(b)?;
                if divisor == 0 {
                    None
                } else {
                    Some(x(a)? / divisor)
                }
            }
            WasmLang::I32Shl([a, b]) => Some(x(a)? << x(b)?),
            _ => None,
        }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data {
            let const_node = egraph.add(WasmLang::I32Const(c));
            egraph.union(id, const_node);
        }
    }
}

fn is_nonzero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| matches!(egraph[subst[var]].data, Some(n) if n != 0)
}

fn is_pure_computation(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        egraph[subst[var]].nodes.iter().all(|n| {
            matches!(
                n,
                WasmLang::I32Add(_)
                    | WasmLang::I32Mul(_)
                    | WasmLang::I32DivU(_)
                    | WasmLang::I32DivS(_)
                    | WasmLang::I32Shl(_)
                    | WasmLang::I32Const(_)
                    | WasmLang::Symbol(_)
            )
        })
    }
}

pub fn arith_rules() -> Vec<Rewrite<WasmLang, ConstantFolding>> {
    vec![
        rw!("add-comm"; "(i32.add ?a ?b)" => "(i32.add ?b ?a)"),
        rw!("mul-comm"; "(i32.mul ?a ?b)" => "(i32.mul ?b ?a)"),
        rw!("mul-to-shl"; "(i32.mul ?x 2)" => "(i32.shl ?x 1)"),
        rw!("div-u-self"; "(i32.div_u ?x ?x)" => "1" if is_nonzero("?x")),
        rw!("div-s-self"; "(i32.div_s ?x ?x)" => "1" if is_nonzero("?x")),
    ]
}

pub fn effect_rules() -> Vec<Rewrite<WasmLang, ConstantFolding>> {
    vec![
        rw!("eliminate-pure-drop"; "(drop ?s ?val)" => "?s" if is_pure_computation("?val")),
        rw!(
            "dead-local-store";
            "(local.set ?idx ?v2 (local.set ?idx ?v1 ?s))"
            => "(local.set ?idx ?v2 (drop ?s ?v1))"
        ),
        rw!(
            "mem-dead-store";
            "(i32.store ?ptr ?v2 (i32.store ?ptr ?v1 ?s))"
            => "(i32.store ?ptr ?v2 ?s)"
        ),
        rw!("state-seq-id"; "(state_seq ?s ?s)" => "?s"),
    ]
}

pub fn manual_rules() -> Vec<Rewrite<WasmLang, ConstantFolding>> {
    let mut all = arith_rules();
    all.extend(effect_rules());
    all
}
