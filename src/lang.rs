//! E-graph language and constant-folding analysis.

use egg::*;

define_language! {
    pub enum WasmLang {
        I32Const(i32),
        "i32.add"   = I32Add([Id; 2]),
        "i32.mul"   = I32Mul([Id; 2]),
        "i32.div_u" = I32DivU([Id; 2]),
        "i32.div_s" = I32DivS([Id; 2]),
        "i32.shl"   = I32Shl([Id; 2]),
        "stack.end"  = StackEnd,
        "stack.slot" = StackSlot([Id; 2]),
        Symbol(Symbol),
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
            WasmLang::I32Shl([a, b]) => Some(x(a)?.wrapping_shl(x(b)? as u32 & 31)),
            WasmLang::StackEnd | WasmLang::StackSlot(_) => None,
            WasmLang::Symbol(_) => None,
        }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data {
            let const_node = egraph.add(WasmLang::I32Const(c));
            egraph.union(id, const_node);
        }
    }
}
