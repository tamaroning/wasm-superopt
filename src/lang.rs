//! E-graph language.

use egg::*;

define_language! {
    pub enum ValueLang {
        I32Const(i32),
        "i32.add"   = I32Add([Id; 2]),
        "i32.sub"   = I32Sub([Id; 2]),
        "i32.mul"   = I32Mul([Id; 2]),
        "i32.div_u" = I32DivU([Id; 2]),
        "i32.div_s" = I32DivS([Id; 2]),
        "i32.shl"   = I32Shl([Id; 2]),
        "i32.eq"    = I32Eq([Id; 2]),
        "i32.ne"    = I32Ne([Id; 2]),
        "i32.lt_s"  = I32LtS([Id; 2]),
        "i32.le_s"  = I32LeS([Id; 2]),
        "i32.gt_s"  = I32GtS([Id; 2]),
        Symbol(Symbol),
    }
}
