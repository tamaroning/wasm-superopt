//! E-graph language.

use egg::*;

define_language! {
    pub enum ValueLang {
        I32Const(i32),
        "i32.add"   = I32Add([Id; 2]),
        "i32.mul"   = I32Mul([Id; 2]),
        "i32.div_u" = I32DivU([Id; 2]),
        "i32.div_s" = I32DivS([Id; 2]),
        "i32.shl"   = I32Shl([Id; 2]),
        Symbol(Symbol),
    }
}
