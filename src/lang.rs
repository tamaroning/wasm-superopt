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
        "i32.rem_u" = I32RemU([Id; 2]),
        "i32.rem_s" = I32RemS([Id; 2]),
        "i32.shl"   = I32Shl([Id; 2]),
        "i32.and"   = I32And([Id; 2]),
        "i32.or"    = I32Or([Id; 2]),
        "i32.xor"   = I32Xor([Id; 2]),
        "i32.shr_u" = I32ShrU([Id; 2]),
        "i32.shr_s" = I32ShrS([Id; 2]),
        "i32.rotl"  = I32Rotl([Id; 2]),
        "i32.rotr"  = I32Rotr([Id; 2]),
        "i32.eq"    = I32Eq([Id; 2]),
        "i32.ne"    = I32Ne([Id; 2]),
        "i32.lt_s"  = I32LtS([Id; 2]),
        "i32.le_s"  = I32LeS([Id; 2]),
        "i32.gt_s"  = I32GtS([Id; 2]),
        "i32.eqz"   = I32Eqz([Id; 1]),
        "i32.clz"   = I32Clz([Id; 1]),
        "i32.ctz"   = I32Ctz([Id; 1]),
        "i32.popcnt" = I32Popcnt([Id; 1]),
        Symbol(Symbol),
    }
}
