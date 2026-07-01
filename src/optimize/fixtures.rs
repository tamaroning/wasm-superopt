//! Parsed `examples/example.wat` / `example-opt.wat` for unit tests (idea.md §12).

use crate::sym::SymState;
use crate::wasm::{StraightSegment, materialize_segments, parse_wasm_bytes};
use std::sync::OnceLock;

const BLOATED_WAT: &str = include_str!("../../examples/example.wat");
const OPT_WAT: &str = include_str!("../../examples/example-opt.wat");

fn bloated_segment() -> &'static StraightSegment {
    static SEG: OnceLock<StraightSegment> = OnceLock::new();
    SEG.get_or_init(|| {
        let wasm = wat::parse_str(BLOATED_WAT).expect("examples/example.wat must parse");
        let info = parse_wasm_bytes(&wasm).expect("examples/example.wat must yield wasm");
        assert_eq!(info.segments.len(), 1);
        materialize_segments(&info.segments, 1)
            .into_iter()
            .next()
            .unwrap()
    })
}

fn canonical_fin() -> &'static SymState {
    static FIN: OnceLock<SymState> = OnceLock::new();
    FIN.get_or_init(|| {
        let wasm = wat::parse_str(OPT_WAT).expect("examples/example-opt.wat must parse");
        let info = parse_wasm_bytes(&wasm).expect("examples/example-opt.wat must yield wasm");
        assert_eq!(info.segments.len(), 1);
        materialize_segments(&info.segments, 1)[0].fin.clone()
    })
}

pub fn init() -> SymState {
    bloated_segment().init.clone()
}

pub fn fin() -> SymState {
    canonical_fin().clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::parse_value_expr;

    #[test]
    fn running_example_fin_local_uses_const_shift() {
        let fin = fin();
        let local0 = fin
            .locals
            .get(&0)
            .and_then(|req| match req {
                crate::sym::LocalReq::Need(v) => Some(v.to_string()),
                _ => None,
            })
            .expect("local 0");
        let expected = parse_value_expr("(i32.shl ?L0 1)").to_string();
        assert_eq!(local0, expected, "example-opt local 0");
    }
}
