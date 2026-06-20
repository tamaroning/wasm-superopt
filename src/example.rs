//! Running example from [`examples/example.wat`](../examples/example.wat) (idea.md §12).

use crate::goal::MachineState;
use crate::wasm::{parse_wasm_bytes, StraightSegment};
use std::sync::OnceLock;

const BLOATED_WAT: &str = include_str!("../examples/example.wat");
const OPT_WAT: &str = include_str!("../examples/example-opt.wat");

fn bloated_segment() -> &'static StraightSegment {
    static SEG: OnceLock<StraightSegment> = OnceLock::new();
    SEG.get_or_init(|| {
        let wasm = wat::parse_str(BLOATED_WAT).expect("examples/example.wat must parse");
        let info = parse_wasm_bytes(&wasm).expect("examples/example.wat must yield wasm");
        assert_eq!(
            info.segments.len(),
            1,
            "examples/example.wat must be one straight-line segment"
        );
        info.segments.into_iter().next().unwrap()
    })
}

fn canonical_fin() -> &'static MachineState {
    static FIN: OnceLock<MachineState> = OnceLock::new();
    FIN.get_or_init(|| {
        let wasm = wat::parse_str(OPT_WAT).expect("examples/example-opt.wat must parse");
        let info = parse_wasm_bytes(&wasm).expect("examples/example-opt.wat must yield wasm");
        assert_eq!(info.segments.len(), 1);
        info.segments[0].fin.clone()
    })
}

pub fn init() -> MachineState {
    bloated_segment().init.clone()
}

/// Canonical `fin` from the optimal sequence (not the bloated forward state).
pub fn fin() -> MachineState {
    canonical_fin().clone()
}

/// Bloated input segment used for end-to-end optimization demos.
pub fn segment() -> &'static StraightSegment {
    bloated_segment()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn init_fin_within_bounds() {
        assert!(init().validate_bounds());
        assert!(fin().validate_bounds());
    }

    #[test]
    fn bloated_input_is_longer_than_optimal() {
        assert!(segment().original_len() > 7);
    }
}
