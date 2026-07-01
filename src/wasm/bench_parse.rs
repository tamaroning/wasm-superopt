//! Integration timing checks for large benchmarks.

#[cfg(test)]
mod tests {
    use crate::wasm::{materialize_segments, parse_wasm_file, split_raw_segments};
    use std::time::Instant;

    #[test]
    fn mux1_1_fast_parse_is_subsecond() {
        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        let t0 = Instant::now();
        let info = parse_wasm_file(path).expect("parse mux1_1");
        let elapsed = t0.elapsed();
        eprintln!(
            "mux1_1 fast parse: {:.3}s, {} raw segments",
            elapsed.as_secs_f64(),
            info.segments.len()
        );
        assert!(elapsed.as_secs_f32() < 1.0, "fast parse took {:?}", elapsed);
    }

    #[test]
    fn mux1_1_split_materialize_is_fast() {
        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        let info = parse_wasm_file(path).expect("parse");
        let raw = split_raw_segments(&info.segments, 10);
        let t0 = Instant::now();
        let segs = materialize_segments(&raw, 20);
        eprintln!(
            "mux1_1 split+materialize (split=10, j=20): {:.2}s -> {} chunks",
            t0.elapsed().as_secs_f64(),
            segs.len()
        );
        assert!(t0.elapsed().as_secs_f32() < 30.0, "took {:?}", t0.elapsed());
        assert!(segs.len() > info.segments.len());
    }
}
