# wasm benchmark suite: length vs solver time

Scripts to run SuperStack and ewasm on a benchmark suite, aggregate CSVs, and plot the
relationship between block length (`initial_length`) and solver time (`solver_time_in_sec`).

## Benchmark suites

| `--suite` | Source | Notes |
|---|---|---|
| `r3` | `../wasm-benchmarks/wasm-r3-bench/*.wasm` | External wasm-r3-bench (default) |
| `rosetta` | `benchmarks/rosetta/*.wasm` | Rosetta Code benchmarks in this repo |
| `rosetta-c-o0` | `benchmarks/rosetta_c/O0/*.wasm` | C sources compiled with wasi-clang `-O0` |
| `rosetta-c-o3` | `benchmarks/rosetta_c/O3/*.wasm` | C sources compiled with wasi-clang `-O3` |
| `wsouper` | `benchmarks/wsouper/*.wasm` | Souper benchmarks in this repo |

Results are written under `bench-results/<suite>/`.

## Prerequisites

- [uv](https://docs.astral.sh/uv/) installed
- ewasm: built automatically by `wasm-bench-run` (`cargo build --release`; use `--no-build` to skip)
- SuperStack: `cd ../superstack && python -m venv .venv && .venv/bin/pip install -r requirements.txt` (the runner uses that `.venv` automatically)
- For `r3` suite: wasm files in `../wasm-benchmarks/wasm-r3-bench/`
- For `rosetta-c-o0` / `rosetta-c-o3`: build with `make -C benchmarks/rosetta_c` (requires wasi-sdk)

## Setup

```bash
cd scripts
uv sync
```

## Usage

From the repository root:

```bash
# 1) Run benchmarks (SuperStack SAT + ewasm)
#  - sequence timeout: 300s
#  - timeout for each program: 3600s
uv run --project scripts wasm-bench-run --suite wsouper -j 25 --split 12 --segment-timeout 10 --timeout 1200 --only mux1_1,sign_test

# 2) Re-merge raw CSVs (optional; plot also auto-merges if combined_blocks.csv is missing)
uv run --project scripts wasm-bench-merge --suite wsouper

# 3) Plot (requires wasm-bench-run output; auto-merges raw/*.csv when combined_blocks.csv is absent)
uv run --project scripts wasm-bench-plot --suite wsouper
uv run --project scripts wasm-bench-plot --suite r3 --benchmark game-of-life --exclude ''
```

From inside `scripts/`, you can omit `--project scripts`:

```bash
cd scripts
uv run wasm-bench-run --help
```

Note: superstack only supports the following r3 benchmarks:
- factorial, ffmepg, game-of-life, hydro, jqkungfu, pathfinding, sandspiel


## Output

| File | Description |
|---|---|
| `bench-results/<suite>/raw/*.csv` | Per-benchmark, per-tool statistics |
| `bench-results/<suite>/combined_blocks.csv` | All block rows (with `tool`, `benchmark` columns) |
| `bench-results/<suite>/run_summary.csv` | Success/failure, wall-clock time, block count |
| `bench-results/<suite>/plots/*.png` | Solver time vs length; improvement (saved instructions) scatter, binned means, improvement rate, per-tool summary, and per-program instruction reduction (%) |
| `bench-results/<suite>/plots/summary_by_benchmark.csv` | Per-benchmark total instruction reduction (%) and block stats by tool |

## Caveats (comparison limits)

1. **ewasm type support** — i32/i64/f32/f64 pure arithmetic and conversions are optimized (A* peel + SAT tables). Side effects (memory, `call`, `global.*`) remain opaque / uninterpreted, like SuperStack; segment splitting continues across all value types.
2. **SuperStack greedy ≠ ewasm A\*** — `r3` / `rosetta` default to `superstack-greedy` (fast heuristic). `wsouper` defaults to `superstack` (SAT via `--ub-greedy`). ewasm uses A* shortest-path search by default; pass `--ewasm-solver sat` to use the descending Pure-SAT backend (CaDiCaL) instead. The SAT backend encodes side effects directly (SuperStack-style): memory/global/call/opaque ops become uninterpreted instructions with `storage` (exactly-once), at-most-once, and dependency-order (`deplist`) constraints, so there is no A* fallback. If a segment is too large to encode or cannot be improved, the original sequence is kept.
3. **Default split** — `wasm-bench-run` uses `--split 25` / `-sp 25` by default (ewasm CLI alone defaults to 10; SuperStack defaults to no splitting).
4. **Parallelism** — `-j` maps to ewasm `-j` and SuperStack `-j` for parallel block optimization.
5. **Segment timeout** — `--segment-timeout SECS` sets a fixed solver timeout per sequence/block for both ewasm and SuperStack (default: `10 × (1 + storage ops)`; SuperStack `-w` / ewasm `-w` use 300s).
6. **Large benchmarks** — `ffmpeg.wasm` has 300k+ blocks. Use `--exclude ffmpeg` when plotting the r3 suite.
7. **SuperStack wasm support** — SuperStack's bundled `pywasm` only supports MVP-ish wasm. Many r3 benchmarks (including `mandelbrot`) use bulk-memory (`0xfc` opcodes) or other extensions and fail with `section size mismatch` / `KeyError: 252`. ewasm uses its own parser and can still run them. Benchmarks that typically work with SuperStack: `factorial`, `game-of-life`, `hydro`, `jqkungfu`, `jsc`, `pathfinding`, `sandspiel`, `ffmpeg`.

---

# `--opt-locals` benchmark suite

Scripts to run ewasm `--opt-locals` on `benchmarks/` wasm files, aggregate per-function CSVs, and plot per-program reduction.

Results are written under `bench-results/locals-<suite>/`.

## Usage

```bash
# 1) Run --opt-locals on all wsouper benchmarks
uv run --project scripts wasm-locals-run --suite wsouper -j 20 --locals-timeout-ms 3000

# Quick smoke test on a few programs
uv run --project scripts wasm-locals-run --suite rosetta-c-o3 --only addition_chains,banker -j 4

# 2) Re-merge raw CSVs (optional; plot auto-merges when combined_functions.csv is missing)
uv run --project scripts wasm-locals-merge --suite wsouper

# 3) Plot per-program reduction
uv run --project scripts wasm-locals-plot --suite wsouper
```

## Output (`bench-results/locals-<suite>/`)

| File | Description |
|---|---|
| `raw/<benchmark>.csv` | Per-function statistics from ewasm `-c` |
| `raw/<benchmark>.log` | Full stdout/stderr from ewasm |
| `combined_functions.csv` | All function rows (with `benchmark` column) |
| `module_summary.csv` | Per-benchmark totals (instr/locals saved, status counts, solver time) |
| `plots/reduction_pct_by_program.png` | Bar chart: instruction/local reduction **rate (%)** per program, with absolute counts annotated |
| `plots/reduction_summary.txt` | Text table: per-program instr/locals saved (absolute) and reduction (%) |
| `plots/copies_removed_by_program.png` | Self-copy removal rate (%) per program, with absolute count annotated |
| `plots/function_status_by_program.png` | Stacked bar: improved / unchanged / timeout / skipped |
| `plots/solver_time_vs_webs.png` | Scatter: solver time vs web count (per function) |
| `plots/summary_by_benchmark.csv` | Copy of module summary used for plots |

## Notes

- Reduction is measured in **instruction count** and **local slot count** (not Wasm byte size yet).
- Default per-function solver timeout is 30s (`--locals-timeout-ms`).
- Use `--suite rosetta`, `--suite rosetta-c-o0`, `--suite rosetta-c-o3`, or `--suite wsouper` for in-repo benchmarks under `benchmarks/`.
