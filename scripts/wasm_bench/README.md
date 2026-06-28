# wasm benchmark suite: length vs solver time

Scripts to run SuperStack and ewasm on a benchmark suite, aggregate CSVs, and plot the
relationship between block length (`initial_length`) and solver time (`solver_time_in_sec`).

## Benchmark suites

| `--suite` | Source | Notes |
|---|---|---|
| `r3` | `../wasm-benchmarks/wasm-r3-bench/*.wasm` | External wasm-r3-bench (default) |
| `rosetta` | `benchmarks/rosetta/*.wasm` | Rosetta Code benchmarks in this repo |
| `wsouper` | `benchmarks/wsouper/*.wasm` | Souper benchmarks in this repo |

Results are written under `bench-results/<suite>/`.

## Prerequisites

- [uv](https://docs.astral.sh/uv/) installed
- ewasm: `cargo build --release`
- SuperStack: `cd ../superstack && python -m venv .venv && .venv/bin/pip install -r requirements.txt` (the runner uses that `.venv` automatically)
- For `r3` suite: wasm files in `../wasm-benchmarks/wasm-r3-bench/`

## Setup

```bash
cd scripts
uv sync
```

## Usage

From the repository root:

```bash
# 1) Run benchmarks (SuperStack SAT + ewasm; default split width 15)
uv run --project scripts wasm-bench-run \
  --suite r3 \
  --tools superstack ewasm \
  --only factorial \
  -j 28 \
  --timeout 600

# Rosetta benchmarks
uv run --project scripts wasm-bench-run --suite rosetta -j 8

# Souper benchmarks
uv run --project scripts wasm-bench-run --suite wsouper --only mimc_test

# 2) Re-merge raw CSVs (example: exclude huge benchmarks like ffmpeg on r3)
uv run --project scripts wasm-bench-merge --suite r3 --exclude ffmpeg

# 3) Plot
uv run --project scripts wasm-bench-plot --suite r3 --exclude ffmpeg
uv run --project scripts wasm-bench-plot --suite rosetta
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
| `bench-results/<suite>/plots/*.png` | Scatter plots and binned mean ± std dev |

## Caveats (comparison limits)

1. **ewasm type support** — i32 arithmetic is optimized with A*. i64/f32/f64 locals and instructions are parsed as symbolic execution (`opaque`), like SuperStack; segment splitting continues. Only i32 is optimized.
2. **SuperStack greedy ≠ ewasm A\*** — SuperStack here uses `--greedy` (fast heuristic). ewasm uses A* shortest-path search. Add `--tools superstack-sat` for SAT comparison.
3. **Default split** — `wasm-bench-run` uses `--split 15` / `-sp 15` by default (ewasm CLI alone defaults to 10; SuperStack defaults to no splitting).
4. **Parallelism** — `-j` maps to ewasm `-j` and SuperStack `-j` for parallel block optimization.
5. **Large benchmarks** — `ffmpeg.wasm` has 300k+ blocks. Use `--exclude ffmpeg` when plotting the r3 suite.
6. **SuperStack wasm support** — SuperStack's bundled `pywasm` only supports MVP-ish wasm. Many r3 benchmarks (including `mandelbrot`) use bulk-memory (`0xfc` opcodes) or other extensions and fail with `section size mismatch` / `KeyError: 252`. ewasm uses its own parser and can still run them. Benchmarks that typically work with SuperStack: `factorial`, `game-of-life`, `hydro`, `jqkungfu`, `jsc`, `pathfinding`, `sandspiel`, `ffmpeg`.
