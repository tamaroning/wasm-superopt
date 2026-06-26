# wasm-r3-bench: length vs solver time

Scripts to run SuperStack and ewasm on wasm-r3-bench, aggregate CSVs, and plot the
relationship between block length (`initial_length`) and solver time (`solver_time_in_sec`).

## Prerequisites

- [uv](https://docs.astral.sh/uv/) installed
- ewasm: `cargo build --release`
- SuperStack: `cd ../superstack && python -m venv .venv && .venv/bin/pip install -r requirements.txt` (the runner uses that `.venv` automatically)
- Benchmarks: `/home/tamaron/work/wasm-benchmarks/wasm-r3-bench/*.wasm`

## Setup

```bash
cd scripts
uv sync
```

## Usage

From the repository root:

```bash
# 1) Run benchmarks (SuperStack SAT + ewasm, both with split width 10)
uv run --project scripts r3-run-benchmarks \
  --tools superstack ewasm \
  --split 10 \
  --only factorial \
  -j 28 \
  --timeout 600 \
  --out-dir bench-results/r3

# 2) Re-merge raw CSVs (example: exclude huge benchmarks like ffmpeg)
uv run --project scripts r3-merge-csvs --exclude ffmpeg

# 3) Plot
uv run --project scripts r3-plot --exclude ffmpeg
uv run --project scripts r3-plot --benchmark game-of-life --exclude ''
```

From inside `scripts/`, you can omit `--project scripts`:

```bash
cd scripts
uv run r3-run-benchmarks --help
```

Note: superstack only supports the following benchmarks:
- factorial, ffmepg, game-of-life, hydro, jqkungfu, pathfinding, sandspiel


## Output

| File | Description |
|---|---|
| `bench-results/r3/raw/*.csv` | Per-benchmark, per-tool statistics |
| `bench-results/r3/combined_blocks.csv` | All block rows (with `tool`, `benchmark` columns) |
| `bench-results/r3/run_summary.csv` | Success/failure, wall-clock time, block count |
| `bench-results/r3/plots/*.png` | Scatter plots and binned mean ± std dev |

## Caveats (comparison limits)

1. **ewasm type support** — i32 arithmetic is optimized with A*. i64/f32/f64 locals and instructions are parsed as symbolic execution (`opaque`), like SuperStack; segment splitting continues. Only i32 is optimized.
2. **SuperStack greedy ≠ ewasm A\*** — SuperStack here uses `--greedy` (fast heuristic). ewasm uses A* shortest-path search. Add `--tools superstack-sat` for SAT comparison.
3. **Default split** — Both use `--split 10` / `-sp 10` (ewasm default is 10; SuperStack default is no splitting).
4. **Parallelism** — `-j` maps to ewasm `-j` and SuperStack `-j` for parallel block optimization.
5. **Large benchmarks** — `ffmpeg.wasm` has 300k+ blocks. Use `--exclude ffmpeg` when plotting.
6. **SuperStack wasm support** — SuperStack's bundled `pywasm` only supports MVP-ish wasm. Many r3 benchmarks (including `mandelbrot`) use bulk-memory (`0xfc` opcodes) or other extensions and fail with `section size mismatch` / `KeyError: 252`. ewasm uses its own parser and can still run them. Benchmarks that typically work with SuperStack: `factorial`, `game-of-life`, `hydro`, `jqkungfu`, `jsc`, `pathfinding`, `sandspiel`, `ffmpeg`.
