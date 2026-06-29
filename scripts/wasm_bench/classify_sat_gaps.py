#!/usr/bin/env python3
"""Classify ewasm SAT gaps vs SuperStack (parallel via ewasm -j)."""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

from wasm_bench.suites import SUITE_NAMES, combined_csv, resolve_suite

_REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_EWASM = _REPO_ROOT / "target/release/ewasm"


def cli() -> None:
    parser = argparse.ArgumentParser(
        description="Classify SAT failure modes where SuperStack improved but ewasm did not"
    )
    parser.add_argument("--suite", choices=SUITE_NAMES, default="wsouper")
    parser.add_argument("--only", metavar="NAME", help="Single benchmark stem (e.g. mux1_1)")
    parser.add_argument("-j", "--jobs", type=int, default=8, help="Parallel diagnose jobs (default: 8)")
    parser.add_argument("--split", type=int, default=12, help="Segment split width (default: 12)")
    parser.add_argument(
        "--segment-timeout",
        type=int,
        default=10,
        help="Per-segment SAT timeout in seconds (default: 10)",
    )
    parser.add_argument(
        "--ewasm",
        type=Path,
        default=DEFAULT_EWASM,
        help="Path to ewasm binary",
    )
    parser.add_argument(
        "--combined-csv",
        type=Path,
        help="combined_blocks.csv (default: bench-results/<suite>/combined_blocks.csv)",
    )
    parser.add_argument("--no-build", action="store_true", help="Skip cargo build --release")
    args = parser.parse_args()

    suite = resolve_suite(args.suite)
    combined = args.combined_csv or combined_csv(args.suite)
    if not combined.is_file():
        print(f"error: {combined} not found (run wasm-bench-run first)", file=sys.stderr)
        sys.exit(1)

    benchmarks = sorted(suite.bench_dir.glob("*.wasm"))
    if args.only:
        benchmarks = [b for b in benchmarks if b.stem == args.only]
        if not benchmarks:
            print(f"error: benchmark {args.only!r} not in suite {args.suite}", file=sys.stderr)
            sys.exit(1)

    if not args.no_build:
        subprocess.run(["cargo", "build", "--release"], cwd=_REPO_ROOT, check=True)

    for bench in benchmarks:
        wasm = bench
        cmd = [
            str(args.ewasm),
            str(wasm),
            "--classify-sat-gaps",
            str(combined),
            "--solver",
            "sat",
            "--split",
            str(args.split),
            "--segment-timeout",
            str(args.segment_timeout),
            "-j",
            str(args.jobs),
        ]
        print(f">> {' '.join(cmd)}", flush=True)
        subprocess.run(cmd, cwd=_REPO_ROOT, check=True)


if __name__ == "__main__":
    cli()
