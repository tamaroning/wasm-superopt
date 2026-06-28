#!/usr/bin/env python3
"""Merge raw per-benchmark CSVs into one combined_blocks.csv."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

from wasm_bench.suites import SUITE_NAMES, combined_csv, raw_dir


def infer_meta(path: Path) -> tuple[str, str]:
    name = path.stem
    if name.startswith("ewasm-"):
        return "ewasm", name.removeprefix("ewasm-")
    if name.startswith("superstack-greedy-"):
        return "superstack-greedy", name.removeprefix("superstack-greedy-")
    if name.startswith("superstack-sat-"):
        return "superstack-sat", name.removeprefix("superstack-sat-")
    if name.startswith("superstack-"):
        return "superstack", name.removeprefix("superstack-")
    raise ValueError(f"unrecognized csv name: {path.name}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--suite",
        choices=SUITE_NAMES,
        default="r3",
        help="Benchmark suite whose results to merge (default: r3)",
    )
    parser.add_argument(
        "--raw-dir",
        type=Path,
        default=None,
        help="Directory with per-benchmark CSVs (default: bench-results/<suite>/raw)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output CSV path (default: bench-results/<suite>/combined_blocks.csv)",
    )
    parser.add_argument("--benchmark", action="append", help="Include only these benchmarks")
    parser.add_argument("--exclude", action="append", help="Exclude these benchmarks")
    args = parser.parse_args()

    raw_dir_path = args.raw_dir or raw_dir(args.suite)
    out_path = args.out or combined_csv(args.suite)

    rows: list[dict[str, str]] = []
    for csv_path in sorted(raw_dir_path.glob("*.csv")):
        tool, benchmark = infer_meta(csv_path)
        if args.benchmark and benchmark not in args.benchmark:
            continue
        if args.exclude and benchmark in args.exclude:
            continue
        with csv_path.open(newline="") as f:
            reader = csv.DictReader(f)
            for row in reader:
                row["tool"] = tool
                row["benchmark"] = benchmark
                rows.append(row)

    if not rows:
        print("no rows")
        return 1

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = sorted({k for row in rows for k in row})
    with out_path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    print(f"wrote {out_path} ({len(rows)} rows)")
    return 0


def cli() -> None:
    raise SystemExit(main())


if __name__ == "__main__":
    cli()
