#!/usr/bin/env python3
"""Merge raw per-benchmark CSVs into one combined_blocks.csv."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_RAW = _REPO_ROOT / "bench-results/r3/raw"
DEFAULT_OUT = _REPO_ROOT / "bench-results/r3/combined_blocks.csv"


def infer_meta(path: Path) -> tuple[str, str]:
    name = path.stem
    if name.startswith("ewasm-"):
        return "ewasm", name.removeprefix("ewasm-")
    if name.startswith("superstack-greedy-"):
        return "superstack-greedy", name.removeprefix("superstack-greedy-")
    if name.startswith("superstack-sat-"):
        return "superstack-sat", name.removeprefix("superstack-sat-")
    raise ValueError(f"unrecognized csv name: {path.name}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-dir", type=Path, default=DEFAULT_RAW)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--benchmark", action="append", help="Include only these benchmarks")
    parser.add_argument("--exclude", action="append", help="Exclude these benchmarks")
    args = parser.parse_args()

    rows: list[dict[str, str]] = []
    for csv_path in sorted(args.raw_dir.glob("*.csv")):
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

    args.out.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = sorted({k for row in rows for k in row})
    with args.out.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    print(f"wrote {args.out} ({len(rows)} rows)")
    return 0


def cli() -> None:
    raise SystemExit(main())


if __name__ == "__main__":
    cli()
