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


def collect_raw_rows(
    raw_dir_path: Path,
    *,
    benchmark: list[str] | None = None,
    exclude: list[str] | None = None,
) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    if not raw_dir_path.is_dir():
        return rows
    for csv_path in sorted(raw_dir_path.glob("*.csv")):
        tool, bench = infer_meta(csv_path)
        if benchmark and bench not in benchmark:
            continue
        if exclude and bench in exclude:
            continue
        with csv_path.open(newline="") as f:
            reader = csv.DictReader(f)
            for row in reader:
                row["tool"] = tool
                row["benchmark"] = bench
                rows.append(row)
    return rows


def write_combined_csv(out_path: Path, rows: list[dict[str, str]]) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = sorted({k for row in rows for k in row})
    with out_path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def merge_raw_csvs(
    suite: str,
    *,
    raw_dir_path: Path | None = None,
    out_path: Path | None = None,
    benchmark: list[str] | None = None,
    exclude: list[str] | None = None,
) -> tuple[Path, int]:
    raw_dir_path = raw_dir_path or raw_dir(suite)
    out_path = out_path or combined_csv(suite)
    rows = collect_raw_rows(raw_dir_path, benchmark=benchmark, exclude=exclude)
    if not rows:
        return out_path, 0
    write_combined_csv(out_path, rows)
    return out_path, len(rows)


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

    out_path, count = merge_raw_csvs(
        args.suite,
        raw_dir_path=args.raw_dir,
        out_path=args.out,
        benchmark=args.benchmark,
        exclude=args.exclude,
    )
    if count == 0:
        print("no rows")
        return 1

    print(f"wrote {out_path} ({count} rows)")
    return 0


def cli() -> None:
    raise SystemExit(main())


if __name__ == "__main__":
    cli()
