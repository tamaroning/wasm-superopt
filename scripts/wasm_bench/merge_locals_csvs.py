#!/usr/bin/env python3
"""Merge raw per-benchmark locals CSVs into combined_functions.csv and module_summary.csv."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

from wasm_bench.run_locals_benchmarks import summarize_module
from wasm_bench.suites import SUITE_NAMES, locals_combined_functions_csv, locals_out_dir, locals_raw_dir


def collect_function_rows(
    raw_dir_path: Path,
    *,
    benchmark: list[str] | None = None,
    exclude: list[str] | None = None,
) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    if not raw_dir_path.is_dir():
        return rows
    for csv_path in sorted(raw_dir_path.glob("*.csv")):
        bench = csv_path.stem
        if benchmark and bench not in benchmark:
            continue
        if exclude and bench in exclude:
            continue
        with csv_path.open(newline="") as f:
            reader = csv.DictReader(f)
            for row in reader:
                row["benchmark"] = bench
                rows.append(row)
    return rows


def write_csv(path: Path, rows: list[dict[str, str | int | float]], fieldnames: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def merge_locals_csvs(
    suite: str,
    *,
    raw_dir_path: Path | None = None,
    out_dir_path: Path | None = None,
    benchmark: list[str] | None = None,
    exclude: list[str] | None = None,
    locals_timeout_ms: int = 30_000,
    jobs: int = 1,
) -> tuple[Path, Path, int]:
    raw_dir_path = raw_dir_path or locals_raw_dir(suite)
    out_dir_path = out_dir_path or locals_out_dir(suite)
    function_rows = collect_function_rows(raw_dir_path, benchmark=benchmark, exclude=exclude)
    combined_path = out_dir_path / "combined_functions.csv"
    summary_path = out_dir_path / "module_summary.csv"

    if not function_rows:
        return combined_path, summary_path, 0

    combined_fieldnames = sorted({k for row in function_rows for k in row})
    write_csv(combined_path, function_rows, combined_fieldnames)

    by_benchmark: dict[str, list[dict[str, str]]] = {}
    for row in function_rows:
        by_benchmark.setdefault(row["benchmark"], []).append(row)

    module_rows: list[dict[str, str | int | float]] = []
    for bench, rows in sorted(by_benchmark.items()):
        wasm_path = raw_dir_path / f"{bench}.wasm"
        if not wasm_path.exists():
            wasm_path = Path()
        module_rows.append(
            summarize_module(
                bench,
                wasm_path,
                rows,
                status="ok",
                wall_time_sec=0.0,
                locals_timeout_ms=locals_timeout_ms,
                jobs=jobs,
            )
        )

    summary_fieldnames = [
        "benchmark",
        "status",
        "wall_time_sec",
        "wasm_bytes",
        "locals_timeout_ms",
        "jobs",
        "functions",
        "functions_improved",
        "functions_unchanged",
        "functions_timeout",
        "functions_skipped",
        "instr_before",
        "instr_after",
        "instr_saved",
        "instr_reduction_pct",
        "local_slots_before",
        "local_slots_after",
        "local_slots_saved",
        "local_slots_reduction_pct",
        "copies_removed",
        "solver_time_secs",
        "webs_total",
        "interferes_total",
        "bb_count_total",
        "h4_clauses_total",
    ]
    write_csv(summary_path, module_rows, summary_fieldnames)
    return combined_path, summary_path, len(function_rows)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--suite",
        choices=SUITE_NAMES,
        default="wsouper",
        help="Benchmark suite whose results to merge (default: wsouper)",
    )
    parser.add_argument("--raw-dir", type=Path, default=None)
    parser.add_argument("--out-dir", type=Path, default=None)
    parser.add_argument("--benchmark", action="append")
    parser.add_argument("--exclude", action="append")
    args = parser.parse_args()

    combined_path, summary_path, count = merge_locals_csvs(
        args.suite,
        raw_dir_path=args.raw_dir,
        out_dir_path=args.out_dir,
        benchmark=args.benchmark,
        exclude=args.exclude,
    )
    if count == 0:
        print("no rows")
        return 1

    print(f"wrote {combined_path} ({count} function rows)")
    print(f"wrote {summary_path}")
    return 0


def cli() -> None:
    raise SystemExit(main())


if __name__ == "__main__":
    cli()
