#!/usr/bin/env python3
"""Run ewasm --opt-locals on a benchmark suite and collect per-function CSVs."""

from __future__ import annotations

import argparse
import csv
import subprocess
import sys
from pathlib import Path

from rich.console import Console
from rich.table import Table

from wasm_bench.progress import BenchmarkRunnerUI, RunState, run_cmd_plain, run_cmd_tracked
from wasm_bench.suites import SUITE_NAMES, locals_out_dir, resolve_suite

_REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_EWASM = _REPO_ROOT / "target/release/ewasm"


def _format_cmd(cmd: list[str]) -> str:
    return " ".join(f'"{part}"' if " " in part else part for part in cmd)


def _parse_only_names(values: list[str] | None) -> set[str] | None:
    if not values:
        return None
    names: set[str] = set()
    for value in values:
        for part in value.split(","):
            part = part.strip()
            if part:
                names.add(part)
    return names or None


def build_ewasm(*, console: Console, plain: bool) -> int:
    cmd = ["cargo", "build", "--release"]
    label = _format_cmd(cmd)
    if plain:
        print(f">> {label}", flush=True)
    else:
        console.print(f"[bold]Building ewasm[/] ({label})")
    proc = subprocess.run(cmd, cwd=_REPO_ROOT)
    if proc.returncode != 0:
        console.print("[red]cargo build --release failed[/]")
        return proc.returncode
    if not plain:
        console.print("[green]ewasm built successfully[/]")
    return 0


def read_function_rows(path: Path, benchmark: str) -> list[dict[str, str]]:
    if not path.exists():
        return []
    with path.open(newline="") as f:
        reader = csv.DictReader(f)
        rows = []
        for row in reader:
            row["benchmark"] = benchmark
            rows.append(row)
        return rows


def summarize_module(
    benchmark: str,
    wasm_path: Path,
    function_rows: list[dict[str, str]],
    *,
    status: str,
    wall_time_sec: float,
    locals_timeout_ms: int,
    jobs: int,
) -> dict[str, str | int | float]:
    numeric_fields = (
        "instr_before",
        "instr_after",
        "instr_saved",
        "local_slots_before",
        "local_slots_after",
        "local_slots_saved",
        "copies_removed",
        "webs",
        "interferes",
        "bb_count",
        "h4_clauses",
        "solver_time_secs",
    )
    totals = {field: 0 for field in numeric_fields}
    counts = {
        "functions": len(function_rows),
        "functions_improved": 0,
        "functions_unchanged": 0,
        "functions_timeout": 0,
        "functions_skipped": 0,
    }
    for row in function_rows:
        for field in numeric_fields:
            totals[field] += int(float(row.get(field, 0) or 0))
        status_label = row.get("status", "")
        if status_label == "improved":
            counts["functions_improved"] += 1
        elif status_label == "unchanged":
            counts["functions_unchanged"] += 1
        elif status_label == "timeout":
            counts["functions_timeout"] += 1
        else:
            counts["functions_skipped"] += 1

    instr_before = totals["instr_before"]
    instr_saved = totals["instr_saved"]
    local_before = totals["local_slots_before"]
    local_saved = totals["local_slots_saved"]
    instr_reduction_pct = (100.0 * instr_saved / instr_before) if instr_before > 0 else 0.0
    local_slots_reduction_pct = (100.0 * local_saved / local_before) if local_before > 0 else 0.0

    return {
        "benchmark": benchmark,
        "status": status,
        "wall_time_sec": round(wall_time_sec, 3),
        "wasm_bytes": wasm_path.stat().st_size if wasm_path.exists() else 0,
        "locals_timeout_ms": locals_timeout_ms,
        "jobs": jobs,
        "functions": counts["functions"],
        "functions_improved": counts["functions_improved"],
        "functions_unchanged": counts["functions_unchanged"],
        "functions_timeout": counts["functions_timeout"],
        "functions_skipped": counts["functions_skipped"],
        "instr_before": totals["instr_before"],
        "instr_after": totals["instr_after"],
        "instr_saved": totals["instr_saved"],
        "instr_reduction_pct": round(instr_reduction_pct, 4),
        "local_slots_before": totals["local_slots_before"],
        "local_slots_after": totals["local_slots_after"],
        "local_slots_saved": totals["local_slots_saved"],
        "local_slots_reduction_pct": round(local_slots_reduction_pct, 4),
        "copies_removed": totals["copies_removed"],
        "solver_time_secs": round(totals["solver_time_secs"], 3),
        "webs_total": totals["webs"],
        "interferes_total": totals["interferes"],
        "bb_count_total": totals["bb_count"],
        "h4_clauses_total": totals["h4_clauses"],
    }


def run_opt_locals(
    ewasm_bin: Path,
    wasm: Path,
    csv_path: Path,
    jobs: int,
    locals_timeout_ms: int,
    locals_limit: int,
    timeout: int,
    *,
    ui: BenchmarkRunnerUI | None = None,
) -> tuple[str, str, float]:
    cmd = [
        str(ewasm_bin),
        str(wasm),
        "--opt-locals",
        "-j",
        str(jobs),
        "--locals-timeout-ms",
        str(locals_timeout_ms),
        "-c",
        str(csv_path),
    ]
    if locals_limit > 0:
        cmd.extend(["--locals-limit", str(locals_limit)])
    if ui is not None:
        code, output, elapsed = run_cmd_tracked(cmd, timeout=timeout, ui=ui)
    else:
        code, output, elapsed = run_cmd_plain(cmd, timeout=timeout)
    if code == 124:
        status = "timeout"
    elif code != 0 or "error parsing" in output or "error:" in output:
        status = "error"
    elif csv_path.exists():
        status = "ok"
    else:
        status = "error"
    return status, output, elapsed


def _print_summary_table(console: Console, rows: list[dict[str, str | float | int]]) -> None:
    table = Table(title="Local allocation run summary")
    table.add_column("benchmark")
    table.add_column("status")
    table.add_column("instr Δ", justify="right")
    table.add_column("locals Δ", justify="right")
    table.add_column("copies", justify="right")
    table.add_column("time (s)", justify="right")
    for row in rows:
        table.add_row(
            str(row["benchmark"]),
            str(row["status"]),
            str(row["instr_saved"]),
            str(row["local_slots_saved"]),
            str(row["copies_removed"]),
            f"{row['wall_time_sec']:.1f}",
        )
    console.print(table)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--suite",
        choices=SUITE_NAMES,
        default="wsouper",
        help="Benchmark suite to run (default: wsouper)",
    )
    parser.add_argument(
        "--bench-dir",
        type=Path,
        default=None,
        help="Override benchmark directory (default: suite-specific path)",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=None,
        help="Output directory (default: bench-results/locals-<suite>)",
    )
    parser.add_argument("--ewasm", type=Path, default=DEFAULT_EWASM)
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=1,
        help="Parallel jobs for per-function optimization (default: 1)",
    )
    parser.add_argument(
        "--locals-timeout-ms",
        type=int,
        default=30_000,
        help="Per-function solver timeout in milliseconds (default: 30000)",
    )
    parser.add_argument(
        "--locals-limit",
        type=int,
        default=0,
        help="Maximum functions to optimize per module (0 = all)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=3600,
        help="Per-benchmark wall-clock timeout in seconds (default: 3600)",
    )
    parser.add_argument("--limit", type=int, default=0, help="Limit number of wasm files (0 = all)")
    parser.add_argument(
        "--only",
        nargs="*",
        metavar="NAME",
        help="Run only these benchmark basenames (comma- or space-separated)",
    )
    parser.add_argument(
        "--plain",
        action="store_true",
        help="Plain text output (no rich progress UI; streams subprocess output)",
    )
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="Skip automatic `cargo build --release` before running ewasm",
    )
    args = parser.parse_args()

    suite = resolve_suite(args.suite)
    bench_dir = args.bench_dir or suite.bench_dir
    out_dir_path = args.out_dir or locals_out_dir(args.suite)
    console = Console(stderr=True)

    if not bench_dir.is_dir():
        console.print(f"[red]benchmark directory not found:[/] {bench_dir}")
        return 1

    out_dir_path.mkdir(parents=True, exist_ok=True)
    raw_dir = out_dir_path / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)
    (out_dir_path / ".keep").touch()

    wasm_files = sorted(bench_dir.glob("*.wasm"))
    only = _parse_only_names(args.only)
    if only:
        wasm_files = [p for p in wasm_files if p.stem in only]
    if args.limit:
        wasm_files = wasm_files[: args.limit]

    if not wasm_files:
        console.print(f"[red]no .wasm files found in[/] {bench_dir}")
        return 1

    if not args.no_build:
        build_code = build_ewasm(console=console, plain=args.plain)
        if build_code != 0:
            return build_code

    console.print(f"[bold]Suite:[/] {suite.label} ({bench_dir})")
    console.print(f"[bold]Output:[/] {out_dir_path}")
    console.print(f"[bold]Runs:[/] {len(wasm_files)} wasm module(s)")

    module_rows: list[dict[str, str | float | int]] = []
    combined_rows: list[dict[str, str]] = []

    ui = None if args.plain else BenchmarkRunnerUI(console)
    if ui is not None:
        ui.start()

    try:
        for bench_index, wasm in enumerate(wasm_files, start=1):
            benchmark = wasm.stem
            if ui is not None:
                ui.begin_run(
                    RunState(
                        suite=suite.name,
                        benchmark=benchmark,
                        tool="opt-locals",
                        benchmark_index=bench_index,
                        benchmark_total=len(wasm_files),
                        run_index=bench_index,
                        run_total=len(wasm_files),
                    )
                )
            elif args.plain:
                print(f"\n=== {benchmark} ({bench_index}/{len(wasm_files)}) ===", flush=True)

            csv_path = raw_dir / f"{benchmark}.csv"
            cmd = [
                str(args.ewasm),
                str(wasm),
                "--opt-locals",
                "-j",
                str(args.jobs),
                "--locals-timeout-ms",
                str(args.locals_timeout_ms),
                "-c",
                str(csv_path),
            ]
            if args.locals_limit > 0:
                cmd.extend(["--locals-limit", str(args.locals_limit)])
            if args.plain:
                print(f"  >> {_format_cmd(cmd)}", flush=True)

            status, output, elapsed = run_opt_locals(
                args.ewasm,
                wasm,
                csv_path,
                args.jobs,
                args.locals_timeout_ms,
                args.locals_limit,
                args.timeout,
                ui=ui,
            )

            if ui is not None:
                ui.finish_run(status)
            elif args.plain:
                print(f"  << opt-locals: {status} ({elapsed:.1f}s)", flush=True)

            log_path = raw_dir / f"{benchmark}.log"
            log_path.write_text(output)
            function_rows = read_function_rows(csv_path, benchmark)
            combined_rows.extend(function_rows)
            module_rows.append(
                summarize_module(
                    benchmark,
                    wasm,
                    function_rows,
                    status=status,
                    wall_time_sec=elapsed,
                    locals_timeout_ms=args.locals_timeout_ms,
                    jobs=args.jobs,
                )
            )
    finally:
        if ui is not None:
            ui.stop()

    module_summary_path = out_dir_path / "module_summary.csv"
    module_fieldnames = [
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
    with module_summary_path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=module_fieldnames)
        writer.writeheader()
        writer.writerows(module_rows)

    combined_path = out_dir_path / "combined_functions.csv"
    if combined_rows:
        fieldnames = sorted({k for row in combined_rows for k in row})
        with combined_path.open("w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(combined_rows)

    if not args.plain:
        console.print()
        _print_summary_table(console, module_rows)
    console.print(f"\n[green]Wrote[/] {module_summary_path}")
    console.print(f"[green]Wrote[/] {combined_path} ({len(combined_rows)} function rows)")
    return 0


def cli() -> None:
    raise SystemExit(main())


if __name__ == "__main__":
    cli()
