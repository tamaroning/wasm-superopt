#!/usr/bin/env python3
"""Run ewasm and SuperStack on a benchmark suite and collect per-block statistics CSVs."""

from __future__ import annotations

import argparse
import csv
import subprocess
import sys
from pathlib import Path

from rich.console import Console
from rich.table import Table

from wasm_bench.progress import BenchmarkRunnerUI, RunState, run_cmd_plain, run_cmd_tracked
from wasm_bench.suites import DEFAULT_SPLIT, SUITE_NAMES, out_dir, resolve_suite

_REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_EWASM = _REPO_ROOT / "target/release/ewasm"
DEFAULT_SUPERSTACK = (_REPO_ROOT / "../superstack/superstack.py").resolve()


def default_superstack_python(superstack: Path = DEFAULT_SUPERSTACK) -> Path:
    """Prefer SuperStack's own .venv; fall back to the current interpreter."""
    venv_python = superstack.parent / ".venv" / "bin" / "python"
    if venv_python.is_file():
        return venv_python
    return Path(sys.executable)


def _format_cmd(cmd: list[str]) -> str:
    return " ".join(f'"{part}"' if " " in part else part for part in cmd)


def _parse_only_names(values: list[str] | None) -> set[str] | None:
    """Split --only values on commas and whitespace (e.g. mux1_1,mux2_2 or mux1_1 mux2_2)."""
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


def read_statistics_rows(path: Path, tool: str, benchmark: str) -> list[dict[str, str]]:
    if not path.exists():
        return []
    with path.open(newline="") as f:
        reader = csv.DictReader(f)
        rows = []
        for row in reader:
            row["tool"] = tool
            row["benchmark"] = benchmark
            rows.append(row)
        return rows


def run_ewasm(
    ewasm_bin: Path,
    wasm: Path,
    csv_path: Path,
    split: int,
    jobs: int,
    timeout: int,
    segment_timeout: int | None,
    solver: str = "sat",
    *,
    ui: BenchmarkRunnerUI | None = None,
    cwd: Path | None = None,
) -> tuple[str, str, float]:
    cmd = [
        str(ewasm_bin),
        str(wasm),
        "--split",
        str(split),
        "-j",
        str(jobs),
        "-c",
        str(csv_path),
        "--solver",
        solver,
    ]
    if segment_timeout is not None:
        cmd.extend(["--segment-timeout", str(segment_timeout)])
    if ui is not None:
        code, output, elapsed = run_cmd_tracked(cmd, timeout=timeout, ui=ui, cwd=cwd)
    else:
        code, output, elapsed = run_cmd_plain(cmd, timeout=timeout, cwd=cwd)
    if code == 124:
        status = "timeout"
    elif code != 0 or "error parsing" in output:
        status = "error"
    elif csv_path.exists():
        status = "ok"
    else:
        status = "error"
    return status, output, elapsed


def run_superstack(
    python: Path,
    superstack: Path,
    wasm: Path,
    csv_path: Path,
    split: int,
    jobs: int,
    timeout: int,
    segment_timeout: int | None,
    mode: str,
    *,
    ui: BenchmarkRunnerUI | None = None,
) -> tuple[str, str, float]:
    cmd = [
        str(python),
        str(superstack),
        "wasm",
        str(wasm),
        "-sp",
        str(split),
        "-j",
        str(jobs),
        "-c",
        str(csv_path),
    ]
    if segment_timeout is not None:
        cmd.extend(["--segment-timeout", str(segment_timeout)])
    if mode == "greedy":
        cmd.append("--greedy")
    elif mode == "sat":
        cmd.append("--ub-greedy")
    else:
        raise ValueError(f"unknown superstack mode: {mode}")

    if ui is not None:
        code, output, elapsed = run_cmd_tracked(
            cmd, timeout=timeout, ui=ui, cwd=superstack.parent
        )
    else:
        code, output, elapsed = run_cmd_plain(cmd, timeout=timeout, cwd=superstack.parent)
    if code == 124:
        status = "timeout"
    elif code != 0:
        status = "error"
    elif csv_path.exists():
        status = "ok"
    else:
        status = "error"
    return status, output, elapsed


def _print_summary_table(console: Console, rows: list[dict[str, str | float | int]]) -> None:
    table = Table(title="Run summary")
    table.add_column("benchmark")
    table.add_column("tool")
    table.add_column("status")
    table.add_column("time (s)", justify="right")
    table.add_column("blocks", justify="right")
    for row in rows:
        table.add_row(
            str(row["benchmark"]),
            str(row["tool"]),
            str(row["status"]),
            f"{row['wall_time_sec']:.1f}",
            str(row["blocks"]),
        )
    console.print(table)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--suite",
        choices=SUITE_NAMES,
        default="r3",
        help="Benchmark suite to run (default: r3)",
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
        help="Output directory (default: bench-results/<suite>)",
    )
    parser.add_argument("--ewasm", type=Path, default=DEFAULT_EWASM)
    parser.add_argument(
        "--ewasm-solver",
        choices=["astar", "sat"],
        default="sat",
        help="ewasm solver backend: sat (default, descending Pure-SAT) or astar",
    )
    parser.add_argument("--superstack", type=Path, default=DEFAULT_SUPERSTACK)
    parser.add_argument(
        "--superstack-python",
        type=Path,
        default=None,
        help="Python for SuperStack (default: ../superstack/.venv/bin/python if present)",
    )
    parser.add_argument(
        "--split",
        type=int,
        default=DEFAULT_SPLIT,
        help=f"Match ewasm --split / SuperStack -sp (default: {DEFAULT_SPLIT})",
    )
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=1,
        help="Parallel jobs for ewasm and SuperStack block optimization (default: 1)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=3600,
        help="Per-benchmark timeout in seconds (default: 3600 = 1 hour)",
    )
    parser.add_argument(
        "--segment-timeout",
        type=int,
        default=None,
        metavar="SECS",
        help="Fixed solver timeout per sequence/block in seconds (ewasm/SuperStack --segment-timeout)",
    )
    parser.add_argument(
        "--tools",
        nargs="+",
        choices=["ewasm", "superstack-greedy", "superstack"],
        default=None,
        help="Tools to run (default: suite-specific; wsouper uses ewasm + superstack SAT)",
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
    tools = args.tools or list(suite.default_tools)
    bench_dir = args.bench_dir or suite.bench_dir
    out_dir_path = args.out_dir or out_dir(args.suite)
    superstack_python = args.superstack_python or default_superstack_python(args.superstack)
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

    if "ewasm" in tools and not args.no_build:
        build_code = build_ewasm(console=console, plain=args.plain)
        if build_code != 0:
            return build_code

    run_total = len(wasm_files) * len(tools)
    console.print(f"[bold]Suite:[/] {suite.label} ({bench_dir})")
    console.print(f"[bold]Tools:[/] {', '.join(tools)}")
    console.print(f"[bold]Output:[/] {out_dir_path}")
    console.print(f"[bold]Runs:[/] {len(wasm_files)} benchmarks × {len(tools)} tools = {run_total}")

    summary_rows: list[dict[str, str | float | int]] = []
    combined_rows: list[dict[str, str]] = []

    superstack_modes = {
        "superstack-greedy": "greedy",
        "superstack": "sat",
    }

    ui = None if args.plain else BenchmarkRunnerUI(console)
    if ui is not None:
        ui.start()

    run_index = 0
    try:
        for bench_index, wasm in enumerate(wasm_files, start=1):
            benchmark = wasm.stem

            for tool_name in tools:
                run_index += 1
                if ui is not None:
                    ui.begin_run(
                        RunState(
                            suite=suite.name,
                            benchmark=benchmark,
                            tool=tool_name,
                            benchmark_index=bench_index,
                            benchmark_total=len(wasm_files),
                            run_index=run_index,
                            run_total=run_total,
                        )
                    )
                elif args.plain:
                    print(f"\n=== {benchmark} / {tool_name} ({run_index}/{run_total}) ===", flush=True)

                if tool_name == "ewasm":
                    csv_path = raw_dir / f"ewasm-{benchmark}.csv"
                    cmd = [
                        str(args.ewasm),
                        str(wasm),
                        "--split",
                        str(args.split),
                        "-j",
                        str(args.jobs),
                        "-c",
                        str(csv_path),
                        "--solver",
                        args.ewasm_solver,
                    ]
                    if args.segment_timeout is not None:
                        cmd.extend(["--segment-timeout", str(args.segment_timeout)])
                    if args.plain:
                        print(f"  >> {_format_cmd(cmd)}", flush=True)
                    status, output, elapsed = run_ewasm(
                        args.ewasm,
                        wasm,
                        csv_path,
                        args.split,
                        args.jobs,
                        args.timeout,
                        args.segment_timeout,
                        args.ewasm_solver,
                        ui=ui,
                    )
                elif tool_name in superstack_modes:
                    csv_path = raw_dir / f"{tool_name}-{benchmark}.csv"
                    mode = superstack_modes[tool_name]
                    if args.plain:
                        cmd = [
                            str(superstack_python),
                            str(args.superstack),
                            "wasm",
                            str(wasm),
                            "-sp",
                            str(args.split),
                            "-j",
                            str(args.jobs),
                            "-c",
                            str(csv_path),
                        ]
                        if mode == "greedy":
                            cmd.append("--greedy")
                        else:
                            cmd.append("--ub-greedy")
                        if args.segment_timeout is not None:
                            cmd.extend(["--segment-timeout", str(args.segment_timeout)])
                        print(f"  >> {_format_cmd(cmd)}", flush=True)
                    status, output, elapsed = run_superstack(
                        superstack_python,
                        args.superstack,
                        wasm,
                        csv_path,
                        args.split,
                        args.jobs,
                        args.timeout,
                        args.segment_timeout,
                        mode,
                        ui=ui,
                    )
                else:
                    raise ValueError(f"unknown tool: {tool_name}")

                if ui is not None:
                    ui.finish_run(status)
                elif args.plain:
                    print(f"  << {tool_name}: {status} ({elapsed:.1f}s)", flush=True)

                log_path = raw_dir / f"{tool_name}-{benchmark}.log"
                log_path.write_text(output)
                summary_rows.append(
                    {
                        "benchmark": benchmark,
                        "tool": tool_name,
                        "status": status,
                        "wall_time_sec": round(elapsed, 3),
                        "blocks": len(read_statistics_rows(csv_path, tool_name, benchmark)),
                    }
                )
                combined_rows.extend(read_statistics_rows(csv_path, tool_name, benchmark))
    finally:
        if ui is not None:
            ui.stop()

    summary_path = out_dir_path / "run_summary.csv"
    with summary_path.open("w", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=["benchmark", "tool", "status", "wall_time_sec", "blocks"],
        )
        writer.writeheader()
        writer.writerows(summary_rows)

    combined_path = out_dir_path / "combined_blocks.csv"
    if combined_rows:
        fieldnames = sorted({k for row in combined_rows for k in row})
        with combined_path.open("w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(combined_rows)

    if not args.plain:
        console.print()
        _print_summary_table(console, summary_rows)
    console.print(f"\n[green]Wrote[/] {summary_path}")
    console.print(f"[green]Wrote[/] {combined_path} ({len(combined_rows)} block rows)")
    return 0


def cli() -> None:
    raise SystemExit(main())


if __name__ == "__main__":
    cli()
