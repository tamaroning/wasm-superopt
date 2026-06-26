#!/usr/bin/env python3
"""Run ewasm and SuperStack on wasm-r3-bench and collect per-block statistics CSVs."""

from __future__ import annotations

import argparse
import csv
import subprocess
import sys
import threading
import time
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BENCH_DIR = (_REPO_ROOT / "../wasm-benchmarks/wasm-r3-bench").resolve()
DEFAULT_EWASM = _REPO_ROOT / "target/release/ewasm"
DEFAULT_SUPERSTACK = (_REPO_ROOT / "../superstack/superstack.py").resolve()
DEFAULT_OUT = _REPO_ROOT / "bench-results/r3"


def default_superstack_python(superstack: Path = DEFAULT_SUPERSTACK) -> Path:
    """Prefer SuperStack's own .venv; fall back to the current interpreter."""
    venv_python = superstack.parent / ".venv" / "bin" / "python"
    if venv_python.is_file():
        return venv_python
    return Path(sys.executable)


def _format_cmd(cmd: list[str]) -> str:
    return " ".join(f'"{part}"' if " " in part else part for part in cmd)


def run_cmd(cmd: list[str], timeout: int, cwd: Path | None = None) -> tuple[int, str, float]:
    """Run *cmd*, streaming stdout/stderr to the terminal and returning captured output."""
    start = time.monotonic()
    output_chunks: list[str] = []

    def _emit(text: str) -> None:
        output_chunks.append(text)
        sys.stdout.write(text)
        sys.stdout.flush()

    proc = subprocess.Popen(
        cmd,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    assert proc.stdout is not None

    def _reader() -> None:
        for line in proc.stdout:
            _emit(line)

    reader = threading.Thread(target=_reader, daemon=True)
    reader.start()
    try:
        returncode = proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()
        msg = f"\n[timeout after {timeout}s]\n"
        _emit(msg)
        reader.join(timeout=2)
        return 124, "".join(output_chunks), time.monotonic() - start

    reader.join(timeout=2)
    return returncode, "".join(output_chunks), time.monotonic() - start


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
    ]
    code, output, elapsed = run_cmd(cmd, timeout=timeout)
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
    mode: str,
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
    if mode == "greedy":
        cmd.append("--greedy")
    elif mode == "sat":
        cmd.append("--ub-greedy")
    else:
        raise ValueError(f"unknown superstack mode: {mode}")

    code, output, elapsed = run_cmd(cmd, timeout=timeout, cwd=superstack.parent)
    if code == 124:
        status = "timeout"
    elif code != 0:
        status = "error"
    elif csv_path.exists():
        status = "ok"
    else:
        status = "error"
    return status, output, elapsed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bench-dir", type=Path, default=DEFAULT_BENCH_DIR)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--ewasm", type=Path, default=DEFAULT_EWASM)
    parser.add_argument("--superstack", type=Path, default=DEFAULT_SUPERSTACK)
    parser.add_argument(
        "--superstack-python",
        type=Path,
        default=None,
        help="Python for SuperStack (default: ../superstack/.venv/bin/python if present)",
    )
    parser.add_argument("--split", type=int, default=10, help="Match ewasm --split / SuperStack -sp")
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=1,
        help="Parallel jobs for ewasm and SuperStack block optimization (default: 1)",
    )
    parser.add_argument("--timeout", type=int, default=600, help="Per-benchmark timeout (seconds)")
    parser.add_argument(
        "--tools",
        nargs="+",
        choices=["ewasm", "superstack-greedy", "superstack"],
        default=["ewasm", "superstack-greedy"],
    )
    parser.add_argument("--limit", type=int, default=0, help="Limit number of wasm files (0 = all)")
    parser.add_argument("--only", nargs="*", help="Run only these benchmark basenames")
    args = parser.parse_args()
    superstack_python = args.superstack_python or default_superstack_python(args.superstack)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    raw_dir = args.out_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir / ".keep").touch()

    wasm_files = sorted(args.bench_dir.glob("*.wasm"))
    if args.only:
        only = set(args.only)
        wasm_files = [p for p in wasm_files if p.stem in only]
    if args.limit:
        wasm_files = wasm_files[: args.limit]

    summary_rows: list[dict[str, str | float | int]] = []
    combined_rows: list[dict[str, str]] = []

    superstack_modes = {
        "superstack-greedy": "greedy",
        "superstack": "sat",
    }

    for wasm in wasm_files:
        benchmark = wasm.stem
        print(f"\n=== {benchmark} ===", flush=True)

        for tool_name in args.tools:
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
                ]
                print(
                    f"\n  >> ewasm ({benchmark})"
                    f"  split={args.split} jobs={args.jobs} timeout={args.timeout}s",
                    flush=True,
                )
                print(f"     {_format_cmd(cmd)}", flush=True)
                status, output, elapsed = run_ewasm(
                    args.ewasm, wasm, csv_path, args.split, args.jobs, args.timeout
                )
            elif tool_name in superstack_modes:
                csv_path = raw_dir / f"{tool_name}-{benchmark}.csv"
                mode = superstack_modes[tool_name]
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
                print(
                    f"\n  >> {tool_name} ({benchmark})"
                    f"  split={args.split} jobs={args.jobs} timeout={args.timeout}s",
                    flush=True,
                )
                print(f"     {_format_cmd(cmd)}", flush=True)
                status, output, elapsed = run_superstack(
                    superstack_python,
                    args.superstack,
                    wasm,
                    csv_path,
                    args.split,
                    args.jobs,
                    args.timeout,
                    mode,
                )
            else:
                raise ValueError(f"unknown tool: {tool_name}")

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

    summary_path = args.out_dir / "run_summary.csv"
    with summary_path.open("w", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=["benchmark", "tool", "status", "wall_time_sec", "blocks"],
        )
        writer.writeheader()
        writer.writerows(summary_rows)

    combined_path = args.out_dir / "combined_blocks.csv"
    if combined_rows:
        fieldnames = sorted({k for row in combined_rows for k in row})
        with combined_path.open("w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(combined_rows)

    print(f"\nWrote {summary_path}")
    print(f"Wrote {combined_path} ({len(combined_rows)} block rows)")
    return 0


def cli() -> None:
    raise SystemExit(main())


if __name__ == "__main__":
    cli()
