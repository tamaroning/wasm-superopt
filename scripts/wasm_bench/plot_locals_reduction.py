#!/usr/bin/env python3
"""Plot per-program instruction/local reduction from --opt-locals benchmark results."""

from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

from wasm_bench.merge_locals_csvs import merge_locals_csvs
from wasm_bench.suites import (
    SUITE_NAMES,
    locals_combined_functions_csv,
    locals_out_dir,
    locals_plots_dir,
    locals_summary_csv,
    resolve_suite,
)


def enrich_reduction_columns(df: pd.DataFrame) -> pd.DataFrame:
    df = df.copy()
    for col in (
        "instr_saved",
        "local_slots_saved",
        "copies_removed",
        "instr_before",
        "local_slots_before",
        "instr_reduction_pct",
        "local_slots_reduction_pct",
        "wall_time_sec",
        "solver_time_secs",
    ):
        if col in df.columns:
            df[col] = pd.to_numeric(df[col], errors="coerce").fillna(0)

    if "instr_reduction_pct" not in df.columns:
        df["instr_reduction_pct"] = 0.0
    if "local_slots_reduction_pct" not in df.columns:
        df["local_slots_reduction_pct"] = 0.0

    missing_instr_pct = df["instr_reduction_pct"].eq(0) & df["instr_saved"].gt(0)
    df.loc[missing_instr_pct, "instr_reduction_pct"] = np.where(
        df.loc[missing_instr_pct, "instr_before"] > 0,
        100.0 * df.loc[missing_instr_pct, "instr_saved"] / df.loc[missing_instr_pct, "instr_before"],
        0.0,
    )

    missing_local_pct = df["local_slots_reduction_pct"].eq(0) & df["local_slots_saved"].gt(0)
    df.loc[missing_local_pct, "local_slots_reduction_pct"] = np.where(
        df.loc[missing_local_pct, "local_slots_before"] > 0,
        100.0
        * df.loc[missing_local_pct, "local_slots_saved"]
        / df.loc[missing_local_pct, "local_slots_before"],
        0.0,
    )
    return df


def load_module_summary(path: Path, exclude: list[str]) -> pd.DataFrame:
    df = pd.read_csv(path)
    if exclude:
        df = df[~df["benchmark"].isin(exclude)]
    df = enrich_reduction_columns(df)
    return df.sort_values("benchmark").reset_index(drop=True)


def load_functions(path: Path, exclude: list[str]) -> pd.DataFrame:
    df = pd.read_csv(path)
    if exclude:
        df = df[~df["benchmark"].isin(exclude)]
    for col in (
        "instr_saved",
        "local_slots_saved",
        "copies_removed",
        "instr_before",
        "local_slots_before",
        "solver_time_secs",
        "webs",
        "interferes",
        "bb_count",
        "h4_clauses",
    ):
        if col in df.columns:
            df[col] = pd.to_numeric(df[col], errors="coerce").fillna(0)
    return df


def short_label(name: str, max_len: int = 24) -> str:
    if len(name) <= max_len:
        return name
    return name[: max_len - 1] + "…"


def _format_saved(value: float, unit: str) -> str:
    n = int(value)
    if n == 0:
        return f"0 {unit}"
    return f"−{n} {unit}"


def plot_reduction_pct(module_df: pd.DataFrame, out: Path, suite_label: str) -> None:
    """Grouped bar chart: instruction/local reduction rate (%) with absolute counts annotated."""
    benchmarks = module_df["benchmark"].tolist()
    labels = [short_label(b) for b in benchmarks]
    x = np.arange(len(benchmarks))
    width = 0.36

    instr_pct = module_df["instr_reduction_pct"].to_numpy()
    local_pct = module_df["local_slots_reduction_pct"].to_numpy()
    instr_saved = module_df["instr_saved"].to_numpy()
    local_saved = module_df["local_slots_saved"].to_numpy()

    ymax = max(float(instr_pct.max()), float(local_pct.max()), 0.05)
    pad = ymax * 0.06

    fig, ax = plt.subplots(figsize=(max(11, len(benchmarks) * 0.5), 6.5))
    ax.bar(x - width / 2, instr_pct, width, label="instructions", color="#2563eb")
    ax.bar(x + width / 2, local_pct, width, label="local slots", color="#16a34a")

    for i in range(len(benchmarks)):
        ax.text(
            x[i] - width / 2,
            instr_pct[i] + pad,
            f"{instr_pct[i]:.2f}%\n{_format_saved(instr_saved[i], 'instr')}",
            ha="center",
            va="bottom",
            fontsize=7,
            linespacing=1.15,
        )
        ax.text(
            x[i] + width / 2,
            local_pct[i] + pad,
            f"{local_pct[i]:.2f}%\n{_format_saved(local_saved[i], 'locals')}",
            ha="center",
            va="bottom",
            fontsize=7,
            linespacing=1.15,
        )

    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right")
    ax.set_ylabel("reduction (%)")
    ax.set_title(f"{suite_label}: per-program reduction (--opt-locals)")
    ax.set_ylim(0, ymax * 1.35)
    ax.legend(loc="upper right")
    ax.grid(axis="y", alpha=0.3)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)


def write_reduction_summary_txt(module_df: pd.DataFrame, out: Path, suite_label: str) -> None:
    lines = [
        f"# {suite_label}: --opt-locals reduction summary",
        "",
        f"{'benchmark':<28} {'instr_saved':>11} {'instr_%':>8} {'locals_saved':>12} {'locals_%':>9}",
        "-" * 72,
    ]
    for row in module_df.itertuples(index=False):
        lines.append(
            f"{row.benchmark:<28} "
            f"{int(row.instr_saved):>11} "
            f"{row.instr_reduction_pct:>7.2f}% "
            f"{int(row.local_slots_saved):>12} "
            f"{row.local_slots_reduction_pct:>8.2f}%"
        )

    total_instr_before = module_df["instr_before"].sum()
    total_instr_saved = module_df["instr_saved"].sum()
    total_local_before = module_df["local_slots_before"].sum()
    total_local_saved = module_df["local_slots_saved"].sum()
    total_instr_pct = 100.0 * total_instr_saved / total_instr_before if total_instr_before else 0.0
    total_local_pct = 100.0 * total_local_saved / total_local_before if total_local_before else 0.0

    lines.extend(
        [
            "-" * 72,
            f"{'TOTAL':<28} "
            f"{int(total_instr_saved):>11} "
            f"{total_instr_pct:>7.2f}% "
            f"{int(total_local_saved):>12} "
            f"{total_local_pct:>8.2f}%",
            "",
            f"programs: {len(module_df)}",
            f"total instr before: {int(total_instr_before)}",
            f"total local slots before: {int(total_local_before)}",
        ]
    )
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def plot_copies_removed(module_df: pd.DataFrame, out: Path, suite_label: str) -> None:
    benchmarks = module_df["benchmark"].tolist()
    labels = [short_label(b) for b in benchmarks]
    copies = module_df["copies_removed"].to_numpy()
    instr_before = module_df["instr_before"].to_numpy()
    copies_pct = np.where(instr_before > 0, 100.0 * copies / instr_before, 0.0)

    x = np.arange(len(benchmarks))
    ymax = max(float(copies_pct.max()), 0.05)
    pad = ymax * 0.06

    fig, ax = plt.subplots(figsize=(max(10, len(benchmarks) * 0.45), 5))
    ax.bar(x, copies_pct, color="#dc2626")
    for i in range(len(benchmarks)):
        ax.text(
            x[i],
            copies_pct[i] + pad,
            f"{copies_pct[i]:.3f}%\n−{int(copies[i])} copies",
            ha="center",
            va="bottom",
            fontsize=7,
            linespacing=1.15,
        )
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right")
    ax.set_ylabel("copy removal (%)")
    ax.set_title(f"{suite_label}: self-copy removals by program")
    ax.set_ylim(0, ymax * 1.35)
    ax.grid(axis="y", alpha=0.3)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)


def plot_solver_time_vs_webs(func_df: pd.DataFrame, out: Path, suite_label: str) -> None:
    fig, ax = plt.subplots(figsize=(8, 6))
    improved = func_df["status"] == "improved"
    ax.scatter(
        func_df.loc[~improved, "webs"],
        func_df.loc[~improved, "solver_time_secs"],
        alpha=0.45,
        s=24,
        color="#94a3b8",
        label="unchanged/skipped/timeout",
    )
    ax.scatter(
        func_df.loc[improved, "webs"],
        func_df.loc[improved, "solver_time_secs"],
        alpha=0.7,
        s=30,
        color="#2563eb",
        label="improved",
    )
    ax.set_xlabel("webs per function")
    ax.set_ylabel("solver time (s)")
    ax.set_title(f"{suite_label}: solver time vs web count")
    ax.set_yscale("log")
    ax.legend()
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)


def plot_status_breakdown(module_df: pd.DataFrame, out: Path, suite_label: str) -> None:
    benchmarks = module_df["benchmark"].tolist()
    labels = [short_label(b) for b in benchmarks]
    x = np.arange(len(benchmarks))
    width = 0.6
    improved = module_df["functions_improved"].to_numpy()
    unchanged = module_df["functions_unchanged"].to_numpy()
    timeout = module_df["functions_timeout"].to_numpy()
    skipped = module_df["functions_skipped"].to_numpy()
    total = improved + unchanged + timeout + skipped

    fig, ax = plt.subplots(figsize=(max(10, len(benchmarks) * 0.45), 5))
    ax.bar(x, improved, width, label="improved", color="#16a34a")
    ax.bar(x, unchanged, width, bottom=improved, label="unchanged", color="#94a3b8")
    ax.bar(x, timeout, width, bottom=improved + unchanged, label="timeout", color="#f59e0b")
    ax.bar(
        x,
        skipped,
        width,
        bottom=improved + unchanged + timeout,
        label="skipped",
        color="#dc2626",
    )
    for i in range(len(benchmarks)):
        if total[i] <= 0:
            continue
        improved_pct = 100.0 * improved[i] / total[i]
        ax.text(
            x[i],
            total[i] + 0.3,
            f"{int(improved[i])}/{int(total[i])}\n({improved_pct:.0f}% improved)",
            ha="center",
            va="bottom",
            fontsize=6.5,
            linespacing=1.1,
        )
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right")
    ax.set_ylabel("function count")
    ax.set_title(f"{suite_label}: function status breakdown")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out, dpi=150)
    plt.close(fig)


def ensure_data(suite: str, combined_path: Path, summary_path: Path) -> None:
    if combined_path.exists() and summary_path.exists():
        return
    merge_locals_csvs(suite)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--suite",
        choices=SUITE_NAMES,
        default="wsouper",
        help="Benchmark suite to plot (default: wsouper)",
    )
    parser.add_argument(
        "--summary",
        type=Path,
        default=None,
        help="module_summary.csv path (default: bench-results/locals-<suite>/module_summary.csv)",
    )
    parser.add_argument(
        "--functions",
        type=Path,
        default=None,
        help="combined_functions.csv path (default: bench-results/locals-<suite>/combined_functions.csv)",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=None,
        help="Directory for PNG outputs (default: bench-results/locals-<suite>/plots)",
    )
    parser.add_argument("--exclude", nargs="*", default=[], help="Benchmark names to omit")
    args = parser.parse_args()

    suite = resolve_suite(args.suite)
    summary_path = args.summary or locals_summary_csv(args.suite)
    combined_path = args.functions or locals_combined_functions_csv(args.suite)
    out_dir = args.out_dir or locals_plots_dir(args.suite)

    ensure_data(args.suite, combined_path, summary_path)
    if not summary_path.exists():
        print(f"missing summary CSV: {summary_path}")
        return 1

    module_df = load_module_summary(summary_path, args.exclude)
    if module_df.empty:
        print("no module rows to plot")
        return 1

    out_dir.mkdir(parents=True, exist_ok=True)
    plot_reduction_pct(module_df, out_dir / "reduction_pct_by_program.png", suite.label)
    plot_copies_removed(module_df, out_dir / "copies_removed_by_program.png", suite.label)
    plot_status_breakdown(module_df, out_dir / "function_status_by_program.png", suite.label)
    write_reduction_summary_txt(module_df, out_dir / "reduction_summary.txt", suite.label)

    if combined_path.exists():
        func_df = load_functions(combined_path, args.exclude)
        if not func_df.empty:
            plot_solver_time_vs_webs(func_df, out_dir / "solver_time_vs_webs.png", suite.label)

    module_df.to_csv(out_dir / "summary_by_benchmark.csv", index=False)
    print(f"wrote plots under {out_dir}")
    print(f"wrote {out_dir / 'reduction_summary.txt'}")
    return 0


def cli() -> None:
    raise SystemExit(main())


if __name__ == "__main__":
    cli()
