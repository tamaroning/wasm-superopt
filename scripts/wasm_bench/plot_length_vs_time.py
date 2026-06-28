#!/usr/bin/env python3
"""Plot instruction length vs solver time from benchmark combined CSV."""

from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

from wasm_bench.merge_raw_csvs import merge_raw_csvs
from wasm_bench.suites import SUITE_NAMES, combined_csv, plots_dir, raw_dir, resolve_suite

TOOL_COLORS = {
    "ewasm": "#2563eb",
    "superstack": "#dc2626",
    "superstack-greedy": "#dc2626",
    "superstack-sat": "#16a34a",
}
FALLBACK_COLORS = ("#9333ea", "#ca8a04", "#0891b2", "#be123c")


def tool_color(tool: str, index: int) -> str:
    if tool in TOOL_COLORS:
        return TOOL_COLORS[tool]
    return FALLBACK_COLORS[index % len(FALLBACK_COLORS)]


def load_data(path: Path, benchmark: str | None, exclude: list[str], max_length: int) -> pd.DataFrame:
    df = pd.read_csv(path)
    if benchmark:
        df = df[df["benchmark"] == benchmark]
    if exclude:
        df = df[~df["benchmark"].isin(exclude)]
    df["initial_length"] = pd.to_numeric(df["initial_length"], errors="coerce")
    df["solver_time_in_sec"] = pd.to_numeric(df["solver_time_in_sec"], errors="coerce")
    df = df.dropna(subset=["initial_length", "solver_time_in_sec"])
    df = df[df["initial_length"] > 0]
    if max_length > 0:
        df = df[df["initial_length"] <= max_length]
    return df


def bucket_lengths(lengths: pd.Series, width: int) -> pd.Series:
    return ((lengths - 1) // width) * width + 1


def scatter_x_positions(lengths: pd.Series, tool_index: int, tool_count: int, dodge: float) -> np.ndarray:
    if tool_count <= 1 or dodge <= 0:
        return lengths.to_numpy(dtype=float)
    offset = (tool_index - (tool_count - 1) / 2) * dodge
    return lengths.to_numpy(dtype=float) + offset


def plot_scatter(df: pd.DataFrame, out: Path, suite_label: str, dodge: float = 0.18) -> None:
    fig, ax = plt.subplots(figsize=(10, 6))
    tools = sorted(df["tool"].unique())
    for i, tool in enumerate(tools):
        sub = df[df["tool"] == tool]
        ax.scatter(
            scatter_x_positions(sub["initial_length"], i, len(tools), dodge),
            sub["solver_time_in_sec"],
            alpha=0.55,
            s=28,
            label=tool,
            color=tool_color(tool, i),
        )
    lengths = sorted(df["initial_length"].unique())
    ax.set_xticks(lengths)
    ax.set_xlabel("Block length (instructions)")
    ax.set_ylabel("Solver time (seconds)")
    ax.set_title(f"Block length vs solver time ({suite_label})")
    ax.grid(True, alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(out, dpi=160)
    plt.close(fig)


def plot_binned_stats(df: pd.DataFrame, out: Path, bucket_width: int) -> None:
    df = df.copy()
    df["length_bucket"] = bucket_lengths(df["initial_length"], bucket_width)
    grouped = (
        df.groupby(["tool", "length_bucket"])["solver_time_in_sec"]
        .agg(["mean", "std", "count"])
        .reset_index()
    )
    grouped = grouped[grouped["count"] >= 1]

    tools = sorted(df["tool"].unique())
    buckets = sorted(grouped["length_bucket"].unique())
    x = np.arange(len(buckets))
    width = 0.8 / max(len(tools), 1)

    fig, ax = plt.subplots(figsize=(12, 6))
    for i, tool in enumerate(tools):
        sub = grouped[grouped["tool"] == tool].set_index("length_bucket").reindex(buckets)
        means = sub["mean"].to_numpy()
        stds = sub["std"].fillna(0).to_numpy()
        counts = sub["count"].fillna(0).to_numpy()
        offset = (i - (len(tools) - 1) / 2) * width
        bars = ax.bar(
            x + offset,
            means,
            width,
            yerr=stds,
            capsize=3,
            label=tool,
            color=tool_color(tool, i),
            alpha=0.85,
        )
        for bar, mean, count in zip(bars, means, counts):
            if np.isnan(mean) or count == 0:
                continue
            ax.text(
                bar.get_x() + bar.get_width() / 2,
                bar.get_height(),
                f"n={int(count)}",
                ha="center",
                va="bottom",
                fontsize=7,
                rotation=90,
            )

    if bucket_width == 1:
        labels = [f"{b}" for b in buckets]
        xlabel = "Block length (instructions)"
    else:
        labels = [f"{b}-{b + bucket_width - 1}" for b in buckets]
        xlabel = f"Block length bucket ({bucket_width}-instr bins)"
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right")
    ax.set_xlabel(xlabel)
    ax.set_ylabel("Mean solver time (seconds)")
    ax.set_title("Mean ± std solver time by block length")
    ax.grid(True, axis="y", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(out, dpi=160)
    plt.close(fig)


def write_summary_table(df: pd.DataFrame, out: Path) -> None:
    summary = (
        df.groupby("tool")
        .agg(
            blocks=("solver_time_in_sec", "count"),
            mean_length=("initial_length", "mean"),
            std_length=("initial_length", "std"),
            mean_time=("solver_time_in_sec", "mean"),
            std_time=("solver_time_in_sec", "std"),
            median_time=("solver_time_in_sec", "median"),
            p95_time=("solver_time_in_sec", lambda s: s.quantile(0.95)),
        )
        .reset_index()
    )
    summary.to_csv(out, index=False)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--suite",
        choices=SUITE_NAMES,
        default="r3",
        help="Benchmark suite to plot (default: r3)",
    )
    parser.add_argument(
        "--input",
        type=Path,
        default=None,
        help="Combined CSV path (default: bench-results/<suite>/combined_blocks.csv)",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=None,
        help="Plot output directory (default: bench-results/<suite>/plots)",
    )
    parser.add_argument("--benchmark", help="Plot only this benchmark")
    parser.add_argument(
        "--exclude",
        action="append",
        default=None,
        help="Exclude benchmarks (default: suite-specific, e.g. ffmpeg for r3; use '' to exclude none)",
    )
    parser.add_argument("--max-length", type=int, default=0, help="Keep blocks up to this length (0 = all)")
    parser.add_argument("--bucket-width", type=int, default=1)
    args = parser.parse_args()

    suite = resolve_suite(args.suite)
    input_path = args.input or combined_csv(args.suite)
    out_dir_path = args.out_dir or plots_dir(args.suite)

    if args.exclude is None:
        exclude = list(suite.default_exclude)
    else:
        exclude = [x for x in args.exclude if x]

    if not input_path.exists():
        out_path, count = merge_raw_csvs(
            args.suite,
            out_path=input_path,
            exclude=exclude or None,
        )
        if count == 0:
            raw_dir_path = raw_dir(args.suite)
            print(f"missing input: {input_path}")
            if not raw_dir_path.is_dir() or not any(raw_dir_path.glob("*.csv")):
                print(
                    f"No benchmark results for suite {args.suite!r}. "
                    f"Run first:\n"
                    f"  uv run --project scripts wasm-bench-run --suite {args.suite}"
                )
            else:
                print(
                    f"Raw CSVs exist under {raw_dir_path} but produced no rows "
                    f"(check --exclude filters)."
                )
            return 1
        print(f"merged {count} rows from {raw_dir(args.suite)} -> {out_path}")
        input_path = out_path

    out_dir_path.mkdir(parents=True, exist_ok=True)
    df = load_data(input_path, args.benchmark, exclude, args.max_length)
    if df.empty:
        print("no rows to plot")
        return 1

    plot_scatter(df, out_dir_path / "length_vs_time_scatter.png", suite.label)
    plot_binned_stats(df, out_dir_path / "length_vs_time_binned.png", args.bucket_width)
    write_summary_table(df, out_dir_path / "summary_by_tool.csv")

    print(f"rows: {len(df)}")
    print(f"tools: {sorted(df['tool'].unique())}")
    print(f"wrote plots to {out_dir_path}")
    return 0


def cli() -> None:
    raise SystemExit(main())


if __name__ == "__main__":
    cli()
