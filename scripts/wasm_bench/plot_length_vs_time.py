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
    df["saved_length"] = pd.to_numeric(df.get("saved_length", 0), errors="coerce").fillna(0)
    df = df.dropna(subset=["initial_length", "solver_time_in_sec"])
    df = df[df["initial_length"] > 0]
    df["saved_length"] = df["saved_length"].clip(lower=0)
    if "timeout" in df.columns:
        timeout = pd.to_numeric(df["timeout"], errors="coerce")
        df["timed_out"] = df["solver_time_in_sec"] >= timeout - 0.01
    else:
        df["timed_out"] = False
    df["improved"] = df["saved_length"] > 0
    df["reduction_pct"] = np.where(
        df["improved"],
        100.0 * df["saved_length"] / df["initial_length"],
        0.0,
    )
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


def plot_saved_scatter(df: pd.DataFrame, out: Path, suite_label: str, dodge: float = 0.18) -> None:
    fig, ax = plt.subplots(figsize=(10, 6))
    tools = sorted(df["tool"].unique())
    for i, tool in enumerate(tools):
        sub = df[df["tool"] == tool]
        ax.scatter(
            scatter_x_positions(sub["initial_length"], i, len(tools), dodge),
            sub["saved_length"],
            alpha=0.55,
            s=28,
            label=tool,
            color=tool_color(tool, i),
        )
    lengths = sorted(df["initial_length"].unique())
    ax.set_xticks(lengths)
    ax.set_xlabel("Block length (instructions)")
    ax.set_ylabel("Instructions saved")
    ax.set_title(f"Block length vs improvement ({suite_label})")
    ax.grid(True, alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(out, dpi=160)
    plt.close(fig)


def plot_saved_binned(df: pd.DataFrame, out: Path, bucket_width: int) -> None:
    df = df.copy()
    df["length_bucket"] = bucket_lengths(df["initial_length"], bucket_width)
    grouped = (
        df.groupby(["tool", "length_bucket"])["saved_length"]
        .agg(["mean", "std", "count", "sum"])
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
    ax.set_ylabel("Mean instructions saved")
    ax.set_title("Mean ± std instructions saved by block length")
    ax.grid(True, axis="y", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(out, dpi=160)
    plt.close(fig)


def plot_improvement_rate_binned(df: pd.DataFrame, out: Path, bucket_width: int) -> None:
    df = df.copy()
    df["length_bucket"] = bucket_lengths(df["initial_length"], bucket_width)
    grouped = (
        df.groupby(["tool", "length_bucket"])["improved"]
        .agg(["mean", "count"])
        .reset_index()
        .rename(columns={"mean": "improvement_rate"})
    )
    grouped = grouped[grouped["count"] >= 1]

    tools = sorted(df["tool"].unique())
    buckets = sorted(grouped["length_bucket"].unique())
    x = np.arange(len(buckets))
    width = 0.8 / max(len(tools), 1)

    fig, ax = plt.subplots(figsize=(12, 6))
    for i, tool in enumerate(tools):
        sub = grouped[grouped["tool"] == tool].set_index("length_bucket").reindex(buckets)
        rates = 100.0 * sub["improvement_rate"].fillna(0).to_numpy()
        counts = sub["count"].fillna(0).to_numpy()
        offset = (i - (len(tools) - 1) / 2) * width
        bars = ax.bar(
            x + offset,
            rates,
            width,
            label=tool,
            color=tool_color(tool, i),
            alpha=0.85,
        )
        for bar, rate, count in zip(bars, rates, counts):
            if count == 0:
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
    ax.set_ylabel("Blocks improved (%)")
    ax.set_ylim(0, 100)
    ax.set_title("Share of blocks with any instruction reduction")
    ax.grid(True, axis="y", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(out, dpi=160)
    plt.close(fig)


def filter_blocks_without_timeouts(df: pd.DataFrame) -> pd.DataFrame:
    """Drop blocks where any tool hit the segment timeout (paired exclusion)."""
    block_timed_out = df.groupby(["benchmark", "block_id"], sort=False)["timed_out"].transform("any")
    return df.loc[~block_timed_out]


def benchmarks_with_all_tools(df: pd.DataFrame) -> list[str]:
    tools = sorted(df["tool"].unique())
    if not tools:
        return []
    present = df.groupby("benchmark")["tool"].apply(lambda s: set(s.unique()))
    return sorted(bench for bench, tool_set in present.items() if set(tools) <= tool_set)


def benchmark_reduction_stats(df: pd.DataFrame) -> pd.DataFrame:
    grouped = (
        df.groupby(["benchmark", "tool"])
        .agg(
            blocks=("initial_length", "count"),
            total_initial=("initial_length", "sum"),
            total_saved=("saved_length", "sum"),
            blocks_improved=("improved", "sum"),
        )
        .reset_index()
    )
    grouped["reduction_pct"] = np.where(
        grouped["total_initial"] > 0,
        100.0 * grouped["total_saved"] / grouped["total_initial"],
        0.0,
    )
    grouped["blocks_improved_pct"] = np.where(
        grouped["blocks"] > 0,
        100.0 * grouped["blocks_improved"] / grouped["blocks"],
        0.0,
    )
    return grouped


def plot_reduction_by_benchmark(
    df: pd.DataFrame,
    out: Path,
    suite_label: str,
    *,
    exclude_timeouts: bool = False,
) -> None:
    plot_df = filter_blocks_without_timeouts(df) if exclude_timeouts else df
    if exclude_timeouts:
        benchmarks = benchmarks_with_all_tools(plot_df)
        plot_df = plot_df[plot_df["benchmark"].isin(benchmarks)]
    else:
        benchmarks = sorted(plot_df["benchmark"].unique())
    grouped = benchmark_reduction_stats(plot_df)
    tools = sorted(grouped["tool"].unique())
    y = np.arange(len(benchmarks))
    bar_height = 0.8 / max(len(tools), 1)
    fig_height = max(5.0, len(benchmarks) * 0.32 + 1.5)

    fig, ax = plt.subplots(figsize=(10, fig_height))
    for i, tool in enumerate(tools):
        sub = grouped[grouped["tool"] == tool].set_index("benchmark").reindex(benchmarks)
        rates = sub["reduction_pct"].fillna(0).to_numpy()
        offset = (i - (len(tools) - 1) / 2) * bar_height
        bars = ax.barh(
            y + offset,
            rates,
            bar_height,
            label=tool,
            color=tool_color(tool, i),
            alpha=0.85,
        )
        for bar, rate in zip(bars, rates):
            if rate <= 0:
                continue
            ax.text(
                bar.get_width(),
                bar.get_y() + bar.get_height() / 2,
                f"{rate:.1f}%",
                ha="left",
                va="center",
                fontsize=7,
                clip_on=False,
            )

    ax.set_yticks(y)
    ax.set_yticklabels(benchmarks)
    ax.set_xlabel("Instructions reduced (%)")
    ax.set_ylabel("Benchmark")
    title_suffix = " (excluding segment timeouts on either tool)" if exclude_timeouts else ""
    ax.set_title(f"Instruction reduction by program ({suite_label}){title_suffix}")
    ax.grid(True, axis="x", alpha=0.25)
    ax.legend(loc="lower right")
    fig.tight_layout()
    fig.savefig(out, dpi=160, bbox_inches="tight")
    plt.close(fig)


def plot_improvement_summary(df: pd.DataFrame, out: Path, suite_label: str) -> None:
    tools = sorted(df["tool"].unique())
    totals = [df.loc[df["tool"] == tool, "saved_length"].sum() for tool in tools]
    rates = [
        100.0 * df.loc[df["tool"] == tool, "improved"].mean() if len(df[df["tool"] == tool]) else 0.0
        for tool in tools
    ]

    x = np.arange(len(tools))
    width = 0.35

    fig, ax1 = plt.subplots(figsize=(8, 5))
    bars = ax1.bar(
        x - width / 2,
        totals,
        width,
        label="Total instructions saved",
        color=[tool_color(tool, i) for i, tool in enumerate(tools)],
        alpha=0.85,
    )
    ax1.set_ylabel("Total instructions saved")
    ax1.set_xlabel("Tool")
    ax1.set_xticks(x)
    ax1.set_xticklabels(tools, rotation=20, ha="right")
    for bar, total in zip(bars, totals):
        ax1.text(
            bar.get_x() + bar.get_width() / 2,
            bar.get_height(),
            f"{int(total)}",
            ha="center",
            va="bottom",
            fontsize=9,
        )

    ax2 = ax1.twinx()
    ax2.plot(
        x + width / 2,
        rates,
        "o-",
        color="#374151",
        linewidth=2,
        markersize=8,
        label="Blocks improved (%)",
    )
    ax2.set_ylabel("Blocks improved (%)")
    ax2.set_ylim(0, max(100, max(rates) * 1.1 if rates else 100))

    lines1, labels1 = ax1.get_legend_handles_labels()
    lines2, labels2 = ax2.get_legend_handles_labels()
    ax1.legend(lines1 + lines2, labels1 + labels2, loc="upper right")
    ax1.set_title(f"Optimization summary ({suite_label})")
    ax1.grid(True, axis="y", alpha=0.25)
    fig.tight_layout()
    fig.savefig(out, dpi=160)
    plt.close(fig)


def write_benchmark_summary_table(df: pd.DataFrame, out: Path) -> None:
    benchmark_reduction_stats(df).to_csv(out, index=False)


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
            total_saved=("saved_length", "sum"),
            blocks_improved=("improved", "sum"),
            pct_improved=("improved", "mean"),
            mean_saved=("saved_length", "mean"),
            mean_saved_when_improved=("saved_length", lambda s: s[s > 0].mean() if (s > 0).any() else 0.0),
            mean_reduction_pct=("reduction_pct", lambda s: s[s > 0].mean() if (s > 0).any() else 0.0),
        )
        .reset_index()
    )
    summary["pct_improved"] = 100.0 * summary["pct_improved"]
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
    plot_saved_scatter(df, out_dir_path / "length_vs_saved_scatter.png", suite.label)
    plot_saved_binned(df, out_dir_path / "length_vs_saved_binned.png", args.bucket_width)
    plot_improvement_rate_binned(df, out_dir_path / "improvement_rate_binned.png", args.bucket_width)
    plot_improvement_summary(df, out_dir_path / "improvement_summary.png", suite.label)
    plot_reduction_by_benchmark(df, out_dir_path / "reduction_by_benchmark.png", suite.label)
    plot_reduction_by_benchmark(
        df,
        out_dir_path / "reduction_by_benchmark_no_timeout.png",
        suite.label,
        exclude_timeouts=True,
    )
    write_summary_table(df, out_dir_path / "summary_by_tool.csv")
    write_benchmark_summary_table(df, out_dir_path / "summary_by_benchmark.csv")

    print(f"rows: {len(df)}")
    print(f"tools: {sorted(df['tool'].unique())}")
    print(f"wrote plots to {out_dir_path}")
    return 0


def cli() -> None:
    raise SystemExit(main())


if __name__ == "__main__":
    cli()
