#!/usr/bin/env python3
"""Plot instruction length vs solver time from r3 benchmark combined CSV."""

from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

_REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_INPUT = _REPO_ROOT / "bench-results/r3/combined_blocks.csv"
DEFAULT_OUT = _REPO_ROOT / "bench-results/r3/plots"


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


def plot_scatter(df: pd.DataFrame, out: Path) -> None:
    fig, ax = plt.subplots(figsize=(10, 6))
    tools = sorted(df["tool"].unique())
    colors = {"ewasm": "#2563eb", "superstack-greedy": "#dc2626", "superstack-sat": "#16a34a"}
    for tool in tools:
        sub = df[df["tool"] == tool]
        ax.scatter(
            sub["initial_length"],
            sub["solver_time_in_sec"],
            alpha=0.55,
            s=28,
            label=tool,
            color=colors.get(tool, None),
        )
    ax.set_xlabel("Block length (instructions)")
    ax.set_ylabel("Solver time (seconds)")
    ax.set_title("Block length vs solver time (wasm-r3-bench)")
    ax.set_yscale("log")
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
    colors = {"ewasm": "#2563eb", "superstack-greedy": "#dc2626", "superstack-sat": "#16a34a"}
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
            color=colors.get(tool, None),
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

    labels = [f"{b}-{b + bucket_width - 1}" for b in buckets]
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right")
    ax.set_xlabel(f"Block length bucket ({bucket_width}-instr bins)")
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
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--benchmark", help="Plot only this benchmark")
    parser.add_argument("--exclude", action="append", default=["ffmpeg"], help="Exclude benchmarks (use '' to exclude none)")
    parser.add_argument("--max-length", type=int, default=0, help="Keep blocks up to this length (0 = all)")
    parser.add_argument("--bucket-width", type=int, default=5)
    args = parser.parse_args()

    if not args.input.exists():
        print(f"missing input: {args.input}")
        return 1

    args.out_dir.mkdir(parents=True, exist_ok=True)
    exclude = [x for x in (args.exclude or []) if x]
    df = load_data(args.input, args.benchmark, exclude, args.max_length)
    if df.empty:
        print("no rows to plot")
        return 1

    plot_scatter(df, args.out_dir / "length_vs_time_scatter.png")
    plot_binned_stats(df, args.out_dir / "length_vs_time_binned.png", args.bucket_width)
    write_summary_table(df, args.out_dir / "summary_by_tool.csv")

    print(f"rows: {len(df)}")
    print(f"tools: {sorted(df['tool'].unique())}")
    print(f"wrote plots to {args.out_dir}")
    return 0


def cli() -> None:
    raise SystemExit(main())


if __name__ == "__main__":
    cli()
