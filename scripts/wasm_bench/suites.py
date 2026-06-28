"""Benchmark suite definitions and default paths."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]

SUITE_NAMES = ("r3", "rosetta", "wsouper")

# Default segment split width passed to ewasm --split / SuperStack -sp.
DEFAULT_SPLIT = 25


@dataclass(frozen=True)
class BenchmarkSuite:
    name: str
    label: str
    bench_dir: Path
    default_exclude: tuple[str, ...]


SUITES: dict[str, BenchmarkSuite] = {
    "r3": BenchmarkSuite(
        name="r3",
        label="wasm-r3-bench",
        bench_dir=(_REPO_ROOT / "../wasm-benchmarks/wasm-r3-bench").resolve(),
        default_exclude=("ffmpeg",),
    ),
    "rosetta": BenchmarkSuite(
        name="rosetta",
        label="Rosetta Code benchmarks",
        bench_dir=_REPO_ROOT / "benchmarks/rosetta",
        default_exclude=(),
    ),
    "wsouper": BenchmarkSuite(
        name="wsouper",
        label="Souper benchmarks",
        bench_dir=_REPO_ROOT / "benchmarks/wsouper",
        default_exclude=(),
    ),
}


def resolve_suite(name: str) -> BenchmarkSuite:
    try:
        return SUITES[name]
    except KeyError as exc:
        choices = ", ".join(SUITE_NAMES)
        raise ValueError(f"unknown suite {name!r}; choose from: {choices}") from exc


def out_dir(suite: str) -> Path:
    return _REPO_ROOT / "bench-results" / suite


def raw_dir(suite: str) -> Path:
    return out_dir(suite) / "raw"


def combined_csv(suite: str) -> Path:
    return out_dir(suite) / "combined_blocks.csv"


def plots_dir(suite: str) -> Path:
    return out_dir(suite) / "plots"
