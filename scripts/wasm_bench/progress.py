"""Rich progress display for benchmark subprocess runs."""

from __future__ import annotations

import re
import subprocess
import sys
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path

from rich.console import Console, Group
from rich.live import Live
from rich.panel import Panel
from rich.progress import (
    BarColumn,
    MofNCompleteColumn,
    Progress,
    SpinnerColumn,
    TaskProgressColumn,
    TextColumn,
    TimeElapsedColumn,
)
from rich.table import Table
from rich.text import Text

OPTIMIZING_TOTAL_RE = re.compile(r"=== Optimizing (\d+) segment")
PARALLEL_START_RE = re.compile(r"optimizing (\d+) segment\(s\) with (\d+) threads")
SEGMENT_STEP_RE = re.compile(r"\[(\d+)/(\d+)\]")
DONE_STATUS_RE = re.compile(r"instr done \((improved|timeout|unchanged)\)")
FUNC_SEGMENT_RE = re.compile(r"^func \d+ segment ")
FUNC_IMPROVED_RE = re.compile(r"->\s*\d+\s*\(saved ")
FUNC_TIMEOUT_RE = re.compile(r"\(timeout\)\s*$")
TOTAL_SUMMARY_RE = re.compile(r"Total: .+ across (\d+) segment")


@dataclass
class SegmentState:
    total: int | None = None
    done: int = 0
    parallel_jobs: int | None = None
    parallel_phase: bool = False
    last_line: str = ""
    improved: int = 0
    timeout: int = 0
    unchanged: int = 0
    inline_counted: bool = False


@dataclass
class RunState:
    suite: str
    benchmark: str
    tool: str
    benchmark_index: int
    benchmark_total: int
    run_index: int
    run_total: int
    segments: SegmentState = field(default_factory=SegmentState)
    status: str = "running"
    elapsed_sec: float = 0.0


class BenchmarkRunnerUI:
    def __init__(self, console: Console | None = None) -> None:
        self.console = console or Console(stderr=True)
        self.overall = Progress(
            SpinnerColumn(),
            TextColumn("[bold]{task.description}"),
            BarColumn(bar_width=32),
            MofNCompleteColumn(),
            TimeElapsedColumn(),
            console=self.console,
            expand=True,
        )
        self.segments = Progress(
            SpinnerColumn(),
            TextColumn("{task.description}"),
            BarColumn(bar_width=32),
            TaskProgressColumn(),
            TimeElapsedColumn(),
            console=self.console,
            expand=True,
        )
        self._overall_task = self.overall.add_task("Preparing", total=1)
        self._segment_task = self.segments.add_task("Idle", total=1)
        self._state: RunState | None = None
        self._live: Live | None = None
        self._ticker_stop = threading.Event()
        self._ticker: threading.Thread | None = None

    def _renderable(self):
        state = self._state
        if state is None:
            return Group(self.overall)

        info = Table.grid(padding=(0, 1))
        info.add_row("Suite", state.suite)
        info.add_row("Benchmark", f"{state.benchmark} ({state.benchmark_index}/{state.benchmark_total})")
        info.add_row("Tool", state.tool)
        info.add_row("Run", f"{state.run_index}/{state.run_total}")
        seg = state.segments
        if seg.improved or seg.timeout or seg.unchanged:
            results = Text()
            results.append(f"{seg.improved} improved", style="green")
            results.append(" · ")
            results.append(f"{seg.timeout} timeout", style="red")
            results.append(" · ")
            results.append(f"{seg.unchanged} unchanged", style="yellow")
            info.add_row("Results", results)
        if seg.last_line:
            info.add_row("Latest", Text(seg.last_line, overflow="ellipsis", no_wrap=True))

        return Group(
            Panel(info, title="wasm-bench", border_style="cyan"),
            self.overall,
            self.segments,
        )

    def start(self) -> None:
        self._live = Live(self._renderable(), console=self.console, refresh_per_second=8)
        self._live.start()

    def stop(self) -> None:
        self._stop_ticker()
        if self._live is not None:
            self._live.stop()
            self._live = None

    def begin_run(self, state: RunState) -> None:
        self._state = state
        self.overall.update(
            self._overall_task,
            total=state.run_total,
            completed=state.run_index - 1,
            description=f"[cyan]{state.suite}[/] — {state.benchmark} ({state.tool})",
        )
        self._reset_segment_task("Parsing…", total=None)
        self._refresh()

    def finish_run(self, status: str) -> None:
        if self._state is None:
            return
        self._state.status = status
        self._stop_ticker()
        self.overall.advance(self._overall_task)
        self._reset_segment_task(f"Done ({status})", total=1, completed=1)
        self._refresh()

    def _reset_segment_task(
        self,
        description: str,
        *,
        total: int | None,
        completed: int = 0,
    ) -> None:
        self.segments.reset(
            self._segment_task,
            total=total,
            completed=completed,
            description=description,
        )

    def _refresh(self) -> None:
        if self._live is not None:
            self._live.update(self._renderable())

    def _start_ticker(self) -> None:
        self._stop_ticker()
        self._ticker_stop.clear()

        def _loop() -> None:
            while not self._ticker_stop.wait(0.5):
                state = self._state
                if state is None or not state.segments.parallel_phase:
                    continue
                seg = state.segments
                if seg.total is None:
                    continue
                jobs = seg.parallel_jobs or 1
                state.elapsed_sec += 0.5
                self._reset_segment_task(
                    f"Parallel optimization: {seg.total} segments / {jobs} threads ({state.elapsed_sec:.0f}s)",
                    total=None,
                    completed=0,
                )
                self._refresh()

        self._ticker = threading.Thread(target=_loop, daemon=True)
        self._ticker.start()

    def _stop_ticker(self) -> None:
        self._ticker_stop.set()
        if self._ticker is not None:
            self._ticker.join(timeout=1)
            self._ticker = None

    def handle_line(self, line: str) -> None:
        state = self._state
        if state is None:
            return

        stripped = line.rstrip("\n")
        if stripped:
            state.segments.last_line = stripped

        match = OPTIMIZING_TOTAL_RE.search(stripped)
        if match:
            state.segments.total = int(match.group(1))
            state.segments.done = 0
            state.segments.parallel_phase = False
            state.segments.improved = 0
            state.segments.timeout = 0
            state.segments.unchanged = 0
            state.segments.inline_counted = False
            total = state.segments.total
            self._reset_segment_task(f"Preparing optimization: {total} segments", total=total, completed=0)
            self._refresh()
            return

        match = PARALLEL_START_RE.search(stripped)
        if match:
            total = int(match.group(1))
            jobs = int(match.group(2))
            state.segments.total = total
            state.segments.done = 0
            state.segments.parallel_jobs = jobs
            state.segments.parallel_phase = True
            state.segments.improved = 0
            state.segments.timeout = 0
            state.segments.unchanged = 0
            state.segments.inline_counted = False
            state.elapsed_sec = 0.0
            self._reset_segment_task(
                f"Parallel optimization: {total} segments / {jobs} threads",
                total=None,
                completed=0,
            )
            self._start_ticker()
            self._refresh()
            return

        match = SEGMENT_STEP_RE.search(stripped)
        if match:
            done = int(match.group(1))
            total = int(match.group(2))
            seg = state.segments
            seg.total = total
            seg.done = done
            seg.parallel_phase = False
            status_match = DONE_STATUS_RE.search(stripped)
            if status_match:
                status = status_match.group(1)
                if status == "improved":
                    seg.improved += 1
                elif status == "timeout":
                    seg.timeout += 1
                else:
                    seg.unchanged += 1
                seg.inline_counted = True
            self._stop_ticker()
            self._reset_segment_task(
                f"Optimizing: {done}/{total} segments",
                total=total,
                completed=done,
            )
            self._refresh()
            return

        if FUNC_SEGMENT_RE.match(stripped):
            seg = state.segments
            if not seg.inline_counted:
                if FUNC_IMPROVED_RE.search(stripped):
                    seg.improved += 1
                elif FUNC_TIMEOUT_RE.search(stripped):
                    seg.timeout += 1
                else:
                    seg.unchanged += 1
            if seg.total is not None:
                seg.done = min(seg.done + 1, seg.total)
                self._stop_ticker()
                seg.parallel_phase = False
                self.segments.update(
                    self._segment_task,
                    completed=seg.done,
                    description=f"Writing results: {seg.done}/{seg.total} segments",
                )
                self._refresh()
            return

        match = TOTAL_SUMMARY_RE.search(stripped)
        if match:
            total = int(match.group(1))
            state.segments.total = total
            state.segments.done = total
            state.segments.parallel_phase = False
            self._stop_ticker()
            self._reset_segment_task(f"Optimization complete: {total} segments", total=total, completed=total)
            self._refresh()


def run_cmd_tracked(
    cmd: list[str],
    timeout: int,
    ui: BenchmarkRunnerUI,
    *,
    cwd: Path | None = None,
) -> tuple[int, str, float]:
    start = time.monotonic()
    output_chunks: list[str] = []

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
            output_chunks.append(line)
            ui.handle_line(line)

    reader = threading.Thread(target=_reader, daemon=True)
    reader.start()
    try:
        returncode = proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()
        msg = f"\n[timeout after {timeout}s]\n"
        output_chunks.append(msg)
        ui.handle_line(msg)
        reader.join(timeout=2)
        return 124, "".join(output_chunks), time.monotonic() - start

    reader.join(timeout=2)
    return returncode, "".join(output_chunks), time.monotonic() - start


def run_cmd_plain(
    cmd: list[str],
    timeout: int,
    *,
    cwd: Path | None = None,
) -> tuple[int, str, float]:
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
