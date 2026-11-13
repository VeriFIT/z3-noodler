"""Plots of a benchmark of run.py: the times of two solvers, old and new (called by report.py).

scatter.png  the time of each formula, old against new, on log scales, with the diagonal and the lines of 2× slower and faster;
sets.png     the total time of each set, new relative to old.
Timeouts count as the timeout.
"""

from __future__ import annotations

from pathlib import Path

import matplotlib

# The plots are only written to files, so matplotlib must not look for a display.
matplotlib.use("Agg")

import matplotlib.pyplot as plt
import matplotlib.ticker
import pandas as pd
import seaborn as sns
from matplotlib.figure import Figure

# Times below this are shown as this, as a log scale has no zero.
# report.py uses the same limit in its ratios of times.
MIN_TIME = 0.01

# The ticks of the axis of the ratios of times.
RATIO_TICKS = [0.01, 0.03, 0.1, 0.25, 0.5, 1, 2, 4, 10, 30, 100]

# Tick labels such as 0.01 and 10 instead of powers of ten.
PLAIN_NUMBERS = matplotlib.ticker.FuncFormatter(lambda value, _: f"{value:g}")


def write_plots(runs: pd.DataFrame, old: str, new: str, out_dir: Path, note: str | None = None) -> None:
    """Writes scatter.png and sets.png into out_dir, with an optional note below each plot.

    runs has one row per run, with the columns file, set, solver and seconds.
    old and new are the names of the two solvers.
    """
    sns.set_theme(style="whitegrid")
    out_dir.mkdir(exist_ok=True)

    # One row per formula, with the time of each solver in its own column.
    seconds = runs.pivot(index="file", columns="solver", values="seconds")

    plot_scatter(seconds[old], seconds[new], old, new, out_dir / "scatter.png", note)
    plot_sets(runs, old, new, out_dir / "sets.png", note)


def plot_scatter(
    old_seconds: pd.Series,
    new_seconds: pd.Series,
    old: str,
    new: str,
    path: Path,
    note: str | None = None,
) -> None:
    """The time of each formula, old on the x axis and new on the y axis, with an optional note below the plot.

    old_seconds and new_seconds hold the times of the same formulas in the same order.
    """
    figure, axes = plt.subplots(figsize=(6.5, 6.5))

    # One dot per formula.
    sns.scatterplot(
        x=old_seconds.clip(lower=MIN_TIME),
        y=new_seconds.clip(lower=MIN_TIME),
        s=10,
        alpha=0.3,
        linewidth=0,
        rasterized=True,
        ax=axes,
    )

    # Both axes show the same range, a little wider than the times.
    limits = (MIN_TIME * 0.8, max(old_seconds.max(), new_seconds.max()) * 1.25)

    # The diagonal (same time) and the dotted lines of 2× slower and 2× faster.
    axes.plot(limits, limits, color="gray", linewidth=1, linestyle="--")
    for factor in (2, 0.5):
        axes.plot(limits, [limit * factor for limit in limits], color="gray", linewidth=0.8, linestyle=":")

    # Log scales, labels and the title.
    axes.set(
        xscale="log",
        yscale="log",
        xlim=limits,
        ylim=limits,
        xlabel=f"{old} [s]",
        ylabel=f"{new} [s]",
        title=f"Time per formula ({len(old_seconds):,} formulas)",
    )
    for axis in (axes.xaxis, axes.yaxis):
        axis.set_major_formatter(PLAIN_NUMBERS)

    save(figure, path, note)


def plot_sets(runs: pd.DataFrame, old: str, new: str, path: Path, note: str | None = None) -> None:
    """The total time of each set, new relative to old, with the two totals next to each dot and an optional note below the plot.

    runs has one row per run, with the columns set, solver and seconds.
    """
    # The total time of each set (rows) and solver (columns), and the ratio new / old of each set, the smallest first.
    totals = runs.groupby(["set", "solver"], observed=True).seconds.sum().unstack()
    ratios = (totals[new] / totals[old]).sort_values()

    # One row per set, numbered in the order of the ratios.
    # A categorical axis of seaborn may order the sets differently, which would separate the dots from their labels.
    rows = list(range(len(ratios)))
    figure, axes = plt.subplots(figsize=(8, 0.3 * len(ratios) + 1.5))

    # One dot per set, the vertical line of the same total time, and the names of the sets on the left.
    axes.scatter(ratios.to_numpy(), rows, s=40, zorder=3)
    axes.axvline(1, color="gray", linewidth=1, linestyle="--")
    axes.set_yticks(rows, [str(name) for name in ratios.index])

    # The y axis is turned over, so that the smallest ratio is on top.
    axes.set_ylim(len(ratios) - 0.5, -0.5)

    # The two totals of each set are the tick labels of a second axis on the right, so that they do not overlap the dots.
    total_labels = [f"{totals.at[name, old]:,.1f} s → {totals.at[name, new]:,.1f} s" for name in ratios.index]
    totals_axis = axes.twinx()
    totals_axis.set_ylim(axes.get_ylim())
    totals_axis.set_yticks(rows, total_labels)
    totals_axis.tick_params(axis="y", labelsize=8, labelcolor="dimgray")
    totals_axis.grid(False)

    # A log scale, so that 2× slower and 2× faster are equally far from 1.
    # It shows at least the range from 0.5 to 2, with a margin on both sides.
    axes.set_xscale("log")
    low = min(ratios.min(), 0.5) / 1.25
    high = max(ratios.max(), 2) * 1.25
    axes.set_xlim(low, high)

    # Plain numbers at the ticks that are in the range, and no labels at the minor ticks.
    axes.set_xticks([tick for tick in RATIO_TICKS if low <= tick <= high])
    axes.xaxis.set_major_formatter(PLAIN_NUMBERS)
    axes.xaxis.set_minor_formatter(matplotlib.ticker.NullFormatter())

    axes.set(xlabel=f"total time of {new} / total time of {old}", ylabel="", title="Total time per set")

    save(figure, path, note)


def save(figure: Figure, path: Path, note: str | None = None) -> None:
    """Saves a figure as a PNG and closes it, with an optional note in small text below the plot."""
    if note:
        # The note is at the bottom of the figure, and the plot leaves about 0.3 inch for it.
        figure.text(0.5, 0.01, note, ha="center", va="bottom", fontsize=8, color="dimgray")
        figure.tight_layout(rect=(0, 0.3 / figure.get_figheight(), 1, 1))
    else:
        figure.tight_layout()

    figure.savefig(path, dpi=150)
    plt.close(figure)
