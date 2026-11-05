#!/usr/bin/env python3
"""Plots of a benchmark of run_bench.py: a new solver against a baseline solver.

Writes into OUT_DIR:
  scatter.png  the time of each formula, baseline against new;
  tail.png     how many formulas are not finished within each time;
  ratio.png    histogram of the per-formula time ratio (formulas solved by both, at least 0.1 s in one of them);
  sets.png     the total time of each set, new relative to baseline.

Example: plots.py out/runs.csv --baseline old --new new --out out/plots
"""
import argparse
import os

import matplotlib.ticker
import numpy as np
import matplotlib.pyplot as plt

import bench_data
import plot_style
from bench_data import MIN_TIME


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("runs", nargs="+", help="runs.csv of run_bench.py (several are concatenated)")
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--new", required=True)
    parser.add_argument("--out", required=True, help="directory of the plots")
    return parser.parse_args()


def count_label(count):
    return f"{count} formula" if count == 1 else f"{count} formulas"


def seconds_label(seconds):
    if seconds >= 10:
        return f"{seconds:.0f} s"
    if seconds >= 1:
        return f"{seconds:.1f} s"
    return f"{seconds:.2f} s"


def plot_scatter(old_seconds, new_seconds, baseline, new, path):
    timeout = max(old_seconds.max(), new_seconds.max())
    figure, axes = plt.subplots(figsize=(6.5, 6.2))
    axes.scatter(old_seconds, new_seconds, s=3, color=plot_style.BLUE, alpha=0.25, linewidths=0, rasterized=True)
    limits = (MIN_TIME * 0.8, timeout * 1.25)
    axes.plot(limits, limits, color=plot_style.SECONDARY_TEXT, linewidth=1, linestyle="--")
    for factor in (bench_data.NOTABLE_RATIO, 1 / bench_data.NOTABLE_RATIO):
        axes.plot(limits, [limit * factor for limit in limits], color=plot_style.SECONDARY_TEXT, linewidth=0.8, linestyle=":")
    axes.set(xscale="log", yscale="log", xlim=limits, ylim=limits, xlabel=f"{baseline} time [s]", ylabel=f"{new} time [s]")
    slower = int(bench_data.notably_slower(new_seconds, old_seconds).sum())
    faster = int(bench_data.notably_faster(new_seconds, old_seconds).sum())
    notable = f"{bench_data.NOTABLE_RATIO}× and {bench_data.NOTABLE_SECONDS} s"
    axes.text(0.03, 0.97, f"{count_label(slower)} more than {notable} slower", transform=axes.transAxes, va="top", color=plot_style.SECONDARY_TEXT)
    axes.text(0.97, 0.03, f"{count_label(faster)} more than {notable} faster", transform=axes.transAxes, ha="right",
              color=plot_style.SECONDARY_TEXT)
    axes.set_title(f"Time per formula ({len(old_seconds)} formulas; dotted: {bench_data.NOTABLE_RATIO}×)")
    save(figure, path)


def plot_tail(old_seconds, new_seconds, baseline, new, path):
    """For each time t, the number of formulas not finished (solved or not) within t."""
    times = np.logspace(np.log10(MIN_TIME), np.log10(max(old_seconds.max(), new_seconds.max())), 300)
    figure, axes = plt.subplots(figsize=(7.5, 4.5))
    for seconds, name, color in [(old_seconds, baseline, plot_style.BLUE), (new_seconds, new, plot_style.ORANGE)]:
        sorted_seconds = np.sort(seconds.to_numpy())
        not_finished = len(sorted_seconds) - np.searchsorted(sorted_seconds, times, side="right")
        axes.plot(times, not_finished, color=color, linewidth=2, label=name)
    axes.set(xscale="log", yscale="log", xlabel="time t [s]", ylabel="formulas not finished within t")
    axes.legend(frameon=False)
    axes.set_title(f"Tail of the time distribution ({len(old_seconds)} formulas)")
    save(figure, path)


def plot_ratio(old_seconds, new_seconds, solved_by_both, baseline, new, path, min_seconds=0.1):
    """Histogram of the time ratio new / baseline of the formulas solved by both, taking at least min_seconds in one of them."""
    kept = solved_by_both & ((old_seconds >= min_seconds) | (new_seconds >= min_seconds))
    ratios = bench_data.time_ratio(new_seconds[kept], old_seconds[kept])
    if ratios.empty:
        return
    # bins symmetric around 1
    smallest = max(min(ratios.min(), 1 / ratios.max()) / 1.2, 1e-3)
    bins = np.logspace(np.log10(smallest), -np.log10(smallest), 80)
    figure, axes = plt.subplots(figsize=(7.5, 4.2))
    axes.hist(ratios.clip(bins[0], bins[-1]), bins=bins, color=plot_style.BLUE, edgecolor=plot_style.BACKGROUND, linewidth=0.5)
    axes.axvline(1, color=plot_style.SECONDARY_TEXT, linewidth=1, linestyle="--")
    axes.set(xscale="log", yscale="log", xlabel=f"time of {new} / time of {baseline}", ylabel="formulas")
    axes.set_title(f"Per-formula time ratio (geometric mean {bench_data.geometric_mean(ratios):.3f})\n"
                   f"{count_label(int(kept.sum()))} solved by both, at least {min_seconds:g} s in one of them")
    save(figure, path)


def plot_sets(runs, baseline, new, path):
    """The total time of each set, new relative to baseline."""
    total = runs.groupby(["set", "solver"]).seconds.sum().unstack()
    ratios = (total[new] / total[baseline]).sort_values()
    figure, axes = plt.subplots(figsize=(7.5, 0.28 * len(ratios) + 1.2))
    rows = np.arange(len(ratios))
    axes.hlines(rows, 1, ratios, color=plot_style.GRID, linewidth=2)
    axes.scatter(ratios, rows, s=40, color=plot_style.BLUE, zorder=3)
    for row, (set_name, ratio) in enumerate(ratios.items()):
        label = f"{ratio:.2f}  ({seconds_label(total.at[set_name, baseline])} → {seconds_label(total.at[set_name, new])})"
        axes.annotate(label, (ratio, row), xytext=(6, -3), textcoords="offset points", color=plot_style.SECONDARY_TEXT, fontsize=8)
    axes.axvline(1, color=plot_style.SECONDARY_TEXT, linewidth=1, linestyle="--")
    axes.set_yticks(rows, ratios.index)
    axes.set_xscale("log")
    axes.set_xlim(min(ratios.min(), 0.5) / 1.5, max(ratios.max(), 2) * 4)
    low, high = axes.get_xlim()
    ticks = [tick for tick in [0.03, 0.1, 0.25, 0.5, 1, 2, 4, 10, 30] if low <= tick <= high]
    axes.set_xticks(ticks, [f"{tick:g}" for tick in ticks])
    axes.xaxis.set_minor_formatter(matplotlib.ticker.NullFormatter())
    axes.grid(axis="y", visible=False)
    axes.set_xlabel(f"total time of {new} / total time of {baseline} (timeouts included)")
    axes.set_title("Total time per set")
    save(figure, path)


def save(figure, path):
    figure.tight_layout()
    figure.savefig(path, dpi=150)
    plt.close(figure)


def main():
    args = parse_arguments()
    plot_style.apply()
    os.makedirs(args.out, exist_ok=True)
    runs, _ = bench_data.load_runs(args.runs, [args.baseline, args.new])
    seconds = bench_data.seconds_table(runs)
    outcomes = bench_data.outcome_table(runs)
    old_seconds, new_seconds = seconds[args.baseline], seconds[args.new]
    solved_by_both = (outcomes[args.baseline] == "solved") & (outcomes[args.new] == "solved")
    plot_scatter(old_seconds, new_seconds, args.baseline, args.new, f"{args.out}/scatter.png")
    plot_tail(old_seconds, new_seconds, args.baseline, args.new, f"{args.out}/tail.png")
    plot_ratio(old_seconds, new_seconds, solved_by_both, args.baseline, args.new, f"{args.out}/ratio.png")
    plot_sets(runs, args.baseline, args.new, f"{args.out}/sets.png")


if __name__ == "__main__":
    main()
