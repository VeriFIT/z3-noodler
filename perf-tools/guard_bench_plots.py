#!/usr/bin/env python3
"""Plots of a smtbench_run.py benchmark of a new solver against a baseline (and of several thresholds against it).

Writes into OUT: scatter.png (per-formula times), tail.png (formulas not finished within a time), ratio.png (histogram of
the per-formula time ratios), sets.png (total-time ratio per set) and, with --thresholds, thresholds.png (the solvers named
NAME-NUMBER of the given benches against the baseline of each).
Usage: guard_bench_plots.py BENCH.csv BASELINE NEW --out DIR [--thresholds LABEL=BENCH.csv...] [--timeout 30]
"""
import argparse
import os

import matplotlib
import matplotlib.ticker
import numpy as np

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

from guard_bench_report import load, solver_order  # noqa: E402

# the reference palette of the dataviz method: categorical slots 1 and 2, light surface, text and grid
BLUE, ORANGE = "#2a78d6", "#eb6834"
SURFACE, INK, INK_2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
MIN_TIME = 0.01

plt.rcParams.update({"figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "savefig.facecolor": SURFACE, "text.color": INK,
                     "axes.labelcolor": INK, "xtick.color": INK_2, "ytick.color": INK_2, "axes.edgecolor": INK_2, "font.size": 10,
                     "axes.spines.top": False, "axes.spines.right": False, "axes.grid": True, "grid.color": GRID,
                     "grid.linewidth": 0.6, "axes.titlesize": 11, "axes.titlelocation": "left"})


def formulas(n):
    return f"{n} formula" if n == 1 else f"{n} formulas"


def seconds(t):
    return f"{t:.0f} s" if t >= 10 else f"{t:.1f} s" if t >= 1 else f"{t:.2f} s"


def times(runs, baseline, new):
    wide = runs.pivot(index="file", columns="solver", values="seconds").clip(lower=MIN_TIME)
    outcome = runs.pivot(index="file", columns="solver", values="outcome")
    sets = runs.groupby("file").set.first()
    return wide[baseline], wide[new], outcome[baseline], outcome[new], sets


def scatter(runs, baseline, new, timeout, out):
    old, cur, old_o, new_o, _ = times(runs, baseline, new)
    fig, ax = plt.subplots(figsize=(6.5, 6.2))
    ax.scatter(old, cur, s=3, color=BLUE, alpha=0.25, linewidths=0, rasterized=True)
    lim = (MIN_TIME * 0.8, timeout * 1.25)
    ax.plot(lim, lim, color=INK_2, linewidth=1, linestyle="--")
    for factor in (2, 0.5):
        ax.plot(lim, [x * factor for x in lim], color=INK_2, linewidth=0.8, linestyle=":")
    ax.set(xscale="log", yscale="log", xlim=lim, ylim=lim, xlabel=f"{baseline} time [s]", ylabel=f"{new} time [s]")
    ratio = cur / old
    faster = int(((ratio < 0.5) & (old - cur > 0.1)).sum())
    slower = int(((ratio > 2) & (cur - old > 0.1)).sum())
    ax.text(0.03, 0.97, f"{formulas(slower)} more than 2× and 0.1 s slower", transform=ax.transAxes, va="top", color=INK_2)
    ax.text(0.97, 0.03, f"{formulas(faster)} more than 2× and 0.1 s faster", transform=ax.transAxes, ha="right", color=INK_2)
    ax.set_title(f"Time per formula ({len(old)} formulas; timeouts at {timeout:g} s; dotted: 2×)")
    fig.tight_layout()
    fig.savefig(f"{out}/scatter.png", dpi=150)
    plt.close(fig)


def tail(runs, baseline, new, timeout, out):
    """For each time t, the number of formulas not finished (solved or not) within t."""
    old, cur, *_ = times(runs, baseline, new)
    grid = np.logspace(np.log10(MIN_TIME), np.log10(timeout), 300)
    fig, ax = plt.subplots(figsize=(7.5, 4.5))
    left = {}
    for series, name, color in [(old, baseline, BLUE), (cur, new, ORANGE)]:
        values = np.sort(series.to_numpy())
        left[name] = len(values) - np.searchsorted(values, grid, side="right")
        ax.plot(grid, left[name], color=color, linewidth=2, label=name)
    # direct labels where the curves are the farthest apart, the upper one above and the lower one below its curve
    i = int(np.argmax(np.abs(np.log1p(left[baseline]) - np.log1p(left[new]))))
    upper, lower = (baseline, new) if left[baseline][i] >= left[new][i] else (new, baseline)
    ax.annotate(upper, (grid[i], left[upper][i]), xytext=(0, 6), textcoords="offset points", ha="center", va="bottom", color=INK)
    ax.annotate(lower, (grid[i], left[lower][i]), xytext=(0, -6), textcoords="offset points", ha="center", va="top", color=INK)
    ax.set(xscale="log", yscale="log", xlabel="time t [s]", ylabel="formulas not finished within t")
    ax.legend(frameon=False)
    ax.set_title(f"Tail of the time distribution ({len(old)} formulas; the timeout {timeout:g} s is the right end)")
    fig.tight_layout()
    fig.savefig(f"{out}/tail.png", dpi=150)
    plt.close(fig)


def ratio(runs, baseline, new, out, min_time=0.1):
    """Histogram of the time ratio new/baseline of the formulas solved by both, taking at least min_time in one of them."""
    old, cur, old_o, new_o, _ = times(runs, baseline, new)
    keep = (old_o == "solved") & (new_o == "solved") & ((old >= min_time) | (cur >= min_time))
    r = (cur / old)[keep]
    fig, ax = plt.subplots(figsize=(7.5, 4.2))
    # symmetric around 1
    low = max(min(r.min(), 1 / r.max()) / 1.2, 1e-3)
    bins = np.logspace(np.log10(low), -np.log10(low), 80)
    ax.hist(r.clip(bins[0], bins[-1]), bins=bins, color=BLUE, edgecolor=SURFACE, linewidth=0.5)
    ax.axvline(1, color=INK_2, linewidth=1, linestyle="--")
    ax.set(xscale="log", yscale="log", xlabel=f"time of {new} / time of {baseline}", ylabel="formulas")
    ax.set_title(f"Per-formula time ratio (geometric mean {np.exp(np.log(r).mean()):.3f})\n"
                 f"{int(keep.sum())} formulas solved by both, at least {min_time:g} s in one of them")
    fig.tight_layout()
    fig.savefig(f"{out}/ratio.png", dpi=150)
    plt.close(fig)


def sets(runs, baseline, new, out):
    """Total time of the new solver relative to the baseline per set."""
    total = runs.groupby(["set", "solver"]).seconds.sum().unstack()
    r = (total[new] / total[baseline]).sort_values()
    fig, ax = plt.subplots(figsize=(7.5, 0.28 * len(r) + 1.2))
    y = np.arange(len(r))
    ax.hlines(y, 1, r, color=GRID, linewidth=2)
    ax.scatter(r, y, s=40, color=BLUE, zorder=3)
    for i, (name, value) in enumerate(r.items()):
        ax.annotate(f"{value:.2f}  ({seconds(total.at[name, baseline])} → {seconds(total.at[name, new])})", (value, i), xytext=(6, -3),
                    textcoords="offset points", color=INK_2, fontsize=8)
    ax.axvline(1, color=INK_2, linewidth=1, linestyle="--")
    ax.set_yticks(y, r.index)
    ax.set_xscale("log")
    ax.set_xlim(min(r.min(), 0.5) / 1.5, max(r.max(), 2) * 4)
    ticks = [t for t in [0.03, 0.1, 0.25, 0.5, 1, 2, 4, 10, 30] if ax.get_xlim()[0] <= t <= ax.get_xlim()[1]]
    ax.set_xticks(ticks, [f"{t:g}" for t in ticks])
    ax.xaxis.set_minor_formatter(matplotlib.ticker.NullFormatter())
    ax.grid(axis="y", visible=False)
    ax.set_xlabel(f"total time of {new} / total time of {baseline} (timeouts included)")
    ax.set_title("Total time per set")
    fig.tight_layout()
    fig.savefig(f"{out}/sets.png", dpi=150)
    plt.close(fig)


def thresholds(benches, baseline, out):
    """Against the bound, for each bench (its solvers named NAME-NUMBER against its own baseline): the total time, the
    geometric mean of the per-formula time ratio of the formulas solved by both, and the formulas more than 2× and 0.5 s
    slower per 1000 formulas.
    Formulas on which every solver of a bench times out are left out, so that the benches are comparable."""
    fig, axes = plt.subplots(1, 3, figsize=(13, 4.4))
    for (label, path), color in zip(benches, [BLUE, ORANGE]):
        runs, solvers = load(path)
        bounds = [s for s in solvers if s != baseline]
        values = [solver_order(s)[1] for s in bounds]
        outcome = runs.pivot(index="file", columns="solver", values="outcome")
        outcome = outcome[outcome.ne("timeout").any(axis=1)]
        wide = runs.pivot(index="file", columns="solver", values="seconds").clip(lower=MIN_TIME).loc[outcome.index]
        total = [wide[s].sum() / wide[baseline].sum() for s in bounds]
        both = [(outcome[s] == "solved") & (outcome[baseline] == "solved") for s in bounds]
        geometric = [np.exp(np.log(wide[s] / wide[baseline])[b].mean()) for s, b in zip(bounds, both)]
        slower = [1000 * ((wide[s] / wide[baseline] > 2) & (wide[s] - wide[baseline] > 0.5)).mean() for s in bounds]
        for ax, series in zip(axes, [total, geometric, slower]):
            ax.plot(values, series, color=color, linewidth=2, marker="o", markersize=8, label=f"{label} ({len(wide)} formulas)")
            if values[0] == 1:
                ax.annotate("no reduction", (values[0], series[0]), xytext=(8, 0), textcoords="offset points", color=INK_2, va="center")
    for ax, title in zip(axes, [f"Total time relative to {baseline}\n(timeouts count as the timeout)",
                                f"Geometric mean of the time ratio to {baseline}\n(formulas solved by both)",
                                f"Formulas more than 2× and 0.5 s slower\nthan {baseline}, per 1000 formulas"]):
        ax.set(xscale="log", yscale="log", xlabel="bound on states × transitions")
        ax.set_title(title)
        low, high = ax.get_ylim()
        ticks = [t for t in [0.5, 0.6, 0.7, 0.8, 0.9, 1, 1.5, 2, 3, 5, 7, 10, 20, 30, 50, 100] if low <= t <= high]
        ax.set_yticks(ticks, [f"{t:g}" for t in ticks])
        ax.yaxis.set_minor_formatter(matplotlib.ticker.NullFormatter())
    for ax in axes[:2]:
        ax.axhline(1, color=INK_2, linewidth=1, linestyle="--")
    fig.legend(*axes[0].get_legend_handles_labels(), frameon=False, loc="lower center", ncol=2)
    fig.tight_layout(rect=(0, 0.06, 1, 1))
    fig.savefig(f"{out}/thresholds.png", dpi=150)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("bench")
    parser.add_argument("baseline")
    parser.add_argument("new")
    parser.add_argument("--out", required=True)
    parser.add_argument("--thresholds", nargs="*", default=[], help="LABEL=BENCH.csv: benches of several bounds")
    parser.add_argument("--timeout", type=float, default=30)
    args = parser.parse_args()
    os.makedirs(args.out, exist_ok=True)

    if args.thresholds:
        thresholds([spec.split("=", 1) for spec in args.thresholds], args.baseline, args.out)
    runs, _ = load(args.bench, solvers=[args.baseline, args.new])
    scatter(runs, args.baseline, args.new, args.timeout, args.out)
    tail(runs, args.baseline, args.new, args.timeout, args.out)
    ratio(runs, args.baseline, args.new, args.out)
    sets(runs, args.baseline, args.new, args.out)


if __name__ == "__main__":
    main()
