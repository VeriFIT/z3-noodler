"""Plots of a benchmark of run.py: the times of two solvers, old and new (called by report.py).

scatter.png  the time of each formula, old against new, on log scales, with the diagonal and the lines of 2× slower and faster;
sets.png     the total time of each set, new relative to old.
Timeouts count as the timeout.
"""
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import matplotlib.ticker  # noqa: E402
import seaborn as sns  # noqa: E402

# Times below this are shown as this, as a log scale has no zero.
MIN_TIME = 0.01
# The ticks of the axis of the ratios of times.
RATIO_TICKS = [0.01, 0.03, 0.1, 0.25, 0.5, 1, 2, 4, 10, 30, 100]
# Tick labels such as 0.01 and 10 instead of powers of ten.
PLAIN_NUMBERS = matplotlib.ticker.FuncFormatter(lambda value, _: f"{value:g}")


def write_plots(runs, old, new, out_dir):
    """Writes scatter.png and sets.png into out_dir."""
    sns.set_theme(style="whitegrid")
    out_dir.mkdir(exist_ok=True)
    seconds = runs.pivot(index="file", columns="solver", values="seconds")
    plot_scatter(seconds[old], seconds[new], old, new, out_dir / "scatter.png")
    plot_sets(runs, old, new, out_dir / "sets.png")


def plot_scatter(old_seconds, new_seconds, old, new, path):
    """The time of each formula, old on the x axis and new on the y axis."""
    figure, axes = plt.subplots(figsize=(6.5, 6.5))
    sns.scatterplot(x=old_seconds.clip(lower=MIN_TIME), y=new_seconds.clip(lower=MIN_TIME), s=10, alpha=0.3, linewidth=0, rasterized=True,
                    ax=axes)

    # the diagonal (same time) and the dotted lines of 2× slower and 2× faster
    limits = (MIN_TIME * 0.8, max(old_seconds.max(), new_seconds.max()) * 1.25)
    axes.plot(limits, limits, color="gray", linewidth=1, linestyle="--")
    for factor in (2, 0.5):
        axes.plot(limits, [limit * factor for limit in limits], color="gray", linewidth=0.8, linestyle=":")

    axes.set(xscale="log", yscale="log", xlim=limits, ylim=limits, xlabel=f"{old} [s]", ylabel=f"{new} [s]",
             title=f"Time per formula ({len(old_seconds):,} formulas)")
    for axis in (axes.xaxis, axes.yaxis):
        axis.set_major_formatter(PLAIN_NUMBERS)
    save(figure, path)


def plot_sets(runs, old, new, path):
    """The total time of each set, new relative to old, with the two totals next to each dot."""
    totals = runs.groupby(["set", "solver"]).seconds.sum().unstack()
    ratios = (totals[new] / totals[old]).sort_values()

    figure, axes = plt.subplots(figsize=(8, 0.3 * len(ratios) + 1.5))
    sns.scatterplot(x=ratios.to_numpy(), y=ratios.index, s=60, ax=axes)
    axes.axvline(1, color="gray", linewidth=1, linestyle="--")
    for row, (name, ratio) in enumerate(ratios.items()):
        label = f"{totals.at[name, old]:,.1f} s → {totals.at[name, new]:,.1f} s"
        axes.annotate(label, (ratio, row), xytext=(8, 0), textcoords="offset points", va="center", fontsize=8, color="dimgray")

    # a log scale, so that 2× slower and 2× faster are equally far from 1, with room for the labels on the right
    axes.set_xscale("log")
    low, high = min(ratios.min(), 0.5) / 1.5, max(ratios.max(), 2) * 4
    axes.set_xlim(low, high)
    axes.set_xticks([tick for tick in RATIO_TICKS if low <= tick <= high])
    axes.xaxis.set_major_formatter(PLAIN_NUMBERS)
    axes.xaxis.set_minor_formatter(matplotlib.ticker.NullFormatter())
    axes.set(xlabel=f"total time of {new} / total time of {old}", ylabel="", title="Total time per set")
    save(figure, path)


def save(figure, path):
    """Saves a figure as a PNG and closes it."""
    figure.tight_layout()
    figure.savefig(path, dpi=150)
    plt.close(figure)
