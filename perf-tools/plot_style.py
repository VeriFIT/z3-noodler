"""Colors and matplotlib settings shared by the plots, so that they look alike."""
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

BLUE = "#2a78d6"
ORANGE = "#eb6834"
BACKGROUND = "#fcfcfb"
TEXT = "#0b0b0b"
SECONDARY_TEXT = "#52514e"
GRID = "#e4e3df"
# light to dark blue, for densities
BLUES = ["#cde2fb", "#9ec5f4", "#6da7ec", "#3987e5", "#256abf", "#184f95", "#0d366b"]


def apply():
    plt.rcParams.update({"figure.facecolor": BACKGROUND, "axes.facecolor": BACKGROUND, "savefig.facecolor": BACKGROUND,
                         "text.color": TEXT, "axes.labelcolor": TEXT, "xtick.color": SECONDARY_TEXT, "ytick.color": SECONDARY_TEXT,
                         "axes.edgecolor": SECONDARY_TEXT, "font.size": 10, "axes.spines.top": False, "axes.spines.right": False,
                         "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.6, "axes.titlesize": 11, "axes.titlelocation": "left"})
