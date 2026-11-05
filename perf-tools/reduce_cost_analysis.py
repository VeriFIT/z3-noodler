#!/usr/bin/env python3
"""Statistical analysis of the cost of mata::nfa::reduce from the statistics of reduce_stats_collect.py (REDUCE-COST-PLAN.md, section 4).

Steps: merging of repeated calls, ranking of single properties (Spearman, Kendall, ROC AUC of "expensive"), OLS cost models of log(time)
with standard errors clustered by formula, grouped cross-validation, censored calls, benefit of the reductions, and candidate guards.
The tables go to OUT/analysis.md (and stdout), the plots to OUT/*.png.
Usage: reduce_cost_analysis.py PREFIX [PREFIX...] --out DIR [--budgets-ms 1,5,10,20,50,100] [--sample N]
PREFIX is the prefix of a collection (PREFIX-calls.csv, PREFIX-formulas.csv, PREFIX-callers.csv); several collections are concatenated.
"""
import argparse
import os
import sys

import numpy as np
import pandas as pd
import pyarrow as pa
import pyarrow.csv as pa_csv
import statsmodels.api as sm
from scipy import stats
from sklearn.linear_model import LinearRegression
from sklearn.metrics import roc_auc_score
from sklearn.model_selection import GroupKFold
from sklearn.tree import DecisionTreeClassifier, export_text
from statsmodels.stats.outliers_influence import variance_inflation_factor

PROPERTIES = ["states", "initial", "final", "useful", "transitions", "moves", "epsilon", "self_loops", "symbols", "max_out", "max_targets",
              "deterministic", "sccs", "max_scc", "cyclic"]
# properties computable in O(transitions) without a graph search, the candidates for the guard
CHEAP = ["states", "transitions", "moves", "symbols"]
# sites whose reduction is guarded by a state bound in the branch
GUARDED_PREFIXES = ("construction:", "final_check_intersection", "memb_heuristic_")
UNGUARDED_CONSTRUCTION = ("construction:loop_body", "construction:loop_body_unbounded")
# palette of the dataviz reference instance
SURFACE, INK, INK_2, BLUE, ORANGE = "#fcfcfb", "#0b0b0b", "#52514e", "#2a78d6", "#eb6834"
SEQUENTIAL = ["#cde2fb", "#9ec5f4", "#6da7ec", "#3987e5", "#256abf", "#184f95", "#0d366b"]

out_lines = []


def emit(text=""):
    print(text)
    out_lines.append(text)


def table(df, floatfmt=".3g"):
    emit(df.to_markdown(floatfmt=floatfmt))
    emit()


def site_of(function, location, operation):
    """Short name of a call site."""
    name = function.split("(")[0].split("::")[-1] if isinstance(function, str) else "?"
    line = location.rsplit(":", 1)[-1] if isinstance(location, str) else "?"
    if name == "create_nfa_for_expr":
        return f"construction:{operation}"
    if name == "create_aut_assignment_for_formula":
        return "final_check_intersection"
    if name == "compute_next_solution":
        return "memb_heuristic_intersection" if line == "125" else "memb_heuristic_union"
    return f"{name}:{line}" if line not in ("?", "0") else name


def is_guarded(site):
    return site.startswith(GUARDED_PREFIXES) and site not in UNGUARDED_CONSTRUCTION


def load(prefixes):
    calls, formulas = [], []
    for prefix in prefixes:
        parquet = f"{prefix}-calls.parquet"
        if os.path.exists(parquet) and os.path.getmtime(parquet) >= os.path.getmtime(f"{prefix}-calls.csv"):
            c = pd.read_parquet(parquet)
        else:
            options = pa_csv.ConvertOptions(column_types={"caller": pa.string(), "operation": pa.string()})
            c = pa_csv.read_csv(f"{prefix}-calls.csv", convert_options=options).to_pandas()
            c.to_parquet(parquet)
        callers = pd.read_csv(f"{prefix}-callers.csv").set_index("caller")
        pairs = c[["caller", "operation"]].drop_duplicates()
        pairs["site"] = [site_of(callers.function.get(a), callers.location.get(a), op) for a, op in zip(pairs.caller, pairs.operation)]
        c = c.merge(pairs, on=["caller", "operation"], how="left")
        calls.append(c)
        formulas.append(pd.read_csv(f"{prefix}-formulas.csv"))
    return pd.concat(calls, ignore_index=True), pd.concat(formulas, ignore_index=True)


def merge_repeats(calls):
    """One row per distinct call of a formula (same site, properties and result), with the median time and the number of repeats.

    The collector merges the calls already; raw rows (one per call) of older collections are merged here.
    """
    if "repeats" in calls:
        merged = calls
    else:
        key = ["file", "site"] + PROPERTIES + ["res_states", "res_transitions", "censored"]
        calls["key"] = pd.util.hash_pandas_object(calls[key], index=False)
        merged = calls.groupby(["file", "key"], sort=False).agg(
            set=("set", "first"), site=("site", "first"), alphabet=("alphabet", "max"), ns=("ns", "median"), ns_min=("ns", "min"),
            ns_max=("ns", "max"), ns_sum=("ns", "sum"), repeats=("ns", "size"),
            **{p: (p, "first") for p in PROPERTIES + ["res_states", "res_transitions", "censored"]})
        merged = merged.reset_index().drop(columns="key")
    # the alphabet of the formula where the call site does not know it
    merged["alphabet"] = merged["alphabet"].where(merged["alphabet"] >= 0)
    merged["alphabet"] = merged["alphabet"].fillna(merged.groupby("file")["alphabet"].transform("max"))
    return merged


def add_features(df):
    q, t, s, m = (df[c].astype(float) for c in ["states", "transitions", "symbols", "moves"])
    df["Q*T"] = q * t
    df["Q*M"] = q * m
    df["Q*S"] = q * s
    df["Q^2*S"] = q * q * s
    df["T/Q"] = t / q.clip(lower=1)
    df["completeness"] = m / (q * s).clip(lower=1)
    for c in PROPERTIES + ["Q*T", "Q*M", "Q*S", "Q^2*S", "T/Q", "completeness", "alphabet", "res_states"]:
        df[f"l_{c}"] = np.log(df[c].astype(float).clip(lower=0) + 1)
    df["l_states^2"] = df["l_states"] ** 2
    df["l_transitions^2"] = df["l_transitions"] ** 2
    df["l_ns"] = np.log(df["ns"].astype(float).clip(lower=1))
    return df


def overview(merged, formulas):
    emit("## Overview")
    emit()
    emit(f"{len(formulas)} formulas, {int(merged.repeats.sum())} calls, {len(merged)} distinct calls (same formula, site, properties and result), "
         f"{int(merged.censored.sum())} censored.")
    emit()
    f = formulas.assign(timeout=formulas.result.eq("timeout"))
    per_set = f.groupby("set").agg(formulas=("file", "size"), timeouts=("timeout", "sum"), seconds=("seconds", "sum"),
                                   reduce_s=("reduce_ns", lambda x: x.sum() / 1e9), calls=("calls", "sum"))
    per_set["reduce_share"] = per_set.reduce_s / per_set.seconds
    table(per_set.sort_values("reduce_s", ascending=False))
    emit("Per site (median and p99 over the distinct calls):")
    emit()
    per_site = merged.groupby("site").agg(calls=("repeats", "sum"), distinct=("ns", "size"), total_s=("ns_sum", lambda x: x.sum() / 1e9),
                                          median_us=("ns", lambda x: x.median() / 1e3), p99_ms=("ns", lambda x: x.quantile(.99) / 1e6),
                                          max_ms=("ns", lambda x: x.max() / 1e6), censored=("censored", "sum"))
    per_site["guarded"] = [is_guarded(s) for s in per_site.index]
    table(per_site.sort_values("total_s", ascending=False))


def ranking(df, thresholds_ms):
    emit("## Ranking of single properties")
    emit()
    emit("Spearman ρ and Kendall τ with the time (non-censored distinct calls; τ on a sample of at most 200k), "
         "ROC AUC of each property for a call over the threshold (censored calls over it count as expensive).")
    emit()
    done = df[df.censored == 0]
    sample = done.sample(min(len(done), 200_000), random_state=1)
    rows = {}
    for c in PROPERTIES + ["alphabet", "Q*T", "Q*M", "Q*S", "Q^2*S", "T/Q", "completeness"]:
        # nan_policy="omit" falls back to the masked versions, which are quadratic
        d, s = done[done[c].notna()], sample[sample[c].notna()]
        row = {"spearman": stats.spearmanr(d[c], d.ns).statistic, "kendall": stats.kendalltau(s[c], s.ns).statistic}
        for ms in thresholds_ms:
            y = df.ns > ms * 1e6
            known = (df.censored == 0) | y
            if y[known].nunique() == 2:
                row[f"AUC>{ms}ms"] = roc_auc_score(y[known], df.loc[known, c].fillna(0))
        rows[c] = row
    table(pd.DataFrame(rows).T.sort_values("spearman", ascending=False))


MODELS = {
    "Q": ["l_states"],
    "T": ["l_transitions"],
    "Q*T": ["l_Q*T"],
    "Q+T": ["l_states", "l_transitions"],
    "Q+T+S": ["l_states", "l_transitions", "l_symbols"],
    "Q+T+S+M": ["l_states", "l_transitions", "l_symbols", "l_moves"],
    "Q+T/Q+S+compl": ["l_states", "l_T/Q", "l_symbols", "l_completeness"],
    "Q+T+S+structure": ["l_states", "l_transitions", "l_symbols", "l_moves", "l_useful", "l_sccs", "l_max_scc", "l_cyclic", "l_max_out",
                        "l_max_targets", "deterministic", "l_final", "l_initial"],
    "Q+T+Q²+T²": ["l_states", "l_transitions", "l_states^2", "l_transitions^2"],
    "Q+T+S+Q²+T²": ["l_states", "l_transitions", "l_symbols", "l_states^2", "l_transitions^2"],
    "post: Q+T+S+classes": ["l_states", "l_transitions", "l_symbols", "l_res_states"],
}


def cv_score(df, features, groups, folds=5):
    """Grouped (by formula) k-fold cross-validated R² and RMSE of log(time)."""
    x, y = df[features].to_numpy(), df["l_ns"].to_numpy()
    sse, sst = 0.0, 0.0
    for train, test in GroupKFold(n_splits=folds).split(x, y, groups):
        model = LinearRegression().fit(x[train], y[train])
        sse += ((model.predict(x[test]) - y[test]) ** 2).sum()
        sst += ((y[test] - y[train].mean()) ** 2).sum()
    return 1 - sse / sst, np.sqrt(sse / len(y))


def cost_models(df, name):
    emit(f"## Cost models of log(time): {name}")
    emit()
    done = df[df.censored == 0].copy()
    groups = done["file"].astype("category").cat.codes.to_numpy()
    emit(f"{len(done)} distinct non-censored calls of {len(np.unique(groups))} formulas; standard errors clustered by formula.")
    emit()
    rows, fits = {}, {}
    for model_name, features in MODELS.items():
        x = sm.add_constant(done[features].astype(float))
        fit = sm.OLS(done["l_ns"], x).fit(cov_type="cluster", cov_kwds={"groups": groups})
        r2_cv, rmse_cv = cv_score(done, features, groups)
        fits[model_name] = fit
        rows[model_name] = {"R2": fit.rsquared, "R2_cv": r2_cv, "RMSE_cv": rmse_cv, "AIC": fit.aic, "BIC": fit.bic,
                            "coefficients": ", ".join(f"{f.removeprefix('l_')} {fit.params[f]:.2f}±{fit.bse[f]:.2f}" for f in features)}
    table(pd.DataFrame(rows).T, floatfmt=".4g")
    base, bigger = fits["Q+T+S"], fits["Q+T+S+structure"]
    lr = 2 * (bigger.llf - base.llf)
    emit(f"Likelihood-ratio test structure vs Q+T+S: LR {lr:.1f}, df {bigger.df_model - base.df_model:.0f}, "
         f"p {stats.chi2.sf(lr, bigger.df_model - base.df_model):.3g} (non-robust; with this many calls, effect sizes and CV decide).")
    emit()
    x = sm.add_constant(done[MODELS["Q+T+S+M"]].astype(float))
    vif = {c: variance_inflation_factor(x.to_numpy(), i) for i, c in enumerate(x.columns) if c != "const"}
    emit("VIF (Q+T+S+M): " + ", ".join(f"{c.removeprefix('l_')} {v:.1f}" for c, v in vif.items()))
    emit()
    return fits


def censored_check(df, fit, features):
    emit("## Censored calls")
    emit()
    cens = df[df.censored == 1]
    if cens.empty:
        emit("No censored calls.")
        emit()
        return
    pred = np.exp(fit.predict(sm.add_constant(cens[features].astype(float), has_constant="add")))
    out = cens[["set", "site", "states", "transitions", "symbols", "moves", "ns"]].assign(lower_bound_ms=cens.ns / 1e6, predicted_ms=pred / 1e6)
    emit(f"{len(cens)} censored calls; predicted time vs the lower bound (time until the end of the run):")
    emit()
    table(out.drop(columns="ns").sort_values("lower_bound_ms", ascending=False).head(30))


def benefit(df):
    emit("## Benefit of the reductions")
    emit()
    done = df[df.censored == 0].copy()
    done["state_ratio"] = done.res_states / done.states.clip(lower=1)
    done["transition_ratio"] = done.res_transitions / done.transitions.clip(lower=1)
    done["cost"] = pd.cut(done.ns / 1e6, [0, 0.1, 1, 10, 100, 1e3, 1e9], labels=["<0.1ms", "0.1-1ms", "1-10ms", "10-100ms", "0.1-1s", ">1s"])
    emit("Median ratios after/before by cost of the call (guarded sites):")
    emit()
    g = done[done.site.map(is_guarded)].groupby("cost", observed=True).agg(calls=("ns", "size"), state_ratio=("state_ratio", "median"),
                                                                            transition_ratio=("transition_ratio", "median"))
    table(g)
    emit("By site:")
    emit()
    g = done.groupby("site").agg(calls=("ns", "size"), state_ratio=("state_ratio", "median"), transition_ratio=("transition_ratio", "median"),
                                 unchanged=("state_ratio", lambda x: (x >= 1).mean()))
    table(g.sort_values("calls", ascending=False))


def out_of_fold(df, features, folds=5):
    """Predictions of log(time) for each non-censored call by a model fitted on the other folds (grouped by formula); censored calls get
    the prediction of the model fitted on all non-censored calls."""
    done = df.censored == 0
    x, y = df[features].to_numpy(float), df["l_ns"].to_numpy()
    groups = df["file"].astype("category").cat.codes.to_numpy()
    pred = LinearRegression().fit(x[done], y[done]).predict(x)
    idx = np.flatnonzero(done)
    for train, test in GroupKFold(n_splits=folds).split(idx, groups=groups[idx]):
        pred[idx[test]] = LinearRegression().fit(x[idx[train]], y[idx[train]]).predict(x[idx[test]])
    return pred


def product_rule(df, product, budget_ns, folds=5):
    """Out-of-fold decisions (True = reduce) of the rule product <= c, with c chosen on the other folds (grouped by formula) to maximize
    the balanced accuracy of telling the calls over budget_ns, and the threshold chosen on all calls."""
    y = (df.ns > budget_ns).to_numpy()
    known = ((df.censored == 0) | y).to_numpy()
    p = df[product].to_numpy(float)
    groups = df["file"].astype("category").cat.codes.to_numpy()

    def best_threshold(rows):
        rows = rows[known[rows]]
        if y[rows].all() or not y[rows].any():
            return np.inf
        candidates = np.unique(np.quantile(p[rows], np.linspace(0, 1, 400)))
        pos, neg = y[rows].sum(), (~y[rows]).sum()
        scores = [((p[rows] > c) & y[rows]).sum() / pos + ((p[rows] <= c) & ~y[rows]).sum() / neg for c in candidates]
        return candidates[int(np.argmax(scores))]

    reduce = np.zeros(len(df), dtype=bool)
    for train, test in GroupKFold(n_splits=folds).split(p, groups=groups):
        reduce[test] = p[test] <= best_threshold(train)
    return reduce, best_threshold(np.arange(len(df)))


def guards(df, fit, features, budgets_ms):
    emit("## Candidate guards (guarded sites, calls weighted by repeats, out-of-fold decisions)")
    emit()
    g = df[df.site.map(is_guarded)].copy()
    g["predicted"] = np.exp(out_of_fold(g, features))
    g["weight"] = g.repeats
    total = (g.ns * g.weight).sum()
    removed = (g.states - g.res_states.fillna(g.states)).clip(lower=0)
    rules = {"Q<100": g.states < 100, "Q<250": g.states < 250, "Q<1000": g.states < 1000}
    thresholds = {}
    for ms in budgets_ms:
        rules[f"model<={ms}ms"] = g.predicted <= ms * 1e6
        for product in ["Q*T", "Q*M"]:
            reduce, c = product_rule(g, product, ms * 1e6)
            rules[f"{product}<=c({ms}ms)"] = pd.Series(reduce, index=g.index)
            thresholds[f"{product}<=c({ms}ms)"] = c
    emit("Columns: share of reduced calls, share of the reduce time still spent, for each budget B the calls over B still reduced and the "
         "calls under B skipped, and the share of the states removed by the reductions that is lost by skipping.")
    emit()
    rows = {}
    for name, reduce in rules.items():
        row = {"reduced_calls": (g.weight * reduce).sum() / g.weight.sum(), "time_kept": (g.ns * g.weight * reduce).sum() / total}
        for ms in budgets_ms:
            expensive = g.ns > ms * 1e6
            row[f"kept>{ms}ms"] = int((g.weight * (reduce & expensive)).sum())
            row[f"skipped<={ms}ms"] = int((g.weight * (~reduce & ~expensive)).sum())
        row["states_removed_lost"] = (removed * g.weight * ~reduce).sum() / max(1, (removed * g.weight).sum())
        rows[name] = row
    table(pd.DataFrame(rows).T)
    emit("Thresholds of the product rules fitted on all guarded calls: " + ", ".join(f"{k}: c = {v:.3g}" for k, v in thresholds.items()))
    emit()
    for ms in budgets_ms:
        y = g.ns > ms * 1e6
        known = (g.censored == 0) | y
        if y[known].nunique() < 2:
            continue
        tree = DecisionTreeClassifier(max_depth=2, class_weight="balanced").fit(g.loc[known, [f"l_{c}" for c in CHEAP]], y[known],
                                                                                 sample_weight=g.loc[known, "weight"])
        emit(f"Depth-2 tree for > {ms} ms (thresholds on log(x+1) of {', '.join(CHEAP)}):")
        emit("```")
        emit(export_text(tree, feature_names=[f"l_{c}" for c in CHEAP]).rstrip())
        emit("```")
        emit()


def plots(df, fit, features, out):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.colors import LinearSegmentedColormap

    cmap = LinearSegmentedColormap.from_list("blue", SEQUENTIAL)
    plt.rcParams.update({"figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "text.color": INK, "axes.labelcolor": INK,
                         "xtick.color": INK_2, "ytick.color": INK_2, "axes.edgecolor": INK_2, "font.size": 10})
    done, cens = df[df.censored == 0], df[df.censored == 1]
    pred = fit.predict(sm.add_constant(df[features].astype(float), has_constant="add"))
    panels = [("states", np.log10(df.states.clip(lower=1))), ("transitions", np.log10(df.transitions.clip(lower=1))),
              ("states × transitions", np.log10((df.states * df.transitions).clip(lower=1))), ("predicted time [ns]", pred / np.log(10))]
    fig, axes = plt.subplots(1, 4, figsize=(18, 4.5), sharey=True)
    for ax, (label, x) in zip(axes, panels):
        ax.hexbin(x[done.index], np.log10(done.ns.clip(lower=1)), gridsize=60, bins="log", cmap=cmap, mincnt=1, linewidths=0)
        ax.scatter(x[cens.index], np.log10(cens.ns.clip(lower=1)), marker="^", s=24, color=ORANGE, label="censored (lower bound)")
        ax.set_xlabel(f"log10 {label}")
        ax.grid(color="#e4e3df", linewidth=0.6)
    axes[0].set_ylabel("log10 time of reduce [ns]")
    axes[0].legend(loc="upper left", frameon=False)
    lim = axes[3].get_xlim()
    axes[3].plot(lim, lim, color=INK_2, linewidth=1, linestyle="--")
    fig.suptitle("Time of mata::nfa::reduce (distinct calls; density of non-censored calls, log scale)", color=INK)
    fig.tight_layout()
    fig.savefig(f"{out}/reduce-time.png", dpi=130)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("prefixes", nargs="+")
    parser.add_argument("--out", required=True)
    parser.add_argument("--budgets-ms", default="1,5,10,20,50,100")
    parser.add_argument("--model", default="Q+T+S", help="the model used for the censored calls, the guards and the plots")
    args = parser.parse_args()
    budgets = [float(b) if "." in b else int(b) for b in args.budgets_ms.split(",")]
    os.makedirs(args.out, exist_ok=True)

    calls, formulas = load(args.prefixes)
    merged = add_features(merge_repeats(calls))
    emit("# Cost of mata::nfa::reduce")
    emit()
    emit(f"Collections: {', '.join(args.prefixes)}")
    emit()
    overview(merged, formulas)
    ranking(merged, [1, 10, 50])
    fits = cost_models(merged, "all distinct calls")
    guarded = merged[merged.site.map(is_guarded)]
    cost_models(guarded, "guarded sites")
    cost_models(merged[merged.states >= 100], "calls with at least 100 states")
    features = MODELS[args.model]
    censored_check(merged, fits[args.model], features)
    benefit(merged)
    guards(merged, fits[args.model], features, budgets)
    plots(merged, fits[args.model], features, args.out)
    with open(f"{args.out}/analysis.md", "w") as f:
        f.write("\n".join(out_lines) + "\n")


if __name__ == "__main__":
    sys.exit(main())
