#!/usr/bin/env python3
"""Statistical analysis of the cost of mata::nfa::reduce: which properties of the input automaton predict the time of a reduction.

Input: a benchmark of run_bench.py --reduce-log, best of a variant without guards (instrumentation/no-guards.patch) and with
REDUCE_LOG_GRAPH=1, so that every automaton is reduced and all properties are recorded.
Sections:
  overview      the time spent in reductions per set and per call site;
  ranking       each single property against the time: Spearman ρ, Kendall τ, and ROC AUC for "the call takes over N ms";
  cost models   linear models of log(time) on the logarithms of the properties, compared by cross-validation (grouped by formula);
                log(Q^a · T^b) = a·log Q + b·log T, so the fitted coefficients give the best products of powers of the properties;
  censored      the calls cut by the timeout, against the prediction of the model;
  benefit       how much the reductions shrink the automata, by cost and by site;
  guards        rules deciding whether to reduce, evaluated on the guarded sites.
Writes OUT_DIR/analysis.md and OUT_DIR/reduce-time.png.

Example: reduce_cost_analysis.py collection-dir --out collection-dir/analysis
"""
import argparse
import os
from pathlib import Path

import numpy as np
import pandas as pd
import statsmodels.api as sm
from scipy import stats
from sklearn.linear_model import LinearRegression
from sklearn.metrics import roc_auc_score
from sklearn.model_selection import GroupKFold
from sklearn.tree import DecisionTreeClassifier, export_text

import plot_style
import reduce_log

# Properties computable in one pass over the transitions, the candidates for a guard.
CHEAP_PROPERTIES = ["states", "transitions", "moves", "symbols"]
# Combinations of properties ranked next to the properties themselves (Q = states, T = transitions, M = moves, S = symbols).
COMBINATIONS = {"Q*T": ("states", "transitions"), "Q*M": ("states", "moves"), "Q*S": ("states", "symbols")}
# Models of log(time); each name lists the log-properties of the model.
MODELS = {
    "Q": ["states"],
    "T": ["transitions"],
    "Q*T": ["Q*T"],
    "Q+T": ["states", "transitions"],
    "Q+T+S": ["states", "transitions", "symbols"],
    "Q+T+S+M": ["states", "transitions", "symbols", "moves"],
    "Q+T+S+structure": ["states", "transitions", "symbols", "moves", "useful", "sccs", "max_scc", "cyclic", "max_out", "max_targets",
                        "deterministic", "final", "initial"],
    # the result is not known before the reduction; this model shows how much the number of simulation classes would explain
    "Q+T+S+result states": ["states", "transitions", "symbols", "res_states"],
}
MODEL_FOR_GUARDS = "Q+T+S"
FOLDS = 5
RANKING_THRESHOLDS_MS = [1, 10, 50]
GUARD_BUDGETS_MS = [1, 5, 10, 20, 50, 100]
# the state bounds of the branch before the cost guard, for comparison
STATE_BOUNDS = [100, 250, 1000]


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("bench_dirs", nargs="+", type=Path, help="output directories of run_bench.py --reduce-log (concatenated)")
    parser.add_argument("--out", required=True, type=Path, help="directory of analysis.md and the plot")
    return parser.parse_args()


def load(bench_dirs):
    """The distinct calls (one row per merged call of a run) and the runs."""
    calls = pd.concat([pd.read_csv(directory / "reduce-calls.csv", dtype={"caller": str, "operation": str}) for directory in bench_dirs],
                      ignore_index=True)
    runs = pd.concat([pd.read_csv(directory / "runs.csv") for directory in bench_dirs], ignore_index=True)
    for column in ["file", "set", "site"]:
        calls[column] = calls[column].astype("category")
    calls["guarded"] = calls.site.map(reduce_log.is_guarded).astype(bool)
    calls["formula"] = calls.file.cat.codes
    calls["ns"] = calls.ns_median
    for name, (left, right) in COMBINATIONS.items():
        calls[name] = calls[left].astype(float) * calls[right]
    return calls, runs


def log_features(calls, properties):
    """log(1 + x) of the properties, the inputs of the models."""
    return np.log1p(calls[properties].astype(float).clip(lower=0))


def log_time(calls):
    return np.log(calls.ns.astype(float).clip(lower=1))


def markdown(table, floatfmt=".3g"):
    return table.to_markdown(floatfmt=floatfmt)


def overview(calls, runs):
    per_set = runs.groupby("set").agg(formulas=("file", "nunique"), timeouts=("outcome", lambda outcome: (outcome == "timeout").sum()),
                                      solving_seconds=("seconds", "sum"), reductions=("reduce_calls", "sum"),
                                      reduce_seconds=("reduce_ns", lambda ns: ns.sum() / 1e9))
    per_set["reduce_share"] = per_set.reduce_seconds / per_set.solving_seconds
    per_site = calls.groupby("site", observed=True).agg(guarded=("guarded", "first"), reductions=("repeats", "sum"), distinct=("ns", "size"),
                                                         total_seconds=("ns_sum", lambda ns: ns.sum() / 1e9),
                                                         median_us=("ns", lambda ns: ns.median() / 1e3),
                                                         p99_ms=("ns", lambda ns: ns.quantile(0.99) / 1e6),
                                                         max_ms=("ns", lambda ns: ns.max() / 1e6), censored=("censored", "sum"))
    return "\n\n".join(["## Overview",
                        f"{runs.file.nunique()} formulas, {int(calls.repeats.sum())} reductions, {len(calls)} distinct ones "
                        f"(same run, site, input and result), {int(calls.censored.sum())} censored.",
                        markdown(per_set.sort_values("reduce_seconds", ascending=False)),
                        "Per call site (median and 99th percentile over the distinct reductions):",
                        markdown(per_site.sort_values("total_seconds", ascending=False))])


def expensive_and_known(calls, threshold_ms):
    """Whether each call takes over the threshold, and whether that is known (a censored call is known to be expensive only if its lower
    bound is over the threshold)."""
    expensive = calls.ns > threshold_ms * 1e6
    known = (calls.censored == 0) | expensive
    return expensive, known


def ranking(calls):
    finished = calls[calls.censored == 0]
    sample = finished.sample(min(len(finished), 200_000), random_state=1)
    time_ranks = finished.ns.rank()
    rows = {}
    for column in reduce_log.PROPERTIES + list(COMBINATIONS):
        values = finished[column]
        if values.nunique() < 2:
            continue
        # Spearman's ρ is the correlation of the ranks
        row = {"spearman": np.corrcoef(values.rank(), time_ranks)[0, 1], "kendall": stats.kendalltau(sample[column], sample.ns).statistic}
        for threshold_ms in RANKING_THRESHOLDS_MS:
            expensive, known = expensive_and_known(calls, threshold_ms)
            if expensive[known].nunique() == 2:
                row[f"AUC > {threshold_ms} ms"] = roc_auc_score(expensive[known], calls.loc[known, column])
        rows[column] = row
    return "\n\n".join(["## Ranking of single properties",
                        "Spearman ρ and Kendall τ (on a sample of at most 200k) with the time of the finished distinct calls, and the ROC AUC "
                        "of each property for a call over the threshold (censored calls over it count as expensive).",
                        markdown(pd.DataFrame(rows).T.sort_values("spearman", ascending=False))])


def grouped_folds(calls):
    """Cross-validation folds that keep the calls of one formula together."""
    return list(GroupKFold(n_splits=FOLDS).split(calls, groups=calls.formula))


def cross_validated(features, target, folds):
    """Out-of-fold predictions of a linear model, and the R² and RMSE of them."""
    predictions = np.empty(len(target))
    for train, test in folds:
        model = LinearRegression().fit(features[train], target[train])
        predictions[test] = model.predict(features[test])
    residual = ((target - predictions) ** 2).sum()
    return predictions, 1 - residual / ((target - target.mean()) ** 2).sum(), np.sqrt(residual / len(target))


def variance_inflation(features):
    """The variance inflation factor of each feature: the diagonal of the inverse of their correlation matrix."""
    return np.diag(np.linalg.inv(np.corrcoef(features, rowvar=False)))


def cost_models(calls, title):
    finished = calls[calls.censored == 0]
    target = log_time(finished).to_numpy()
    folds = grouped_folds(finished)
    rows, fits = {}, {}
    for name, properties in MODELS.items():
        features = log_features(finished, properties)
        fit = sm.OLS(target, sm.add_constant(features)).fit(cov_type="cluster", cov_kwds={"groups": finished.formula})
        _, r2_cv, rmse_cv = cross_validated(features.to_numpy(), target, folds)
        fits[name] = fit
        coefficients = ", ".join(f"{p} {fit.params[p]:.2f}±{fit.bse[p]:.2f}" for p in properties)
        rows[name] = {"R2": fit.rsquared, "R2_cv": r2_cv, "RMSE_cv": rmse_cv, "AIC": fit.aic, "coefficients": coefficients}
    base, bigger = fits["Q+T+S"], fits["Q+T+S+structure"]
    likelihood_ratio = 2 * (bigger.llf - base.llf)
    degrees = bigger.df_model - base.df_model
    inflation = variance_inflation(log_features(finished, MODELS["Q+T+S+M"]).to_numpy())
    return fits, "\n\n".join([
        f"## Cost models of log(time): {title}",
        f"{len(finished)} finished distinct calls of {finished.formula.nunique()} formulas; standard errors clustered by formula; "
        f"R2_cv and RMSE_cv by {FOLDS}-fold cross-validation grouped by formula.",
        markdown(pd.DataFrame(rows).T, floatfmt=".4g"),
        f"Likelihood-ratio test of the structure against Q+T+S: {likelihood_ratio:.1f}, df {degrees:.0f}, "
        f"p {stats.chi2.sf(likelihood_ratio, degrees):.3g} (with this many calls nearly any term is significant; effect sizes and R2_cv decide).",
        "Variance inflation of Q+T+S+M: " + ", ".join(f"{p} {v:.1f}" for p, v in zip(MODELS["Q+T+S+M"], inflation))])


def censored_calls(calls, fit):
    censored = calls[calls.censored == 1]
    if censored.empty:
        return "## Censored calls\n\nNone."
    predicted_ms = np.exp(fit.predict(sm.add_constant(log_features(censored, MODELS[MODEL_FOR_GUARDS]), has_constant="add"))) / 1e6
    table = censored[["set", "site", "states", "transitions", "symbols"]].assign(lower_bound_ms=censored.ns / 1e6, predicted_ms=predicted_ms)
    return "\n\n".join(["## Censored calls",
                        f"{len(censored)} calls cut by the timeout; their time is a lower bound (until the end of the run). The longest:",
                        markdown(table.sort_values("lower_bound_ms", ascending=False).head(30))])


def benefit(calls):
    finished = calls[calls.censored == 0].assign(state_ratio=lambda c: c.res_states / c.states.clip(lower=1),
                                                 transition_ratio=lambda c: c.res_transitions / c.transitions.clip(lower=1))
    cost = pd.cut(finished.ns / 1e6, [0, 0.1, 1, 10, 100, 1e3, np.inf], labels=["<0.1 ms", "0.1-1 ms", "1-10 ms", "10-100 ms", "0.1-1 s", ">1 s"])
    by_cost = finished[finished.guarded].groupby(cost[finished.guarded], observed=True).agg(
        calls=("ns", "size"), state_ratio=("state_ratio", "median"), transition_ratio=("transition_ratio", "median"))
    by_site = finished.groupby("site", observed=True).agg(calls=("ns", "size"), state_ratio=("state_ratio", "median"),
                                                           transition_ratio=("transition_ratio", "median"),
                                                           unchanged=("state_ratio", lambda ratio: (ratio >= 1).mean()))
    return "\n\n".join(["## Benefit of the reductions",
                        "Median ratios after / before by the cost of the call (guarded sites):", markdown(by_cost),
                        "By site (unchanged: the share of reductions that remove no state):", markdown(by_site.sort_values("calls", ascending=False))])


def best_threshold(values, expensive):
    """The threshold c of the rule "reduce if value <= c" with the best balanced accuracy at telling the expensive calls apart.

    Balanced accuracy weighs the rare expensive calls as much as the cheap ones, so the threshold is lower than the budget suggests.
    """
    order = np.argsort(values, kind="stable")
    sorted_values, sorted_expensive = values[order], expensive[order]
    # with c = sorted_values[i], the calls up to i are reduced and the others skipped
    cheap_reduced = np.cumsum(~sorted_expensive)
    expensive_reduced = np.cumsum(sorted_expensive)
    expensive_total, cheap_total = expensive_reduced[-1], cheap_reduced[-1]
    if expensive_total == 0 or cheap_total == 0:
        return np.inf
    balanced_accuracy = (expensive_total - expensive_reduced) / expensive_total + cheap_reduced / cheap_total
    # a threshold must not split equal values
    last_of_its_value = np.append(sorted_values[1:] != sorted_values[:-1], True)
    return sorted_values[np.argmax(np.where(last_of_its_value, balanced_accuracy, -np.inf))]


def threshold_rule(calls, column, budget_ms, folds):
    """Out-of-fold decisions (True = reduce) of "reduce if column <= c", with c chosen on the other folds, and c chosen on all calls."""
    expensive, known = expensive_and_known(calls, budget_ms)
    values, expensive, known = calls[column].to_numpy(float), expensive.to_numpy(), known.to_numpy()
    reduce = np.zeros(len(calls), dtype=bool)
    for train, test in folds:
        train = train[known[train]]
        reduce[test] = values[test] <= best_threshold(values[train], expensive[train])
    return reduce, best_threshold(values[known], expensive[known])


def guards(calls):
    guarded = calls[calls.guarded].copy()
    folds = grouped_folds(guarded)
    features = log_features(guarded, MODELS[MODEL_FOR_GUARDS]).to_numpy()
    finished = (guarded.censored == 0).to_numpy()
    predictions, _, _ = cross_validated(features[finished], log_time(guarded).to_numpy()[finished],
                                        grouped_folds(guarded[finished]))
    guarded["predicted_ns"] = np.inf
    guarded.loc[finished, "predicted_ns"] = np.exp(predictions)
    rules = {f"states < {bound}": guarded.states < bound for bound in STATE_BOUNDS}
    thresholds = {}
    for budget_ms in GUARD_BUDGETS_MS:
        rules[f"model ≤ {budget_ms} ms"] = guarded.predicted_ns <= budget_ms * 1e6
        for column in ["Q*T", "Q*M"]:
            reduce, threshold = threshold_rule(guarded, column, budget_ms, folds)
            rules[f"{column} ≤ c({budget_ms} ms)"] = pd.Series(reduce, index=guarded.index)
            thresholds[f"{column} ≤ c({budget_ms} ms)"] = threshold
    weight = guarded.repeats
    removed_states = (guarded.states - guarded.res_states.fillna(guarded.states)).clip(lower=0)
    rows = {}
    for name, reduce in rules.items():
        row = {"reduced": (weight * reduce).sum() / weight.sum(), "time_kept": (guarded.ns * weight * reduce).sum() / (guarded.ns * weight).sum(),
               "removed_states_lost": (removed_states * weight * ~reduce).sum() / max(1, (removed_states * weight).sum())}
        for budget_ms in GUARD_BUDGETS_MS:
            expensive = guarded.ns > budget_ms * 1e6
            row[f"kept > {budget_ms} ms"] = int((weight * (reduce & expensive)).sum())
            row[f"skipped ≤ {budget_ms} ms"] = int((weight * (~reduce & ~expensive)).sum())
        rows[name] = row
    sections = ["## Candidate guards",
                "On the guarded sites, calls weighted by their repeats, out-of-fold decisions. Columns: the share of the reductions done, the "
                "share of the reduction time still spent, the share of the removed states lost by skipping, and for each budget B the calls "
                "over B still reduced and the calls under B skipped. c(B) is chosen by balanced accuracy (see best_threshold).",
                markdown(pd.DataFrame(rows).T),
                "Thresholds chosen on all guarded calls: " + ", ".join(f"{name}: c = {value:.3g}" for name, value in thresholds.items())]
    for budget_ms in GUARD_BUDGETS_MS:
        expensive, known = expensive_and_known(guarded, budget_ms)
        if expensive[known].nunique() < 2:
            continue
        names = [f"log_{p}" for p in CHEAP_PROPERTIES]
        tree = DecisionTreeClassifier(max_depth=2, class_weight="balanced").fit(
            log_features(guarded[known], CHEAP_PROPERTIES).to_numpy(), expensive[known], sample_weight=weight[known])
        sections.append(f"Depth-2 decision tree for over {budget_ms} ms (thresholds on log(1 + x)):\n```\n"
                        f"{export_text(tree, feature_names=names).rstrip()}\n```")
    return "\n\n".join(sections)


def plot_time(calls, fit, path):
    import matplotlib.pyplot as plt
    from matplotlib.colors import LinearSegmentedColormap

    plot_style.apply()
    finished, censored = calls[calls.censored == 0], calls[calls.censored == 1]
    predicted = fit.predict(sm.add_constant(log_features(calls, MODELS[MODEL_FOR_GUARDS]), has_constant="add")) / np.log(10)
    panels = [("states", np.log10(calls.states.clip(lower=1))), ("transitions", np.log10(calls.transitions.clip(lower=1))),
              ("states × transitions", np.log10(calls["Q*T"].clip(lower=1))), ("predicted time [ns]", predicted)]
    colors = LinearSegmentedColormap.from_list("blues", plot_style.BLUES)
    figure, axes = plt.subplots(1, 4, figsize=(18, 4.5), sharey=True)
    for panel, (label, x) in zip(axes, panels):
        panel.hexbin(x[finished.index], np.log10(finished.ns.clip(lower=1)), gridsize=60, bins="log", cmap=colors, mincnt=1, linewidths=0)
        panel.scatter(x[censored.index], np.log10(censored.ns.clip(lower=1)), marker="^", s=24, color=plot_style.ORANGE,
                      label="censored (lower bound)")
        panel.set_xlabel(f"log10 {label}")
    axes[0].set_ylabel("log10 time of reduce [ns]")
    axes[0].legend(loc="upper left", frameon=False)
    limits = axes[3].get_xlim()
    axes[3].plot(limits, limits, color=plot_style.SECONDARY_TEXT, linewidth=1, linestyle="--")
    figure.suptitle("Time of mata::nfa::reduce (distinct calls; density of the finished ones, log scale)")
    figure.tight_layout()
    figure.savefig(path, dpi=130)
    plt.close(figure)


def main():
    args = parse_arguments()
    os.makedirs(args.out, exist_ok=True)
    calls, runs = load(args.bench_dirs)
    fits, all_models = cost_models(calls, "all distinct calls")
    _, guarded_models = cost_models(calls[calls.guarded], "guarded sites")
    _, big_models = cost_models(calls[calls.states >= 100], "calls with at least 100 states")
    sections = ["# Cost of mata::nfa::reduce", f"Benchmarks: {', '.join(map(str, args.bench_dirs))}", overview(calls, runs), ranking(calls),
                all_models, guarded_models, big_models, censored_calls(calls, fits[MODEL_FOR_GUARDS]), benefit(calls), guards(calls)]
    text = "\n\n".join(sections) + "\n"
    (args.out / "analysis.md").write_text(text)
    plot_time(calls, fits[MODEL_FOR_GUARDS], args.out / "reduce-time.png")
    print(text)


if __name__ == "__main__":
    main()
