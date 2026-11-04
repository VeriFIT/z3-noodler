# Handoff: z3-noodler performance experiment (branch `perf-experiment`)

Written 2026-11-04 on the laptop, which will not be used anymore.
The next session runs on a more powerful machine and focuses on **a cost-based guard for `mata::nfa::reduce`**: collect statistics of every `reduce` call on all smt-bench formulas, find the metric that predicts its cost by statistical tests, implement the guard and compare it with the current state.
The user expects this to be a big performance leap.

The plan of that work is in `perf-tools/REDUCE-COST-PLAN.md` (do not duplicate it, follow it).
Per-set results of all benchmarks run since 2026-11-03 are in `perf-tools/results/SUMMARY.md`.

## Where things are

- Repo: `VeriFIT/z3-noodler` (remote `origin`), branch `perf-experiment`.
  Base: 2d58ba1af, the tip of `fix-from-regex-quantifier` (PR #553, the last of the stacked chain #550 `ecma-unknown-issues` ← #551 `from-regex` ← #552 `re2-regex` ← #553).
- State at handoff: committed in one commit per component (see "What the branch contains") and pushed to `origin/perf-experiment`.
  The last commit adds this handoff and `perf-tools/`; it is only for moving them to the new machine and is to be dropped before the changes are split into pull requests.
  Decided with the user: `RED_BOUND` stays 1000 in the branch (250 is the best state-count value measured, see below), the unit-test expectations and an e2e test for the `handle_in_re` fix are done on the new machine.
- `perf-tools/` (helper folder, committed only in the last commit):
  - `REDUCE-COST-PLAN.md`: the plan.
  - `results/SUMMARY.md`: brief per-set results of every run (appended by `summarize.py`).
  - `smtbench_run.py`: runner; either `--sets` of smt-bench (`$SMT_BENCH` = its `bench/` dir) or `--list FILE` with lines `SET;ABSOLUTE_PATH;OPTIONS`; random order, the runs of one formula queued next to each other, resumable (skips rows already in the CSV), `--minutes` deadline, `--sample`/`--sample-all`; runs `z3 OPTIONS model=false -smt2 -in` on the formula cleaned like smt-bench's `bin/clean-formula.sh`.
  - `smtbench_compare.py RESULTS.csv A B`: per-set outcomes (solved, wrong vs `:status`, sat/unsat disagreement, timeout, unknown, crash), time on formulas solved by both, changed outcomes, biggest slowdowns/speedups.
  - `summarize.py TITLE --note ... CSV...`: appends a per-set table to `results/SUMMARY.md`.
  - `bound_probe.py`: runs an instrumented binary (`$PROBE_Z3`) on a formula list and records the largest intersection reduced in `create_aut_assignment_for_formula`; the base for the planned collection runner.
  - `reduce_wrap.cpp`: link-time wrapper of `mata::nfa::reduce` (see "Methods"); the base for the planned instrumentation.
  - `build_variant.sh NAME SRC=REPLACEMENT...`: builds `build/<preset>/variants/NAME/z3` from the existing build, recompiling only the replaced `.cpp` files (a file or a git revision) and relinking; `REPO` and `PRESET` env vars.
  - `patches/fix-bounded-loop-on-devel-02df8c931.patch`: the clean #502 fix on devel (branch `fix-bounded-loop` exists locally at 02df8c931 without commits); the same code is in `perf-experiment`.
- Raw CSVs, logs, variant binaries and old scripts stayed on the laptop (`~/Documents/perf-experiment-archive-2026-11-04/` and `build/release/variants/`); everything needed from them is in `SUMMARY.md` and below.
- Benchmarks (sibling repos):
  - `ecma2020-smt-bench` (Kumismar/ecma2020-smt-bench): `smt_out/memberships/` (8815) and `smt_out/mixed_constraints/bmp/` (4000: lang_ops 400, lang_inclusion 1000, lang_equality 1000, random_mix 1600); `run.py` (several binaries `./z3-<suffix>` in one random pool, `;` CSV), `compare.py`, `run_memory_ceiling.sh`.
    Options per folder in `run.py`'s `SOLVER_OPTIONS`: memberships none, mixed constraints `smt.str.ecma_engine_semantics=true`.
  - `smt-bench` (the VeriFIT benchmarking platform): `bench/<set>.input` lists, `download_smt_benchmarks.sh` (SMT-LIB'25 QF_S/QF_SLIA/QF_SNIA from Zenodo, ~36 MB), submodules zaligvinder, regex-smt-benchmarks, ecma2020-smt-bench; `smt.yaml` tool `z3-noodler-ecma` adds engine semantics.
  - `ecma-2020-mixed-constraints-bench` (private): the older mixed set used for the v1/v2 runs.

## What the branch contains

Relative to 2d58ba1af (see `git diff`/`git log` for the code):
1. **#502 bounded loops** (`regex.h` `concatenate_up_to_nth_power`, `regex.cpp` loop cases of the NFA and NFT construction): `{lo,hi}` was built as `concatenate_nth_power` of (body | ε), which links every copy to all later copies (`{2,256}` over 70 symbols: 2.27M transitions, 13 s reduce); now a linear chain of copies whose ends stay final.
   Tests: `src/test/noodler/regex.cpp` (new Catch2 file, added to `src/test/noodler/CMakeLists.txt`), `src/test/noodler/e2e/issue-502-bounded-loop.smt2`.
2. **#501 co-finiteness** (`aut_assignment.h`): `is_co_finite` complements without `minimize`, with a pre-check `accepts_long_powers` (for each symbol a, whether all long a^n are accepted; the sets of states reached by a^n repeat).
3. **#503 fewer reductions** (`regex.cpp`): no `reduce` of leaf automata (`num_of_regex_arguments_of_cur_expr > 0`) and of bounded-loop chains of reduced bodies (`is_almost_reduced`).
   Note: one `regex.cpp` hunk mixes #502 and #503 (`is_almost_reduced = true` inside the loop case), splitting them into commits needs a hand-made patch (`git apply --cached`), interactive staging is not available.
4. **Intersection guard** (`theory_str_noodler_final_check.cpp`, `regex.h`): the intersection of the memberships of one variable in `create_aut_assignment_for_formula` is reduced only below `regex::INTERSECTION_RED_BOUND = 100` states (devel always reduces it).
   `RED_BOUND` (1000) stays for the NFA construction and the membership heuristics.
5. **Soundness fix in `handle_in_re`** (`theory_str_noodler.cpp`): for a membership of a complex term, the axiom uses `ctx.get_literal(e)`; `mk_literal(e)` rewrote `e` again, and the prefix-factoring rule of `seq_rewriter::mk_re_union` (6ccaa5f31) is not idempotent, so the axiom constrained an unassigned copy (unsound sat on `[0-9]{9}|[0-9]{14}` over `y ++ z`).
   Plus a guard in `internalize_term`: return if `ctx.b_internalized(term)` after internalizing the arguments (two `re.from_regex` memberships with the same classical regex internalized the term twice).
6. **Regex simplification** (new `extended_regex/regex_simplification.{h,cpp}`, called from `extended_regex.cpp`, added to `src/smt/CMakeLists.txt`): `make_matching_explicit` (absorbs `^`/`$` anchors and makes the engine semantics explicit, then `build_rcg(..., false)`), Σ* trimming, `fold_lookarounds` (single-character lookarounds folded, no global flattening).
   Effect: ~36 % of ecma2020 patterns are anchored and used to need fresh variables, equations and a quantified axiom; now many become classical regexes (e.g., regex_3299 6.5 → 0.14 s).
7. **Translation of repetitions** (`extended_regex/regex_constraint_graph.cpp`): `re.loop` instead of chains of concatenations (never `re.^`, which the NFA construction of language (dis)equations does not support: unknowns), `{min,}` as `re.loop min min` · star, and a "ladder" for repetitions with captures (each iteration followed by the rest, exitable from `min` on) instead of alternating all chains.
- Tests (to do on the new machine): as of 2026-10-30, about 34 unit assertions with exact RCG/formula strings (`src/test/noodler/` ecma_regex/re2_regex tests) needed new expectations because of 6 and 7; e2e `from_*`/loop files passed.
  Re-verify and update the expectations in a `test:` commit (never run the full `test-noodler`, see preferences).
- An e2e test for the `handle_in_re` fix (5) is still missing; this formula gave an unsound sat before the fix (expected unsat):
  ```smt2
  (set-logic QF_SLIA)
  (set-info :status unsat)
  (set-option :smt.str.ecma_engine_semantics true)
  (declare-const x String)
  (declare-const y String)
  (declare-const z String)
  (assert (= x (str.++ y z)))
  (assert (or (= y "<pre on") (= y "<style>:target {transform: rotate(180deg);}</style><li id=x style=""transition:tr")))
  (assert (or (= z "own=""alert(1)"" contenteditable>test</hr>") (= z "p=""alert(1)"">test</script>")))
  (assert (str.in_re x ((_ re.from_regex ecma2020) "[0-9]{9}|[0-9]{14}")))
  (check-sat)
  ```

## Experiments and findings

Older ones (2026-10-30 to 11-02, release, 10 s, 4 jobs; passed/wrong/timeout/unknown):
- #502 alone on ecma2020: 8650/50 timeouts vs HEAD 8620/80, only timeout → passed.
- "v2" (all of the above except the intersection bound value, with a `RED_BOUND` guard on the intersection): ecma2020 HEAD 8619/1/81/114 → 8684/1/16/114 (2000 → 560 s); new mixed set 590/0/133/277 → 886/0/49/65; older mixed set 426/1/299/274 → 748/0/205/47.
- Remaining slowdowns then: dense complements of negated anchored patterns (now classical) and `mata::nfa::reduce` (simulation): about half of the solver time on the mixed set was `reduce`.
  substr_0087: one NFA-construction `reduce` of 772 states / 33k transitions took 57 s; a variant with `num_of_transitions() < 20000` added to the `regex.cpp` guard fixed it (timeout → 0.7 s).
  CJK cases (bool_mix_0878, two_patterns_0024/0048): alphabet of ~20k symbols, `is_co_finite` → `trim` → `Delta::defragment`.
- An earlier session also judged a transition-count guard as net zero overall (where exactly it was applied is not recorded); with the cost-model plan this should be re-measured rather than trusted.

2026-11-03, full ecma2020-smt-bench, old 2d58ba1af vs `perf-experiment` (then with the intersection guard at 1000): see `SUMMARY.md`.
Memberships 2556 → 575 s (median 0.029 → 0.022 s, p99 10 s → 0.7 s), lang_equality 463 → 772 passed, lang_inclusion 426 → 754, lang_ops 375 → 389, random_mix 297 → 346 but 73 passed → timeout; 0 wrong.

random_mix analysis:
- The regressions are more final checks, not big automata (random_mix_3737: 2 → 223 final checks, each finds the Boolean assignment unsat in preprocessing).
- Only two changes cause them: the regex simplification (6) and the `handle_in_re` fix (5); reverting both restores all 27 checked regressions exactly, and the same two changes give 119 of the 124 random_mix gains.
- Mechanism (debug trace of random_mix_0921): before, negated anchored patterns were a quantified axiom and Noodler never saw them; now they are classical memberships in every final check, and the conflict lemma (`construct_refinement`/`block_curr_len` in `theory_str_noodler_final_check.cpp`) is the negation of the conjunction of **all** relevant predicates, so each extra predicate weakens it and the SAT solver enumerates more combinations (10 → 23 final checks).
  A smaller conflict lemma (only the predicates involved in the unsat preprocessing) would be a separate, more general improvement (also for devel).
- Strongly seed-dependent (`smt.random_seed`/`sat.random_seed`): at seeds 1–4 the old version also times out on many of the "regressions".
  Consistent regressions: random_mix_0921, 0956 (simplification), 1769 (`handle_in_re` fix), 0836 (both).

2026-11-03, formulas without ECMAScript regexes (smt-bench, 10-minute random sample, 2393 formulas over 23 sets): identical outcomes, 0 wrong, 0.97× time; redos looked 3 % slower, but redos has no intersections at all: binaries differing only in code a formula never executes differed by ±2 % (binary layout), so this is noise.

2026-11-04, intersection bound (`INTERSECTION_RED_BOUND`), fixed sample of 12412 formulas (all memberships, all lang_* families, 300 random_mix, 40 of each smt-bench set):
- A probe with the no-guard instrumented binary showed that no smt-bench formula or membership has an intersection of 185 states or more; only lang_ops and random_mix reach the guard.
- lang_ops time on formulas solved by all bounds: 1000: 156.6 s, 250: 109.1, 200: 106.6, 150: 101.4, 100: 89.4, 50: 86.3; 125 vs 100 in one pool: a tie (lang_ops_0145 0.20 s with 100 vs 1.42 s with 125).
  The reductions of dense intersections of 150–600 states cost 0.5–0.8 s each and the later steps do not need them.
- Bound 1 (never reduce) breaks pyex (+39 timeouts) and norn (10× slower); their intersections reach 47 and 55 states.
- 100 was put into the source as its own constant.

2026-11-04, `RED_BOUND` (NFA construction in `regex.cpp`, membership heuristics), with `INTERSECTION_RED_BOUND = 100`, same 12412 formulas:
- 100: 0.93× total (memberships 0.86×, automatark 0.72×, stringfuzz 0.75×, denghang 0.84×, lang_ops 0.92×), but two reproducible regressions: lang_inclusion_1722 0.42 → 5.6 s (pattern `^[^\s*]([a-zA-Z…\s]+){0,150}$`: the bounded-loop NFA of a few hundred states stays unreduced and `are_equivalent` (antichains) gets slow) and random_mix_1041 5.3 → 11.3 s (solved → timeout).
- Spot check: 250 keeps both regressions fixed and most membership gains (regex_7153, 2187, 8302, 6059 ~2–6 s → ~0.1 s; regex_7316 timeout → 0.07 s); 500 behaves like 1000.
- 1000 vs 250 on the 12412 formulas: same outcomes except regex_7316 (timeout → solved), 0 wrong, no regressions; 0.96× total on formulas solved by both (memberships 0.92×, stringfuzz 0.75×, automatark 0.90×, others 0.93–1.02×).
  So 250 is the best state-count value found for `RED_BOUND`; the user decided to keep 1000 in the branch for now (the cost-based guard is to replace both bounds).

Conclusion that motivates the plan: the cost of the simulation is roughly (simulation classes) × (transitions), with counters growing with states × symbols (Simlib `SimulationEngine::init`), so a state count conflates sparse automata (cheap to reduce and worth it, e.g., bounded loops) with dense complements over a big ECMAScript alphabet (expensive).

## Methods that worked

- **Variants without a full rebuild**: `build_variant.sh` recompiles single files and relinks (~1 min).
  A `const` in a header has internal linkage, so for a header constant only the translation units that use it need recompiling (that is how `RED_BOUND` variants were built: `regex.cpp` and `memb_heuristics_procedures.cpp` with the literal replaced).
- **Instrumenting mata without touching it**: `-Wl,--wrap=<mangled mata::nfa::reduce>` on the link command (from `ninja -t commands -s z3`) plus `reduce_wrap.cpp`, which declares `__real_`/`__wrap_` functions with `asm` labels; caller via `__builtin_return_address(0)`, resolved by `nm -C -S` ranges or `gdb -batch -ex 'info symbol ADDR'` (the release binary is not PIE).
- **Separating signal from noise**: the probe (`bound_probe.py`) tells which formulas reach the changed code; all others behave identically, so their time differences are noise.
- **Profiling** (no `perf` on the laptop): sampling stacks with `gdb -p PID -batch -ex 'bt'` a few times.
- **Debug traces**: `-tr:str` in a debug build writes `.z3-trace` (final-check predicates, generated regex constraints, refinements).
- **Statistics**: `-st` prints `:noodler-final_checks`, `:str-num-proc-stabilization-solved-preprocess` etc.

## Gotchas

- Timing noise: ±2 % between binaries that differ only in unexecuted code, up to 5 % between separate runs; compare variants in one random-order pool, check whether differing formulas reach the changed code, repeat a single formula a few times interleaved.
- random_mix outcomes depend on the random seed; selecting regressions at one seed is biased.
- The shell of the agent was zsh: `set -- $var` does not split words, and `$PWD` in a backgrounded compound command was not the `cd` target (use absolute paths).
- A hook redirected `curl`/`wget` in Bash; downloads were done with Python `urllib`.
- A restart of the Claude Code session kills its background commands (a benchmark was stopped twice this way); run long benchmarks as a transient systemd service (`systemd-run --user --unit=NAME --working-directory=... -p MemoryHigh=... -p StandardOutput=append:LOG ...`) and wait with a loop on `systemctl --user is-active`; `smtbench_run.py` resumes an interrupted CSV.
- `/tmp` (and the agent's scratchpad in it) is wiped at reboot.
- transducer_plus: 11 crashes (SIGABRT) in both old and new; omark/transducer_plus/matching have many 10 s timeouts in both.
- The laptop powered off once during a benchmark at 4 jobs (no thermal or OOM message); later runs logged the CPU temperature (peaks 70–75 °C).

## Known issues not addressed (also on devel)

- The length-based procedure loops on `(= "abb" (str.++ r0 "a" r4))` (an axiom is lost on backjump); causes timeouts of `^?a` / `a$?` under engine semantics; the user said to leave it.
- `quant_lia_solver` gets an untracked context, so its unsat core is empty, loop protection adds `false` and loops.
- MBQI model validation fails on `str.contains` skolems (bool_mix_0744 → unknown, seed-dependent).
- two_patterns_0672 is ~1.4–2× slower than devel, cause not investigated.

## User preferences (from the agent memory on the laptop, which the new machine does not have)

- Never commit, push (also force-push) or create/edit a PR without explicit permission; first show the commit split with exact messages or the exact PR title and body and wait for a yes.
- No `Co-Authored-By: Claude` trailer and no Claude attribution in PRs (overrides the default).
- Commit subjects like the repo log (`feat:`, `fix #N:`, `test:`, `refactor:`, `style:`); body empty or 1–2 short sentences; tests in separate commits; stage explicit paths, never `git add -A`/`.`.
- PR bodies short (like #533, #534, #550): per change why and what, Testing lists only reproducible committed tests, no local benchmark numbers.
- Code: comments one sentence per line, no hard wrapping; Doxygen only in headers, helpers declared in headers, no anonymous namespaces in `src`; new code split into small files by meaning; match the surrounding style.
- Tests: never run the full `test-noodler`; run tagged Catch2 tests and e2e `.smt2` files one by one with a timeout.
- Builds: CMakePresets `debug`/`release` in `build/<preset>` (clang), never build in a scratch/temp dir, memory-capped (`systemd-run --user --scope -p MemoryHigh=... -p MemorySwapMax=0`).
- Search with `rg`, not `grep`.
- Benchmarks: the user likes short focused runs (10–40 min) with brief per-set results saved to `SUMMARY.md`, and iterating towards the best value.
- Unicode in regexes: code points as given (ASCII + `\u{..}` escapes), no UTF-8 decoding (team decision pending).
- The user likes SMT-LIB and git concepts explained when they matter.

## Next steps

1. Tests: the unit-test expectations and the e2e test for the `handle_in_re` fix (see above), each in its own `test:` commit.
2. New machine: clone, build `release` (and `debug` for traces) with mata installed (the laptop used mata c1d78d93 in `/usr/local`), clone smt-bench with submodules and run its download script, create a Python venv (pandas, scipy, statsmodels, scikit-learn, matplotlib; only numpy was installed on the laptop).
3. Follow `perf-tools/REDUCE-COST-PLAN.md`: instrumentation → variant without guards → collection on all smt-bench formulas (30 s timeout) → statistical analysis → guard → known cases → benchmark against the current state on all smt-bench formulas → `SUMMARY.md`.
4. Later: split the experiment into separately reviewable PR branches (#502, #501, #503 + guards, `handle_in_re` fix, simplification, translation of repetitions), and consider the smaller conflict lemma for random_mix as its own topic.

## Suggested skills

- `mattpocock-skills:diagnosing-bugs`: for performance regressions the benchmarks reveal.
- `dataviz`: before writing the plots of the analysis script.
- `mattpocock-skills:tdd`: when updating the unit-test expectations and testing the new guard.
- `mattpocock-skills:code-review`: before splitting and publishing the branch.
- `mattpocock-skills:pr`: when writing the PR bodies of the split branches.
