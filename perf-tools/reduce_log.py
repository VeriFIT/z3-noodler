"""Reading the logs of the reduce wrapper (instrumentation/reduce_wrap.cpp): the mata::nfa::reduce calls of a run.

The wrapper appends two lines per call to the file in $REDUCE_LOG:
    S <seq> <start_ns> <caller> <operation> <alphabet> <the PROPERTIES of the input automaton>
    E <seq> <result states> <result transitions> <ns>
A call cut by a timeout or a crash has only its S line; it is recorded as censored, with the time until the end of the run (a lower bound).
Calls with the same caller, input and result (e.g., in repeated final checks) are merged into one row while reading.
Only the Python standard library is used here.
"""
import subprocess
from statistics import median

# Properties of the input automaton, in the order of the S line (see reduce_wrap.cpp).
PROPERTIES = ["states", "initial", "final", "useful", "transitions", "moves", "epsilon", "self_loops", "symbols", "max_out", "max_targets",
              "deterministic", "sccs", "max_scc", "cyclic"]
# The S line after its seq and start_ns.
INPUT_FIELDS = ["caller", "operation", "alphabet"] + PROPERTIES
RESULT_FIELDS = ["res_states", "res_transitions", "censored"]
CALL_FIELDS = ["site"] + INPUT_FIELDS + RESULT_FIELDS + ["repeats", "ns_median", "ns_min", "ns_max", "ns_sum"]


def read_merged_calls(log_path, end_ns):
    """The calls in a log, merged into rows of CALL_FIELDS (without the site, see SiteNames).

    end_ns (time.monotonic_ns() at the end of the run) gives the time of the censored calls.
    """
    times = {}  # (input fields, result fields) -> times of the calls
    pending = {}  # seq -> (start_ns, input fields) of the calls without an E line yet
    with open(log_path, errors="replace") as log:
        for line in log:
            kind, seq, rest = (line.rstrip("\n").split(" ", 2) + ["", ""])[:3]
            if kind == "S":
                start_ns, inputs = rest.split(" ", 1)
                pending[seq] = (int(start_ns), inputs)
            elif kind == "E" and seq in pending:
                _, inputs = pending.pop(seq)
                res_states, res_transitions, ns = rest.split()
                times.setdefault((inputs, f"{res_states} {res_transitions} 0"), []).append(int(ns))
    for start_ns, inputs in pending.values():
        times.setdefault((inputs, "  1"), []).append(max(0, end_ns - start_ns))
    rows = []
    for (inputs, results), call_times in times.items():
        row = dict(zip(INPUT_FIELDS, inputs.split()))
        row.update(zip(RESULT_FIELDS, results.split(" ")))
        row.update(repeats=len(call_times), ns_median=int(median(call_times)), ns_min=min(call_times), ns_max=max(call_times),
                   ns_sum=sum(call_times))
        rows.append(row)
    return rows


class SiteNames:
    """Names the call site of a reduce call by the function that called it, plus the operation tag of the regex construction.

    The function of a caller address comes from addr2line on the binary (from the symbol table, no debug info needed).
    The names are cached per address, as one binary has only a few hundred call sites.
    """

    def __init__(self, z3):
        self.z3 = z3
        self.functions = {}

    def add_sites(self, rows):
        """Sets the site of each row, resolving the callers not seen before."""
        unknown = sorted({row["caller"] for row in rows} - self.functions.keys())
        if unknown:
            self.functions.update(zip(unknown, self.resolve(unknown)))
        for row in rows:
            function = self.functions[row["caller"]]
            row["site"] = function if row["operation"] == "-" else f"{function}:{row['operation']}"

    def resolve(self, addresses):
        # A return address points after the call instruction, so the call is at the address before it.
        call_addresses = [hex(int(address, 16) - 1) for address in addresses]
        output = subprocess.run(["addr2line", "-f", "-C", "-e", self.z3, *call_addresses], capture_output=True, text=True).stdout
        # addr2line prints two lines per address: the function and the source location.
        functions = output.split("\n")[0::2][:len(addresses)]
        return [short_function_name(function) for function in functions]


def is_guarded(site):
    """Whether a reduction site is guarded by a bound on the size of the automaton (regex::should_reduce in the branch).

    These are the regex construction (except the loop bodies, which are always reduced), the intersection of the memberships of a
    variable in the final check, and the membership heuristics.
    """
    if site.startswith("NfaConstructor::create_nfa_for_expr:"):
        return not site.endswith((":loop_body", ":loop_body_unbounded"))
    return site in ("theory_str_noodler::create_aut_assignment_for_formula", "MultMembHeuristicProcedure::compute_next_solution")


def short_function_name(function):
    """smt::noodler::FormulaPreprocessor::reduce_automata(...) -> FormulaPreprocessor::reduce_automata"""
    parts = function.split("(")[0].split("::")
    return "::".join(parts[-2:])
