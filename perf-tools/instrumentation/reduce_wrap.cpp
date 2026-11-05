// Link-time wrapper of mata::nfa::reduce that logs every call, for the statistics of the reduction (see perf-tools/README.md).
//
// build_variant.py --reduce-log compiles this file with -DREDUCE_SYMBOL=<the mangled name of mata::nfa::reduce> and links z3 with
// -Wl,--wrap=<that name>, so the calls of reduce from outside libmata go to wrap_reduce below, which calls the original function.
// If $REDUCE_LOG is set, each call appends two lines to that file (read by perf-tools/reduce_log.py):
//   S <seq> <start_ns> <caller> <operation> <alphabet> <states> <initial> <final> <useful> <transitions> <moves> <epsilon> <self_loops>
//     <symbols> <max_out> <max_targets> <deterministic> <sccs> <max_scc> <cyclic>
//   E <seq> <result states> <result transitions> <ns>
// The S line is written before the call, so a call cut by a timeout still leaves its S line.
// The lines are written by write(2), so they are in the file even if the process is killed.
// The properties are computed outside the timed part.
// useful, sccs, max_scc and cyclic need a search of the automaton and are computed only if $REDUCE_LOG_GRAPH is set (-1 otherwise).
// caller is the return address in the calling code; operation and alphabet are set by the tags of instrumentation/reduce-tags.patch
// (- and -1 for the calls without a tag).
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <fcntl.h>
#include <unistd.h>

#include <mata/nfa/nfa.hh>

#ifndef REDUCE_SYMBOL
#error "REDUCE_SYMBOL must be the mangled name of mata::nfa::reduce (build_variant.py sets it)"
#endif

using mata::nfa::Nfa;
using mata::nfa::State;
using StateRenaming = std::unordered_map<State, State>;

// The context of the next call, set by the tags in the calling code and cleared by every call.
thread_local const char* reduce_tag_operation = nullptr;
thread_local long reduce_tag_alphabet = -1;

Nfa real_reduce(const Nfa& aut, StateRenaming* renaming, const mata::nfa::ParameterMap& params) asm("__real_" REDUCE_SYMBOL);
Nfa wrap_reduce(const Nfa& aut, StateRenaming* renaming, const mata::nfa::ParameterMap& params) asm("__wrap_" REDUCE_SYMBOL);

struct Properties {
    long states = 0;
    long initial = 0;
    long final = 0;
    long useful = -1;      // states reachable from an initial state and reaching a final state
    long transitions = 0;  // (state, symbol, target) triples
    long moves = 0;        // (state, symbol) pairs with at least one target
    long epsilon = 0;      // transitions over epsilon
    long self_loops = 0;
    long symbols = 0;      // distinct symbols on the transitions
    long max_out = 0;      // the most transitions from one state
    long max_targets = 0;  // the most targets of one move
    long deterministic = 1;
    long sccs = -1;        // strongly connected components
    long max_scc = -1;     // states of the largest one
    long cyclic = -1;      // states on a cycle
};

static bool has_self_loop(const Nfa& aut, const State state) {
    for (const mata::nfa::SymbolPost& move : aut.delta.state_post(state)) {
        if (std::find(move.targets.begin(), move.targets.end(), state) != move.targets.end()) {
            return true;
        }
    }
    return false;
}

static Properties properties(const Nfa& aut) {
    Properties p;
    p.states = static_cast<long>(aut.num_of_states());
    p.initial = static_cast<long>(aut.initial.size());
    p.final = static_cast<long>(aut.final.size());
    p.deterministic = p.initial <= 1;
    p.symbols = static_cast<long>(aut.delta.get_used_symbols().size());
    for (State state = 0; state < aut.num_of_states(); ++state) {
        long out = 0;
        for (const mata::nfa::SymbolPost& move : aut.delta.state_post(state)) {
            const long targets = static_cast<long>(move.targets.size());
            ++p.moves;
            out += targets;
            p.max_targets = std::max(p.max_targets, targets);
            p.self_loops += std::find(move.targets.begin(), move.targets.end(), state) != move.targets.end();
            if (move.symbol == mata::nfa::EPSILON) {
                p.epsilon += targets;
            }
            if (targets > 1 || move.symbol == mata::nfa::EPSILON) {
                p.deterministic = 0;
            }
        }
        p.transitions += out;
        p.max_out = std::max(p.max_out, out);
    }
    return p;
}

static void add_graph_properties(const Nfa& aut, Properties& p) {
    const mata::BoolVector useful = aut.get_useful_states();
    p.useful = static_cast<long>(std::count(useful.begin(), useful.end(), 1));
    p.sccs = 0;
    p.max_scc = 0;
    p.cyclic = 0;
    Nfa::TarjanDiscoverCallback callback;
    callback.scc_discover = [&](const std::vector<State>& scc, const std::vector<State>&) {
        const long size = static_cast<long>(scc.size());
        ++p.sccs;
        p.max_scc = std::max(p.max_scc, size);
        if (size > 1) {
            p.cyclic += size;
        } else if (has_self_loop(aut, scc[0])) {
            ++p.cyclic;
        }
        return false;  // continue the search
    };
    aut.tarjan_scc_discover(callback);
}

static int log_file() {
    static const int fd = [] {
        const char* path = std::getenv("REDUCE_LOG");
        return path ? open(path, O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0644) : -1;
    }();
    return fd;
}

// The clock of Python's time.monotonic_ns(), which reduce_log.py uses for the end of a run.
static long long monotonic_ns() {
    timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return static_cast<long long>(now.tv_sec) * 1000000000 + now.tv_nsec;
}

Nfa wrap_reduce(const Nfa& aut, StateRenaming* renaming, const mata::nfa::ParameterMap& params) {
    const char* operation = reduce_tag_operation;
    const long alphabet = reduce_tag_alphabet;
    reduce_tag_operation = nullptr;
    reduce_tag_alphabet = -1;
    const int fd = log_file();
    if (fd < 0) {
        return real_reduce(aut, renaming, params);
    }

    static unsigned long calls = 0;
    const unsigned long seq = calls++;
    Properties p = properties(aut);
    if (std::getenv("REDUCE_LOG_GRAPH")) {
        add_graph_properties(aut, p);
    }
    char line[512];
    int length = snprintf(line, sizeof line, "S %lu %lld %p %s %ld %ld %ld %ld %ld %ld %ld %ld %ld %ld %ld %ld %ld %ld %ld %ld\n", seq,
                          monotonic_ns(), __builtin_return_address(0), operation ? operation : "-", alphabet, p.states, p.initial, p.final,
                          p.useful, p.transitions, p.moves, p.epsilon, p.self_loops, p.symbols, p.max_out, p.max_targets, p.deterministic,
                          p.sccs, p.max_scc, p.cyclic);
    (void)!write(fd, line, length);

    const long long start = monotonic_ns();
    Nfa result = real_reduce(aut, renaming, params);
    const long long ns = monotonic_ns() - start;

    length = snprintf(line, sizeof line, "E %lu %zu %zu %lld\n", seq, result.num_of_states(), result.delta.num_of_transitions(), ns);
    (void)!write(fd, line, length);
    return result;
}
