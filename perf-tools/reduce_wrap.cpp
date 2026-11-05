// Link-time wrapper of mata::nfa::reduce (link with -Wl,--wrap=<mangled name>) collecting statistics of its calls.
// If $REDUCE_LOG is set, each call appends to that file a START line with the properties of the input automaton and an END line with the
// result and the time of reduce, so that a call cut by a timeout still leaves its START line.
// The properties are computed outside the timed part; the lines are written by write(2), so they are in the file even if the process is killed.
//
// S seq start_ns caller operation alphabet states initial final useful transitions moves epsilon self_loops symbols max_out max_targets
//   deterministic sccs max_scc cyclic
// E seq states transitions ns
//
// start_ns is CLOCK_MONOTONIC (the clock of Python's time.monotonic_ns), caller the return address in the calling code, operation and alphabet
// the context set by the instrumented callers in perf-tools/variant-src (- and -1 if not set).
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fcntl.h>
#include <unistd.h>
#include <vector>
#include <mata/nfa/nfa.hh>

#define REDUCE_SYM "_ZN4mata3nfa6reduceERKNS0_3NfaEPSt13unordered_mapImmSt4hashImESt8equal_toImESaISt4pairIKmmEEERKS4_INSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEESK_S5_ISK_ES7_ISK_ESaIS9_IKSK_SK_EEE"

using mata::nfa::State;
using StateMap = std::unordered_map<State, State>;

// Context of the next call, set by the instrumented callers and cleared by every call.
thread_local const char* reduce_tag_operation = nullptr;
thread_local long reduce_tag_alphabet = -1;

mata::nfa::Nfa real_reduce(const mata::nfa::Nfa& aut, StateMap* renaming, const mata::nfa::ParameterMap& params) asm("__real_" REDUCE_SYM);
mata::nfa::Nfa wrap_reduce(const mata::nfa::Nfa& aut, StateMap* renaming, const mata::nfa::ParameterMap& params) asm("__wrap_" REDUCE_SYM);

struct Properties {
    size_t states = 0, initial = 0, final = 0, useful = 0, transitions = 0, moves = 0, epsilon = 0, self_loops = 0, symbols = 0;
    size_t max_out = 0, max_targets = 0, sccs = 0, max_scc = 0, cyclic = 0;
    bool deterministic = true;
};

// Marks the states reachable in graph from the states in start.
static std::vector<bool> reachable(const std::vector<std::vector<State>>& graph, const std::vector<State>& start) {
    std::vector<bool> seen(graph.size(), false);
    std::vector<State> todo;
    for (const State s : start) {
        if (s < graph.size() && !seen[s]) { seen[s] = true; todo.push_back(s); }
    }
    while (!todo.empty()) {
        const State s = todo.back();
        todo.pop_back();
        for (const State t : graph[s]) {
            if (!seen[t]) { seen[t] = true; todo.push_back(t); }
        }
    }
    return seen;
}

// Counts the strongly connected components of graph (iterative Tarjan), the size of the largest one and the states on a cycle.
static void count_sccs(const std::vector<std::vector<State>>& graph, const std::vector<bool>& self_loop, Properties& p) {
    const size_t n = graph.size();
    const size_t unvisited = SIZE_MAX;
    std::vector<size_t> index(n, unvisited), low(n, 0);
    std::vector<bool> on_stack(n, false);
    std::vector<State> stack;
    std::vector<std::pair<State, size_t>> calls; // state and the position of its next successor
    size_t next_index = 0;
    for (State root = 0; root < n; ++root) {
        if (index[root] != unvisited) { continue; }
        index[root] = low[root] = next_index++;
        stack.push_back(root);
        on_stack[root] = true;
        calls.emplace_back(root, 0);
        while (!calls.empty()) {
            const State v = calls.back().first;
            const size_t i = calls.back().second;
            if (i < graph[v].size()) {
                calls.back().second = i + 1;
                const State w = graph[v][i];
                if (index[w] == unvisited) {
                    index[w] = low[w] = next_index++;
                    stack.push_back(w);
                    on_stack[w] = true;
                    calls.emplace_back(w, 0);
                } else if (on_stack[w]) {
                    low[v] = std::min(low[v], index[w]);
                }
                continue;
            }
            calls.pop_back();
            if (!calls.empty()) { low[calls.back().first] = std::min(low[calls.back().first], low[v]); }
            if (low[v] != index[v]) { continue; }
            size_t size = 0;
            State w;
            do {
                w = stack.back();
                stack.pop_back();
                on_stack[w] = false;
                ++size;
            } while (w != v);
            ++p.sccs;
            p.max_scc = std::max(p.max_scc, size);
            if (size > 1) { p.cyclic += size; }
            else if (self_loop[v]) { ++p.cyclic; }
        }
    }
}

static Properties properties(const mata::nfa::Nfa& aut) {
    Properties p;
    const size_t n = aut.num_of_states();
    p.states = n;
    p.initial = aut.initial.size();
    p.final = aut.final.size();
    p.deterministic = p.initial <= 1;
    std::vector<std::vector<State>> succ(n), pred(n);
    std::vector<bool> self_loop(n, false);
    std::vector<mata::Symbol> symbols;
    for (State s = 0; s < n; ++s) {
        size_t out = 0;
        for (const mata::nfa::SymbolPost& move : aut.delta.state_post(s)) {
            ++p.moves;
            symbols.push_back(move.symbol);
            out += move.targets.size();
            p.max_targets = std::max(p.max_targets, move.targets.size());
            if (move.targets.size() > 1) { p.deterministic = false; }
            if (move.symbol == mata::nfa::EPSILON) {
                p.epsilon += move.targets.size();
                p.deterministic = false;
            }
            for (const State t : move.targets) {
                if (t == s) { ++p.self_loops; self_loop[s] = true; }
                succ[s].push_back(t);
                pred[t].push_back(s);
            }
        }
        p.transitions += out;
        p.max_out = std::max(p.max_out, out);
    }
    std::sort(symbols.begin(), symbols.end());
    p.symbols = std::unique(symbols.begin(), symbols.end()) - symbols.begin();
    const std::vector<bool> from_initial = reachable(succ, std::vector<State>(aut.initial.begin(), aut.initial.end()));
    const std::vector<bool> to_final = reachable(pred, std::vector<State>(aut.final.begin(), aut.final.end()));
    for (State s = 0; s < n; ++s) {
        if (from_initial[s] && to_final[s]) { ++p.useful; }
    }
    count_sccs(succ, self_loop, p);
    return p;
}

static int log_fd() {
    static const int fd = [] {
        const char* path = std::getenv("REDUCE_LOG");
        return path ? open(path, O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0644) : -1;
    }();
    return fd;
}

static int64_t monotonic_ns() {
    timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return int64_t(ts.tv_sec) * 1000000000 + ts.tv_nsec;
}

mata::nfa::Nfa wrap_reduce(const mata::nfa::Nfa& aut, StateMap* renaming, const mata::nfa::ParameterMap& params) {
    const char* operation = reduce_tag_operation;
    const long alphabet = reduce_tag_alphabet;
    reduce_tag_operation = nullptr;
    reduce_tag_alphabet = -1;
    const int fd = log_fd();
    if (fd < 0) { return real_reduce(aut, renaming, params); }

    static unsigned long calls = 0;
    const unsigned long seq = calls++;
    void* caller = __builtin_return_address(0);
    const Properties p = properties(aut);
    char line[512];
    int len = std::snprintf(line, sizeof(line), "S %lu %lld %p %s %ld %zu %zu %zu %zu %zu %zu %zu %zu %zu %zu %zu %d %zu %zu %zu\n", seq,
                            static_cast<long long>(monotonic_ns()), caller, operation ? operation : "-", alphabet, p.states, p.initial, p.final,
                            p.useful, p.transitions, p.moves, p.epsilon, p.self_loops, p.symbols, p.max_out, p.max_targets,
                            p.deterministic ? 1 : 0, p.sccs, p.max_scc, p.cyclic);
    (void)!write(fd, line, len);

    const auto start = std::chrono::steady_clock::now();
    mata::nfa::Nfa result = real_reduce(aut, renaming, params);
    const long long ns = std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now() - start).count();

    len = std::snprintf(line, sizeof(line), "E %lu %zu %zu %lld\n", seq, result.num_of_states(), result.delta.num_of_transitions(), ns);
    (void)!write(fd, line, len);
    return result;
}
