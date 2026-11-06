// Link-time wrapper of mata::nfa::reduce that logs every call, for counting the reductions (see perf-tools/README.md).
//
// build_variant.py --reduce-log compiles this file with -DREDUCE_SYMBOL=<the mangled name of mata::nfa::reduce> and links z3 with
// -Wl,--wrap=<that name>, so the calls of reduce from z3 go to wrap_reduce below, which calls the original function.
// If $REDUCE_LOG is set, each call appends one line to that file (read by perf-tools/run.py):
//   <caller> <states> <transitions> <result states> <result transitions> <ns> <guarded>
// caller is the return address in the calling code (hexadecimal, relative to the load address of z3), from which addr2line finds the calling function.
// guarded is 1 if regex::should_reduce allowed this reduction (instrumentation/guard-flag.patch sets reduce_guarded).
// The sizes of the automata are computed outside the timed part.
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fcntl.h>
#include <link.h>
#include <unistd.h>

#include <mata/nfa/nfa.hh>

#ifndef REDUCE_SYMBOL
#error "REDUCE_SYMBOL must be the mangled name of mata::nfa::reduce (build_variant.py sets it)"
#endif

using mata::nfa::Nfa;
using StateRenaming = std::unordered_map<mata::nfa::State, mata::nfa::State>;

// Set by regex::should_reduce right before the reduction it allows, cleared by every reduction.
thread_local bool reduce_guarded = false;

Nfa real_reduce(const Nfa& aut, StateRenaming* renaming, const mata::nfa::ParameterMap& params) asm("__real_" REDUCE_SYMBOL);
Nfa wrap_reduce(const Nfa& aut, StateRenaming* renaming, const mata::nfa::ParameterMap& params) asm("__wrap_" REDUCE_SYMBOL);

// The log file, or -1 if $REDUCE_LOG is not set.
static int log_file() {
    static const int fd = [] {
        const char* path = std::getenv("REDUCE_LOG");
        return path ? open(path, O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0644) : -1;
    }();
    return fd;
}

// How far z3 is loaded from the addresses in the binary (0 unless z3 is a position-independent executable).
static uintptr_t load_offset() {
    static const uintptr_t offset = [] {
        uintptr_t result = 0;
        // the first object visited is the executable
        dl_iterate_phdr([](dl_phdr_info* info, size_t, void* data) {
            *static_cast<uintptr_t*>(data) = info->dlpi_addr;
            return 1;
        }, &result);
        return result;
    }();
    return offset;
}

Nfa wrap_reduce(const Nfa& aut, StateRenaming* renaming, const mata::nfa::ParameterMap& params) {
    const bool guarded = reduce_guarded;
    reduce_guarded = false;
    const int fd = log_file();
    if (fd < 0) {
        return real_reduce(aut, renaming, params);
    }

    const uintptr_t caller = reinterpret_cast<uintptr_t>(__builtin_return_address(0)) - load_offset();
    const size_t states = aut.num_of_states();
    const size_t transitions = aut.delta.num_of_transitions();

    const auto start = std::chrono::steady_clock::now();
    Nfa result = real_reduce(aut, renaming, params);
    const long long ns = std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now() - start).count();

    // one write(2) per line, so that the lines of the finished calls are in the file even if z3 is killed
    char line[160];
    const int length = snprintf(line, sizeof line, "%lx %zu %zu %zu %zu %lld %d\n", static_cast<unsigned long>(caller), states, transitions,
                                result.num_of_states(), result.delta.num_of_transitions(), ns, guarded ? 1 : 0);
    (void)!write(fd, line, length);
    return result;
}
