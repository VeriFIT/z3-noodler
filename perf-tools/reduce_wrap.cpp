// Link-time wrapper of mata::nfa::reduce (link with -Wl,--wrap=<mangled name>).
// Prints the caller address, the sizes before and after, and the time of each call to stderr.
#include <chrono>
#include <cstdio>
#include <mata/nfa/nfa.hh>

#define REDUCE_SYM "_ZN4mata3nfa6reduceERKNS0_3NfaEPSt13unordered_mapImmSt4hashImESt8equal_toImESaISt4pairIKmmEEERKS4_INSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEESK_S5_ISK_ES7_ISK_ESaIS9_IKSK_SK_EEE"

using StateMap = std::unordered_map<mata::nfa::State, mata::nfa::State>;

mata::nfa::Nfa real_reduce(const mata::nfa::Nfa& aut, StateMap* renaming, const mata::nfa::ParameterMap& params) asm("__real_" REDUCE_SYM);
mata::nfa::Nfa wrap_reduce(const mata::nfa::Nfa& aut, StateMap* renaming, const mata::nfa::ParameterMap& params) asm("__wrap_" REDUCE_SYM);

mata::nfa::Nfa wrap_reduce(const mata::nfa::Nfa& aut, StateMap* renaming, const mata::nfa::ParameterMap& params) {
    void* caller = __builtin_return_address(0);
    auto start = std::chrono::steady_clock::now();
    mata::nfa::Nfa result = real_reduce(aut, renaming, params);
    double ms = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - start).count();
    std::fprintf(stderr, "REDUCE caller=%p states=%zu trans=%zu -> states=%zu trans=%zu ms=%.3f\n", caller,
                 aut.num_of_states(), aut.delta.num_of_transitions(), result.num_of_states(),
                 result.delta.num_of_transitions(), ms);
    return result;
}
