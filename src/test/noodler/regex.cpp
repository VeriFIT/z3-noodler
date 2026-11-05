#include <catch2/catch_test_macros.hpp>
#include <mata/nfa/builder.hh>
#include <mata/nfa/nfa.hh>

#include "smt/theory_str_noodler/regex.h"

using namespace smt::noodler;

TEST_CASE("regex::concatenate_up_to_nth_power", "[regex]") {
    // body accepts the words "a", "b" and "c"
    mata::nfa::Nfa body(2, {0}, {1});
    for (const mata::Symbol symbol : {'a', 'b', 'c'}) {
        body.delta.add(0, symbol, 1);
    }

    SECTION("accepts body^low ∪ ... ∪ body^(low+n)") {
        for (const unsigned low : {0, 1, 2}) {
            for (const unsigned n : {0, 1, 3}) {
                mata::nfa::Nfa result = mata::nfa::concatenate_nth_power(body, low);
                regex::concatenate_up_to_nth_power(result, body, n);

                mata::nfa::Nfa expected = mata::nfa::concatenate_nth_power(body, low);
                for (unsigned k = low + 1; k <= low + n; ++k) {
                    expected = mata::nfa::union_nondet(expected, mata::nfa::concatenate_nth_power(body, k));
                }
                CHECK(mata::nfa::are_equivalent(result, expected));
            }
        }
    }

    SECTION("body accepting the empty word") {
        mata::nfa::Nfa nullable_body = body;
        nullable_body.final.insert(0);
        mata::nfa::Nfa result = mata::nfa::builder::create_empty_string_nfa();
        regex::concatenate_up_to_nth_power(result, nullable_body, 3);
        CHECK(mata::nfa::are_equivalent(result, mata::nfa::concatenate_nth_power(nullable_body, 3)));
    }

    SECTION("size is linear in n") {
        mata::nfa::Nfa result = mata::nfa::builder::create_empty_string_nfa();
        regex::concatenate_up_to_nth_power(result, body, 300);
        CHECK(result.num_of_states() == 301);
        CHECK(result.delta.num_of_transitions() == 3 * 300);
    }
}

TEST_CASE("regex::should_reduce", "[regex]") {
    // n states with a self-loop on each of k symbols, so their number times the number of transitions is n * n * k
    auto self_loops = [](size_t n, size_t k) {
        mata::nfa::Nfa nfa(n, {0}, {0});
        for (mata::nfa::State state = 0; state < n; ++state) {
            for (mata::Symbol symbol = 0; symbol < k; ++symbol) {
                nfa.delta.add(state, symbol, state);
            }
        }
        return nfa;
    };
    const size_t n = 100;
    const size_t k = regex::REDUCTION_COST_BOUND / (n * n);

    CHECK(regex::should_reduce(self_loops(1, 1)));
    CHECK(regex::should_reduce(mata::nfa::Nfa(n)));
    CHECK(regex::should_reduce(self_loops(n, k)));
    CHECK_FALSE(regex::should_reduce(self_loops(n, k + 1)));
}
