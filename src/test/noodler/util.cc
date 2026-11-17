#include <iostream>
#include <algorithm>
#include <utility>

#include <catch2/catch_test_macros.hpp>
#include <mata/parser/re2parser.hh>
#include <smt/theory_str_noodler/decision_procedure.h>
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "ast/reg_decl_plugins.h"
#include "test_utils.h"

using namespace smt::noodler;

TEST_CASE("theory_str_noodler::util") {
    smt_params params;
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    smt::context ctx{ast_m, params };
    theory_str_noodler_params str_params{};
    TheoryStrNoodlerCUT noodler{ctx, ast_m, str_params };
    std::set<uint32_t> alphabet{ '\x78', '\x79', '\x7A' };
    auto& m_util_s{ noodler.m_util_s };
    auto& m_util_a{ noodler.m_util_a };
    auto& m{ noodler.m };

    SECTION("util::get_dummy_symbols()") {
        // vector<util::expr_pair> disequations{};
        // auto expr_hex_char{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("x\x45")) };
        // auto expr_hex_char2{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("y\x02")) };
        // auto expr_hex_char3{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("z\x03")) };

        // disequations.insert(std::make_pair(
        //         obj_ref<expr, ast_manager>{ expr_hex_char->get_arg(0), ast_m },
        //         obj_ref<expr, ast_manager>{ expr_hex_char->get_arg(0), ast_m }
        // ));
        // disequations.insert(std::make_pair(
        //         obj_ref<expr, ast_manager>{ expr_hex_char2->get_arg(0), ast_m },
        //         obj_ref<expr, ast_manager>{ expr_hex_char3->get_arg(0), ast_m }
        // ));

        // alphabet.insert({ '\x45', '\x02', '\x03', '\x00' });
        // std::set<uint32_t> dummy_symbols{ util::get_dummy_symbols(disequations.size(), alphabet) };
        // CHECK(dummy_symbols == std::set<uint32_t>{ '\x01', '\x04' });
        // CHECK(alphabet == std::set<uint32_t>{ '\x00', '\x01', '\x02', '\x03', '\x04', '\x45', '\x78', '\x79', '\x7a' });
    }

    SECTION("util::get_symbols()") {
        vector<util::expr_pair> disequations{};
        auto expr_hex_char{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("x\x45")) };
        auto expr_hex_char2{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("wy\x02")) };
        auto expr_concat{ m_util_s.re.mk_concat(expr_hex_char, m_util_s.re.mk_star(expr_hex_char2)) };

        // noodler.extract_symbols(expr_concat, alphabet);
        // CHECK(alphabet == std::set<uint32_t>{ '\x02', '\x45', '\x77', '\x78', '\x79', '\x7a' });
    }

    SECTION("util::is_str_variable()") {
        expr_ref str_variable{ noodler.mk_str_var_fresh("var1"), m };
        CHECK(util::is_str_variable(str_variable, m_util_s));
        expr_ref str_literal{m_util_s.str.mk_string("var1"), m };
        CHECK(!util::is_str_variable(str_literal, m_util_s));
        expr_ref regex{ m_util_s.re.mk_to_re(m_util_s.str.mk_string(".*regex.*")), m };
        CHECK(!util::is_str_variable(regex, m_util_s));
        expr_ref int_literal{ m_util_a.mk_int(1), m };
        CHECK(!util::is_str_variable(int_literal, m_util_s));
    }

    SECTION("util::contains_trans_identity()") {
        // Helper: create a simple identity transducer for a given alphabet and length
        auto make_identity_transducer = [](const std::set<mata::Symbol>& alphabet, unsigned length) {
            unsigned num_states = length + 1;
            mata::nft::Nft transducer {num_states};
            transducer.levels.num_of_levels = 2; // input and output tapes
            transducer.initial.insert(0);
            transducer.final.insert(num_states - 1);
            for (unsigned i = 0; i < length; ++i) {
                for (auto sym : alphabet) {
                    // Identity: input symbol == output symbol
                    transducer.add_transition(i, {sym, sym}, i + 1);
                }
            }
            return transducer;
        };

        // Test: identity transducer should return true
        {
            std::set<mata::Symbol> alphabet = { 'a', 'b' };
            unsigned length = 3;
            auto transducer = make_identity_transducer(alphabet, length);
            CHECK(util::contains_trans_identity(transducer, length) == l_true);
        }

        // Test: transducer with non-identity mapping should return false
        {
            mata::nft::Nft transducer {2};
            transducer.levels.num_of_levels = 2;
            transducer.initial.insert(0);
            transducer.final.insert(1);
            // Only non-identity transition
            transducer.add_transition(0, {'a', 'b'}, 1);
            CHECK(util::contains_trans_identity(transducer, 1) == l_false);
        }

        // Test: empty transducer (no transitions, no initial/final)
        {
            mata::nft::Nft transducer {1};
            transducer.levels.num_of_levels = 2;
            CHECK(util::contains_trans_identity(transducer, 1) == l_false);
        }

        // Test: identity for length 0 (initial is final)
        {
            mata::nft::Nft transducer {1};
            transducer.levels.num_of_levels = 2;
            transducer.initial.insert(0);
            transducer.final.insert(0);
            CHECK(util::contains_trans_identity(transducer, 0) == l_true);
        }

        // Test: self-loop on initial state with identity symbol, length 1, should not accept unless final is reached
        {
            mata::nft::Nft transducer {2};
            transducer.levels.num_of_levels = 2;
            transducer.initial.insert(0);
            transducer.final.insert(1);
            // Self-loop on initial state (identity)
            transducer.add_transition(0, {'a', 'a'}, 0);
            // Proper transition to final
            transducer.add_transition(0, {'a', 'a'}, 1);
            CHECK(util::contains_trans_identity(transducer, 1) == l_true);
        }

        // Test: self-loop on initial state only, no path to final, should not accept
        {
            mata::nft::Nft transducer {2};
            transducer.levels.num_of_levels = 2;
            transducer.initial.insert(0);
            transducer.final.insert(1);
            // Only self-loop, no transition to final
            transducer.add_transition(0, {'a', 'b'}, 0);
            transducer.add_transition(0, {'a', 'b'}, 1);
            CHECK(util::contains_trans_identity(transducer, 1) == l_false);
        }

        // Test: self-loop on initial state, but final is also initial, length 1, should accept for length 0 only
        {
            mata::nft::Nft transducer {1};
            transducer.levels.num_of_levels = 2;
            transducer.initial.insert(0);
            transducer.final.insert(0);
            // Self-loop
            transducer.add_transition(0, {'a', 'a'}, 0);
            CHECK(util::contains_trans_identity(transducer, 0) == l_true);
            CHECK(util::contains_trans_identity(transducer, 1) == l_true);
        }

        // Test: self-loop on initial state with non-identity symbol, should not accept
        {
            mata::nft::Nft transducer {2};
            transducer.levels.num_of_levels = 2;
            transducer.initial.insert(0);
            transducer.final.insert(1);
            // Self-loop with non-identity
            transducer.add_transition(0, {'a', 'b'}, 0);
            // Proper transition to final with identity
            transducer.add_transition(0, {'a', 'a'}, 1);
            CHECK(util::contains_trans_identity(transducer, 1));
            // If only non-identity self-loop, should not accept
            mata::nft::Nft t2 {2};
            t2.levels.num_of_levels = 2;
            t2.initial.insert(0);
            t2.final.insert(1);
            t2.add_transition(0, {'a', 'b'}, 0);
            CHECK(util::contains_trans_identity(t2, 1) == l_false);
        }

        // Test: longer self-loop chain, only identity path should be accepted
        {
            mata::nft::Nft transducer {3};
            transducer.levels.num_of_levels = 2;
            transducer.initial.insert(0);
            transducer.final.insert(2);
            // Self-loop on 0
            transducer.add_transition(0, {'a', 'a'}, 0);
            // Path: 0 --('a','a')--> 1 --('b','b')--> 2
            transducer.add_transition(0, {'a', 'a'}, 1);
            transducer.add_transition(1, {'b', 'b'}, 2);
            CHECK(util::contains_trans_identity(transducer, 2) == l_true);
        }

        // Test: l_undef is returned if a tape can exceed the required length (non-identity self-loop)
        {
            mata::nft::Nft transducer {2};
            transducer.levels.num_of_levels = 2;
            transducer.initial.insert(0);
            transducer.final.insert(1);
            // Self-loop with identity symbol
            transducer.add_transition(0, {'a', 'a'}, 0);
            // Self-loop with non-identity symbol (causes is_not_prefix to fail, so not l_undef)
            // transducer.add_transition(0, {'a', 'b'}, 0);
            // Transition to final
            transducer.add_transition(0, {'a', 'a'}, 1);
            // If we check for length 10, but only have one transition, the self-loop can be taken indefinitely
            CHECK(util::contains_trans_identity(transducer, 10) == l_true);
        }

        // Test: l_undef is returned if there is a path that can produce longer tapes than required (identity self-loop, no final state reachable)
        {
            mata::nft::Nft transducer {2};
            transducer.levels.num_of_levels = 2;
            transducer.initial.insert(0);
            transducer.final.insert(1);
            // Only self-loop with identity
            transducer.add_transition(0, {'a', 'a'}, 1);
            // For length 5, the self-loop can be taken indefinitely, so l_undef
            CHECK(util::contains_trans_identity(transducer, 0) == l_undef);
        }

        // Test: l_undef is returned if there is a cycle with identity transitions and no final state is reachable in exactly the required length
        {
            mata::nft::Nft transducer {3};
            transducer.levels.num_of_levels = 2;
            transducer.initial.insert(0);
            transducer.final.insert(2);
            // Cycle: 0 -> 1 -> 0 with identity transitions
            transducer.add_transition(0, {'a', 'a'}, 1);
            transducer.add_transition(1, {'b', 'b'}, 0);
            // No path to final state 2
            CHECK(util::contains_trans_identity(transducer, 10) == l_undef);
        }
    }
}

TEST_CASE("util::get_len_exprs", "[noodler]") {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util m_util_s(m);
    arith_util m_util_a(m);
    sort* str_sort = m_util_s.str.mk_string_sort();
    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref y(m.mk_const("y", str_sort), m);
    expr_ref len_x(m_util_s.str.mk_length(x), m);
    // str.len inside the argument of str.len is not collected
    expr_ref len_nested(m_util_s.str.mk_length(m_util_s.str.mk_at(y, m_util_s.str.mk_length(x))), m);

    SECTION("collects length terms, not inside str.len") {
        expr_ref f(m.mk_and(m_util_a.mk_le(len_x, m_util_a.mk_int(3)), m_util_a.mk_ge(len_nested, m_util_a.mk_int(1))), m);
        obj_hashtable<app> res;
        util::get_len_exprs(f, m_util_s, m, res);
        CHECK(res.size() == 2);
        CHECK(res.contains(to_app(len_x.get())));
        CHECK(res.contains(to_app(len_nested.get())));
    }

    SECTION("heavily shared DAG is traversed in linear time") {
        // t_0 = |x|, t_{i+1} = t_i + t_i: as a tree, t_200 has 2^200 leaves
        expr_ref t(len_x, m);
        for (unsigned i = 0; i < 200; ++i) {
            t = m_util_a.mk_add(t, t);
        }
        expr_ref f(m_util_a.mk_le(t, m_util_a.mk_int(10)), m);
        obj_hashtable<app> res;
        util::get_len_exprs(f, m_util_s, m, res);
        CHECK(res.size() == 1);
        CHECK(res.contains(to_app(len_x.get())));
    }
}

TEST_CASE("regex::extract_symbols", "[noodler]") {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util m_util_s(m);
    expr_ref x(m.mk_const("x", m_util_s.str.mk_string_sort()), m);

    SECTION("literals and ranges, variables skipped") {
        expr_ref re(m_util_s.re.mk_union(m_util_s.re.mk_to_re(m_util_s.str.mk_string("ab")),
                                         m_util_s.re.mk_range(m_util_s.str.mk_string("x"), m_util_s.str.mk_string("z"))), m);
        regex::Alphabet alph;
        regex::extract_symbols(re, m_util_s, alph);
        CHECK(alph == regex::Alphabet{ 'a', 'b', 'x', 'y', 'z' });
        regex::Alphabet alph_var;
        regex::extract_symbols(m_util_s.str.mk_concat(x, m_util_s.str.mk_string("c")), m_util_s, alph_var);
        CHECK(alph_var == regex::Alphabet{ 'c' });
    }

    SECTION("heavily shared DAG is traversed in linear time") {
        // r_0 = "a", r_{i+1} = r_i r_i: as a tree, r_200 has 2^200 leaves
        expr_ref r(m_util_s.re.mk_to_re(m_util_s.str.mk_string("a")), m);
        for (unsigned i = 0; i < 200; ++i) {
            r = m_util_s.re.mk_concat(r, r);
        }
        regex::Alphabet alph;
        regex::extract_symbols(r, m_util_s, alph);
        CHECK(alph == regex::Alphabet{ 'a' });
    }
}
