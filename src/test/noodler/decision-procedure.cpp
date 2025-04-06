#include <iostream>
#include <algorithm>
#include <utility>

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_exception.hpp>

#include "smt/theory_str_noodler/decision_procedure.h"
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "ast/reg_decl_plugins.h"
#include "test_utils.h"

TEST_CASE("Decision Procedure", "[noodler]") {
    smt_params params;
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    smt::context ctx{ast_m, params };
    theory_str_noodler_params noodler_params{};
    TheoryStrNoodlerCUT noodler{ ctx, ast_m, noodler_params };
    auto& m_util_s{ noodler.m_util_s };
    auto& m_util_a{ noodler.m_util_a };
    auto& m{ noodler.m };

    mata::nft::Nft identity{1, {0}, {0}};
    identity.add_transition(0, {'a', 'a'}, 0);
    identity.add_transition(0, {'b', 'b'}, 0);

    mata::nft::Nft transform_to_empty{1, {0}, {0}};
    transform_to_empty.add_transition(0, {'a', mata::nft::EPSILON}, 0);
    transform_to_empty.add_transition(0, {'b', mata::nft::EPSILON}, 0);

    AutAssignment init_ass;
    init_ass.set_alphabet({'a', 'b'});

    SECTION("unsat-simple", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("unsat-FM-example", "[noodler]") {

        Formula equalities;
        equalities.add_predicate(create_equality("zyx", "xxz"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a+b+");
        init_ass[get_var('z')] = regex_to_nfa("b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("unsat-simple-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution());
        CHECK(proc.compute_next_solution());
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple-length-substitution", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("ab*");
        init_ass[get_var('z')] = regex_to_nfa("ab*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();

        REQUIRE(proc.compute_next_solution() == lbool::l_true);

        REQUIRE(proc.solution.substitution_map.count(get_var('z')) > 0);
        const auto &z_subst = proc.solution.substitution_map.at(get_var('z'));
        CHECK(z_subst.size() == 1);
        const auto &z_tmp_var = z_subst[0];
        REQUIRE(proc.solution.substitution_map.count(get_var('x')) > 0);
        REQUIRE(proc.solution.substitution_map.at(get_var('x')).size() == 1);
        CHECK(z_tmp_var == proc.solution.substitution_map.at(get_var('x'))[0]);
        REQUIRE(proc.solution.aut_ass.count(z_tmp_var) > 0);
        CHECK(mata::nfa::are_equivalent(*(proc.solution.aut_ass.at(z_subst[0])), *regex_to_nfa("a")));

        CHECK(proc.solution.substitution_map.count(get_var('u')) + proc.solution.substitution_map.count(get_var('y')) == 1);
        CHECK(proc.solution.aut_ass.count(get_var('u')) + proc.solution.aut_ass.count(get_var('y')) == 1);

        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("unsat-two-equations", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        equalities.add_predicate(create_equality("yx", "r"));
        init_ass[get_var('x')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        init_ass[get_var('r')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-two-equations", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        equalities.add_predicate(create_equality("yx", "r"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('r')] = regex_to_nfa("aaa");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("unsat-two-equations-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        equalities.add_predicate(create_equality("yx", "r"));
        init_ass[get_var('x')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        init_ass[get_var('r')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-two-equations-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("yx", "r"));
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("ab*");
        init_ass[get_var('z')] = regex_to_nfa("ab*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('r')] = regex_to_nfa("ab*a");
        DecisionProcedureCUT proc(equalities, init_ass, {
            BasicTerm(BasicTermType::Variable, "x"),
            BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();

        REQUIRE(proc.compute_next_solution());

        proc.solution.flatten_substition_map();
        CHECK(mata::nfa::are_equivalent(proc.solution.aut_ass.get_automaton_concat(proc.solution.substitution_map.at(get_var('x'))), *regex_to_nfa("a")));
        CHECK(mata::nfa::are_equivalent(proc.solution.aut_ass.get_automaton_concat(proc.solution.substitution_map.at(get_var('z'))), *regex_to_nfa("a")));

        // FIXME: Length formula len is different than formula from lambda. Hashes are not equal.
        // auto l_vars = { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") };
        // auto var_map = create_var_map(l_vars, m, m_util_s);
        // expr_ref len = proc.get_lengths(var_map);

        // // result as a lambda (different ordering of variables due to std::unordered_set)
        // auto resf = [&](std::vector<std::string> vc) {
        //     return expr_ref(m.mk_and(
        //     m.mk_and(
        //         m.mk_true(),
        //         m.mk_and(
        //             m.mk_or(
        //                 m.mk_false(),
        //                 m.mk_eq(m_util_s.str.mk_length(var_map.at(BasicTerm(BasicTermType::Variable, vc[0]))), m_util_a.mk_int(1))
        //             ),
        //             m_util_a.mk_ge(m_util_s.str.mk_length(var_map.at(BasicTerm(BasicTermType::Variable, vc[0]))), m_util_a.mk_int(0))
        //         )
        //     ),
        //     m.mk_and(
        //         m.mk_or(
        //             m.mk_false(),
        //             m.mk_eq(m_util_s.str.mk_length(var_map.at(BasicTerm(BasicTermType::Variable, vc[1]))), m_util_a.mk_int(1))
        //         ),
        //         m_util_a.mk_ge(m_util_s.str.mk_length(var_map.at(BasicTerm(BasicTermType::Variable, vc[1]))), m_util_a.mk_int(0))
        //     )
        //     ),
        // m);
        // };

        // CHECK(((resf({"x", "z"})->hash() == len->hash()) || (resf({"z", "x"})->hash() == len->hash())));
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-two-equations-length2", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("yx", "r"));
        equalities.add_predicate(create_equality("xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("ab*");
        init_ass[get_var('z')] = regex_to_nfa("ab*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('r')] = regex_to_nfa("ab*a");
        DecisionProcedureCUT proc(equalities, init_ass, {
                BasicTerm(BasicTermType::Variable, "x"),
                BasicTerm(BasicTermType::Variable, "z"),
                BasicTerm(BasicTermType::Variable, "r") },
            m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();

        REQUIRE(proc.compute_next_solution());
        proc.solution.flatten_substition_map();
        CHECK(mata::nfa::are_equivalent(proc.solution.aut_ass.get_automaton_concat(proc.solution.substitution_map.at(get_var('x'))), *regex_to_nfa("a")));
        CHECK(mata::nfa::are_equivalent(proc.solution.aut_ass.get_automaton_concat(proc.solution.substitution_map.at(get_var('z'))), *regex_to_nfa("a")));
        CHECK(mata::nfa::are_equivalent(proc.solution.aut_ass.get_automaton_concat(proc.solution.substitution_map.at(get_var('r'))), *regex_to_nfa("aa")));

        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("unsat-simple-non-chain-free", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("x", "xx"));
        init_ass[get_var('x')] = regex_to_nfa("aa?b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple-non-chain-free", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("x", "xx"));
        init_ass[get_var('x')] = regex_to_nfa("a*b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("unsat-simple-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "xy", "zu"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("unsat-two-equations-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "xy", "zu"));
        equalities.add_predicate(create_transducer(identity, "yx", "r"));
        init_ass[get_var('x')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        init_ass[get_var('r')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-two-equations-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "xy", "zu"));
        equalities.add_predicate(create_transducer(identity, "yx", "r"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('r')] = regex_to_nfa("aaa");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_true);
    }

    SECTION("sat-emptiness-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(transform_to_empty, "x", "y"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        CHECK(proc.get_model(get_var('x'), {}) == zstring("a"));
        CHECK(proc.get_model(get_var('y'), {}) == zstring(""));
    }

    SECTION("sat-emptiness-transducer2", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(transform_to_empty, "x", "y"));
        init_ass[get_var('x')] = regex_to_nfa("a+");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        CHECK(proc.get_model(get_var('y'), {}) == zstring(""));
    }

    SECTION("unsat-emptiness-transducer", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(transform_to_empty, "y", "x"));
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        CHECK(proc.compute_next_solution() == lbool::l_false);
    }

    SECTION("sat-simple-transducer-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "x", "u"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { get_var('x'), get_var('u') }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        CHECK_NOTHROW(proc.get_lengths());
    }

    SECTION("sat-simple-transducer-length2", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "x", "u"));
        equalities.add_predicate(create_transducer(identity, "z", "x"));
        equalities.add_predicate(create_transducer(identity, "y", "z"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { get_var('y'), get_var('u') }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        CHECK_NOTHROW(proc.get_lengths());
    }

    SECTION("sat-simple-transducer-length3", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "x", "u"));
        equalities.add_predicate(create_transducer(identity, "z", "x"));
        equalities.add_predicate(create_transducer(identity, "y", "z"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { get_var('y'),  get_var('x'),  get_var('z'), get_var('u') }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        CHECK_NOTHROW(proc.get_lengths());
    }

    SECTION("sat-simple-transducer-length4", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_transducer(identity, "x", "u"));
        equalities.add_predicate(create_transducer(identity, "x", "z"));
        equalities.add_predicate(create_transducer(identity, "yy", "x"));
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { get_var('y'),  get_var('x'),  get_var('z'), get_var('u') }, m, m_util_s, m_util_a, {}, noodler_params);
        proc.init_computation();
        REQUIRE(proc.compute_next_solution() == lbool::l_true);
        CHECK_NOTHROW(proc.get_lengths());
    }
}
