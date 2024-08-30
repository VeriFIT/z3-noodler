#include "smt/theory_str_noodler/parikh_image.h"
#include "test_utils.h"

using namespace smt::noodler;
using namespace smt::noodler::parikh;

#include <catch2/catch_test_macros.hpp>

using mata::nfa::State;

std::set<BasicTerm> lookup_abstract_transition_vars(std::vector<std::pair<State, State>> abstract_transitions, std::map<Transition, BasicTerm> parikh_image) {
    std::set<BasicTerm> collected_vars;

    for (std::pair<State, State> abstract_transition : abstract_transitions) {
        auto [source_state, target_state] = abstract_transition;

        for (auto& [transition, var] : parikh_image) {
            if (std::get<0>(transition) == source_state && std::get<2>(transition) == target_state) {
                collected_vars.insert(var);
            }
        }
    }

    return collected_vars;
}


std::set<BasicTerm> extract_summed_basic_terms_from_len_nodes(const std::vector<LenNode>& nodes) {
    std::set<BasicTerm> terms;
    for (const LenNode& node : nodes) {
        REQUIRE(node.type == LenFormulaType::LEAF);
        terms.insert(node.atom_val);
    }
    return terms;
}


TEST_CASE("NotContains::mk_parikh_images_encode_same_word_formula simple", "[noodler]") {
    std::vector<BasicTerm> lhs {get_var('x'), get_var('x')};
    std::vector<BasicTerm> rhs {get_var('x')};
    Predicate not_contains(PredicateType::NotContains, {lhs, rhs});

    AutAssignment aut_assignment;
    aut_assignment[get_var('x')] = regex_to_nfa("abc");

    ca::TagDiseqGen tag_automaton_generator(not_contains, aut_assignment);

    ca::TagAut tag_automaton = tag_automaton_generator.construct_tag_aut();

    REQUIRE(tag_automaton.nfa.num_of_states() == (12 + 1));  // Assume no trimming takes place

    std::set<ca::AtomicSymbol> used_symbols = tag_automaton.gather_used_symbols();

    ParikhImageNotContTag not_contains_parikh(tag_automaton, used_symbols, tag_automaton_generator.get_aut_matrix().get_number_of_states_in_row());

    // Generate two parikh images
    not_contains_parikh.compute_parikh_image();
    const std::map<Transition, BasicTerm> parikh_image = not_contains_parikh.get_trans_vars();

    not_contains_parikh.compute_parikh_image();
    const std::map<Transition, BasicTerm> other_image = not_contains_parikh.get_trans_vars();

    LenNode assertion = not_contains_parikh.mk_parikh_images_encode_same_word_formula(parikh_image, other_image);

    // We rely on the fact that we know the precise structure of the automaton
    size_t states_in_row = 4;
    std::vector<std::pair<State, State>> abstract_transitions = {
        {0 + 0*states_in_row, 1 + 0*states_in_row},
        {0 + 0*states_in_row, 1 + 1*states_in_row},
        {0 + 1*states_in_row, 1 + 1*states_in_row},
        {0 + 1*states_in_row, 1 + 2*states_in_row},
        {0 + 2*states_in_row, 1 + 2*states_in_row},
    };

    std::set<BasicTerm> parikh_vars       = lookup_abstract_transition_vars(abstract_transitions, parikh_image);
    std::set<BasicTerm> other_parikh_vars = lookup_abstract_transition_vars(abstract_transitions, other_image);

    REQUIRE(assertion.type == LenFormulaType::AND);

    bool eq_found = false;
    for (auto& child : assertion.succ) {
        REQUIRE(child.type == LenFormulaType::EQ);
        REQUIRE(child.succ.size() == 2);
        REQUIRE(child.succ[0].type == LenFormulaType::PLUS);
        REQUIRE(child.succ[1].type == LenFormulaType::PLUS);

        std::set<BasicTerm> lhs = extract_summed_basic_terms_from_len_nodes(child.succ[0].succ);
        std::set<BasicTerm> rhs = extract_summed_basic_terms_from_len_nodes(child.succ[1].succ);

        if (lhs == parikh_vars && rhs == other_parikh_vars) {
            eq_found = true;
            break;
        }

        if (rhs == parikh_vars && lhs == other_parikh_vars) { // commute
            eq_found = true;
            break;
        }
    }

    REQUIRE(eq_found);
}


TEST_CASE("NotContains::mk_rhs_longer_than_lhs_formula simple", "[noodler]") {
    std::vector<BasicTerm> lhs {get_var('x'), get_var('x'), get_var('y'), get_var('x')};
    std::vector<BasicTerm> rhs {get_var('x')};
    Predicate not_contains(PredicateType::NotContains, {lhs, rhs});

    AutAssignment aut_assignment;
    aut_assignment[get_var('x')] = regex_to_nfa("abc");
    aut_assignment[get_var('y')] = regex_to_nfa("abc");

    ca::TagDiseqGen tag_automaton_generator(not_contains, aut_assignment);
    ca::TagAut      tag_automaton = tag_automaton_generator.construct_tag_aut();

    size_t states_in_row = 8;  // "abc" is 4-state automaton, we concatenate two of these
    REQUIRE(tag_automaton.nfa.num_of_states() == (3*states_in_row + 1));  // Assume no trimming takes place

    std::set<ca::AtomicSymbol> used_symbols = tag_automaton.gather_used_symbols();

    size_t actual_number_of_states_in_row = tag_automaton_generator.get_aut_matrix().get_number_of_states_in_row();
    ParikhImageNotContTag not_contains_generator(tag_automaton, used_symbols, actual_number_of_states_in_row);

    // We should have |LHS| - |RHS| < offset. So for this test, it should be: 2*|x| + |y| < offset_var
    LenNode assertion = not_contains_generator.mk_rhs_longer_than_lhs_formula(not_contains);

    REQUIRE(assertion.type == LenFormulaType::LT);
    REQUIRE(assertion.succ.size() == 2);

    // Check RHS contains only offset
    LenNode assertion_rhs = assertion.succ[1];
    REQUIRE(assertion_rhs.type == LenFormulaType::LEAF);
    REQUIRE(assertion_rhs.atom_val == not_contains_generator.get_offset_var().atom_val);

    LenNode assertion_lhs = assertion.succ[0];
    REQUIRE(assertion_lhs.type == LenFormulaType::PLUS);
    REQUIRE(assertion_lhs.succ.size() == 2);  // Two variables are present

    std::set<std::pair<zstring, zstring>> raw_sum;
    for (const LenNode& summation_node : assertion_lhs.succ) {
        REQUIRE(summation_node.type == LenFormulaType::TIMES);

        LenNode coef_node = summation_node.succ[0];
        REQUIRE(coef_node.type == LenFormulaType::LEAF);

        LenNode var_node = summation_node.succ[1];
        REQUIRE(var_node.type == LenFormulaType::LEAF);

        raw_sum.insert(std::make_pair(coef_node.atom_val.get_name(), var_node.atom_val.get_name()));
    }

    std::set<std::pair<zstring, zstring>> expected_sum({{zstring("2"), zstring("x")}, {zstring("1"), zstring("y")}});
    REQUIRE(raw_sum == expected_sum);
}

TEST_CASE("NotContains::ensure_symbol_unqueness_using_total_sum simple", "[noodler]") {
    std::vector<BasicTerm> lhs {get_var('x'), get_var('y')};
    std::vector<BasicTerm> rhs {get_var('x')};
    Predicate not_contains(PredicateType::NotContains, {lhs, rhs});

    AutAssignment aut_assignment;
    aut_assignment[get_var('x')] = regex_to_nfa("abc");
    aut_assignment[get_var('y')] = regex_to_nfa("aa");

    ca::TagDiseqGen tag_automaton_generator(not_contains, aut_assignment);
    ca::TagAut      tag_automaton = tag_automaton_generator.construct_tag_aut();

    size_t states_in_row = 7;
    REQUIRE(tag_automaton.nfa.num_of_states() == (3*states_in_row + 1));  // Assume no trimming takes place

    std::set<ca::AtomicSymbol> used_symbols = tag_automaton.gather_used_symbols();

    size_t actual_number_of_states_in_row = tag_automaton_generator.get_aut_matrix().get_number_of_states_in_row();
    ParikhImageNotContTag not_contains_generator(tag_automaton, used_symbols, actual_number_of_states_in_row);

    std::vector<std::pair<State, State>> transitions_over_a = { // Only sampling transitions
        // Transitions from aut('x')
        {0 + 0*states_in_row, 1 + 1*states_in_row},
        {0 + 1*states_in_row, 1 + 2*states_in_row},
        // Transitions from aut('y') - first 'a'
        {4 + 0*states_in_row, 5 + 1*states_in_row},
        {4 + 1*states_in_row, 5 + 2*states_in_row},
        // Transitions from aut('y') - second 'a'
        {5 + 0*states_in_row, 6 + 1*states_in_row},
        {5 + 1*states_in_row, 6 + 2*states_in_row},
    };

    not_contains_generator.compute_parikh_image();
    const std::map<Transition, BasicTerm> parikh_image = not_contains_generator.get_trans_vars();

    not_contains_generator.symbol_count_formula();
    std::map<mata::Symbol, std::vector<LenNode>> transition_vars_by_symbol = not_contains_generator.group_sampling_transition_vars_by_symbol();
    LenNode assertion = not_contains_generator.ensure_symbol_uniqueness_using_total_sum(transition_vars_by_symbol);

    REQUIRE(assertion.type == LenFormulaType::AND);

    std::set<BasicTerm> transition_vars = lookup_abstract_transition_vars(transitions_over_a, parikh_image);

    bool var_set_found = false;
    for (LenNode conjunct : assertion.succ) {
        REQUIRE(conjunct.type == LenFormulaType::LEQ);
        REQUIRE(conjunct.succ.size() == 2);
        REQUIRE(conjunct.succ[0].type == LenFormulaType::PLUS);

        LenNode& sum = conjunct.succ[0];

        std::set<BasicTerm> summed_vars;
        for (auto sum_node : sum.succ) {
            REQUIRE(sum_node.type == LenFormulaType::LEAF);
            summed_vars.insert(sum_node.atom_val);
        }

        if (summed_vars == transition_vars) {
            var_set_found = true;
            break;
        }
    }

    REQUIRE(var_set_found);
}
