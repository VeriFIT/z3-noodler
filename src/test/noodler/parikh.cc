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
