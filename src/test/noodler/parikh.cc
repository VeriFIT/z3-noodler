#include "smt/theory_str_noodler/parikh_image.h"
#include "smt/theory_str_noodler/expr_solver.h"
#include "test_utils.h"


#include "ast/rewriter/arith_rewriter.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "model/model.h"
#include "parsers/smt2/smt2parser.h"

using namespace smt::noodler;
using namespace smt::noodler::parikh;
using namespace smt::noodler::ca;

#include <catch2/catch_test_macros.hpp>

using mata::nfa::State;

struct ParikhImageContext {
    const TagAut& automaton;
    const std::map<Transition, BasicTerm>& transition_labeling;
};

std::set<BasicTerm> lookup_abstract_transition_vars(ParikhImageContext& context, const std::vector<std::pair<State, State>>& abstract_transitions, bool must_cross_levels = false) {
    std::set<BasicTerm> collected_vars;

    for (std::pair<State, State> abstract_transition : abstract_transitions) {
        // Abstract transitions reffer to states in the template (first row) that was copied multiple times to create tag aut
        auto [source_state, target_state] = abstract_transition;
        for (auto& [transition, var] : context.transition_labeling) {
            bool is_matching = true;

            mata::nfa::State transition_source_state_in_copy = context.automaton.metadata.where_is_state_copied_from[std::get<0>(transition)];
            mata::nfa::State transition_target_state_in_copy = context.automaton.metadata.where_is_state_copied_from[std::get<2>(transition)];

            is_matching &= (transition_source_state_in_copy == source_state);
            is_matching &= (transition_target_state_in_copy == target_state);

            if (must_cross_levels) {
                size_t source_level = context.automaton.metadata.levels[std::get<0>(transition)];
                size_t target_level = context.automaton.metadata.levels[std::get<2>(transition)];
                is_matching &= (source_level != target_level);
            }

            if (is_matching) {
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

    REQUIRE(tag_automaton.nfa.num_of_states() == 8);  // 4 states * 3 copies, but half are needless and removed during trimming

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
        {0 + 0*states_in_row, 1 + 0*states_in_row},  // (Copy=0, q0) --> (Copy=0, q1)  (non-sampling)
        {0 + 0*states_in_row, 1 + 1*states_in_row},  // (Copy=0, q0) --> (Copy=1, q1)  (sampling)
        // TRIMMED: {0 + 1*states_in_row, 1 + 1*states_in_row},  // (Copy=1, q0) --> (Copy=1, q1)  (non-sampling)
        // TRIMMED: {0 + 1*states_in_row, 1 + 2*states_in_row},  // (Copy=1, q0) --> (Copy=2, q1)  (sampling)
        // TRIMMED: {0 + 2*states_in_row, 1 + 2*states_in_row},  // (Copy=2, q0) --> (Copy=2, q1)  (sampling)
    };

    ParikhImageContext parikh_image_context { .automaton = tag_automaton, .transition_labeling = parikh_image, };
    ParikhImageContext other_image_context { .automaton = tag_automaton, .transition_labeling = other_image, };

    std::set<BasicTerm> parikh_vars       = lookup_abstract_transition_vars(parikh_image_context, abstract_transitions);
    std::set<BasicTerm> other_parikh_vars = lookup_abstract_transition_vars(other_image_context, abstract_transitions);

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
    REQUIRE(tag_automaton.nfa.num_of_states() == 20);

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
    REQUIRE(tag_automaton.nfa.num_of_states() == 17);

    std::set<ca::AtomicSymbol> used_symbols = tag_automaton.gather_used_symbols();

    size_t actual_number_of_states_in_row = tag_automaton_generator.get_aut_matrix().get_number_of_states_in_row();
    ParikhImageNotContTag not_contains_generator(tag_automaton, used_symbols, actual_number_of_states_in_row);

    std::vector<std::pair<State, State>> transitions_over_a = { // Only sampling transitions
        {0, 1},  // aut(X) - first  'a'
        {4, 5},  // aut(Y) - first ' a'
        {5, 6},  // aut(Y) - second 'a'
    };

    not_contains_generator.compute_parikh_image();
    const std::map<Transition, BasicTerm> parikh_image = not_contains_generator.get_trans_vars();

    not_contains_generator.symbol_count_formula();
    std::map<mata::Symbol, std::vector<LenNode>> transition_vars_by_symbol = not_contains_generator.group_sampling_transition_vars_by_symbol();

    LenNode assertion = not_contains_generator.ensure_symbol_uniqueness_using_total_sum(transition_vars_by_symbol);

    REQUIRE(assertion.type == LenFormulaType::AND);

    ParikhImageContext context { .automaton = tag_automaton, .transition_labeling = parikh_image };
    std::set<BasicTerm> transition_vars = lookup_abstract_transition_vars(context, transitions_over_a, true); // NOTE: must_cross_levels = true

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

LenNode dsl_exists(const BasicTerm& var, const LenNode& subformula) {
    return LenNode(LenFormulaType::EXISTS, {var, subformula});
}

void assert_eq_correct(expr* z3_atom, unsigned var_idx, int rhs) {
    REQUIRE(z3_atom->get_kind() == AST_APP);
    REQUIRE(to_app(z3_atom)->get_name().str() == "=");

    auto z3_lhs = to_app(z3_atom)->get_arg(0);
    REQUIRE(z3_lhs->get_kind() == AST_VAR);
    REQUIRE(to_var(z3_lhs)->get_idx() == var_idx);

    auto z3_rhs = to_app(z3_atom)->get_arg(1);
    REQUIRE(z3_rhs->get_kind() == AST_APP);
    REQUIRE(to_app(z3_rhs)->get_name().str() == "Int");
    REQUIRE(to_app(z3_rhs)->get_parameter(0).get_kind() == parameter::PARAM_RATIONAL);
    REQUIRE(to_app(z3_rhs)->get_parameter(0).get_rational().get_int32() == rhs);
}

void populate_automaton_with_flat(mata::nfa::Nfa& nfa, unsigned symbol) {
    nfa.add_state(0);

    nfa.initial.clear();
    nfa.initial.insert(0);

    nfa.final.clear();
    nfa.final.insert(0);

    mata::nfa::Transition transition(0, symbol, 0);
    nfa.delta.add(transition);
}

TEST_CASE("AutMatrix : state metadata are computed") {
    //
    // NotContains(XYZ, ZYX)
    //

    BasicTerm var_x(BasicTermType::Variable, "X");
    BasicTerm var_y(BasicTermType::Variable, "Y");
    BasicTerm var_z(BasicTermType::Variable, "Z");

    mata::nfa::Nfa lang_x;
    populate_automaton_with_flat(lang_x, 0);
    mata::nfa::Nfa lang_y = lang_x;
    mata::nfa::Nfa lang_z = lang_x;

    std::vector<BasicTerm> lhs {var_x, var_y, var_z};
    std::vector<BasicTerm> rhs {var_z, var_y, var_x};
    Predicate predicate(PredicateType::NotContains, {lhs, rhs});

    AutAssignment assignment;
    assignment[var_x] = std::make_shared<mata::nfa::Nfa>(lang_x);
    assignment[var_y] = std::make_shared<mata::nfa::Nfa>(lang_y);
    assignment[var_z] = std::make_shared<mata::nfa::Nfa>(lang_z);

    DiseqAutMatrix aut_matrix (predicate, assignment);
    AutMatrixUnionResult result = aut_matrix.union_matrix();

    // Every variable automaton has only 1 state - the result should be a 3 states x 3 states matrix
    size_t expected_result_nfa_state_cnt = 3*3;
    REQUIRE(result.nfa.num_of_states() == expected_result_nfa_state_cnt);
    REQUIRE(result.metadata.var_info.size() == expected_result_nfa_state_cnt);

    std::vector<size_t> expected_state_vars {0, 1, 2, 0, 1, 2, 0, 1, 2};
    REQUIRE(result.metadata.var_info == expected_state_vars);

    std::vector<size_t> expected_state_copy_origin {0, 1, 2, 0, 1, 2, 0, 1, 2};
    REQUIRE(result.metadata.where_is_state_copied_from == expected_state_vars);
}

TEST_CASE("LenFormula : variables are numbered correctly", "[noodler]") {
    // Test whether quantified formulae do not change semantics when translated to z3

    /*
     *
     *              \exists x                  \exists x
     *                  |                          |
     *              \exists y                  \exists y
     *                  |                          |
     *                 LOR                        LOR
     *                /   \                     /     \
     *               /     \         ==>       /       \
     *             AND      \                 AND       \
     *            /   \    EXISTS z         /    \       EXISTS z
     *           x=1  y=2     |           (1)=1  (0)=2      |
     *                       AND                           AND
     *                       / \                          /   \
     *                     y=3 z=4                      (1)=3 (0)=4
     */

    BasicTerm var_x (BasicTermType::Variable, "x");
    BasicTerm var_y (BasicTermType::Variable, "y");
    BasicTerm var_z (BasicTermType::Variable, "z");

    LenNode left_conjunction(LenFormulaType::AND, {
        LenNode(LenFormulaType::EQ, {var_x, 1}),
        LenNode(LenFormulaType::EQ, {var_y, 2})
    });
    LenNode right_conjunction(LenFormulaType::AND, {
        LenNode(LenFormulaType::EQ, {var_y, 3}),
        LenNode(LenFormulaType::EQ, {var_z, 4})
    });
    LenNode right_lor_branch = dsl_exists(var_z, right_conjunction);
    LenNode disjunction = LenNode(LenFormulaType::OR, {left_conjunction, right_lor_branch});

    LenNode root = dsl_exists(var_x, LenNode(LenFormulaType::NOT, {dsl_exists(var_y, disjunction)}));

    // Make a blank context
    ast_manager manager;
    reg_decl_plugins(manager);

    arith_util arith_util_i(manager);
    seq_util seq_util_i(manager);
    std::map<std::string, unsigned> quantified_vars;
    std::map<BasicTerm, expr_ref> known_exprs;

    LenFormulaContext ctx {
        .manager = manager,
        .arith_utilities = arith_util_i,
        .seq_utilities = seq_util_i,
        .quantified_vars = quantified_vars,
        .known_z3_exprs = known_exprs,
    };

    expr_ref z3_formula = convert_len_node_to_z3_formula(ctx, root);

    REQUIRE(z3_formula.get()->get_kind() == AST_QUANTIFIER);  // Exists x
    auto quantifier = to_quantifier(z3_formula.get());

    auto application = quantifier->get_expr();
    REQUIRE(application->get_kind() == AST_APP);

    auto exists_y_quantif = to_app(application)->get_arg(0); // Exists y
    REQUIRE(exists_y_quantif->get_kind() == AST_QUANTIFIER);

    auto z3_disjunction = to_quantifier(exists_y_quantif)->get_expr();
    REQUIRE(z3_disjunction->get_kind() == AST_APP);
    REQUIRE(to_app(z3_disjunction)->get_name().str() == "or");

    {
        auto z3_left_conjunction = to_app(z3_disjunction)->get_arg(0);
        REQUIRE(z3_left_conjunction->get_kind() == AST_APP);
        REQUIRE(to_app(z3_left_conjunction)->get_name().str() == "and");
        assert_eq_correct(to_app(z3_left_conjunction)->get_arg(0), 1, 1); // x=1  => (1)=1
        assert_eq_correct(to_app(z3_left_conjunction)->get_arg(1), 0, 2); // y=2  => (0)=2
    }

    {
        auto z3_exists_z = to_app(z3_disjunction)->get_arg(1);
        REQUIRE(z3_exists_z->get_kind() == AST_QUANTIFIER);

        auto z3_right_conjunction = to_quantifier(z3_exists_z)->get_expr();
        REQUIRE(z3_right_conjunction->get_kind() == AST_APP);
        REQUIRE(to_app(z3_right_conjunction)->get_name().str() == "and");

        assert_eq_correct(to_app(z3_right_conjunction)->get_arg(0), 1, 3); // y=3  => (1)=3
        assert_eq_correct(to_app(z3_right_conjunction)->get_arg(1), 0, 4); // z=4  => (0)=4
    }
}

std::optional<size_t> find_mismatch_pos_tag(std::set<AtomicSymbol>& tag_set, const BasicTerm& var) {
    for (auto& tag : tag_set) {
        if (tag.type == AtomicSymbol::TagType::MISMATCH_POS && tag.var == var) return tag.copy_idx;
    }
    return std::nullopt;
}

std::map<size_t, std::set<size_t>> get_nonsampling_transitions_labeled_with_symbol(TagAut& tag_automaton, const BasicTerm& var) {
    std::map<size_t, std::set<size_t>> level_to_mismatch_pos_copy_indices_used;

    for (mata::nfa::State source_state = 0; source_state < tag_automaton.nfa.num_of_states(); source_state++) {
        for (const mata::nfa::SymbolPost& symbol_post : tag_automaton.nfa.delta[source_state]) {
            std::set<AtomicSymbol> tag_set = tag_automaton.alph.get_symbol(symbol_post.symbol);
            auto mismatch_tag = find_mismatch_pos_tag(tag_set, var);
            if (!mismatch_tag.has_value()) continue;

            for (const mata::nfa::State target_state : symbol_post.targets) {
                size_t source_level = tag_automaton.metadata.levels[source_state];
                size_t target_level = tag_automaton.metadata.levels[target_state];
                if (source_level != target_level) continue;

                level_to_mismatch_pos_copy_indices_used[source_level].insert(mismatch_tag.value());
            }
        }
    }

    return level_to_mismatch_pos_copy_indices_used;
}

TEST_CASE("NotContains::copies should differ in transition symbols", "[noodler]") {
    // Check that transitions use different _i_ in their <P, x, _i_> symbols
    std::vector<BasicTerm> lhs {get_var('x'), get_var('y')};
    std::vector<BasicTerm> rhs {get_var('x')};
    Predicate disequation(PredicateType::Equation, {lhs, rhs});

    AutAssignment aut_assignment;
    aut_assignment[get_var('x')] = regex_to_nfa("abc");
    aut_assignment[get_var('y')] = regex_to_nfa("aa");

    ca::TagDiseqGen tag_automaton_generator(disequation, aut_assignment);
    ca::TagAut      tag_automaton = tag_automaton_generator.construct_tag_aut();

    // size_t states_in_row = 7;
    REQUIRE(tag_automaton.nfa.num_of_states() == 17);

    BasicTerm var_x = get_var('x');
    auto what_mismatch_labels_do_levels_contain = get_nonsampling_transitions_labeled_with_symbol(tag_automaton, var_x);

    std::map<size_t, std::set<size_t>> expected_labels_at_levels;
    expected_labels_at_levels[0] = {1};
    expected_labels_at_levels[1] = {2};

    bool do_match = (expected_labels_at_levels == what_mismatch_labels_do_levels_contain);
    REQUIRE(do_match);
}

using TagSet = std::set<ca::AtomicSymbol>;

std::optional<mata::nfa::State> find_state_in_trimmed_aut(const TagAut& aut, mata::nfa::State needle_state, size_t states_in_row_before_trim) {
    size_t state_level = needle_state / states_in_row_before_trim;
    size_t state_copy_origin = needle_state % states_in_row_before_trim;

    for (mata::nfa::State candidate_state = 0; candidate_state < aut.nfa.num_of_states(); candidate_state++) {
        size_t candidate_level  = aut.metadata.levels[candidate_state];
        size_t candidate_origin = aut.metadata.where_is_state_copied_from[candidate_state];

        if (candidate_level == state_level && candidate_origin == state_copy_origin) return candidate_state;
    }

    return std::nullopt;
}

std::string tag_set_to_string(const TagSet& tag_set) {
    std::stringstream string_builder;
    string_builder << "(";
    for (auto& tag : tag_set) {
        string_builder << tag.to_string() << ", ";
    }
    string_builder << ")";
    return string_builder.str();
}

void dump_alphabet(CounterAlphabet& alphabet) {
    std::set<TagSet> known_alphabet_symbols = alphabet.get_all_symbols();
    for (const auto& tag_set : known_alphabet_symbols) {
        std::cout << "  -";
        std::cout << tag_set_to_string(tag_set) << ", ";
        std::cout << "\n";
    }
    std::cout << "\n";
}

struct TagSetTransition {
    mata::nfa::State source;
    TagSet tag_set;
    mata::nfa::State target;
};

namespace std {
    std::ostream& operator<<(std::ostream& output_stream, const TagSetTransition& transition) {
        output_stream << "{.source=" << transition.source
                      << ", .tag_set=" << tag_set_to_string(transition.tag_set)
                      << ", .target=" << transition.target << "}";
        return output_stream;
    }
};

void assert_all_transitions_present(TagAut& aut, std::vector<TagSetTransition>& transitions, size_t states_in_row) {
    std::vector<TagSetTransition> missing_transitions;

    for (auto& transition : transitions) {
        bool found_transition = false;

        auto maybe_source_state = find_state_in_trimmed_aut(aut, transition.source, states_in_row);
        auto maybe_target_state = find_state_in_trimmed_aut(aut, transition.target, states_in_row);
        REQUIRE(maybe_source_state.has_value());
        REQUIRE(maybe_target_state.has_value());

        if (!aut.alph.has_mata_symbol_for(transition.tag_set)) {
            std::cout << "Unknown tag set: ";
            std::cout << tag_set_to_string(transition.tag_set) << "\n";
            std::cout << "Known tag sets: ";
            dump_alphabet(aut.alph);
            std::cout << "\n";
        }

        mata::Symbol tag_set_handle = aut.alph.get_mata_symbol(transition.tag_set);

        mata::nfa::StatePost source_post = aut.nfa.delta[maybe_source_state.value()];

        for (mata::nfa::SymbolPost symbol_post : source_post) {
            if (symbol_post.symbol != tag_set_handle) continue;

            for (mata::nfa::State post_state : symbol_post) {
                if (post_state == maybe_target_state.value()) {
                    found_transition = true;
                    break;
                }
            }

            break;
        }

        if (!found_transition) {
            std::cout << "Transition missing! " << transition << "\n";
            missing_transitions.push_back(transition);
        }
    }

    REQUIRE(missing_transitions.empty());
}

TEST_CASE("Disequations :: tag automaton for a single disequation is correct", "[noodler]") {
    BasicTerm var_x = get_var('x');
    BasicTerm var_y = get_var('y');
    BasicTerm var_z = get_var('z');
    Predicate diseq1(PredicateType::Equation, { {var_x}, {var_y, var_z} });

    AutAssignment aut_assignment;
    aut_assignment[var_x] = regex_to_nfa("a");
    aut_assignment[var_y] = regex_to_nfa("b");
    aut_assignment[var_z] = regex_to_nfa("c");

    ca::TagDiseqGen tag_automaton_generator(diseq1, aut_assignment);
    ca::TagAut      tag_automaton = tag_automaton_generator.construct_tag_aut();

    REQUIRE(tag_automaton.nfa.num_of_states() == 13);

    ca::AtomicSymbol len_x = ca::AtomicSymbol::create_l_symbol(var_x);
    ca::AtomicSymbol len_y = ca::AtomicSymbol::create_l_symbol(var_y);
    ca::AtomicSymbol len_z = ca::AtomicSymbol::create_l_symbol(var_z);
    ca::AtomicSymbol mismatch_pos_x_1 = ca::AtomicSymbol::create_p_symbol(var_x, 1);
    ca::AtomicSymbol mismatch_pos_y_1 = ca::AtomicSymbol::create_p_symbol(var_y, 1);
    ca::AtomicSymbol mismatch_pos_y_2 = ca::AtomicSymbol::create_p_symbol(var_y, 2);
    ca::AtomicSymbol mismatch_pos_z_2 = ca::AtomicSymbol::create_p_symbol(var_z, 2);
    ca::AtomicSymbol register_store_x_1 = ca::AtomicSymbol::create_r_symbol(var_x, 1, 'a');
    ca::AtomicSymbol register_store_y_1 = ca::AtomicSymbol::create_r_symbol(var_y, 1, 'b');
    ca::AtomicSymbol register_store_y_2 = ca::AtomicSymbol::create_r_symbol(var_y, 2, 'b');
    ca::AtomicSymbol register_store_z_2 = ca::AtomicSymbol::create_r_symbol(var_z, 2, 'c');

    size_t states_in_row_before_trimming = 6;

    std::vector<TagSetTransition> expected_transitions = {
        {.source = 0, .tag_set = {len_x, mismatch_pos_x_1}, .target = 1},
        {.source = 0, .tag_set = {len_x, mismatch_pos_x_1, register_store_x_1}, .target = 7},
        {.source = 2, .tag_set = {len_y, mismatch_pos_y_1, register_store_y_1}, .target = 9},
        {.source = 8, .tag_set = {len_y, mismatch_pos_y_2}, .target = 9},
        {.source = 8, .tag_set = {len_y, mismatch_pos_y_2, register_store_y_2}, .target = 15},
        {.source = 8, .tag_set = {len_y, mismatch_pos_y_2, register_store_y_2}, .target = 15},
        {.source = 16, .tag_set = {len_z}, .target = 17},
        {.source = 10, .tag_set = {len_z, mismatch_pos_z_2, register_store_z_2}, .target = 17},
    };

    assert_all_transitions_present(tag_automaton, expected_transitions, states_in_row_before_trimming);
}


void add_all_possible_sampling_transitions(std::vector<TagSetTransition>& transitions, const BasicTerm& var, size_t copy_idx, size_t predicate_count, const mata::nfa::Transition& transition) {
    ca::AtomicSymbol var_len = ca::AtomicSymbol::create_l_symbol(var);
    ca::AtomicSymbol mismatch_pos = ca::AtomicSymbol::create_p_symbol(var, copy_idx);

    for (size_t predicate_idx = 0; predicate_idx < predicate_count; predicate_idx++) {
        ca::AtomicSymbol register_store_left = ca::AtomicSymbol::create_r_symbol_with_predicate_info(predicate_idx, var, AtomicSymbol::PredicateSide::LEFT, copy_idx, transition.symbol);
        TagSet left_tag_set = {var_len, mismatch_pos, register_store_left};
        TagSetTransition transition_sampling_left = {.source = transition.source, .tag_set = left_tag_set, .target = transition.target};
        transitions.push_back(transition_sampling_left);

        ca::AtomicSymbol register_store_right = ca::AtomicSymbol::create_r_symbol_with_predicate_info(predicate_idx, var, AtomicSymbol::PredicateSide::RIGHT, copy_idx, transition.symbol);
        TagSet right_tag_set = {var_len, mismatch_pos, register_store_right};
        TagSetTransition transition_sampling_right = {.source = transition.source, .tag_set = right_tag_set, .target = transition.target};
        transitions.push_back(transition_sampling_right);
    }
}

void add_all_possible_copy_transitions_between_states(std::vector<TagSetTransition>& transitions, const BasicTerm& var, size_t copy_idx, size_t predicate_count, const mata::nfa::Transition& transition) {
    for (size_t predicate_idx = 0; predicate_idx < predicate_count; predicate_idx++) {
        ca::AtomicSymbol copy_for_lhs = ca::AtomicSymbol::create_c_symbol(var, predicate_idx, AtomicSymbol::PredicateSide::LEFT, copy_idx);
        TagSetTransition copy_transtion_for_lhs = {.source = transition.source, .tag_set = {copy_for_lhs}, .target = transition.target};
        transitions.push_back(copy_transtion_for_lhs);

        ca::AtomicSymbol copy_for_rhs = ca::AtomicSymbol::create_c_symbol(var, predicate_idx, AtomicSymbol::PredicateSide::RIGHT, copy_idx);
        TagSetTransition copy_transition_for_rhs = {.source = transition.source, .tag_set = {copy_for_rhs}, .target = transition.target};
        transitions.push_back(copy_transition_for_rhs);
    }
}

void add_copy_transitions_for_variable_state_range(std::vector<TagSetTransition>& transitions, const BasicTerm& var, size_t predicate_count, size_t first_state, size_t last_state, size_t states_in_row) {
    size_t num_of_rows = predicate_count*2 + 1;
    for (mata::nfa::State state = first_state; state <= last_state; state++) {
        for (size_t source_copy_idx = 1; source_copy_idx < num_of_rows - 1; source_copy_idx++) {
            mata::nfa::State source_state = source_copy_idx*states_in_row     + state;
            mata::nfa::State target_state = (source_copy_idx+1)*states_in_row + state;
            mata::nfa::Transition transition(source_state, 'a', target_state);

            size_t expected_copy_idx_labeling_transition = source_copy_idx + 1; // Copy tags are labeled with destination copy
            add_all_possible_copy_transitions_between_states(transitions, var, expected_copy_idx_labeling_transition, predicate_count, transition);
        }
    }
}

void add_sampling_transitions_based_on_template(std::vector<TagSetTransition>& transitions, const mata::nfa::Transition& transition_template, BasicTerm& var, size_t predicate_count, size_t states_in_row) {
    size_t num_of_rows = 2*predicate_count + 1;
    for (size_t source_copy_idx = 0; source_copy_idx < num_of_rows - 1; source_copy_idx++) {
        mata::nfa::Transition transition_instance (transition_template.source + source_copy_idx*states_in_row,
                                                   transition_template.symbol,
                                                   transition_template.target + (source_copy_idx+1)*states_in_row);
        add_all_possible_sampling_transitions(transitions, var, source_copy_idx+1, predicate_count, transition_instance);
    }
}

void add_nonsampling_transitions_based_on_template(std::vector<TagSetTransition>& transitions, const mata::nfa::Transition& transition_template, BasicTerm& var, size_t predicate_count, size_t states_in_row) {
    size_t num_of_rows = 2*predicate_count + 1;
    ca::AtomicSymbol length_tag = ca::AtomicSymbol::create_l_symbol(var);
    for (size_t source_copy_idx = 0; source_copy_idx < num_of_rows; source_copy_idx++) {
        size_t copy_idx_to_display = source_copy_idx + 1;
        ca::AtomicSymbol mismatch_pos_tag_for_this_copy = ca::AtomicSymbol::create_p_symbol(var, copy_idx_to_display);

        TagSet tag_set = {length_tag, mismatch_pos_tag_for_this_copy};
        if (source_copy_idx == num_of_rows-1) {
            tag_set = {length_tag};
        }

        TagSetTransition transition_instance{ transition_template.source + source_copy_idx*states_in_row,
                                              tag_set,
                                              transition_template.target + source_copy_idx*states_in_row};
        transitions.push_back(transition_instance);
    }
}

TEST_CASE("Disequations :: automaton for more predicates is constructed correctly", "[noodler]") {
    BasicTerm var_x = get_var('x');
    BasicTerm var_y = get_var('y');
    BasicTerm var_z = get_var('z');

    Predicate diseq1(PredicateType::Equation, { {var_x}, {var_y} });
    Predicate diseq2(PredicateType::Equation, { {var_y}, {var_z} });

    AutAssignment aut_assignment;
    aut_assignment[var_x] = regex_to_nfa("a");
    aut_assignment[var_y] = regex_to_nfa("b");
    aut_assignment[var_z] = regex_to_nfa("c");

    ca::TagDiseqGen tag_automaton_generator({diseq1, diseq2}, aut_assignment);
    ca::TagAut      tag_automaton = tag_automaton_generator.construct_tag_aut();

    size_t states_in_row_before_trim = 6;
    size_t num_of_rows = 5;
    size_t predicate_count = 2;

    REQUIRE(tag_automaton.nfa.num_of_states() == states_in_row_before_trim*num_of_rows); // 30 states, trimming should not be effective due to Copy tags

    ca::AtomicSymbol len_x = ca::AtomicSymbol::create_l_symbol(var_x);
    ca::AtomicSymbol len_y = ca::AtomicSymbol::create_l_symbol(var_y);
    ca::AtomicSymbol len_z = ca::AtomicSymbol::create_l_symbol(var_z);
    ca::AtomicSymbol mismatch_pos_x_1 = ca::AtomicSymbol::create_p_symbol(var_x, 1);
    ca::AtomicSymbol mismatch_pos_y_1 = ca::AtomicSymbol::create_p_symbol(var_y, 1);
    ca::AtomicSymbol mismatch_pos_z_1 = ca::AtomicSymbol::create_p_symbol(var_z, 1);

    ca::AtomicSymbol mismatch_pos_y_2 = ca::AtomicSymbol::create_p_symbol(var_y, 2);
    ca::AtomicSymbol mismatch_pos_z_2 = ca::AtomicSymbol::create_p_symbol(var_z, 2);

    ca::AtomicSymbol register_store_x_1 = ca::AtomicSymbol::create_r_symbol_with_predicate_info(0, var_x, AtomicSymbol::PredicateSide::LEFT, 1, 'a');

    ca::AtomicSymbol register_store_y_1 = ca::AtomicSymbol::create_r_symbol(var_y, 1, 'b');
    ca::AtomicSymbol register_store_y_2 = ca::AtomicSymbol::create_r_symbol(var_y, 2, 'b');
    ca::AtomicSymbol register_store_z_2 = ca::AtomicSymbol::create_r_symbol(var_z, 2, 'c');

    std::vector<TagSetTransition> expected_transitions = {};

    add_nonsampling_transitions_based_on_template(expected_transitions, mata::nfa::Transition(0, 'a', 1), var_x, predicate_count, states_in_row_before_trim);
    add_nonsampling_transitions_based_on_template(expected_transitions, mata::nfa::Transition(2, 'b', 3), var_y, predicate_count, states_in_row_before_trim);
    add_nonsampling_transitions_based_on_template(expected_transitions, mata::nfa::Transition(4, 'c', 5), var_z, predicate_count, states_in_row_before_trim);

    // Add copy transitions
    add_copy_transitions_for_variable_state_range(expected_transitions, var_x, /* predicate_count */ 2, /*first state*/ 0, /*last state*/ 1, states_in_row_before_trim);
    add_copy_transitions_for_variable_state_range(expected_transitions, var_y, /* predicate_count */ 2, /*first state*/ 2, /*last state*/ 3, states_in_row_before_trim);
    add_copy_transitions_for_variable_state_range(expected_transitions, var_z, /* predicate_count */ 2, /*first state*/ 4, /*last state*/ 5, states_in_row_before_trim);

    // Check for sampling transitions
    add_sampling_transitions_based_on_template(expected_transitions, mata::nfa::Transition(0, 'a', 1), var_x, predicate_count, states_in_row_before_trim);
    add_sampling_transitions_based_on_template(expected_transitions, mata::nfa::Transition(2, 'b', 3), var_y, predicate_count, states_in_row_before_trim);
    add_sampling_transitions_based_on_template(expected_transitions, mata::nfa::Transition(4, 'c', 5), var_z, predicate_count, states_in_row_before_trim);

    assert_all_transitions_present(tag_automaton, expected_transitions, states_in_row_before_trim);
}

TEST_CASE("Disequations :: check assert_every_disequation_has_symbols_sampled", "[noodler]") {
    BasicTerm var_x = get_var('x');
    BasicTerm var_y = get_var('y');
    BasicTerm var_z = get_var('z');

    Predicate diseq1(PredicateType::Equation, { {var_x}, {var_y} });
    Predicate diseq2(PredicateType::Equation, { {var_y}, {var_z} });

    AutAssignment aut_assignment;
    aut_assignment[var_x] = regex_to_nfa("a");
    aut_assignment[var_y] = regex_to_nfa("b");
    aut_assignment[var_z] = regex_to_nfa("c");

    ca::TagDiseqGen tag_automaton_generator({diseq1, diseq2}, aut_assignment);
    ca::TagAut      tag_automaton = tag_automaton_generator.construct_tag_aut();
    TagSet          available_tags = tag_automaton.gather_used_symbols();

    size_t num_of_copies = 5;
    size_t num_of_states_in_row = 6;
    ParikhImageDiseqTag formula_generator (tag_automaton, available_tags, num_of_states_in_row);
    formula_generator.compute_parikh_image();

    std::unordered_map<BasicTerm, Transition> vars_to_transitions;
    for (auto& [transition, var] : formula_generator.get_trans_vars()) {
        vars_to_transitions[var] = transition;
    }

    LenNode all_diseqs_have_samples_assertion = formula_generator.make_sure_every_disequation_has_symbols_sampled();

    REQUIRE(all_diseqs_have_samples_assertion.type == LenFormulaType::AND);
    REQUIRE(all_diseqs_have_samples_assertion.succ.size() == 4); // Two disequations, each has two sides

    std::set<std::pair<mata::nfa::State, mata::nfa::State>> expected_abstract_transitions;

    for (mata::nfa::State state = 0; state < num_of_states_in_row; state++) {
        for (size_t copy_idx = 1; copy_idx < num_of_copies-1; copy_idx++) {
            mata::nfa::State source_state = state + num_of_states_in_row*copy_idx;
            mata::nfa::State target_state = state + num_of_states_in_row*(copy_idx+1);
            expected_abstract_transitions.insert(std::make_pair(source_state, target_state));
        }
    }

    std::vector<std::pair<mata::nfa::State, mata::nfa::State>> register_store_transition_templates {
        {0, 7},
        {2, 9},
        {4, 11},
    };

    for (auto [template_source, template_target] : register_store_transition_templates) {
        for (size_t copy_idx = 0; copy_idx < num_of_copies-1; copy_idx++) {
            mata::nfa::State source_state = template_source + num_of_states_in_row*copy_idx;
            mata::nfa::State target_state = template_target + num_of_states_in_row*copy_idx;
            expected_abstract_transitions.insert(std::make_pair(source_state, target_state));
        }
    }

    for (const LenNode& conjunct: all_diseqs_have_samples_assertion.succ) {
        REQUIRE(conjunct.type == LenFormulaType::EQ);
        const LenNode& lhs = conjunct.succ[0];
        REQUIRE(lhs.succ.size() == 30); // Would be 36, but there are no sampling transitions between frist and second rows

        std::set<std::pair<mata::nfa::State, mata::nfa::State>> abstract_transitions;

        for (const LenNode& var_node : lhs.succ) {
            const BasicTerm& var = var_node.atom_val;
            Transition var_transition = vars_to_transitions[var];

            mata::nfa::State source_state = std::get<0>(var_transition);
            mata::nfa::State target_state = std::get<2>(var_transition);

            abstract_transitions.insert(std::make_pair(source_state, target_state));
        }

        REQUIRE(abstract_transitions == expected_abstract_transitions);
    }
}

struct RegisterValueImplicationVars {
    BasicTerm control_var;
    BasicTerm ordered_register;
    BasicTerm diseq_register;

    bool operator<(const RegisterValueImplicationVars& other_vars) const {
        if (control_var < other_vars.control_var) return true;
        if (control_var > other_vars.control_var) return false;

        if (ordered_register < other_vars.ordered_register) return true;
        if (ordered_register > other_vars.ordered_register) return false;

        return diseq_register < other_vars.diseq_register;
    }

    bool operator==(const RegisterValueImplicationVars& other) const = default;
};

/**
 * Assert that the implication has the form:
 *   (<Something> <= 0) OR (<equation1> AND <equation2>)
 */
void assert_register_store_implication_structure(const LenNode& implication, std::map<RegisterValueImplicationVars, int>& probes) {
    REQUIRE(implication.type == LenFormulaType::OR);
    REQUIRE(implication.succ.size() == 2);

    const LenNode& antecedent = implication.succ[0];
    REQUIRE(antecedent.type == LenFormulaType::LEQ);

    const BasicTerm& control_var = antecedent.succ[0].atom_val;

    LenNode zero (0);
    REQUIRE(antecedent.succ[1].atom_val == zero.atom_val);

    const LenNode& rhs = implication.succ[1];
    REQUIRE(rhs.type == LenFormulaType::AND);
    REQUIRE(rhs.succ.size() == 2);

    LenNode eq0 = rhs.succ[0];
    REQUIRE(eq0.type == LenFormulaType::EQ);
    REQUIRE(eq0.succ[0].type == LenFormulaType::LEAF);

    const BasicTerm& modified_reg_ord = eq0.succ[0].atom_val;

    LenNode eq1 = rhs.succ[1];
    REQUIRE(eq1.type == LenFormulaType::EQ);
    REQUIRE(eq1.succ[0].type == LenFormulaType::LEAF);

    const BasicTerm& modified_reg_diseq = eq1.succ[0].atom_val;

    RegisterValueImplicationVars seen_template = {.control_var = control_var,
                                                  .ordered_register = modified_reg_ord,
                                                  .diseq_register = modified_reg_diseq};

    if (!probes.contains(seen_template)) {
        std::cout << "Missing the following template: "
                  << "{.control_var=" << seen_template.control_var.to_string()
                  << ",.diseq_register=" << seen_template.diseq_register.to_string()
                  << ",.ord_register=" << seen_template.ordered_register.to_string()
                  << "}\n";
    }
    REQUIRE(probes.contains(seen_template));

    probes[seen_template] += 1;
}

void check_register_stores_for_level(int level, const TagAut& tag_automaton, const ParikhImageDiseqTag& formula_generator, const LenNode& implications_conjunction) {
    std::map<RegisterValueImplicationVars, int> seen_register_implications;

    const BasicTerm& reg_ord = formula_generator.registers_in_sampling_order[level].atom_val;
    for (const auto& [transition, var] : formula_generator.get_trans_vars()) {
        mata::nfa::State source_state  = std::get<0>(transition);
        mata::Symbol     symbol_handle = std::get<1>(transition);
        mata::nfa::State target_state  = std::get<2>(transition);

        if (tag_automaton.metadata.levels[source_state] != level || tag_automaton.metadata.levels[target_state] != (level+1)) {
            continue;
        }

        const TagSet& tag_set = tag_automaton.alph.get_symbol(symbol_handle);
        for (const auto& tag : tag_set) {
            if (tag.type == AtomicSymbol::TagType::REGISTER_STORE || tag.type == AtomicSymbol::TagType::COPY_PREVIOUS) {
                DiseqSide side = {.predicate_idx = tag.predicate_idx, .side = tag.predicate_side};
                const BasicTerm& diseq_register = formula_generator.registers_per_disequation_side.at(side).atom_val;

                RegisterValueImplicationVars implication_template = {.control_var = var, .ordered_register = reg_ord, .diseq_register = diseq_register};
                seen_register_implications.emplace(implication_template, 0);
            }
        }
    }

    for (const LenNode& implication : implications_conjunction.succ) {
        assert_register_store_implication_structure(implication, seen_register_implications);
    }

    for (const auto& [implication_template, seen_count] : seen_register_implications) {
        REQUIRE(seen_count == 1);
    }
}


TEST_CASE("Disequations :: check assert_register_values", "[noodler]") {
    BasicTerm var_x = get_var('x');
    BasicTerm var_y = get_var('y');
    BasicTerm var_z = get_var('z');

    Predicate diseq1(PredicateType::Equation, { {var_x}, {var_y} });
    Predicate diseq2(PredicateType::Equation, { {var_y}, {var_z} });

    AutAssignment aut_assignment;
    aut_assignment[var_x] = regex_to_nfa("a");
    aut_assignment[var_y] = regex_to_nfa("b");
    aut_assignment[var_z] = regex_to_nfa("c");

    ca::TagDiseqGen tag_automaton_generator({diseq1, diseq2}, aut_assignment);
    ca::TagAut      tag_automaton = tag_automaton_generator.construct_tag_aut();
    TagSet          available_tags = tag_automaton.gather_used_symbols();

    size_t num_of_copies = 5;
    size_t num_of_states_in_row = 6;
    ParikhImageDiseqTag formula_generator (tag_automaton, available_tags, num_of_states_in_row);
    formula_generator.predicates = {diseq1, diseq2};

    formula_generator.compute_parikh_image();

    LenNode register_values_formula = formula_generator.assert_register_values();

    REQUIRE(register_values_formula.succ[0].succ.size() == 12);
    check_register_stores_for_level(0, tag_automaton, formula_generator, register_values_formula.succ[0]);
    REQUIRE(register_values_formula.succ[1].succ.size() == 36);
    check_register_stores_for_level(1, tag_automaton, formula_generator, register_values_formula.succ[1]);
    REQUIRE(register_values_formula.succ[2].succ.size() == 36);
    check_register_stores_for_level(2, tag_automaton, formula_generator, register_values_formula.succ[2]);
    REQUIRE(register_values_formula.succ[3].succ.size() == 36);
    check_register_stores_for_level(3, tag_automaton, formula_generator, register_values_formula.succ[3]);
}

/**
 * Verifies that a given Z3 formula is satisfiable and matches the expected assignments.
 * 
 * @param m The AST manager used for managing Z3 expressions.
 * @param formula The Z3 formula to be checked.
 * @param assgn A map of variable names to their expected values in the model.
 */
void check_lia_model(ast_manager& m, expr* formula, const std::map<std::string, std::string>& assgn) {
    smt_params str_params{};
    int_expr_solver solver(m, str_params);

    // Check if the formula is satisfiable
    REQUIRE(solver.check_sat(formula) == l_true);

    model_ref mdl;
    solver.m_kernel.get_model(mdl);
    unsigned num = mdl->get_num_constants();

    // Iterate through the model's constants and verify assignments
    for (unsigned i = 0; i < num; i++) {
        func_decl * c = mdl->get_constant(i);
        expr * c_i    = mdl->get_const_interp(c);

        auto it = assgn.find(c->get_name().str());
        if(it != assgn.end()) {
            std::ostringstream buffer;
            buffer << mk_pp(c_i, m);
            // Ensure the model's value matches the expected assignment
            REQUIRE(it->second == buffer.str());
        }
    }
}

/**
 * Converts a LenNode formula into a Z3 expression.
 * 
 * @param m The AST manager used for managing Z3 expressions.
 * @param ctx The command context for parsing SMT-LIB2 formulas.
 * @param formula The LenNode formula to be converted.
 * @return A Z3 expression representing the given LenNode formula.
 */
expr_ref len_node_to_expr(ast_manager& m, cmd_context& ctx, const LenNode& formula) {
    expr_ref result(m);
    std::ostringstream buffer;

    // Serialize the LenNode formula into SMT-LIB2 format
    write_len_formula_as_smt2(formula, buffer);

    std::istringstream is(buffer.str());
    // Parse the SMT-LIB2 formula into the Z3 context
    REQUIRE(parse_smt2_commands(ctx, is));
    REQUIRE(!ctx.assertions().empty());

    // Retrieve the parsed formula as an expr_ref
    result = ctx.assertions().get(0);
    return result;
}

TEST_CASE("Transducers :: simple lengths", "[noodler]") {
   
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context ctx(false, &m);

    SECTION("Simple transducer 1") {
        mata::nft::Nft nft1{2};
        nft1.initial = {0};
        nft1.final = {1};
        nft1.insert_word_by_parts(0, { {'a'}, {'b'} } , 1);

        ParikhImageTransducer pi(nft1);
        LenNode formula = pi.compute_parikh_image();

        expr_ref result = len_node_to_expr(m, ctx, formula);
        check_lia_model(m, result, {{"tape_len!n0", "1"}, {"tape_len!n1", "1"}});
    }

    SECTION("Simple transducer 2") {
        mata::nft::Nft nft2{2};
        nft2.initial = {0};
        nft2.final = {1};
        nft2.insert_word_by_parts(0, { {'a', 'b'}, {'b', 'b'} } , 1);

        ParikhImageTransducer pi(nft2);
        LenNode formula = pi.compute_parikh_image();

        expr_ref result = len_node_to_expr(m, ctx, formula);
        check_lia_model(m, result, {{"tape_len!n2", "2"}, {"tape_len!n3", "2"}});
    }

    SECTION("Simple transducer 3") {
        mata::nft::Nft nft3{2};
        nft3.initial = {0};
        nft3.final = {1};
        nft3.insert_word_by_parts(0, { {'a', 'b'}, {'b'} } , 1);

        ParikhImageTransducer pi(nft3);
        LenNode formula = pi.compute_parikh_image();

        expr_ref result = len_node_to_expr(m, ctx, formula);
        check_lia_model(m, result, {{"tape_len!n4", "2"}, {"tape_len!n5", "1"}});
    }
}
