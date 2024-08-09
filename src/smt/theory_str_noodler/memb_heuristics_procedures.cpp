#include "memb_heuristics_procedures.h"

namespace smt::noodler {
    lbool MembHeuristicProcedure::compute_next_solution() {
        regex::RegexInfo reg_info = regex::get_regex_info(to_app(regex), m_util_s);
        if (is_regex_positive) {
            // x in RE is sat if and only if RE is not empty language
            if (reg_info.empty == l_false) {
                return l_true;
            } else if (reg_info.empty == l_true) {
                return l_false;
            }
        } else {
            // x not in RE is sat if and only if RE does not accept everything
            if (reg_info.universal == l_false) {
                return l_true;
            } else if (reg_info.universal == l_true) {
                return l_false;
            } else {
                // regex heuristic is not enough, so we try to create an automaton,
                // but we won't complement it, instead we will compare it with
                // the universal automaton (as complementation can blow up)

                // create alphabet (start with minterm representing symbols not ocurring in the regex)
                std::set<mata::Symbol> symbols_in_regex{util::get_dummy_symbol()};
                regex::extract_symbols(regex, m_util_s, symbols_in_regex);
                alph = std::make_unique<regex::Alphabet>(symbols_in_regex);

                mata::nfa::Nfa nfa{ regex::conv_to_nfa(to_app(regex), m_util_s, m, *alph, false, false) };

                mata::nfa::Nfa sigma_star = mata::nfa::builder::create_sigma_star_nfa(&(alph->mata_alphabet));

                if(mata::nfa::are_equivalent(nfa, sigma_star)) {
                    // x should not belong in sigma*, so it is unsat
                    // STRACE("str", tout << "Membership " << mk_pp(std::get<0>(reg_data), m) << " not in " << mk_pp(std::get<1>(reg_data), m) << " is unsat" << std::endl;);
                    return l_false;
                } else {
                    // otherwise x should not belong in some nfa that is not sigma*, so it is sat
                    reg_nfa = std::make_unique<mata::nfa::Nfa>(nfa);
                    return l_true;
                }
            }
        }
        return l_undef;
    }

    zstring MembHeuristicProcedure::get_model(BasicTerm var, const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
        SASSERT(var == this->var);

        if (!reg_nfa) {
            // TODO: compute model directly from regex instead of creating nfa
            
            // create alphabet (start with minterm representing symbols not ocurring in the regex)
            std::set<mata::Symbol> symbols_in_regex{util::get_dummy_symbol()};
            regex::extract_symbols(regex, m_util_s, symbols_in_regex);
            alph = std::make_unique<regex::Alphabet>(symbols_in_regex);
            reg_nfa = std::make_unique<mata::nfa::Nfa>(regex::conv_to_nfa(to_app(regex), m_util_s, m, *alph, false, false));
        }
        
        mata::Word word;
        if (is_regex_positive) {
            word = reg_nfa->get_word().value();
        } else {
            word = reg_nfa->get_word_from_complement(&alph->mata_alphabet).value();
        }
    }

    lbool MultMembHeuristicProcedure::compute_next_solution() {
        for (auto& [var, list_of_regexes] : var_to_list_of_regexes_and_complement_flag) {
            // sort the regexes using get_loop_sum, where those regexes that needs to be complemented should all be at the end
            std::sort(list_of_regexes.begin(), list_of_regexes.end(), [this](const std::pair<bool,app*>& l, const std::pair<bool,app*>& r) {
                return ((!l.first && r.first) | (regex::get_loop_sum(l.second, m_util_s) < regex::get_loop_sum(r.second, m_util_s)));
            });

            std::vector<app*> list_of_normal_regs;
            std::vector<app*> list_of_compl_regs;
            for (auto& [is_complement, reg] : list_of_regexes) {
                if (is_complement) {
                    list_of_compl_regs.push_back(reg);
                } else {
                    list_of_normal_regs.push_back(reg);
                }
            }

            // Compute intersection L of all regexes that should not be complemented
            mata::nfa::Nfa intersection(1, {0}, {0});
            // initalize to universal automaton
            for (const mata::Symbol& symb : alph.alphabet) {
                intersection.delta.add(0, symb, 0);
            }

            bool first = true;
            for (auto& reg : list_of_normal_regs) {
                intersection = mata::nfa::intersection(regex::conv_to_nfa(reg, m_util_s, m, alph, false, false), intersection);
                if (!first // for first iteration we won't do reduction, as it would just be done twice, once in conv_to_nfa and once here
                    && intersection.num_of_states() < regex::RED_BOUND)
                {
                    intersection = mata::nfa::reduce(intersection);
                }
                first = false;
                if (intersection.is_lang_empty()) {
                    STRACE("str-mult-memb-heur", tout << "intersection is empty => UNSAT" << std::endl;);
                    return l_false;
                }
            }

            // Compute union L' of all regexes that should be complemented (we are using de Morgan)
            mata::nfa::Nfa unionn; // initialize to empty automaton
            first = true;
            for (auto& reg : list_of_compl_regs) {
                unionn = mata::nfa::union_nondet(regex::conv_to_nfa(reg, m_util_s, m, alph, false, false), unionn);
                if (!first // for first iteration we won't do reduction, as it would just be done twice, once in conv_to_nfa and once here
                    && unionn.num_of_states() < regex::RED_BOUND)
                {
                    unionn = mata::nfa::reduce(unionn);
                }
                first = false;
            }
            
            STRACE("str-mult-memb-heur", tout << "computing inclusion" << std::endl;);

            // We want to know if L \intersect \neg L' is empty, which is same as asking if L is subset of L'
            if (mata::nfa::is_included(intersection, unionn)) {
                // if inclusion holds, the intersection is empty => UNSAT
                STRACE("str-mult-memb-heur", tout << "inclusion holds => UNSAT" << std::endl;);
                return l_false;
            }

            
            if (!list_of_normal_regs.empty()) {
                intersections[var] = intersection;
            }

            if (!list_of_compl_regs.empty()) {
                unions[var] = unionn;
            }
        }

        STRACE("str-mult-memb-heur", tout << "inclusion holds for all vars => SAT" << std::endl;);
        return l_true;
    }
    
    zstring MultMembHeuristicProcedure::get_model(BasicTerm var, const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
        STRACE("str-mult-memb-heur", tout << "getting model for " << var << std::endl;);
        SASSERT(unions.contains(var) || intersections.contains(var));
        mata::Word word;
        if (unions.contains(var)) {
            if (intersections.contains(var)) {
                word = mata::nfa::get_word_from_lang_difference(intersections.at(var), unions.at(var)).value();
            } else {
                word = unions.at(var).get_word_from_complement(&alph.mata_alphabet).value();
            }
        } else {
            word = intersections.at(var).get_word().value();
        }
        return alph.get_string_from_mata_word(word);
    }
}
