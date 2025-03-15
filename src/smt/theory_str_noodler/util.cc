#include <cassert>

#include "util/z3_exception.h"

#include "util.h"
#include "theory_str_noodler.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"

namespace {
    using mata::nfa::Nfa;
}

namespace smt::noodler::util {

    void throw_error(std::string errMsg) {
        // TODO maybe for benchnarking throw_error in release should also really throw error
#ifndef NDEBUG
        // for debugging, we use std::runtime_error, because that one is not caught by z3
        throw std::runtime_error(errMsg);
#else
        // for release, we use this, as it is caught by z3 and it transform it into 'unknown'
        throw default_exception(std::move(errMsg));
#endif
    }

    void get_str_variables(expr* const ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<expr>& res, obj_map<expr, expr*>* pred_map) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_str_variable(ex, m_util_s)) {
            res.insert(ex);
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app{ to_app(ex) };
        if(pred_map != nullptr) {
            expr* rpl;
            if(pred_map->find(ex_app, rpl)) {
                get_str_variables(rpl, m_util_s, m, res, pred_map);
            }
        }

        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_str_variables(arg, m_util_s, m, res, pred_map);
        }
    }

    void get_variable_names(expr* const ex, const seq_util& m_util_s, const ast_manager& m, std::unordered_set<std::string>& res) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_variable(ex)) {
            res.insert(std::to_string(to_app(ex)->get_name()));
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app{ to_app(ex) };

        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_variable_names(arg, m_util_s, m, res);
        }
    }

    bool is_variable(const expr* expression) {
        if (!is_app(expression)) {
            return false;
        }
        const app *n = to_app(expression);
        return n->get_num_args() == 0 && n->get_family_id() == null_family_id && n->get_decl_kind() == null_decl_kind;
    }

    bool is_str_variable(const expr* expression, const seq_util& m_util_s) {
        return m_util_s.is_string(expression->get_sort()) && is_variable(expression);
    }

    void collect_terms(app* const ex, ast_manager& m, const seq_util& m_util_s, obj_map<expr, expr*>& pred_replace,
                       std::map<BasicTerm, expr_ref>& var_name, std::vector<BasicTerm>& terms) {

        if(m_util_s.str.is_string(ex)) { // Handle string literals.
            terms.emplace_back(BasicTermType::Literal, ex->get_parameter(0).get_zstring());
            return;
        }

        if(is_variable(ex)) {
            std::string var = ex->get_decl()->get_name().str();
            BasicTerm bvar(BasicTermType::Variable, var);
            terms.emplace_back(bvar);
            var_name.insert({bvar, expr_ref(ex, m)});
            return;
        }

        if(!m_util_s.str.is_concat(ex)) {
            expr* rpl = pred_replace.find(ex); // dies if it is not found
            collect_terms(to_app(rpl), m, m_util_s, pred_replace, var_name, terms);
            return;
        }

        SASSERT(ex->get_num_args() == 2);
        app *a_x = to_app(ex->get_arg(0));
        app *a_y = to_app(ex->get_arg(1));
        collect_terms(a_x, m, m_util_s, pred_replace, var_name, terms);
        collect_terms(a_y, m, m_util_s, pred_replace, var_name, terms);
    }

    BasicTerm get_variable_basic_term(expr *const variable) {
        SASSERT(is_app(variable));
        const app* variable_app{ to_app(variable) };
        SASSERT(variable_app->get_num_args() == 0);
        return BasicTerm{ BasicTermType::Variable, variable_app->get_decl()->get_name().str() };
    }

    void get_len_exprs(expr* const ex, const seq_util& m_util_s, ast_manager& m, obj_hashtable<app>& res) {

        if(is_quantifier(ex)) {
            quantifier* qf = to_quantifier(ex);
            get_len_exprs(qf->get_expr(), m_util_s, m, res);
            return;
        }
        // quantified variable
        if(is_var(ex)) {
            return;
        }

        if(m_util_s.str.is_length(ex)) {
            res.insert(to_app(ex));
            return;
        }

        SASSERT(is_app(ex));
        app *ex_app = to_app(ex);
        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            get_len_exprs(ex_app->get_arg(i), m_util_s, m, res);
        }
    }

    bool is_len_sub(expr* val, expr* s, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& num_res) {
        expr* num = nullptr;
        expr* len = nullptr;
        expr* str = nullptr;
        if(!m_util_a.is_add(val, num, len)) {
            return false;
        }

        if(!m_util_a.is_int(num)) {
            return false;
        }
        num_res = num;

        if(!m_util_s.str.is_length(len, str) || str->hash() != s->hash()) {
            return false;
        }

        return true;
    }

    bool split_word_to_automata(const zstring& word, const std::vector<std::shared_ptr<mata::nfa::Nfa>>& automata, std::vector<zstring>& words) {
        STRACE("str-split-word-to-automata",
            tout << "split_word_to_automata with word:\n" << word << "\n";
            tout << "and " << automata.size() << " automata\n";
            if (is_trace_enabled("str-nfa")) {
                for (auto aut : automata) {
                    tout << *aut << "\n";
                }
            }
        );

        const unsigned NUM_OF_AUTOMATA = automata.size();
        const unsigned LENGTH_OF_WORD = word.length();

        unsigned current_automaton = 0; // index in automata, of an automaton whose word we are now computing
        unsigned index_in_word = 0; // where in the word we are
        std::vector<unsigned> backtracking_indexes; // vector that remembers to which index in word to backtrack to
        mata::nfa::StateSet current_states{automata[0]->initial}; // the set of states where we are now in the current automaton
        std::vector<mata::nfa::StateSet> backtracking_state_sets; // vector that remembers to which set of states to backtrack to
        zstring current_word; // word we are currently building for current automaton
        bool is_backtracked = false; // whether we just backtracked

        auto backtrack = [&]() {
            --current_automaton;
            index_in_word = backtracking_indexes.back();
            backtracking_indexes.pop_back();
            current_states = std::move(backtracking_state_sets.back());
            backtracking_state_sets.pop_back();
            current_word = std::move(words.back());
            words.pop_back();
            is_backtracked = true;
        };

        while (current_automaton != NUM_OF_AUTOMATA || index_in_word != LENGTH_OF_WORD) {
            STRACE("str-split-word-to-automata", tout << "Current automaton and index in word: " << current_automaton << " " << index_in_word << "\n";);

            // if we did not backtrack, we need to first check whether we can currently accept (if we are backtracking, we need to instead get longer word for the current automaton)
            // also if the current automaton is the last automaton, we need to finish reading the word, so in that case, we only check after we read the whole word
            if (!is_backtracked && (current_automaton != NUM_OF_AUTOMATA-1 || index_in_word == LENGTH_OF_WORD) && automata[current_automaton]->final.intersects_with(current_states)) {
                // if we can accept, we save the current index, states, and word and move to the next automaton
                STRACE("str-split-word-to-automata", tout << "Moving to next automaton\n";);
                backtracking_indexes.push_back(index_in_word);
                backtracking_state_sets.push_back(current_states);
                words.push_back(current_word);
                STRACE("str-split-word-to-automata",
                    tout << "Current words:";
                    for (const auto& word : words) {
                        tout << " " << word;
                    }
                    tout << "\n";
                );

                ++current_automaton;
                if (current_automaton != NUM_OF_AUTOMATA) {
                    // index_in_word is not updated, as we stay at the same position
                    current_states = mata::nfa::StateSet(automata[current_automaton]->initial); // we can imagine this as each final state in previous automaton is connected by epsilon move to initial state of following one
                    current_word = zstring();
                }
                continue;
            }

            if (index_in_word == LENGTH_OF_WORD) {
                // we read the whole word, but we have still some automata left, we need to backtrack
                if (current_automaton == 0) { return false; } // we cannot backtrack, i.e., the word is not accepted by the concatenation of automata
                STRACE("str-split-word-to-automata", tout << "Backtracking at the end of the word\n";);
                backtrack();
                continue;
            }

            // we move by one in word and compute the new set of states
            mata::Symbol current_symbol = word[index_in_word];
            mata::nfa::StateSet new_current_states; // we save here post over current symbol from the set of current states
            for (mata::nfa::State s : current_states) {
                const mata::nfa::StatePost& transitions_from_s = automata[current_automaton]->delta[s];
                auto transitions_from_current_symbol_it = transitions_from_s.find(current_symbol);
                if (transitions_from_current_symbol_it != transitions_from_s.end()) {
                    SASSERT(transitions_from_current_symbol_it->symbol == current_symbol);
                    new_current_states = mata::nfa::StateSet::set_union(new_current_states, transitions_from_current_symbol_it->targets);
                }
            }

            if (new_current_states.empty()) {
                // we need to backtrack, the word is not accepted by the current automaton
                if (current_automaton == 0) { return false; } // we cannot backtrack, i.e., the word is not accepted by the concatenation of automata
                STRACE("str-split-word-to-automata", tout << "Backtracking because the current automaton does not accept\n";);
                backtrack();
            } else {
                // otherwise we just move to the next symbol
                STRACE("str-split-word-to-automata", tout << "Moving to the next symbol\n";);
                ++index_in_word;
                current_states = new_current_states;
                current_word = current_word + zstring(current_symbol);
                is_backtracked = false;
            }
        }

        STRACE("str-split-word-to-automata",
            tout << "str-split-word-to-automata ended with the following words:";
            for (const auto& word : words) {
                tout << " " << word;
            }
            tout << "\n";
        );

        return true;
    }

    mata::Word get_mata_word_zstring(const zstring& word) {
        mata::Word ret{};
        for(size_t i = 0; i < word.length(); i++) {
            ret.push_back(word[i]);
        }
        return ret;
    }

    zstring get_zstring_from_mata_word(const mata::Word& word) {
        return zstring(word.size(), word.data());
    }

    bool aut_contains_one_word(const mata::nfa::Nfa& aut, mata::Word& word) {
        // because aut is trimmed and reduced, the only way for it to accept exactly one word is if the automaton contains
        // only one path in it (on which the word is)
        if (aut.initial.size() != 1 || aut.final.size() != 1 || aut.num_of_states() != aut.delta.num_of_transitions() + 1) {
            return false;
        }
        word = {};
        mata::nfa::State next_state = *aut.initial.begin();
        while (!aut.final.contains(next_state)) {
            const mata::nfa::StatePost& state_post = aut.delta[next_state];
            if (state_post.size() != 1) { return false; }
            const mata::nfa::SymbolPost& symbol_post = *state_post.begin();
            if (symbol_post.num_of_targets() != 1) { return false; }
            word.push_back(symbol_post.symbol);
            next_state = *symbol_post.targets.begin();
        }
        return true;
    }

    std::vector<Predicate> create_inclusions_from_multiple_sides(const std::vector<std::vector<BasicTerm>>& left_sides, const std::vector<std::vector<BasicTerm>>& right_sides) {
        SASSERT(left_sides.size() == right_sides.size());
        std::vector<Predicate> inclusions;
        for (std::vector<std::vector<BasicTerm>>::size_type index = 0; index < left_sides.size(); ++index) {
            inclusions.emplace_back(PredicateType::Equation, std::vector<std::vector<BasicTerm>>{ left_sides[index], right_sides[index] });
        }
        return inclusions;
    }
}

template <typename T>
size_t rec_bin_search_leftmost(const std::vector<T>& haystack, T needle, size_t start_idx, size_t end_idx) {

    if (start_idx == end_idx) {
        if (haystack.at(start_idx) >= needle) return start_idx;
        return -1;
    }

    size_t midpoint = start_idx + (end_idx - start_idx) / 2;
    if (needle < midpoint) {
        return rec_bin_search_leftmost(haystack, needle, start_idx, midpoint);
    }

    size_t match = rec_bin_search_leftmost(haystack, needle, midpoint+1, end_idx);
    if (match == -1) {
        // We have not found the the in [midpoint+1 ... end_idx], therefore, the leftmost smaller is midpoint
        return midpoint;
    }
    return match;
}

template <typename T>
size_t bin_search_leftmost(const std::vector<T>& haystack, T needle) {
    return rec_bin_search_leftmost(haystack, needle, 0, haystack.size());
}
