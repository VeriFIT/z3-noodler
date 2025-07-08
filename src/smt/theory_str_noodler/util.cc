#include <cassert>

#include "util/z3_exception.h"

#include "util.h"
#include "theory_str_noodler.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"

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

    std::vector<Predicate> create_inclusions_from_multiple_sides(const std::vector<std::vector<BasicTerm>>& left_sides, const std::vector<std::vector<BasicTerm>>& right_sides) {
        SASSERT(left_sides.size() == right_sides.size());
        std::vector<Predicate> inclusions;
        for (std::vector<std::vector<BasicTerm>>::size_type index = 0; index < left_sides.size(); ++index) {
            inclusions.push_back(Predicate::create_equation(left_sides[index], right_sides[index]));
        }
        return inclusions;
    }

    void replace_dummy_symbol_in_transducer_with(mata::nft::Nft& transducer, const std::set<mata::Symbol>& symbols_to_replace_with) {
        if (symbols_to_replace_with.size() > 1) {
            // different transitions with dummy symbol can be connected, i.e. they should have the same symbol, if we would replace
            // by multiple symbols, it would allow situations where the transitions have different symbols on them
            // TODO add handling for this? or model generation should be done differently
            util::throw_error("We cannot replace dummy symbol by more than one symbol in transducers yet");
        }
        for (mata::nfa::State state = 0; state < transducer.num_of_states(); ++state) {
            if (!transducer.delta[state].empty()) { // if there is some transition from state
                mata::nfa::StatePost& delta_from_state = transducer.delta.mutable_state_post(state); // then we can for sure get mutable transitions from state without side effect
                for (auto iter = delta_from_state.begin(); iter != delta_from_state.end(); ++iter) {
                    if (iter->symbol == util::get_dummy_symbol()) {
                        mata::nfa::StateSet targets = iter->targets;
                        delta_from_state.erase(iter);
                        for (mata::Symbol replacement : symbols_to_replace_with) {
                            transducer.delta.add(state, replacement, targets); // this invalidates iter, but we are breaking from the loop anyway
                        }
                        break;
                    }
                }
            }
        }
    }

    bool is_concatenation_of_literals(const std::vector<BasicTerm>& concatenation, zstring& literal) {
        literal.reset();
        for (const BasicTerm& bt : concatenation) {
            if (bt.is_literal()) {
                literal += bt.get_name();
            } else {
                return false;
            }
        }
        return true;
    }

    lbool contains_trans_identity(const mata::nft::Nft& transducer, unsigned length) {
        // State represents a node in the BFS: automaton state + tape histories
        struct State {
            mata::nft::State state; // current automaton state
            std::vector<std::vector<mata::Symbol>> tapes; // history of symbols for each tape

            /**
             * Constructor for State.
             * @param s The current automaton state.
             * @param num_tapes The number of tapes (levels) in the transducer.
             * Initializes each tape's history as an empty vector.
             */
            State(mata::nft::State s, unsigned num_tapes) : state(s), tapes(num_tapes) {}

            /**
             * Equality operator for State.
             * @param other The state to compare with.
             * @return True if both the automaton state and all tape histories are equal.
             */
            bool operator==(const State& other) const {
                if (state != other.state) {
                    return false;
                }
                return tapes == other.tapes;
            }

            /**
             * Ordering operator for State (for use in std::set).
             * @param other The state to compare with.
             * @return True if this state is ordered before the other.
             */
            bool operator<(const State& other) const {
                if (state < other.state) {
                    return true;
                }
                if (state > other.state) {
                    return false;
                }
                return tapes < other.tapes;
            }

            /**
             * Checks if any tape differs from the first tape at any position (i.e., not a prefix of identity).
             * In other words the tapes cannot cannot be extended to something having same symbols on all tapes 
             * (e.g., [a, ab] is ok, but [ab, ac] is not).
             * TODO: so-far the function is not able to detect e.g., [ abc, abce, abcd ]
             * @return True if any tape is not a prefix of the first tape; false otherwise.
             */
            bool is_not_prefix() const {
                size_t sz = tapes[0].size();
                for(size_t i = 0; i < sz; i++) {
                    for(size_t j = 1; j < tapes.size(); j++) {
                        if(tapes[j].size() <= i) {
                            continue;
                        } 
                        if (tapes[j][i] != tapes[0][i]) {
                            return true;
                        }
                    }
                }
                return false;
            }

            /**
             * Checks if all tapes are of equal length and have identical symbols at each position (i.e., identity relation).
             * @return True if all tapes are identical; false otherwise.
             */
            bool is_identity() const {
                size_t sz = tapes[0].size();
                for(size_t i = 0; i < sz; i++) {
                    for(size_t j = 1; j < tapes.size(); j++) {
                        if(tapes[j].size() != sz) {
                            return false;
                        }
                        if (tapes[j][i] != tapes[0][i]) {
                            return false;
                        }
                    }
                }
                return true;
            }

            /**
             * Returns a new State after reading/writing a symbol on the given tape.
             * @param sym The symbol to write (if not EPSILON).
             * @param tape The tape index to write the symbol to.
             * @return A new State with the updated tape history.
             */
            State step_state(mata::Symbol sym, unsigned tape) {
                State copy(*this);
                if(sym != mata::nft::EPSILON) {
                    copy.tapes[tape].push_back(sym);
                }
                return copy;
            }

            /**
             * Returns the maximum length of any tape in this state.
             * @return The maximum tape length.
             */
            size_t max_length() {
                size_t length = 0;
                for(size_t i = 0; i < tapes.size(); i++) {
                    if(tapes[i].size() > length) {
                        length = tapes[i].size();
                    }
                }
                return length;
            }
        };

        // BFS over state space: (automaton state, tape histories)
        std::set<State> visited_states;
        std::deque<State> queue;
        for(mata::nft::State initial_state : transducer.initial) {
            queue.emplace_back(initial_state, transducer.num_of_levels);
        }
        while(!queue.empty()) {
            State current_state = queue.front();
            queue.pop_front();
            if(visited_states.contains(current_state)) {
                continue;
            }
            visited_states.insert(current_state);
            // Prune if not a prefix of identity
            if(current_state.is_not_prefix()) {
                continue;
            }
            // Accept if in final state and all tapes are identical of required length
            if(transducer.final.contains(current_state.state) && current_state.is_identity()) {
                return l_true;
            }
            // If any tape exceeds the required length, stop exploring this path
            if(current_state.max_length() > length) {
                return l_undef;
            }
            // Explore all transitions from current state
            for(const auto& post : transducer.delta[current_state.state]) {
                for(mata::nft::State dest : post.targets) {
                    State next_state = current_state.step_state(post.symbol, transducer.levels[current_state.state]);
                    next_state.state = dest;
                    queue.push_back(next_state);
                }
            }
        }
        return l_false;
    }
}
