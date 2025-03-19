#include "aut_assignment.h"
#include "util.h"
#include "regex.h"

namespace smt::noodler {
    LenNode AutAssignment::get_lengths(const BasicTerm& var) const {
        return AutAssignment::get_lengths(*at(var), var);
    }

    LenNode AutAssignment::get_lengths(const mata::nfa::Nfa& aut, const BasicTerm& var) {
        // each (c1, c2) from following set represents the lengths of automaton for var
        // where we take c1 + k*c2 for each k >= 0
        std::set<std::pair<int, int>> aut_constr = mata::strings::get_word_lengths(aut);

        LenNode res(LenFormulaType::FALSE, {});
        for(const auto& cns : aut_constr) { // for each (c1, c2) representing lengths of var
            LenNode c1(cns.first);
            LenNode c2(cns.second);
            LenNode k(util::mk_noodler_var_fresh("k"));

            if(cns.second != 0) {
                // c1 + k*c2
                LenNode right(LenFormulaType::PLUS, {c1, LenNode(LenFormulaType::TIMES, {k, c2})});
                // add (var = c1 + k*c2 && 0 <= k) to result
                res = LenNode(LenFormulaType::OR, 
                                {res,
                                 LenNode(LenFormulaType::AND,
                                            {LenNode(LenFormulaType::EQ, {var, right}),
                                             LenNode(LenFormulaType::LEQ, {LenNode(0), k})
                                            })
                                });
            } else {
                // add (var = c1) to result
                res = LenNode(LenFormulaType::OR, {res, LenNode(LenFormulaType::EQ, {var, c1})});
            }
        }

        // to be safe, var must be >= 0
        res = LenNode(LenFormulaType::AND, {res, LenNode(LenFormulaType::LEQ, {0, var})});
        return res;
    }

    mata::nfa::Nfa AutAssignment::create_word_nfa(const zstring& word) {
        const size_t word_length{ word.length() };
        mata::nfa::Nfa nfa{ word_length, { 0 }, { word_length } };
        nfa.initial.insert(0);
        size_t state{ 0 };
        for (; state < word.length(); ++state) {
            nfa.delta.add(state, word[state], state + 1);
        }
        nfa.final.insert(state);
        return nfa;
    }

    std::vector<interval_word> AutAssignment::get_interval_words(const mata::nfa::Nfa& aut) {
        assert(aut.initial.size() == 1); // is deterministic and accepts a non-empty language
        assert(aut.is_acyclic()); // accepts a finite language


        STRACE("str-interval-words", tout << "NFA for which we compute interval words:" << std::endl << aut << std::endl;);

        // Because aut is minimized (i.e., deterministic) and finite, the automaton aut has a specific structure
        //      - there is exactly one initial and final state
        //      - there are no loops
        // Therefore, each state can be reached exactly after some specific number of steps (and we can never reach it after), so for each step n, starting with 0,
        // we compute the reachable interval words for each state that can be reached in n steps

        // maps all states q reachable in n steps (starting with n=0), into the vector of interval words with which we can reach the given state from the inital state
        std::map<mata::nfa::State, std::vector<interval_word>> cur_level = { {*(aut.initial.begin()), {{}}} };

        while (true) {
            // we will compute the mapping for states reachable in n+1 steps
            std::map<mata::nfa::State,std::vector<interval_word>> next_level;

            for (auto const& [st, interval_words] : cur_level) {
                // st - state reachable in n steps
                // interval_words - interval words with whose we can reach st from the initial state

                auto trans_from_st_it = aut.delta[st].begin();

                if (trans_from_st_it == aut.delta[st].end()) {
                    // if there are no transitions, st must be final state (and there is no other state that can be reached in n number of steps)
                    assert(aut.final.contains(st));
                    assert(cur_level.size() == 1);
                    // interval_words should therefore be the accepted interval words by aut
                    STRACE("str-interval-words",
                        tout << "interval words:" << std::endl;
                        for (const auto& interval_word : interval_words) {
                            tout << "   ";
                            for (const auto& interv : interval_word) {
                                tout << "[" << interv.first << "-" << interv.second << "]";
                            }
                            tout << std::endl;
                        }
                    );
                    return interval_words;
                }

                // From mata representation, symbols are ordered in aut.delta[st], so we can easily compute the intervals by checking
                // for "change" of target of the next transition (aut is deterministic, so we always have just one target).
                // For example, if we have transitions
                //      st -5-> t1
                //      st -6-> t1
                //      st -8-> t1
                //      st -9-> t2
                //      st -10-> t2
                //      st -11-> t2
                //      st -12-> t3
                // we get intervals
                //      st -[5-6]-> t1
                //      st -[8-8]-> t1
                //      st -[9-11]-> t2
                //      st -[12-12]-> t3

                assert(trans_from_st_it->targets.size() == 1); // should be deterministic

                // target of previous transition
                mata::nfa::State last_target = *trans_from_st_it->targets.begin();
                // symbol of previous transition
                mata::Symbol last_symbol = trans_from_st_it->symbol;
                // starting symbol of the interval we are currently computing
                mata::Symbol last_starting_symbol = trans_from_st_it->symbol;

                ++trans_from_st_it;

                while (trans_from_st_it != aut.delta[st].end()) {
                    assert(trans_from_st_it->targets.size() == 1); // should be deterministic

                    mata::nfa::State cur_target = *trans_from_st_it->targets.begin();
                    mata::nfa::State cur_symbol = trans_from_st_it->symbol;
                    
                    if (cur_target != last_target || cur_symbol != last_symbol+1) {
                        // we should end the current interval, as the target changed, or there is a gap between symbols
                        std::pair<mata::Symbol,mata::Symbol> cur_interval = {last_starting_symbol, last_symbol};
                        
                        // add the interval to all interval words with whose we reached st and add these interval words to state last_target
                        for (auto vec_of_intervals : interval_words) {
                            vec_of_intervals.push_back(cur_interval);
                            next_level[last_target].push_back(vec_of_intervals);
                        }

                        // start new interval
                        last_starting_symbol = cur_symbol;
                    }
                    
                    last_target = cur_target;
                    last_symbol = cur_symbol;
                    ++trans_from_st_it;
                }

                // we need to also handle the last interval
                std::pair<mata::Symbol,mata::Symbol> cur_interval = {last_starting_symbol, last_symbol};
                for (auto vec_of_intervals : interval_words) {
                    vec_of_intervals.push_back(cur_interval);
                    next_level[last_target].push_back(vec_of_intervals);
                }
            }
            
            cur_level = next_level;
        }
    }

    bool AutAssignment::is_flat(const BasicTerm& t) const {
        bool flat = true;

        const mata::nfa::Nfa& aut = *this->at(t);

        mata::nfa::Nfa::TarjanDiscoverCallback callback {};
        callback.scc_discover = [&flat,&aut](const std::vector<mata::nfa::State>& scc, const std::vector<mata::nfa::State>& tarjan_stack) -> bool {
            (void) tarjan_stack;

            for (const mata::nfa::State& st : scc) {
                bool one_input_visited = false;

                for (const mata::nfa::SymbolPost& sp : aut.delta[st]) {
                    for (const mata::nfa::State& tgt : scc) {
                        if (sp.targets.find(tgt) != sp.targets.end()) {

                            bool is_dummy = smt::noodler::util::is_dummy_symbol(sp.symbol);
                            if (is_dummy) {  // Dummy symbol is actually an entire set of transitions, so it is the same as seeing transitions with 2 different symbols
                                flat = false;
                                return true;
                            }

                            if (one_input_visited) {
                                flat = false;
                                return true;
                            }

                            one_input_visited = true;
                        }
                    }
                }
            }
            return false;
        };

        aut.tarjan_scc_discover(callback);
        return flat;
    }

    void AutAssignment::add_symbol_from_dummy(mata::Symbol sym) {
        if(alphabet.contains(sym)) { return; }
        bool is_there_some_dummy = false;
        for (auto& [var, nfa] : *this) {
            for (mata::nfa::State state = 0; state < nfa->num_of_states(); ++state) {
                const mata::nfa::StatePost& delta_from_state = nfa->delta[state];
                if (!delta_from_state.empty() && delta_from_state.back().symbol == util::get_dummy_symbol()) { // dummy symbol should be largest (we do not have epsilons), so should be at the back
                    is_there_some_dummy = true;
                    nfa->delta.add(state, sym, nfa->delta[state].back().targets);
                }
            }
        }
        if (is_there_some_dummy) {
            alphabet.insert(sym);
        }
    }

    std::optional<mata::Symbol> AutAssignment::replace_dummy_with_new_symbol() {
        if(alphabet.size() == 0) {
            return std::nullopt;
        }
        mata::Symbol new_symbol = regex::Alphabet(alphabet).get_unused_symbol();
        bool is_there_some_dummy = false;
        for (auto& [var, nfa] : *this) {
            for (mata::nfa::State state = 0; state < nfa->num_of_states(); ++state) {
                if (!nfa->delta[state].empty()) { // if there is some transition from state
                    mata::nfa::StatePost& delta_from_state = nfa->delta.mutable_state_post(state); // then we can for sure get mutable transitions from state without side effect
                    SASSERT(delta_from_state.back().symbol != mata::nfa::EPSILON);
                    if (delta_from_state.back().symbol == util::get_dummy_symbol()) { // dummy symbol should be largest (we do not have epsilons), so should be at the back
                        is_there_some_dummy = true;
                        mata::nfa::StateSet targets = delta_from_state.back().targets;
                        delta_from_state.pop_back();
                        nfa->delta.add(state, new_symbol, targets);
                    }
                }
            }
        }
        if (is_there_some_dummy) {
            alphabet.insert(new_symbol);
            return new_symbol;
        } else {
            return std::nullopt;
        }
    }
}
