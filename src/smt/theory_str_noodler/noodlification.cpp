#include <mata/nfa/algorithms.hh>
#include <mata/nft/algorithms.hh>
#include <mata/nft/builder.hh>

#include "noodlification.h"

namespace {
    /**
     * @brief Unify (as best as possible) the initial states and the final states of NFAs in @p nfas
     *
     * The unification happens only if the given automaton is not already unified, i.e. it is in @p unified_nfas.
     * We also add the newly unified automata to @p unified_nfas.
     *
     * @param[in] nfas The automata to unify
     * @param[in,out] unified_nfas The set of already unified automata
     */
    void unify_initial_and_final_states(const std::vector<std::shared_ptr<mata::nfa::Nfa>>& nfas, std::unordered_set<std::shared_ptr<mata::nfa::Nfa>>& unified_nfas) {
        for (std::shared_ptr<mata::nfa::Nfa> nfa : nfas) {
            if (!unified_nfas.contains(nfa)) {
                nfa->unify_initial();
                nfa->unify_final();
                unified_nfas.insert(nfa);
            }
        }
    }

    mata::nfa::Nfa concatenate_with(const std::vector<std::shared_ptr<mata::nfa::Nfa>>& nfas, mata::Symbol delimiter) {
        mata::nfa::Nfa concatenation{*nfas[0]};
        for (std::vector<std::shared_ptr<mata::nfa::Nfa>>::size_type i = 1; i < nfas.size(); ++i) {
            concatenation = mata::nfa::algorithms::concatenate_eps(concatenation, *nfas[i], delimiter, true);
        }
        return concatenation;
    }
} // namespace

namespace smt::noodler {
    std::vector<TransducerNoodle> noodlify_for_transducer(
        NFT nft,
        const std::vector<std::shared_ptr<mata::nfa::Nfa>>& input_automata,
        const std::vector<std::shared_ptr<mata::nfa::Nfa>>& output_automata,
        bool reduce_intersection
    ) {
        if (input_automata.empty() || output_automata.empty()) { return {}; }

        // delimiters, we cannot use EPSILON, because that is normal EPSILON which can be used in nft (non-preserving lengths nfts are allowed) and EPSILON-1 is DONT_CARE
        constexpr mata::Symbol INPUT_DELIMITER = mata::nft::EPSILON-2;
        constexpr mata::Symbol OUTPUT_DELIMITER = mata::nft::EPSILON-3;

        // to have less noodles, we try to have one initial and one final state for each input/output automaton
        std::unordered_set<std::shared_ptr<mata::nfa::Nfa>> unified_nfas;
        unify_initial_and_final_states(input_automata, unified_nfas);
        unify_initial_and_final_states(output_automata, unified_nfas);

        // concatenate input and output automata to one input/output automaton connected with INPUT_DELIMITER/OUTPUT_DELIMITER
        mata::nfa::Nfa concatenated_input = concatenate_with(input_automata, INPUT_DELIMITER);
        mata::nfa::Nfa concatenated_output = concatenate_with(output_automata, OUTPUT_DELIMITER);

        // we will work with nfts, so we just transfer nfas to nfts
        mata::nft::Nft concatenated_input_nft(std::move(concatenated_input));
        mata::nft::Nft concatenated_output_nft(std::move(concatenated_output));

        auto add_self_loop_for_every_default_state = [](mata::nft::Nft& nft, mata::Symbol symbol) {
            mata::Word sym_word(nft.num_of_levels, symbol);

            size_t original_num_of_states = nft.num_of_states();
            for (mata::nft::State s{ 0 }; s < original_num_of_states; s++) {
                if (nft.levels[s] == 0) {
                    nft.insert_word(s, sym_word, s);
                }
            }
        };

        // We will now construct a concatenation of nft with the input automaton on the input track
        // and then continue by intersecting with the output automaton on the output track.
        // We want to keep the delimiter in the concatenation in such a way, that if it is there,
        // then it is on both tracks of intersection together. We therefore add self loops with
        // INPUT_DELIMITER/INPUT_DELIMITER or OUTPUT_DELIMITER/OUTPUT_DELIMITER for each state
        // of the transducer, so that intersection works correctly (i.e. the delimiters behave
        // as epsilon transitions).

        mata::nft::Nft intersection;

        if (nft.get_is_input_one_symbol()) {
            // For the case that input nft T is of the form where words of length max 1 are replaced, we can
            // do the following optimization. Let I1, ..., In be the input automata. Because T always replaces
            // at most one symbol, we can take the concatenation T(I1).T(I2)...T(In) connected with INPUT_DELIMITER
            // instead of computing the composition with concatenated_input_nft.
            mata::nft::Nft concatenation{mata::nft::compose(mata::nft::Nft(*input_automata[0]), *nft, 0, 0, false)};
            for (std::vector<std::shared_ptr<mata::nfa::Nfa>>::size_type i = 1; i < input_automata.size(); ++i) {
                mata::nft::Nft composition = mata::nft::compose(mata::nft::Nft(*input_automata[i]), *nft, 0, 0, false);
                concatenation = mata::nft::algorithms::concatenate_eps(concatenation, composition, INPUT_DELIMITER, true);
            }
            intersection = std::move(concatenation);

            if(intersection.final.empty()) {
                return {};
            }
    
            // we intersect output nfa with nft on the output track but we need to add OUTPUT_DELIMITER as an "epsilon transition"
            // of nft and we also need to INPUT_DELIMITER as "epsilon transition" of the output nfa, so that we do not lose it
            add_self_loop_for_every_default_state(concatenated_output_nft, INPUT_DELIMITER);
            add_self_loop_for_every_default_state(intersection, OUTPUT_DELIMITER);
            intersection = mata::nft::compose(concatenated_output_nft, intersection, 0, 1, false);
            intersection.trim();
    
            if(intersection.final.empty()) {
                return {};
            }
        } else if (nft.get_is_output_one_symbol()) {
            // We do the same optimization but backwards.
            mata::nft::Nft concatenation{mata::nft::compose(mata::nft::Nft(*output_automata[0]), *nft, 0, 1, false)};
            for (std::vector<std::shared_ptr<mata::nfa::Nfa>>::size_type i = 1; i < output_automata.size(); ++i) {
                mata::nft::Nft composition = mata::nft::compose(mata::nft::Nft(*output_automata[i]), *nft, 0, 1, false);
                concatenation = mata::nft::algorithms::concatenate_eps(concatenation, composition, OUTPUT_DELIMITER, true);
            }
            intersection = std::move(concatenation);

            if(intersection.final.empty()) {
                return {};
            }
    
            // we intersect input nfa with nft on the input track but we need to add INPUT_DELIMITER as an "epsilon transition"
            // of nft and we also need to OUTPUT_DELIMITER as "epsilon transition" of the input nfa, so that we do not lose it
            add_self_loop_for_every_default_state(concatenated_input_nft, OUTPUT_DELIMITER);
            add_self_loop_for_every_default_state(intersection, INPUT_DELIMITER);
            intersection = mata::nft::compose(concatenated_input_nft, intersection, 0, 0, false);
            intersection.trim();
    
            if(intersection.final.empty()) {
                return {};
            }
        } else {
            // Here we must to proper composition with concatenated_input_nft and concatenated_output_nft
            intersection = *nft;
            
            // we intersect input nfa with nft on the input track but we need to add INPUT_DELIMITER as an "epsilon transition" of nft
            add_self_loop_for_every_default_state(intersection, INPUT_DELIMITER);
            intersection = mata::nft::compose(concatenated_input_nft, intersection, 0, 0, false);
            intersection.trim();

            if(intersection.final.empty()) {
                return {};
            }
    
            // we intersect output nfa with nft on the output track but we need to add OUTPUT_DELIMITER as an "epsilon transition"
            // of nft and we also need to INPUT_DELIMITER as "epsilon transition" of the output nfa, so that we do not lose it
            add_self_loop_for_every_default_state(concatenated_output_nft, INPUT_DELIMITER);
            add_self_loop_for_every_default_state(intersection, OUTPUT_DELIMITER);
            intersection = mata::nft::compose(concatenated_output_nft, intersection, 0, 1, false);
            intersection.trim();
    
            if(intersection.final.empty()) {
                return {};
            }
        }

        // we assume that the operations did not add jump transitions
        assert(!intersection.contains_jump_transitions());

        if (reduce_intersection) {
            intersection = mata::nft::reduce(mata::nft::remove_epsilon(intersection).trim()).trim();
        }

        // Delimiters are always on both tracks together, but we want it to become
        // a jump transition, so that noodlify_mult_eps works correctly.
        // To be more precise, in the nfa represenation of the transducer, we will
        // have transitions of the form
        //     source ---DELIMITER---> middle ---DELIMITER---> target
        // where source and target are level 0 states (input track) and middle
        // will be a level 1 state (output track).
        // We assume that middle connects always only one type of delimiter,
        // the previous intersection should work that way.
        std::map<mata::nft::State,mata::nft::Transition> middle_state_to_delimiter_transition_as_target; // maps middle state to "source ---DELIMITER---> middle" transition
        std::map<mata::nft::State,mata::nft::Transition> middle_state_to_delimiter_transition_as_source; // maps middle state to "middle ---DELIMITER---> target" transition
        for (const mata::nft::Transition& trans : intersection.delta.transitions()) {
            if (trans.symbol == INPUT_DELIMITER || trans.symbol == OUTPUT_DELIMITER) {
                if (intersection.levels[trans.source] == mata::nft::DEFAULT_LEVEL) {
                    // source ---DELIMITER---> middle
                    SASSERT(!middle_state_to_delimiter_transition_as_target.contains(trans.target));
                    middle_state_to_delimiter_transition_as_target[trans.target] = trans;
                } else {
                    //middle ---DELIMITER---> target
                    SASSERT(!middle_state_to_delimiter_transition_as_source.contains(trans.source));
                    middle_state_to_delimiter_transition_as_source[trans.source] = trans;
                }
            }
        }

        // we now take the nfa representation and remove all the transitions
        //     source ---DELIMITER---> middle
        //     middle ---DELIMITER---> target
        // and replace it with one transition
        //     source ---DELIMITER---> target
        mata::nfa::Nfa intersection_nfa{intersection.to_nfa_move()};
        // add "source ---DELIMITER---> target" transitions
        for (const auto& [middle_state,first_trans] : middle_state_to_delimiter_transition_as_target) {
            mata::nft::Transition second_trans = middle_state_to_delimiter_transition_as_source.at(middle_state);
            assert(first_trans.symbol == second_trans.symbol);
            intersection_nfa.delta.add(first_trans.source, first_trans.symbol, second_trans.target);
        }
        // remove "source ---DELIMITER---> middle" transitions
        for (const auto& [middle_state,trans] : middle_state_to_delimiter_transition_as_target) {
            intersection_nfa.delta.remove(trans);
        }
        // remove "middle ---DELIMITER---> target" transitions
        for (const auto& [middle_state,trans] : middle_state_to_delimiter_transition_as_source) {
            intersection_nfa.delta.remove(trans);
        }

        // intersection_nfa should now be an NFA that has NFT segments, where segments are divided by
        // delimiters. We would have something like
        //    NFT1  ----possibly multiple transitions with the same delimiter symbols---> NFT2 --->....
        // We can therefore use noodlify_mult_eps, to get noodles, where each NFTi is connected with the
        // next one by one selected delimiter transition. Furthermore, we have only the nfa represenation
        // NFAi of NFTi, therefore, we need to add the levels. That is easy because we assume each NFTi
        // does not contain long jumps, therefore every other state of NFAi should have the same level.
        // That is, it should be either 0 or 1, starting with 0 for initials.

        std::vector<TransducerNoodle> result;
        std::map<std::shared_ptr<mata::nfa::Nfa>,TransducerNoodleElement> seg_nfa_to_transducer_el; // we create for each segment NFAi only one NFTi and keep it here
        for (const auto& noodle : mata::strings::seg_nfa::noodlify_mult_eps(intersection_nfa, {INPUT_DELIMITER, OUTPUT_DELIMITER}, false)) {
            TransducerNoodle new_noodle;
            for (const auto& element : noodle) {
                // element.first is NFAi
                std::shared_ptr<mata::nfa::Nfa> element_aut = element.first;

                // element.second then keeps the index representing which input/output automaton it is connected with

                if (seg_nfa_to_transducer_el.contains(element_aut)) {
                    // we already processed this NFAi so we can find NFTi in seg_nfa_to_transducer_el
                    TransducerNoodleElement transd_el = seg_nfa_to_transducer_el.at(element_aut);
                    // however, we need to update the indexes of input/output automaton
                    transd_el.input_index = element.second[0];
                    transd_el.output_index= element.second[1];
                    new_noodle.push_back(transd_el);
                    continue;
                }

                // We need to create NFTi, therefore we add levels to NFAi by simple DFS which adds to each state
                // the level opposite of the level of the previous state.
                std::shared_ptr<mata::nft::Nft> element_nft = std::make_shared<mata::nft::Nft>(mata::nft::builder::from_nfa_with_levels_advancing(std::move(*element_aut), 2));

                TransducerNoodleElement transd_el{NFT{element_nft, nft.get_is_input_one_symbol(), nft.get_is_output_one_symbol()},
                    // the language of the input automaton is the projection to input track
                    std::make_shared<mata::nfa::Nfa>(mata::nfa::reduce(mata::nfa::remove_epsilon(mata::nft::project_to(*element_nft, 0)))), element.second[0],
                    // the language of the output automaton is the projection to output track
                    std::make_shared<mata::nfa::Nfa>(mata::nfa::reduce(mata::nfa::remove_epsilon(mata::nft::project_to(*element_nft, 1)))), element.second[1]
                };
                seg_nfa_to_transducer_el.insert({element_aut, transd_el});
                new_noodle.push_back(transd_el);
            }
            result.push_back(new_noodle);
        }
        return result;
    }
}
