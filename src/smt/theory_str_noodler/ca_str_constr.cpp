
#include "ca_str_constr.h"
#include "formula.h"
#include "util.h"
#include <mata/nfa/delta.hh>
#include <mata/nfa/nfa.hh>
#include <mata/nfa/strings.hh>
#include <unordered_map>
#include <mata/parser/re2parser.hh>

namespace smt::noodler::ca {

    void DiseqAutMatrix::create_aut_matrix(const std::vector<Predicate>& disequations, const AutAssignment& aut_ass) {
        // we want to include both variables and literals
        std::set<BasicTerm> var_set;
        for (const Predicate& predicate : disequations) {
            for (const BasicTerm& var : predicate.get_vars()) {
                var_set.insert(var);
            }
        }

        // create fixed linear order of variables
        for (const BasicTerm& var : var_set) {
            this->var_order.push_back(var);
        }

        const size_t copy_cnt = 2*disequations.size() + 1;

        // set offset size
        // #Note(mhecko): What is this `+ 1` here?
        this->var_aut_init_states_in_copy.resize(copy_cnt*var_set.size() + 1);

        this->aut_matrix.resize(copy_cnt);
        for (size_t copy_idx = 0; copy_idx < copy_cnt; copy_idx++) {
            this->aut_matrix[copy_idx] = std::vector<mata::nfa::Nfa>(var_set.size());
            for (size_t var_idx = 0; var_idx < this->var_order.size(); var_idx++) {
                // @Optimize: we can avoid creating extra NFA copy here - we replace it with one symbol automaton.
                this->aut_matrix[copy_idx][var_idx] = *aut_ass.at(this->var_order[var_idx]);
            }
        }

        // Recompute the number of states that a row has
        number_of_states_in_row = 0;
        for (size_t var_id = 0; var_id < this->var_order.size(); var_id++) {
            number_of_states_in_row += this->aut_matrix[0][var_id].num_of_states();
        }

        recompute_var_aut_init_state_positions();
    }

    void DiseqAutMatrix::recompute_var_aut_init_state_positions() {
        this->var_aut_init_states_in_copy[0] = 0;

        for(size_t copy = 0; copy < this->get_copy_cnt(); copy++) {
            for(size_t var = 0; var < this->var_order.size(); var++) {
                size_t index = copy*this->var_order.size() + var;
                this->var_aut_init_states_in_copy[index + 1] = this->var_aut_init_states_in_copy[index] + this->aut_matrix[copy][var].num_of_states();
            }
        }
    }

    mata::nfa::Nfa eps_concatenate_matrix_row(const AutMatrix& matrix, size_t row_idx, std::vector<size_t>& state_var_info) {
        const std::vector<mata::nfa::Nfa>& row_elements = matrix[row_idx];
        auto elements_it = row_elements.begin();

        mata::nfa::Nfa result = *elements_it;
        elements_it++;

        for (size_t state = 0; state < result.num_of_states(); state++) {
            state_var_info[state] = 0;
        }


        size_t var_idx = 1;
        for (; elements_it != row_elements.end(); elements_it++) {
            size_t old_size = result.num_of_states();
            result = mata::nfa::concatenate(result, *elements_it, true);

            for (size_t state = old_size; state < result.num_of_states(); state++) {
                state_var_info[state] = var_idx;
            }

            var_idx += 1;
        }

        return result;
    }

    AutMatrixUnionResult DiseqAutMatrix::union_matrix() const {
        const size_t copy_count = this->get_copy_cnt();

        // #Note(mhecko): Relying on unite_nondet_with is problematic - the procedure can do all kinds of
        //                optimalizations, yet we have very clear perception of how the result should look like.
        const size_t copy_to_use_as_a_template = 0;

        size_t copy_states_cnt = 0;
        for (size_t var_id = 0; var_id < this->var_order.size(); var_id++) {
            copy_states_cnt += this->aut_matrix[copy_to_use_as_a_template][var_id].num_of_states();
        }

        std::vector<size_t> state_var_info;
        state_var_info.resize(copy_states_cnt*copy_count);

        mata::nfa::Nfa result_nfa = eps_concatenate_matrix_row(this->aut_matrix, 0, state_var_info);
        mata::nfa::Nfa latest_constructed_row_nfa;

        for (size_t copy_idx = 1; copy_idx < copy_count; copy_idx++) {
            latest_constructed_row_nfa = eps_concatenate_matrix_row(this->aut_matrix, copy_idx, state_var_info);
            result_nfa = mata::nfa::union_nondet(result_nfa, latest_constructed_row_nfa);
        }

        // State origin info for the first copy/row is ready. Propagate the origin info to the remaining copies.
        for (size_t copy_idx = 1; copy_idx < copy_count; copy_idx++) {
            for (mata::nfa::State state = 0; state < copy_states_cnt; state++) {
                state_var_info[copy_idx*copy_states_cnt + state] = state_var_info[state];
            }
        }

        result_nfa.initial = this->aut_matrix[0][0].initial;  // Initial states of the very first automaton

        result_nfa.final.clear();

        if (copy_count == 3) { // We are dealing with only 1 predicate, mark final states accordingly
            // Make states of the first copy accepting if they were accepting in the eps-concatenation stored in latest_constructed_row_nfa
            for (mata::nfa::State final_state : latest_constructed_row_nfa.final) {
                result_nfa.final.insert(final_state);
            }

            // Add final states from the very last row
            size_t last_row_offset = (copy_count - 1) * copy_states_cnt;
            for (mata::nfa::State final_state : latest_constructed_row_nfa.final) {
                mata::nfa::State result_final_state = last_row_offset + final_state;
                result_nfa.final.insert(result_final_state);
            }
        } else { // Dealing with >1 predicates, make accepting states of every copy accepting if they are accepting in the eps-concatenation
            for (size_t copy_idx = 0; copy_idx < copy_count; copy_idx++) {
                for (mata::nfa::State final_state : latest_constructed_row_nfa.final) {
                    mata::nfa::State final_state_for_this_copy = (copy_idx * copy_states_cnt) + final_state;
                    result_nfa.final.insert(final_state_for_this_copy);
                }
            }
        }


        // Construct info about where was a state copied from, so we can group "isomorphic" transitions later
        std::vector<size_t> where_is_state_copied_from(result_nfa.num_of_states());
        std::vector<size_t> state_levels(result_nfa.num_of_states());
        for (size_t copy_idx = 0; copy_idx < copy_count; copy_idx++) {
            const size_t template_state_cnt = latest_constructed_row_nfa.num_of_states();
            for (mata::nfa::State template_state = 0; template_state < template_state_cnt; template_state++) {
                mata::nfa::State union_state = template_state + copy_idx*template_state_cnt;
                where_is_state_copied_from[union_state] = template_state;
                state_levels[union_state] = copy_idx;
            }
        }

        TagAutStateMetadata metadata {
            .var_info = state_var_info,
            .levels   = state_levels,
            .where_is_state_copied_from = where_is_state_copied_from,
        };

        AutMatrixUnionResult result = {
            .nfa = result_nfa,
            .metadata = metadata,
        };

        return result;
    }

    //-----------------------------------------------------------------------------------------------

    void TagDiseqGen::replace_symbols(char copy_idx, size_t var) {
        BasicTerm bt = this->aut_matrix.get_var_order()[var];

        // <L,x>
        TagSet nonsampling_transition ({ ca::AtomicSymbol::create_l_symbol(bt)});
        size_t last_copy_idx = this->get_copy_cnt() - 1;
        if (copy_idx != last_copy_idx) {
            // <P,x,copy+1>
            size_t copy_idx_labeling_tag = this->get_copy_idx_labeling_transition(copy_idx, copy_idx+1);
            nonsampling_transition.insert(ca::AtomicSymbol::create_p_symbol(bt, copy_idx_labeling_tag));
        }

        mata::Symbol new_symbol = this->alph.add_symbol(nonsampling_transition);
        mata::nfa::Nfa aut = this->aut_matrix.get_aut(copy_idx, var);
        mata::nfa::Nfa res = aut.get_one_letter_aut(new_symbol);
        this->aut_matrix.set_aut(copy_idx, var, res, false);
    }

    void TagDiseqGen::add_connection_single_predicate(char copy_start, size_t var_idx, mata::nfa::Nfa& aut_union) {
        // Mapping between original symbols and new counter symbols from this->alph ensuring that the created
        // symbols are named consistently by the same mata state.
        std::map<mata::Symbol, mata::Symbol> original_to_tag_symbols;

        BasicTerm var = this->aut_matrix.get_var_order()[var_idx];

        // We use the original automaton from this->aut_ass because the actual alphabet symbols
        // might not be present in this->aut_matrix because they were replaced earlier by tags (<L, x>, etc.).
        mata::nfa::Nfa& original_automaton = *this->aut_ass.at(var);

        const size_t copy_idx_to_label_symbols_with = copy_start + 1;  // 0 is reserved for special purposes )

        for (mata::nfa::State source_state = 0; source_state < original_automaton.num_of_states(); source_state++) {
            for (const mata::nfa::SymbolPost& symbol_post : original_automaton.delta[source_state]) {
                // compute new mata symbol storing the set of AtomicSymbols
                auto original_sym_mapping_bucket = original_to_tag_symbols.find(symbol_post.symbol);

                mata::Symbol new_symbol;
                if (original_sym_mapping_bucket != original_to_tag_symbols.end()) {
                    new_symbol = original_sym_mapping_bucket->second;
                } else {
                    TagSet new_tag_set({ca::AtomicSymbol::create_l_symbol(var),
                                        ca::AtomicSymbol::create_p_symbol(var, copy_idx_to_label_symbols_with),
                                        ca::AtomicSymbol::create_r_symbol(var, copy_idx_to_label_symbols_with, symbol_post.symbol)});
                    new_symbol = this->alph.add_symbol(new_tag_set);
                    original_to_tag_symbols[symbol_post.symbol] = new_symbol;
                }

                for (const mata::nfa::State& target : symbol_post.targets) {
                    mata::nfa::State source_in_tag_aut = this->aut_matrix.get_union_state(copy_start, var_idx, source_state);
                    mata::nfa::State target_in_tag_aut = this->aut_matrix.get_union_state(copy_start+1, var_idx, target);

                    aut_union.delta.add(source_in_tag_aut, new_symbol, target_in_tag_aut);
                }
            }
        }
    }

    void TagDiseqGen::add_connection_for_multiple_predicates(char copy_start, size_t var_idx, mata::nfa::Nfa& aut_union) {
        BasicTerm var = this->aut_matrix.get_var_order()[var_idx];

        // We use the original automaton from this->aut_ass because the actual alphabet symbols
        // might not be present in this->aut_matrix because they were replaced earlier by tags (<L, x>, etc.).
        mata::nfa::Nfa& original_automaton = *this->aut_ass.at(var);

        const size_t copy_idx_to_label_symbols_with = this->get_copy_idx_labeling_transition(copy_start, copy_start+1);

        for (mata::nfa::State source_state = 0; source_state < original_automaton.num_of_states(); source_state++) {
            for (const mata::nfa::SymbolPost& symbol_post : original_automaton.delta[source_state]) {

                AtomicSymbol var_length   = AtomicSymbol::create_l_symbol(var);
                AtomicSymbol mismatch_pos = AtomicSymbol::create_p_symbol(var, copy_idx_to_label_symbols_with);

                for (size_t predicate_idx = 0; predicate_idx < this->predicates.size(); predicate_idx++) {
                    AtomicSymbol register_store_lhs = ca::AtomicSymbol::create_r_symbol_with_predicate_info(predicate_idx,
                                                                                                            var,
                                                                                                            AtomicSymbol::PredicateSide::LEFT,
                                                                                                            copy_idx_to_label_symbols_with,
                                                                                                            symbol_post.symbol);
                    TagSet lhs_transition_tag_set ({var_length, mismatch_pos, register_store_lhs});
                    mata::Symbol lhs_reg_store_handle = this->alph.add_symbol(lhs_transition_tag_set);

                    AtomicSymbol register_store_rhs = ca::AtomicSymbol::create_r_symbol_with_predicate_info(predicate_idx,
                                                                                                            var,
                                                                                                            AtomicSymbol::PredicateSide::RIGHT,
                                                                                                            copy_idx_to_label_symbols_with,
                                                                                                            symbol_post.symbol);
                    TagSet rhs_transition_tag_set ({var_length, mismatch_pos, register_store_rhs});
                    mata::Symbol rhs_reg_store_handle = this->alph.add_symbol(rhs_transition_tag_set);

                    for (const mata::nfa::State& target : symbol_post.targets) {
                        mata::nfa::State source_in_tag_aut = this->aut_matrix.get_union_state(copy_start, var_idx, source_state);
                        mata::nfa::State target_in_tag_aut = this->aut_matrix.get_union_state(copy_start+1, var_idx, target);

                        aut_union.delta.add(source_in_tag_aut, rhs_reg_store_handle, target_in_tag_aut);
                        aut_union.delta.add(source_in_tag_aut, lhs_reg_store_handle, target_in_tag_aut);
                    }
                }
            }
        }

        if (this->predicates.size() == 1) return;  // We don't add copy transitions when we are dealing with a single predicate
        if (copy_start == 0) return;

        for (size_t predicate_idx = 0; predicate_idx < this->predicates.size(); predicate_idx++) {
            ca::AtomicSymbol copy_for_lhs = ca::AtomicSymbol::create_c_symbol(var, predicate_idx, ca::AtomicSymbol::PredicateSide::LEFT,  copy_idx_to_label_symbols_with);
            ca::AtomicSymbol copy_for_rhs = ca::AtomicSymbol::create_c_symbol(var, predicate_idx, ca::AtomicSymbol::PredicateSide::RIGHT, copy_idx_to_label_symbols_with);

            // There is no need to cache the symbols - we know that every (var, copy_idx) will have a single unique Copy symbol
            mata::Symbol sym_handle_for_lhs = this->alph.add_symbol({copy_for_lhs});
            mata::Symbol sym_handle_for_rhs = this->alph.add_symbol({copy_for_rhs});

            for (mata::nfa::State source_state_rel = 0; source_state_rel < original_automaton.num_of_states(); source_state_rel++) {
                mata::nfa::State source_state_abs = this->aut_matrix.get_union_state(copy_start,   var_idx, source_state_rel);
                mata::nfa::State dest_state_abs   = this->aut_matrix.get_union_state(copy_start+1, var_idx, source_state_rel);

                aut_union.delta.add(source_state_abs, sym_handle_for_lhs, dest_state_abs);
                aut_union.delta.add(source_state_abs, sym_handle_for_rhs, dest_state_abs);
            }
        }
    }

    ca::TagAut TagDiseqGen::construct_tag_aut() {
        const std::vector<BasicTerm>& var_order = this->aut_matrix.get_var_order();
        const size_t copy_cnt = this->get_copy_cnt();

        // update symbols for each inner automaton
        for (char copy = 0; copy < copy_cnt; copy++) {
            for (size_t var = 0; var < var_order.size(); var++) {
                // replace each automaton in the matrix with the specific AtomicSymbol
                replace_symbols(copy, var);
            }
        }

        // union all automata in the matrix
        AutMatrixUnionResult nfa_with_metadata = this->aut_matrix.union_matrix();

        // add mata epsilon symbol to alphabet. Used for DOT export.
        this->alph.insert(mata::nfa::EPSILON, {});

        // generate connecting transitions
        if (this->predicates.size() == 1) {
            for (char copy_idx = 0; static_cast<size_t>(copy_idx) < copy_cnt - 1; copy_idx++) {
                for (size_t var_idx = 0; var_idx < var_order.size(); var_idx++) {
                    this->add_connection_single_predicate(copy_idx, var_idx, nfa_with_metadata.nfa);
                }
            }
        } else {
            for (char copy_idx = 0; static_cast<size_t>(copy_idx) < copy_cnt - 1; copy_idx++) {
                for (size_t var_idx = 0; var_idx < var_order.size(); var_idx++) {
                    this->add_connection_for_multiple_predicates(copy_idx, var_idx, nfa_with_metadata.nfa);
                }
            }
        }

        // Trim the automaton
        if (this->predicates.size() == 1) {
            size_t original_nfa_size = nfa_with_metadata.nfa.num_of_states();

            std::unordered_map<mata::nfa::State, mata::nfa::State> state_renaming; // Original state -> New state

            nfa_with_metadata.nfa.trim(&state_renaming);  // Automaton is modified in-place

            size_t new_nfa_size = nfa_with_metadata.nfa.num_of_states();

            TagAutStateMetadata new_metadata;
            new_metadata.levels.resize(new_nfa_size);
            new_metadata.var_info.resize(new_nfa_size);
            new_metadata.where_is_state_copied_from.resize(new_nfa_size);

            for (mata::nfa::State original_state = 0; original_state < original_nfa_size; original_state++) {
                auto rename_entry_it = state_renaming.find(original_state);
                if (rename_entry_it == state_renaming.end()) {
                    continue; // State has been removed
                }

                mata::nfa::State new_state = rename_entry_it->second;

                new_metadata.levels[new_state]   = nfa_with_metadata.metadata.levels[original_state];
                new_metadata.var_info[new_state] = nfa_with_metadata.metadata.var_info[original_state];
                new_metadata.where_is_state_copied_from[new_state] = nfa_with_metadata.metadata.where_is_state_copied_from[original_state];
            }

            nfa_with_metadata.metadata = std::move(new_metadata);
        }

        TagAut result = {
            nfa_with_metadata.nfa,
            this->alph,
            var_order,
            nfa_with_metadata.metadata
        };

        return result;
    }

    //-----------------------------------------------------------------------------------------------


    //-----------------------------------------------------------------------------------------------

    std::vector<BasicTerm> replace_literals_in_concat(const std::vector<BasicTerm>& concat, std::map<BasicTerm, BasicTerm>& literal_table, AutAssignment& assignment) {
        std::vector<BasicTerm> new_concat;
        for (const BasicTerm& concat_term : concat) {
            if (concat_term.is_literal()) {
                // @Note: Reusing variables for literals can seem unsound as it induces some sort of synchronization, but it is actually OK.
                auto literal_handle_it = literal_table.find(concat_term);
                if (literal_handle_it == literal_table.end()) {
                    BasicTerm literal_handle = util::mk_noodler_var_fresh("literal");  // Unique suffix is added, no need to add anything to "literal"
                    literal_table.emplace(concat_term, literal_handle);
                    new_concat.push_back(literal_handle);
                    assignment[literal_handle] = std::make_shared<mata::nfa::Nfa>(AutAssignment::create_word_nfa(concat_term.get_name()));
                }
            } else {
                new_concat.push_back(concat_term);
            }
        }
        return new_concat;
    }

    Predicate replace_literals_in_predicate(const Predicate& predicate, std::map<BasicTerm, BasicTerm>& literal_table, AutAssignment& aut_assignment) {
        std::vector<BasicTerm> new_lhs = replace_literals_in_concat(predicate.get_left_side(), literal_table, aut_assignment);
        std::vector<BasicTerm> new_rhs = replace_literals_in_concat(predicate.get_right_side(), literal_table, aut_assignment);
        Predicate new_predicate(predicate.get_type(), {new_lhs, new_rhs});
        return new_predicate;
    }

    std::vector<Predicate> replace_literals_with_fresh_vars(const std::vector<Predicate>& predicates, std::map<BasicTerm, BasicTerm>& literal_table, AutAssignment& aut_assignment) {
        std::vector<Predicate> new_predicates;
        for (const Predicate& predicate : predicates) {
            Predicate new_predicate = replace_literals_in_predicate(predicate, literal_table, aut_assignment);
            new_predicates.push_back(new_predicate);
        }
        return new_predicates;
    }

    LenNode get_lia_for_disequations(const Formula& diseqs, const AutAssignment& autass) {

        if (diseqs.get_predicates().size() == 0) {
            return LenNode(LenFormulaType::TRUE);
        }

        FormulaPreprocessor prep_handler{diseqs, autass, {}, {}, {}};
        prep_handler.propagate_eps();
        prep_handler.remove_trivial();
        prep_handler.reduce_diseqalities();

        if(prep_handler.contains_unsat_literals()) {
            return LenNode(LenFormulaType::FALSE);
        }
        if (prep_handler.get_modified_formula().get_predicates().size() == 0) {
            if (prep_handler.get_aut_assignment().is_sat()) {
                return LenNode(LenFormulaType::TRUE);
            }
            return LenNode(LenFormulaType::FALSE);
        }

        if (autass.empty()) {
            STRACE("str-diseq", tout << "Aut assignment is empty, cannot build formula.\n");
            assert(!autass.empty());
        }

        std::vector<Predicate> disequations_with_literals = prep_handler.get_modified_formula().get_predicates();
        STRACE("str-diseq",
            tout << "* Conjunction of disequations: \n";
            for (const auto& diseq: disequations_with_literals) {
                tout << "   - " << diseq << "\n";
            }
        );

        std::map<BasicTerm, BasicTerm> literal_table;
        AutAssignment workspace_aut_assignment = prep_handler.get_aut_assignment(); // Make a local copy that we will modify; do not pollute autass
        std::vector<Predicate> disequations = replace_literals_with_fresh_vars(disequations_with_literals, literal_table, workspace_aut_assignment);

        STRACE("str-diseq",
            tout << "* After replacing literals with fresh variables: \n";
            for (const auto& diseq: disequations) {
                tout << "   - " << diseq << "\n";
            }
            tout << "* Literal table: \n";
            for (const auto& [literal_term, literal_handle]: literal_table) {
                tout << "   - " << literal_handle << " stands for " << literal_term << "\n";
            }
        );

        TagDiseqGen tag_automaton_generator(disequations, workspace_aut_assignment);
        ca::TagAut tag_aut = tag_automaton_generator.construct_tag_aut();

        STRACE("str-diseq",
            tout << "* Variable ordering: " << std::endl;
            tout << concat_to_string(tag_automaton_generator.get_aut_matrix().get_var_order()) << std::endl << std::endl;
        );

        const std::vector<BasicTerm>& all_vars = tag_automaton_generator.get_aut_matrix().get_var_order();
        STRACE("str-diseq",
            tout << "* NFAs for variables: " << std::endl;
            for (const BasicTerm& bt : all_vars) {
                tout << bt.to_string() << ":" << std::endl;
                workspace_aut_assignment.at(bt)->print_to_dot(tout);
            }
            tout << std::endl;
        );

        STRACE("str-diseq",
            tout << "* Tag Automaton for diseq: " << diseqs.to_string() << std::endl;
            tag_aut.print_to_dot(tout);
            tout << std::endl;
        );
        STRACE("str", tout << "TagAut LIA: finished" << std::endl; );

        // we include only those symbols occurring in the reduced tag automaton
        TagSet all_used_tags;
        for (const auto& trans : tag_aut.nfa.delta.transitions()) {
            const TagSet& tag_set = tag_aut.alph.get_symbol(trans.symbol);
            all_used_tags.insert(tag_set.begin(), tag_set.end());
        }

        parikh::ParikhImageDiseqTag diseq_lia_formula_generator(tag_aut, all_used_tags, 0);

        LenNode pi_formula (LenFormulaType::FALSE, {});
        if (disequations.size() == 1) { // Use a simpler construction without Copy tags
            STRACE("str-diseq", tout << "* Generating formulae for a single disequation\n"; );

            Predicate diseq = disequations[0];
            pi_formula = diseq_lia_formula_generator.get_diseq_formula(diseq);
        } else {
            STRACE("str-diseq", tout << "* Generating formulae for multiple disequations\n"; );
            pi_formula = diseq_lia_formula_generator.get_formula_for_multiple_diseqs(disequations);
        }

        STRACE("str-diseq", tout << "* Resulting formula: " << std::endl << pi_formula << std::endl << std::endl; );

        return pi_formula;
    }

    struct WordChoice {
        const BasicTerm& var;   // Mostly for debug
        const std::set<mata::Word>& language;
        std::set<mata::Word>::const_iterator current_word;
    };

    struct WordChoicesForFiniteLanguages {
        std::vector<WordChoice> slots;
        bool exhausted = false;
    };

    bool are_choices_exhausted(const WordChoicesForFiniteLanguages& choices) {
        return choices.exhausted;
    }

    void try_next_word_choice(WordChoicesForFiniteLanguages& choices) {
        bool previous_choices_were_reset = false;
        size_t num_of_slot_overflows = 0;
        for (auto current_slot = choices.slots.begin(); current_slot != choices.slots.end(); current_slot++) {
            WordChoice& current_choice = *current_slot;

            current_choice.current_word++;
            if (current_choice.current_word == current_choice.language.end()) {
                current_choice.current_word = current_choice.language.begin();
                previous_choices_were_reset = true;
                num_of_slot_overflows += 1;
            }

            if (!previous_choices_were_reset) {
                break;
            }
        }

        if (num_of_slot_overflows == choices.slots.size()) {
            choices.exhausted = true;
        }
    }

    void write_word_choices(const WordChoicesForFiniteLanguages& choices, std::ostream& out_stream) {
        for (auto& choice : choices.slots) {
            out_stream << choice.var << "=";
            for (const mata::Symbol& word_symbol : *choice.current_word) {
                out_stream << std::to_string(word_symbol);
            }
            out_stream << ", ";
        }
    }

    struct SharedPredicates {
        std::vector<const Predicate*> predicates;
        std::set<BasicTerm> all_lhs_variables;
    };

    mata::nfa::Nfa prune_subword_from_automaton(const mata::nfa::Nfa& automaton, const mata::Word& word) {
        assert(word.size() == 1);

        mata::Symbol symbol_to_remove = word.at(0);

        if (smt::noodler::util::is_dummy_symbol(symbol_to_remove)) {
            // This is not a symbol, but a symbolic representation of an entire set of symbols
            // Out of this set, we can pick a single symbol such that it is different from any of the symbols
            // in automaton transition. The only exception would be that all alphabet symbols are written
            // somewhere in the NFA... unlikely.
            return automaton;
        }

        mata::nfa::Nfa new_automaton;
        new_automaton.delta.allocate(automaton.num_of_states());

        // We are dealing with a concrete symbol, e.g., 'a'
        for (mata::nfa::State source_state = 0; source_state < automaton.num_of_states(); source_state++) {
            for (const auto& symbol_post : automaton.delta[source_state]) {
                if (symbol_post.symbol == symbol_to_remove) continue;

                for (mata::nfa::State target_state : symbol_post.targets) {
                    new_automaton.delta.add(source_state, symbol_post.symbol, target_state);
                }
            }
        }

        return new_automaton;
    }

    std::optional<LenNode> try_solving_notcontains_with_finite_rhs(const std::vector<Predicate>& not_contains_predicates, const AutAssignment& aut_assignment) {
        // Check that every not-contains has a finite RHS
        // @Note we currently do not support finite languages where RHS contains more than one variable
        bool can_apply_heuristic = true;

        std::map<BasicTerm, std::set<mata::Word>> rhs_var_words;
        for (const Predicate& not_contains : not_contains_predicates) {
            if (not_contains.get_right_side().size() > 1) {
                STRACE("str-not-contains", tout << "* Cannot apply heuristics for finite side not-contains - we do not support more than 1 variable on RHS. Problematic predicate: \n  - " << not_contains << std::endl; );
                can_apply_heuristic = false;
                break;
            }

            const BasicTerm& rhs_var = not_contains.get_right_side().at(0);
            std::shared_ptr<mata::nfa::Nfa> rhs_var_automaton = aut_assignment.at(rhs_var);

            bool is_finite = rhs_var_automaton->is_acyclic();
            if (!is_finite) {
                STRACE("str-not-contains", tout << "* Cannot apply heuristics for finite side not-contains - RHS var has infinite language. Problematic predicate: \n  - " << not_contains << std::endl; );
                can_apply_heuristic = false;
                break;
            }

            std::set<mata::Word> words = rhs_var_automaton->get_words(rhs_var_automaton->num_of_states());

            bool are_all_words_have_length_one = true;  // In principle, nothing prevents us from dealing with the general case, but the implementation would have to be much more complex
            for (const mata::Word& word : words) {
                if (word.size() > 1) {
                    are_all_words_have_length_one = false;
                    break;
                }
            }

            rhs_var_words.emplace(rhs_var, std::move(words));

            if (!are_all_words_have_length_one) {
                STRACE("str-not-contains", tout << "* Cannot apply heuristics for finite side not-contains - RHS var has finite language with words longer than 1. Problematic predicate: \n  - " << not_contains << std::endl; );
                can_apply_heuristic = false;
                break;
            }
        }

        if (!can_apply_heuristic) return std::nullopt;

        std::map<BasicTerm, SharedPredicates> predicates_sharing_rhs_var;
        for (const auto& not_contains : not_contains_predicates) {
            const BasicTerm& rhs_var = not_contains.get_right_side().at(0);
            SharedPredicates& shared_predicates_info = predicates_sharing_rhs_var[rhs_var];
            shared_predicates_info.predicates.push_back(&not_contains);
            for (const BasicTerm& lhs_var : not_contains.get_left_side()) {
                shared_predicates_info.all_lhs_variables.insert(lhs_var);
            }
        }

        WordChoicesForFiniteLanguages word_choices;
        for (const auto& [var, var_words] : rhs_var_words) {
            WordChoice initial_choice = {.var = var, .language = var_words, .current_word = var_words.begin() };
            word_choices.slots.emplace_back(initial_choice);
        }

        LenNode lengths_of_all_solutions (LenFormulaType::OR, {});

        for (; !word_choices.exhausted; try_next_word_choice(word_choices)) {
            AutAssignment assignment_for_this_word_choice = aut_assignment; // Make a local copy of the assignment

            int var_idx = 0;
            for (const auto& [rhs_var, var_predicates] : predicates_sharing_rhs_var) {
                const WordChoice& word_choice_for_var = word_choices.slots[var_idx];

                for (const BasicTerm& lhs_var : var_predicates.all_lhs_variables) {
                    assignment_for_this_word_choice[lhs_var] = std::make_shared<mata::nfa::Nfa>(prune_subword_from_automaton(*assignment_for_this_word_choice[lhs_var], *word_choice_for_var.current_word));
                }

                var_idx += 1;
            }

            // We have automata ready, lets compute the lengths of solutions
            LenNode lengths_of_solutions (LenFormulaType::AND, {});
            for (const auto& [var, var_language] : assignment_for_this_word_choice) {
                parikh::ParikhImage parikh_image_generator (*var_language);
                LenNode parikh_image = parikh_image_generator.compute_parikh_image();

                LenNode word_length_expr = LenNode(LenFormulaType::PLUS, {});
                for (const auto& [transition, transition_var] : parikh_image_generator.get_trans_vars()) {
                    mata::Symbol transition_symbol = std::get<1>(transition);
                    if (transition_symbol == mata::nfa::EPSILON) continue;

                    word_length_expr.succ.push_back(transition_var);
                }

                LenNode lengths_of_var_words = LenNode(LenFormulaType::EQ, {var, word_length_expr});

                lengths_of_solutions.succ.push_back(parikh_image);
                lengths_of_solutions.succ.push_back(lengths_of_var_words);
            }

            lengths_of_all_solutions.succ.push_back(lengths_of_solutions);
        }

        return std::make_optional(lengths_of_all_solutions);
    }

    LenNode convert_loop_representation_of_var_word_lengths_into_formula(const std::set<std::pair<int, int>>& loop_repr, const BasicTerm& var) {
        LenNode disjunction_across_all_loops (LenFormulaType::OR, {});
        BasicTerm loop_rep_var = noodler::util::mk_noodler_var_fresh(var.get_name().encode() + "_loop_rep");

        for (const auto& [stem_size, loop_size] : loop_repr) {
            LenNode repeated_loop_length (LenFormulaType::TIMES, {loop_size, loop_rep_var});
            LenNode word_length (LenFormulaType::PLUS, {repeated_loop_length, stem_size});
            LenNode length (LenFormulaType::EQ, {word_length, var});

            if (loop_repr.size() == 1) {
                return length;
            }

            disjunction_across_all_loops.succ.push_back(length);
        }

        return disjunction_across_all_loops;
    }

    LenNode try_making_rhs_longer_than_lhs(const std::vector<Predicate>& not_contains_predicates, const AutAssignment& aut_assignment) {
        std::set<BasicTerm> used_variables;

        for (const Predicate& not_contains : not_contains_predicates) {
            // We could just get a set of all variables in the predicate, but I guess that are needless extra allocations
            used_variables.insert(not_contains.get_left_side().begin(), not_contains.get_left_side().end());
            used_variables.insert(not_contains.get_right_side().begin(), not_contains.get_right_side().end());
        }

        LenNode variable_lengths_are_correct (LenFormulaType::TRUE, {});
        if (0) { // @Temporary: This should be removed, other parts should make sure that the model is correct wrt. lengths implied by automata
            variable_lengths_are_correct.type = LenFormulaType::AND;

            for (const BasicTerm& used_var : used_variables) {
                std::shared_ptr<mata::nfa::Nfa> var_automaton = aut_assignment.at(used_var);

                std::set<std::pair<int, int>> lengths_of_words_in_var_lang = mata::strings::get_word_lengths(*var_automaton);
                LenNode formula_describing_word_lengths = convert_loop_representation_of_var_word_lengths_into_formula(lengths_of_words_in_var_lang, used_var);
                variable_lengths_are_correct.succ.push_back(formula_describing_word_lengths);
            }
        }

        LenNode all_predicates_have_rhs_longer_than_lhs (LenFormulaType::AND, {});
        for (const Predicate& not_contains : not_contains_predicates) {
            LenNode rhs_minus_lhs_lengths (LenFormulaType::PLUS, {});

            for (const BasicTerm& rhs_var : not_contains.get_right_side()) {
                rhs_minus_lhs_lengths.succ.push_back(rhs_var);
            }

            for (const BasicTerm& lhs_var : not_contains.get_left_side()) {
                LenNode minus_lhs_var (LenFormulaType::MINUS, {lhs_var});
                rhs_minus_lhs_lengths.succ.push_back(minus_lhs_var);
            }

            // not-contains is satisfied if |lhs| < |rhs|  <=> 0 < |rhs| - |lhs|
            LenNode rhs_is_longer_than_lhs (LenFormulaType::LT, {0, rhs_minus_lhs_lengths});
            all_predicates_have_rhs_longer_than_lhs.succ.push_back(rhs_is_longer_than_lhs);
        }

        LenNode result (LenFormulaType::AND, {variable_lengths_are_correct, all_predicates_have_rhs_longer_than_lhs});
        return result;
    }

    std::pair<LenNode, LenNodePrecision> get_lia_for_not_contains(const Formula& formula, const AutAssignment& var_assignment, bool use_tag_proc) {
        if (formula.get_predicates().empty()) {
            return { LenNode(LenFormulaType::TRUE), LenNodePrecision::PRECISE };
        }

        FormulaPreprocessor prep_handler{formula, var_assignment, {}, {}, {}};
        prep_handler.propagate_eps();

        bool is_not_contains_obviously_false = !prep_handler.replace_not_contains();
        bool is_not_contains_syntactically_false = prep_handler.can_unify_not_contains();

        if (is_not_contains_obviously_false || is_not_contains_syntactically_false) {
            return { LenNode(LenFormulaType::FALSE), LenNodePrecision::PRECISE };
        }

        AutAssignment actual_var_assignment = prep_handler.get_aut_assignment();
        const Predicate& not_contains_with_literals = formula.get_predicates().at(0);

        bool can_construct_lia = true;

        { // Priority - apply fast heuristics before attempting to use the great LIA hammer
            std::optional<LenNode> heuristic_solution = try_solving_notcontains_with_finite_rhs({not_contains_with_literals}, actual_var_assignment);
            if (heuristic_solution.has_value()) {
                return { heuristic_solution.value(), LenNodePrecision::PRECISE };
            }
        }

        if(!use_tag_proc) {
            return { LenNode(LenFormulaType::FALSE), LenNodePrecision::UNDERAPPROX };
        }

        if (formula.get_predicates().size() > 1) {
            // We have more than 1 notContains, for now we pretent we don't know what to do with it
            can_construct_lia = false;
        }

        std::map<BasicTerm, BasicTerm> literal_table;
        AutAssignment workspace_aut_assignment = actual_var_assignment;
        Predicate not_contains = replace_literals_in_predicate(not_contains_with_literals, literal_table, workspace_aut_assignment);

        STRACE("str-not-contains", {
            tout << "* Replaced literals with variables: " << not_contains << "\n";
            tout << "* Literal table:\n";
            for (const auto& [literal, literal_handle] : literal_table) {
                tout << "  - " << literal_handle << " stands for: " << literal << "\n";
            }
        });


        // #Optimize(mhecko): Add a Iterator<const BasicTerm> to Predicate - it is pointless to create a set
        const std::set<BasicTerm> vars = not_contains.get_set();
        if (can_construct_lia) {
            for (const BasicTerm& var : vars) {
                if (!workspace_aut_assignment.is_flat(var)) {
                    STRACE("str-not-contains", tout << "* cannot reduce to LIA - one of the input vars does not have a flat langauge\n"; );
                    can_construct_lia = false;
                    break;
                };
            }
        }

        if (!can_construct_lia) {
            // We cannot use the big LIA hammer, maybe we can apply some of the smaller hammers
            LenNode rhs_is_longer_than_lhs = try_making_rhs_longer_than_lhs({not_contains}, workspace_aut_assignment);
            return { rhs_is_longer_than_lhs, LenNodePrecision::UNDERAPPROX }; // Return here, there is nothing better we can do as we cannot construct a precise LIA
        }

        // Preprocess the assignment: reduce the automata and make them deterministic
        for (auto it = workspace_aut_assignment.begin(); it != workspace_aut_assignment.end(); it++) {
            mata::nfa::Nfa reduced_nfa = AutAssignment::reduce_nfa(*it->second);
            mata::nfa::Nfa reduced_dfa = mata::nfa::determinize(reduced_nfa);
            it->second = std::make_shared<mata::nfa::Nfa>(reduced_dfa);
            STRACE("str-not-contains", {
                tout << "* (var assignment) NFA assigned to " << it->first << ":\n";
                it->second->print_to_dot(tout);
            });
        }

        ca::TagDiseqGen tag_automaton_generator(not_contains, workspace_aut_assignment);

        ca::TagAut tag_automaton = tag_automaton_generator.construct_tag_aut();
        std::set<AtomicSymbol> atomic_symbols = tag_automaton.gather_used_symbols();

        STRACE("str-not-contains",
            tout << "* tag automaton: \n";
            tag_automaton.print_to_dot(tout);
            tout << std::endl;
        );

        size_t num_of_states_in_row = tag_automaton_generator.get_aut_matrix().get_number_of_states_in_row();
        parikh::ParikhImageNotContTag not_contains_generator(tag_automaton,
                                                             atomic_symbols,
                                                             num_of_states_in_row);

        LenNode not_contains_formula = not_contains_generator.get_not_cont_formula(not_contains);

        STRACE("str-not-contains",
            tout << "* generated formula: \n";
            tout << not_contains_formula << std::endl;
        );

        return { not_contains_formula, LenNodePrecision::PRECISE };
    }

}

// Questions for noodler devs:
// - how to introduce a new variable (so that the var handle will not be conflicting with any other variables)
