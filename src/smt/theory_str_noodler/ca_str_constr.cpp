
#include "ca_str_constr.h"
#include "util.h"
#include <unordered_map>

namespace smt::noodler::ca {

    void DiseqAutMatrix::create_aut_matrix(const Predicate& diseq, const AutAssignment& aut_ass) {
        // we want to include both variables and literals
        std::set<BasicTerm> var_set = diseq.get_set();

        // create fixed linear order of variables
        for(const BasicTerm& bt : var_set) {
            this->var_order.push_back(bt);
        }

        // set offset size
        this->var_aut_init_states_in_copy.resize(3*var_set.size() + 1);
        // three copies
        this->aut_matrix.resize(3);
        for(size_t copy = 0; copy < 3; copy++) {
            this->aut_matrix[copy] = std::vector<mata::nfa::Nfa>(var_set.size());
            for(size_t var = 0; var < this->var_order.size(); var++) {
                this->aut_matrix[copy][var] = *aut_ass.at(this->var_order[var]);
                // reduce the original nfa
                this->aut_matrix[copy][var] = mata::nfa::reduce(this->aut_matrix[copy][var]);
            }
        }
        recompute_var_aut_init_state_positions();
    }

    void DiseqAutMatrix::recompute_var_aut_init_state_positions() {
        this->var_aut_init_states_in_copy[0] = 0;
        for(size_t copy = 0; copy < 3; copy++) {
            for(size_t var = 0; var < this->var_order.size(); var++) {
                size_t index = copy*this->var_order.size() + var;
                this->var_aut_init_states_in_copy[index + 1] = this->var_aut_init_states_in_copy[index] + this->aut_matrix[copy][var].num_of_states();
            }
        }
    }

    mata::nfa::Nfa DiseqAutMatrix::union_matrix() const {
        mata::nfa::Nfa ret;
        // assumes that the union is updates the states of the original automaton by
        // adding a constant (which is given by the num of states of the original automaton)
        for(size_t copy = 0; copy < 3; copy++) {
            // eps-concatenate each variable automaton in a copy
            mata::nfa::Nfa aut_line = this->aut_matrix[copy][0];
            for(size_t var = 1; var < this->var_order.size(); var++) {
                aut_line = mata::nfa::concatenate(aut_line, this->aut_matrix[copy][var], true);
            }
            // only the first copy contains initial states
            if (copy != 0) {
                aut_line.initial.clear();
            }
            // only the last copy contains final states
            if (copy != 2) {
                aut_line.final.clear();
            }
            ret.unite_nondet_with(aut_line);
        }
        return ret;
    }

    //-----------------------------------------------------------------------------------------------

    void TagDiseqGen::replace_symbols(char copy, size_t var) {
        BasicTerm bt = this->aut_matrix.get_var_order()[var];

        // <L,x>
        std::set<ca::AtomicSymbol> ats({ ca::AtomicSymbol::create_l_symbol(bt)});
        if (copy != 2) {
            // <P,x,copy+1>
            ats.insert(ca::AtomicSymbol::create_p_symbol(bt, char(copy+1)));
        }

        mata::Symbol new_symbol = this->alph.add_symbol(ats);
        mata::nfa::Nfa aut = this->aut_matrix.get_aut(copy, var);
        mata::nfa::Nfa res = aut.get_one_letter_aut(new_symbol);
        this->aut_matrix.set_aut(copy, var, res, false);
    }


    void TagDiseqGen::add_connection(char copy_start, size_t var, mata::nfa::Nfa& aut_union) {

        // mapping between original symbols and new counter symbols from this->alph
        std::map<mata::Symbol, mata::Symbol> symbols;

        // basic term corresponding to the positional var
        BasicTerm bt = this->aut_matrix.get_var_order()[var];

        // lambda for a particular symbol construction
        auto const_symbol = [](char copy, const BasicTerm& bt, mata::Symbol sym) -> std::set<ca::AtomicSymbol> {
            // <L,x>, <P,x,copy>, <R,x,copy,a>
            std::set<ca::AtomicSymbol> ats({ ca::AtomicSymbol::create_l_symbol(bt), ca::AtomicSymbol::create_p_symbol(bt, copy), ca::AtomicSymbol::create_r_symbol(bt, copy, sym) });
            return ats;
        };

        // original automaton --> we need the original symbols to store them to AtomicSymbol
        // (the original symbols are already lost in this->aut_matrix --> already replace by
        // AtomicSymbol completely forgetting the original symbols).
        mata::nfa::Nfa aut_orig = *this->aut_ass.at(bt);
        for (mata::nfa::State st = 0; st < aut_orig.num_of_states(); st++) {
            for(const mata::nfa::SymbolPost& spost : aut_orig.delta[st]) {
                // compute new mata symbol storing the set of AtomicSymbols
                auto it = symbols.find(spost.symbol);
                mata::Symbol new_symbol;
                if (it != symbols.end()) {
                    new_symbol = it->second;
                } else {
                    new_symbol = this->alph.add_symbol(const_symbol(copy_start + 1, bt, spost.symbol));
                    symbols[spost.symbol] = new_symbol;
                }

                for(const mata::nfa::State& tgt : spost.targets) {
                    aut_union.delta.add(
                        this->aut_matrix.get_union_state(copy_start, var, st),
                        new_symbol,
                        this->aut_matrix.get_union_state(copy_start+1, var, tgt)
                    );
                }
            }
        }
    }

    ca::TagAut TagDiseqGen::construct_tag_aut() {

        std::vector<BasicTerm> var_order = this->aut_matrix.get_var_order();
        // update symbols for each inner automaton
        for(char copy = 0; copy < 3; copy++) {
            for(size_t var = 0; var < var_order.size(); var++) {
                // replace each automaton in the matrix with the specific AtomicSymbol
                replace_symbols(copy, var);
            }
        }

        // union all automata in the matrix
        mata::nfa::Nfa aut_union = this->aut_matrix.union_matrix();
        // add mata epsilon symbol to alphabet. Used for DOT export.
        this->alph.insert(mata::nfa::EPSILON, {});

        // generate connecting transitions
        for(char copy = 0; copy < 2; copy++) {
            for(size_t var = 0; var < var_order.size(); var++) {
                add_connection(copy, var, aut_union);
            }
        }

        return { aut_union, this->alph, var_order };
    }

    //-----------------------------------------------------------------------------------------------


    //-----------------------------------------------------------------------------------------------

    LenNode get_lia_for_disequations(const Formula& diseqs, const AutAssignment& autass) {

        if(diseqs.get_predicates().size() == 0) {
            return LenNode(LenFormulaType::TRUE);
        }

        FormulaPreprocessor prep_handler{diseqs, autass, {}, {}, {}};
        prep_handler.propagate_eps();
        prep_handler.remove_trivial();
        prep_handler.reduce_diseqalities();

        if(prep_handler.get_modified_formula().get_predicates().size() == 0) {
            return LenNode(LenFormulaType::FALSE);
        }

        Predicate diseq = prep_handler.get_modified_formula().get_predicates()[0];
        TagDiseqGen gen(diseq, prep_handler.get_aut_assignment());
        ca::TagAut tag_aut = gen.construct_tag_aut();
        tag_aut.nfa.trim();

        STRACE("str-diseq",
            tout << "* Variable ordering: " << std::endl;
            tout << concat_to_string(gen.get_aut_matrix().get_var_order()) << std::endl << std::endl;
        );
        STRACE("str-diseq",
            tout << "* NFAs for variables: " << std::endl;
            for(const BasicTerm& bt : diseq.get_set()) {
                tout << bt.to_string() << ":" << std::endl;
                autass.at(bt)->print_to_dot(tout);
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
        std::set<AtomicSymbol> ats;
        for(const auto& trans : tag_aut.nfa.delta.transitions()) {
            std::set<AtomicSymbol> sms = tag_aut.alph.get_symbol(trans.symbol);
            ats.insert(sms.begin(), sms.end());
        }

        parikh::ParikhImageDiseqTag pi(tag_aut, ats);
        LenNode pi_formula = pi.get_diseq_formula(diseq);

        STRACE("str-diseq", tout << "* Resulting formula: " << std::endl << pi_formula << std::endl << std::endl; );

        return pi_formula;
    }

    std::pair<LenNode, LenNodePrecision> get_lia_for_not_contains(const Formula& formula, const AutAssignment& var_assignment) {

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

        if (formula.get_predicates().size() > 1) {
            // We have more than 1 notContains, for now we pretent we don't know what to do with it
            return { LenNode(LenFormulaType::FALSE), LenNodePrecision::UNDERAPPROX };
        }

        const Predicate& not_contains = formula.get_predicates().at(0);

        // #Optimize(mhecko): Add a Iterator<const BasicTerm> to Predicate - it is pointless to create a set
        std::set<BasicTerm> vars = not_contains.get_set();

        bool can_construct_lia = true;
        for (const BasicTerm& var : vars) {
            if (var.get_type() == BasicTermType::Literal) {
                // var is a literal - right now we do not support that.
                STRACE("str-not-contains", tout << "* not-contains has a literal - we do not support literals yet\n"; );
                can_construct_lia = false;
                break;
            }

            if (!var_assignment.is_flat(var)) {
                STRACE("str-not-contains", tout << "* cannot reduce to LIA - one of the input vars does not have a flat langauge\n"; );
                can_construct_lia = false;
                break;

            };
        }

        // #progress(mhecko): What needs to be implemented:
        // - support for literals
        // - diseq>LIA - allow introducing a constant offset into the resulting formula
        // - Parikh image :: LIA formula that is true iff two given models of a PI encode the same word
        // - Length diff :: LIA formula that is true iff RHS is longer than LHS

        if (!can_construct_lia) {
            return { LenNode(LenFormulaType::FALSE), LenNodePrecision::UNDERAPPROX };
        }

        return { LenNode(LenFormulaType::FALSE), LenNodePrecision::UNDERAPPROX };
    }

    LenNode make_lia_rhs_longer_than_lhs(const TagDiseqGen& lia_generator, const parikh::ParikhImage& parikh_image) {

        auto& first_row = lia_generator.get_aut_matrix().get_matrix_row(0);
        size_t states_in_matrix_row = 0;
        for (const mata::nfa::Nfa& nfa : first_row) { states_in_matrix_row += nfa.num_of_states(); }

        std::unordered_map<int, std::vector<BasicTerm>> var_word_length_constributing_transitions;

        for (auto& [transition, transition_var]: parikh_image.get_trans_vars()) {
            // Figure out to which Aut(x) the transition ultimately belong:
            // taking a (mod nuber_of_states_in_row) shifts the state numbers back into the source row
            mata::nfa::State source_state = std::get<0>(transition) % states_in_matrix_row;
            mata::nfa::State target_state = std::get<2>(transition) % states_in_matrix_row;

            const std::vector<size_t>& var_init_states_offsets = lia_generator.get_aut_matrix().get_var_init_states_pos_in_copies();
            size_t source_var = bin_search_leftmost(var_init_states_offsets, source_state);
            size_t target_var = bin_search_leftmost(var_init_states_offsets, target_state);

            // #Note(mhecko): Temporary, this needs to be removed before merging (?)
            assert (source_origin_var != -1);
            assert (target_origin_var != -1);

            if (source_var != target_var) continue; // eps-transition

            var_word_length_constributing_transitions[source_var].push_back(transition_var);
        }

        const Predicate& not_contains = lia_generator.get_underlying_predicate();

        std::unordered_map<BasicTerm, std::pair<size_t, size_t>> var_occurence_counts;
        for (const BasicTerm& term: not_contains.get_left_side()) {
            auto [old_map_entry, did_emplace_happen] = var_occurence_counts.emplace(term, 1, 0);
            if (!did_emplace_happen) {
                old_map_entry->second.first += 1; // Increment the number of LHS occurrences (.first)
            }
        }

        for (const BasicTerm& term: not_contains.get_right_side()) {
            auto [old_map_entry, did_emplace_happen] = var_occurence_counts.emplace(term, 0, 1);
            if (!did_emplace_happen) {
                old_map_entry->second.second += 1; // Increment the number of RHS occurrences (.second)
            }
        }

        // TODO(mhecko): emit LIA formula

        return LenNode(LenFormulaType::FALSE);
    }
}

// Questions for noodler devs:
// - how to introduce a new variable (so that the var handle will not be conflicting with any other variables)
