
#include "ca_str_constr.h"
#include "formula.h"
#include "util.h"
#include <mata/nfa/delta.hh>
#include <mata/nfa/strings.hh>
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

        // Recompute the number of states that a row has
        number_of_states_in_row = 0;
        for (size_t var_id = 0; var_id < this->var_order.size(); var_id++) {
            number_of_states_in_row += this->aut_matrix[0][var_id].num_of_states();
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
        const size_t copy_count = 3;
        mata::nfa::Nfa result_nfa;

        // #Note(mhecko): Relying on unite_nondet_with is problematic - the procedure can do all kinds of
        //                optilizations, yet we have very clear perception of how the result should look like.

        size_t copy_states_cnt = 0;
        const size_t template_copy = 0;
        for (size_t var_id = 0; var_id < this->var_order.size(); var_id++) {
            copy_states_cnt += this->aut_matrix[template_copy][var_id].num_of_states();
        }

        result_nfa.delta.allocate(copy_states_cnt*copy_count + 1);

        mata::nfa::Nfa row_template = this->aut_matrix[template_copy][0]; // First row of the matrix
        for (size_t var = 1; var < this->var_order.size(); var++) {
            row_template = mata::nfa::concatenate(row_template, this->aut_matrix[template_copy][var], true);
        }

        for (size_t copy = 0; copy < copy_count; copy++) {
            size_t copy_state_offset = copy*copy_states_cnt;

            for (mata::strings::State template_source_state = 0; template_source_state < copy_states_cnt; template_source_state++) {
                mata::nfa::State copy_source_state = template_source_state + copy_state_offset;

                for (const mata::nfa::SymbolPost& symbol_post : row_template.delta.state_post(template_source_state)) {
                    for (auto it = symbol_post.cbegin(); it != symbol_post.cend(); it++) {
                        mata::nfa::State copy_target_state = (*it) + copy_state_offset;
                        result_nfa.delta.add(copy_source_state, symbol_post.symbol, copy_target_state);
                    }
                }
            }
        }

        result_nfa.initial.clear();
        result_nfa.initial = row_template.initial; // The offset of 0th copy is 0, no need to add offset

        result_nfa.final.clear();
        size_t last_row_offset = (copy_count - 1) * copy_states_cnt;
        for (mata::nfa::State final_state : row_template.final) {
            mata::nfa::State result_final_state = last_row_offset + final_state;
            result_nfa.final.insert(result_final_state);
        }

        return result_nfa;
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


    void TagDiseqGen::add_connection(char copy_start, size_t var_idx, mata::nfa::Nfa& aut_union) {

        // mapping between original symbols and new counter symbols from this->alph ensuring that the created
        // symbols are named consistently by the same mata state.
        std::map<mata::Symbol, mata::Symbol> original_to_tag_symbols;

        // basic term corresponding to the positional var
        BasicTerm bt = this->aut_matrix.get_var_order()[var_idx];

        // lambda for a particular symbol construction
        auto const_symbol = [](char copy_idx, const BasicTerm& bt, mata::Symbol sym) -> std::set<ca::AtomicSymbol> {
            // <L,x>, <P,x,copy_idx>, <R,x,copy_idx,a>
            std::set<ca::AtomicSymbol> atomic_symbol({ ca::AtomicSymbol::create_l_symbol(bt),
                                                       ca::AtomicSymbol::create_p_symbol(bt, copy_idx),
                                                       ca::AtomicSymbol::create_r_symbol(bt, copy_idx, sym) });
            return atomic_symbol;
        };

        // We use the original automaton from this->aut_ass because the actual alphabet symbols
        // might not be present in this->aut_matrix because they were replaced earlier by tags (<L, x>, etc.).
        mata::nfa::Nfa original_automaton = *this->aut_ass.at(bt);

        for (mata::nfa::State source_state = 0; source_state < original_automaton.num_of_states(); source_state++) {
            for (const mata::nfa::SymbolPost& symbol_post : original_automaton.delta[source_state]) {
                // compute new mata symbol storing the set of AtomicSymbols
                auto original_sym_mapping_bucket = original_to_tag_symbols.find(symbol_post.symbol);

                mata::Symbol new_symbol;
                if (original_sym_mapping_bucket != original_to_tag_symbols.end()) {
                    new_symbol = original_sym_mapping_bucket->second;
                } else {
                    new_symbol = this->alph.add_symbol(const_symbol(copy_start + 1, bt, symbol_post.symbol));
                    original_to_tag_symbols[symbol_post.symbol] = new_symbol;
                }

                for (const mata::nfa::State& target : symbol_post.targets) {
                    aut_union.delta.add(
                        this->aut_matrix.get_union_state(copy_start, var_idx, source_state),
                        new_symbol,
                        this->aut_matrix.get_union_state(copy_start+1, var_idx, target)
                    );
                }
            }
        }
    }

    ca::TagAut TagDiseqGen::construct_tag_aut() {

        std::vector<BasicTerm> var_order = this->aut_matrix.get_var_order();
        // update symbols for each inner automaton
        for (char copy = 0; copy < 3; copy++) {
            for (size_t var = 0; var < var_order.size(); var++) {
                // replace each automaton in the matrix with the specific AtomicSymbol
                replace_symbols(copy, var);
            }
        }

        // union all automata in the matrix
        mata::nfa::Nfa aut_union = this->aut_matrix.union_matrix();
        // add mata epsilon symbol to alphabet. Used for DOT export.
        this->alph.insert(mata::nfa::EPSILON, {});

        // generate connecting transitions
        for (char copy = 0; copy < 2; copy++) {
            for (size_t var = 0; var < var_order.size(); var++) {
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
            tout << "* Disequation: " << diseq << std::endl;
        );

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
        for (const auto& trans : tag_aut.nfa.delta.transitions()) {
            std::set<AtomicSymbol> sms = tag_aut.alph.get_symbol(trans.symbol);
            ats.insert(sms.begin(), sms.end());
        }

        parikh::ParikhImageDiseqTag pi(tag_aut, ats, 0);
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

        if (!can_construct_lia) {
            return { LenNode(LenFormulaType::FALSE), LenNodePrecision::UNDERAPPROX };
        }

        return { LenNode(LenFormulaType::FALSE), LenNodePrecision::UNDERAPPROX };
    }

}

// Questions for noodler devs:
// - how to introduce a new variable (so that the var handle will not be conflicting with any other variables)
