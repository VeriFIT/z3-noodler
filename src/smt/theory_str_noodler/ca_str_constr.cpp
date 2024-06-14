
#include "ca_str_constr.h"

namespace smt::noodler::ca {

    void DiseqAutMatrix::create_aut_matrix(const Predicate& diseq, const AutAssignment& aut_ass) {
        std::set<BasicTerm> var_set = diseq.get_vars();
            
        // create fixed linear order of variables
        for(const BasicTerm& bt : var_set) {
            this->var_order.push_back(bt);
        }
            
        // set offset size
        this->offsets.resize(3*this->offsets.size() + 1);
        // three copies
        this->aut_matrix.resize(3);
        for(size_t copy = 0; copy < 3; copy++) {
            this->aut_matrix[copy] = std::vector<mata::nfa::Nfa>(var_set.size());
            for(size_t var = 0; var < this->var_order.size(); var++) {
                this->aut_matrix[copy][var] = *aut_ass.at(this->var_order[var]);
            }
        }
        recompute_offset();
    }

    void DiseqAutMatrix::recompute_offset() {
        this->offsets[0] = 0;
        for(size_t copy = 0; copy < 3; copy++) {
            for(size_t var = 0; var < this->var_order.size(); var++) {
                size_t index = copy*this->var_order.size() + var;
                this->offsets[index + 1] = this->offsets[index] + this->aut_matrix[copy][var].num_of_states();
            }
        }
    }

    mata::nfa::Nfa DiseqAutMatrix::union_matrix() const {
        mata::nfa::Nfa ret;
        // assumes that the union is updates the states of the original automaton by 
        // adding a constant (which is given by the num of states of the original automaton)
        for(size_t copy = 0; copy < 3; copy++) {
            for(size_t var = 0; var < this->var_order.size(); var++) {
                ret.uni(this->aut_matrix[copy][var]);
            }
        }
        return ret;
    }

    //-----------------------------------------------------------------------------------------------

    void CADiseqGen::replace_symbols(char copy, size_t var) {
        BasicTerm bt = this->aut_matrix.get_var_order()[var];

        // <L,x>
        std::set<ca::AtomicSymbol> ats({ ca::AtomicSymbol{0, bt, 0, 0}});
        if (copy != 2) {
            // <P,x,copy+1>
            ats.insert(ca::AtomicSymbol{1, bt, char(copy+1), 0});
        }

        mata::Symbol new_symbol = this->alph.add_symbol(ats);
        mata::nfa::Nfa aut = this->aut_matrix.get_aut(copy, var);
        mata::nfa::Nfa res = aut.get_one_letter_aut(new_symbol);
        this->aut_matrix.set_aut(copy, var, res, false);
    }


    void CADiseqGen::add_connection(char copy_start, size_t var, mata::nfa::Nfa& aut_union) {

        // mapping between original symbols and new counter symbols from this->alph
        std::map<mata::Symbol, mata::Symbol> symbols;

        // basic term corresponding to the positional var
        BasicTerm bt = this->aut_matrix.get_var_order()[var];

        auto const_symbol = [](char copy, const BasicTerm& bt, mata::Symbol sym) -> std::set<ca::AtomicSymbol> {
            // <L,x>, <P,x,copy>, <R,copy,a>
            std::set<ca::AtomicSymbol> ats({ ca::AtomicSymbol{0, bt, 0, 0}, ca::AtomicSymbol{1, bt, copy, 0}, ca::AtomicSymbol{2, BasicTerm(BasicTermType::Variable), copy, sym} });
            return ats;
        };

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

    ca::CA CADiseqGen::construct_tag_aut() {

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

        // generate connecting transitions
        for(char copy = 0; copy < 2; copy++) {
            for(size_t var = 0; var < var_order.size(); var++) {
                add_connection(copy, var, aut_union);
            } 
        }

        // TODO: add epsilon connection between variable automata
        return { aut_union, this->alph };
    }


}
