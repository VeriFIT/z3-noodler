#ifndef Z3_STR_CA_CONSTR_H_
#define Z3_STR_CA_CONSTR_H_

#include <iostream>
#include <map>
#include <set>
#include <queue>
#include <string>
#include <memory>
#include <concepts>
#include <compare>
#include <variant>

#include <mata/nfa/nfa.hh>
#include <mata/nfa/strings.hh>
#include <mata/nfa/builder.hh>

#include "formula.h"
#include "counter_automaton.h"
#include "aut_assignment.h"

namespace smt::noodler::ca {

    static LenNode get_lia_for_disequations(const Formula& diseqs, const AutAssignment& autass) {
        return LenNode(LenFormulaType::FALSE);
    }

    using AutMatrix = std::vector<std::vector<mata::nfa::Nfa>>;

    class DiseqAutMatrix {
    
    private:
        AutMatrix aut_matrix {};
        std::vector<BasicTerm> var_order {};
        std::vector<size_t> offsets {};

    protected:
        void create_aut_matrix(const Predicate& diseq, const AutAssignment& aut_ass);

        void recompute_offset();

        size_t get_offset(size_t copy, size_t var) const {
            return this->offsets[copy*this->var_order.size() + var];
        } 

    public: 
        DiseqAutMatrix(const Predicate& diseq, const AutAssignment& aut_ass) : aut_matrix(), var_order(), offsets() {
            create_aut_matrix(diseq, aut_ass);
        }

        mata::nfa::State get_union_state(size_t copy, size_t var, mata::nfa::State state) const {
            return get_offset(copy, var) + state;
        }

        mata::nfa::Nfa union_matrix() const;

        const std::vector<BasicTerm>& get_var_order() const {
            return this->var_order;
        }

        void set_aut(size_t copy, size_t var, const mata::nfa::Nfa& aut, bool re_offset = false) {
            this->aut_matrix[copy][var] = aut;
            if(re_offset) {
                recompute_offset();
            }
        }

        const mata::nfa::Nfa& get_aut(size_t copy, size_t var) const {
            return this->aut_matrix[copy][var];
        }
    };

    class CADiseqGen {

    private:
        DiseqAutMatrix aut_matrix;
        AutAssignment aut_ass;
        Predicate diseq;
        ca::CounterAlphabet alph {};

    public:
        CADiseqGen(const Predicate& diseq, const AutAssignment& aut_ass) : aut_matrix(diseq, aut_ass), 
            aut_ass(aut_ass), diseq(diseq), alph() { }

    protected:

        void replace_symbols(char copy, size_t var);

        void add_connection(char copy_start, size_t var, mata::nfa::Nfa& aut_union);

    public:

        ca::CA construct_tag_aut();

    };

}

#endif