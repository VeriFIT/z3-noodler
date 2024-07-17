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
#include "formula_preprocess.h"
#include "parikh_image.h"

namespace smt::noodler::ca {

    using AutMatrix = std::vector<std::vector<mata::nfa::Nfa>>;

    /**
     * @brief Class representing copies of automata for each variable. 
     * X axis = variables 
     * Y axis = copy
     */
    class DiseqAutMatrix {
    
    private:
        AutMatrix aut_matrix {};
        // order of variables
        std::vector<BasicTerm> var_order {};
        // starting state of each automaton
        std::vector<size_t> offsets {};

    protected:
        void create_aut_matrix(const Predicate& diseq, const AutAssignment& aut_ass);

        /**
         * @brief Recompute offsets.
         */
        void recompute_offset();

        /**
         * @brief Get offset in the Big unified NFA (i.e., starting state of the particular NFA [ @p copy, @p var ] in the Big NFA)
         * 
         * @param copy Copy index
         * @param var Variable index
         * @return size_t Smallest/starting state
         */
        size_t get_offset(size_t copy, size_t var) const {
            return this->offsets[copy*this->var_order.size() + var];
        } 

    public: 
        DiseqAutMatrix(const Predicate& diseq, const AutAssignment& aut_ass) : aut_matrix(), var_order(), offsets() {
            create_aut_matrix(diseq, aut_ass);
        }

        /**
         * @brief Get state in unified automaton (where all automata in matrix are unioned).
         * 
         * @param copy Index of the copy
         * @param var Index of the variable (index in @p var_order)
         * @param state State of the particular automaton at [ @p copy, @p var ]
         * @return mata::nfa::State State in the big NFA
         */
        mata::nfa::State get_union_state(size_t copy, size_t var, mata::nfa::State state) const {
            return get_offset(copy, var) + state;
        }

        /**
         * @brief Unify all particular automata into a single NFA.
         * 
         * @return mata::nfa::Nfa Big NFA
         */
        mata::nfa::Nfa union_matrix() const;

        const std::vector<BasicTerm>& get_var_order() const {
            return this->var_order;
        }

        void set_aut(size_t copy, size_t var, const mata::nfa::Nfa& aut, bool recomp_offset = false) {
            this->aut_matrix[copy][var] = aut;
            if(recomp_offset) {
                recompute_offset();
            }
        }

        const mata::nfa::Nfa& get_aut(size_t copy, size_t var) const {
            return this->aut_matrix[copy][var];
        }
    };

    /**
     * @brief Class for Tag aut generation for a single disequation.
     */
    class TagDiseqGen {

    private:
        DiseqAutMatrix aut_matrix;
        AutAssignment aut_ass;
        Predicate diseq;
        ca::CounterAlphabet alph {};

    public:
        TagDiseqGen(const Predicate& diseq, const AutAssignment& aut_ass) : aut_matrix(diseq, aut_ass), 
            aut_ass(aut_ass), diseq(diseq), alph() { }

    protected:
        /**
         * @brief Replace symbols in a particular variable automaton. Replace original symbols with 
         * the AtomicSymbols of the form <L,x> ...
         * 
         * @param copy Copy identifying particular variable automaton
         * @param var Variable of the automaton
         */
        void replace_symbols(char copy, size_t var);

        /**
         * @brief Add connections between copies. 
         * 
         * @param copy_start Starting copy (transitions source)
         * @param var Variable
         * @param aut_union Union automaton contains all copies in a single automaton.
         */
        void add_connection(char copy_start, size_t var, mata::nfa::Nfa& aut_union);

    public:
        /**
         * @brief Construct tagged automaton for a single disequation.
         * 
         * @return ca::CA Tagged automaton.
         */
        ca::TagAut construct_tag_aut();

        const DiseqAutMatrix& get_aut_matrix() const {
            return this->aut_matrix;
        }

    };

    /**
     * @brief Get LIA formula for disequations. The LIA formula describes all length 
     * models of the diseqation. 
     * 
     * TODO: So-far it supports only one disequation. 
     * 
     * @param diseqs Disequations
     * @param autass Automata assignmnent after stabilization
     * @return LenNode LIA formula describing lengths of string models
     */
    LenNode get_lia_for_disequations(const Formula& diseqs, const AutAssignment& autass);

    /**
     * @brief Get LIA formula for not contains. So-far it performs only simple checks.
     * 
     * @param not_conts Not contains
     * @param autass Automata assignmnent after stabilization
     * @return std::pair<LenNode, LenNodePrecision> LIA formula describing lengths of string models together with the precision.
     */
    std::pair<LenNode, LenNodePrecision> get_lia_for_not_contains(const Formula& not_conts, const AutAssignment& autass);

}

#endif