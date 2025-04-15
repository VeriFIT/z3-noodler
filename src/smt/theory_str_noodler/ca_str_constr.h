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

#include "util.h"
#include "formula.h"
#include "counter_automaton.h"
#include "aut_assignment.h"
#include "formula_preprocess.h"
#include "parikh_image.h"

namespace smt::noodler::ca {

    using AutMatrix = std::vector<std::vector<mata::nfa::Nfa>>;

    struct AutMatrixUnionResult { // In case we need export more structural properties
        mata::nfa::Nfa      nfa;
        TagAutStateMetadata metadata;
    };

    /**
     * @brief Class representing copies of automata for each variable.
     * X axis = variables
     * Y axis = copy
     */
    class DiseqAutMatrix {

    private:
        // 2D matrix of (modified) NFAs originating from aut_assignment
        AutMatrix aut_matrix {};
        // order of variables
        std::vector<BasicTerm> var_order {};
        // starting state of each automaton
        std::vector<size_t> var_aut_init_states_in_copy {};

        size_t number_of_states_in_row;

    protected:
        void create_aut_matrix(const std::vector<Predicate>& disequations, const AutAssignment& aut_ass);

        /**
         * @brief Recompute offsets.
         */
        void recompute_var_aut_init_state_positions();

        /**
         * @brief Get offset in the Big unified NFA (i.e., starting state of the particular NFA [ @p copy, @p var ] in the Big NFA)
         *
         * @param copy Copy index
         * @param var Variable index
         * @return size_t Smallest/starting state
         */
        size_t get_var_aut_init_state_pos(size_t copy, size_t var) const {
            size_t result = this->var_aut_init_states_in_copy[copy*this->var_order.size() + var];
            return result;
        }

    public:
        DiseqAutMatrix(const std::vector<Predicate>& disequations, const AutAssignment& aut_ass) : aut_matrix(), var_order(), var_aut_init_states_in_copy() {
            create_aut_matrix(disequations, aut_ass);
        }

        DiseqAutMatrix(const Predicate& diseq, const AutAssignment& aut_ass) : aut_matrix(), var_order(), var_aut_init_states_in_copy() {
            std::vector disequations {diseq};
            create_aut_matrix(disequations, aut_ass);
        }

        size_t get_copy_cnt() const {
            return this->aut_matrix.size();
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
            return get_var_aut_init_state_pos(copy, var) + state;
        }

        std::vector<size_t>& get_var_init_states_pos_in_copies() {
            return this->var_aut_init_states_in_copy;
        }

        /**
         * @brief Unify all particular automata into a single NFA.
         *
         * @return mata::nfa::Nfa Big NFA
         */
        AutMatrixUnionResult union_matrix() const;

        const std::vector<BasicTerm>& get_var_order() const {
            return this->var_order;
        }

        void set_aut(size_t copy, size_t var, const mata::nfa::Nfa& aut, bool recomp_offset = false) {
            this->aut_matrix[copy][var] = aut;
            if(recomp_offset) {
                recompute_var_aut_init_state_positions();
            }
        }

        const std::vector<mata::nfa::Nfa>& get_matrix_row(size_t row_idx) const {
            return this->aut_matrix[row_idx];
        }

        const mata::nfa::Nfa& get_aut(size_t copy, size_t var) const {
            return this->aut_matrix[copy][var];
        }

        size_t get_number_of_states_in_row() const {
            return number_of_states_in_row;
        }
    };

    /**
     * @brief Class for Tag aut generation for a single disequation.
     */
    class TagDiseqGen {

    private:
        DiseqAutMatrix          aut_matrix;
        AutAssignment           aut_ass;
        std::vector<Predicate>  predicates;
        ca::CounterAlphabet     alph {};

    protected:
        /**
         * @brief Replace symbols in the variable automaton in the matrix cell given by @p copy
         *        and @p var with symbols of the form AtomicSymbols of the form <L,x>...
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
        void add_connection_for_multiple_predicates(char copy_start, size_t var, mata::nfa::Nfa& aut_union);

        void add_connection_single_predicate(char copy_start, size_t var, mata::nfa::Nfa& aut_union);
        void add_sampling_transitions_for_predicate_idx(size_t copy_start, size_t var_idx, std::map<mata::Symbol, mata::Symbol>& register_store_symbol_cache, mata::nfa::Nfa& nfa);

        inline size_t get_copy_idx_labeling_transition(size_t source_copy_idx, size_t target_copy_idx) {
            return target_copy_idx;
        }
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


        const std::vector<Predicate>& get_underlying_predicates() const {
            return this->predicates;
        };

        const size_t get_copy_cnt() const {
            return 2*this->predicates.size() + 1;
        }

        TagDiseqGen(const Predicate& diseq, const AutAssignment& aut_ass) : aut_matrix(diseq, aut_ass),
            aut_ass(aut_ass), predicates({diseq}), alph() { }

        TagDiseqGen(const std::vector<Predicate>& disequations, const AutAssignment& aut_ass) : aut_matrix(disequations, aut_ass),
            aut_ass(aut_ass), predicates(disequations), alph() { }


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
     * @brief Construct a LIA formula that is true iff the RHS of the given @p not_contains is longer
     *        than its LHS given a model of @p parikh_image
     *
     * @param not_contains A not-contains predicate whose RHS should be longer than its LHS
     * @param autass Automata assignmnent after stabilization
     * @return LenNode LIA formula that is true iff the RHS of the given not_contains is longer than its LHS
    */
    LenNode make_lia_rhs_longer_than_lhs(const Predicate& not_contains, const DiseqAutMatrix& automaton_matrix, const parikh::ParikhImage& parikh_image);

    /**
     * @brief Get LIA formula for not contains. So-far it performs only simple checks.
     *
     * @param not_conts Not contains
     * @param autass Automata assignmnent after stabilization
     * @param use_tag_proc Whether to use the tag-based procedure
     * @return std::pair<LenNode, LenNodePrecision> LIA formula describing lengths of string models together with the precision.
     */
    std::pair<LenNode, LenNodePrecision> get_lia_for_not_contains(const Formula& not_conts, const AutAssignment& autass, bool use_tag_proc);

}

#endif
