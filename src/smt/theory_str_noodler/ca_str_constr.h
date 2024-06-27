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
        ca::CA construct_tag_aut();

        const DiseqAutMatrix& get_aut_matrix() const {
            return this->aut_matrix;
        }

    };

    static LenNode get_lia_for_disequations(const Formula& diseqs, const AutAssignment& autass) {

        if(diseqs.get_predicates().size() == 0) {
            return LenNode(LenFormulaType::TRUE);
        }

        // disequation to be solved
        Predicate diseq_orig = diseqs.get_predicates()[0];

        Concat left {};
        Concat right {};
        std::copy_if(diseq_orig.get_left_side().begin(), diseq_orig.get_left_side().end(), std::back_inserter(left),
                [&](const BasicTerm& n){ return !autass.is_epsilon(n); });
        std::copy_if(diseq_orig.get_right_side().begin(), diseq_orig.get_right_side().end(), std::back_inserter(right),
                [&](const BasicTerm& n){ return !autass.is_epsilon(n); });
        Predicate diseq(PredicateType::Inequation, {left, right});

        if(left == right) {
            return LenNode(LenFormulaType::FALSE);
        }


        CADiseqGen gen(diseq, autass);
        ca::CA tag_aut = gen.construct_tag_aut();
        tag_aut.nfa.trim();

        STRACE("str-diseq",
            tout << "* Variable ordering: " << std::endl;
            tout << concat_to_string(gen.get_aut_matrix().get_var_order()) << std::endl << std::endl;
        );
        STRACE("str-diseq",
            tout << "* NFAs for variables: " << std::endl;
            for(const BasicTerm& bt : diseq.get_set()) {
                tout << bt.to_string() << ":" << std::endl;
                autass.at(bt)->print_to_DOT(tout);
            }
            tout << std::endl;
        );
        STRACE("str-diseq",
            tout << "* Tag Automaton for diseq: " << diseqs.to_string() << std::endl;
            tag_aut.print_to_DOT(tout);
            tout << std::endl;
        );
        STRACE("str", tout << "CA LIA: finished" << std::endl; );

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

    static std::pair<LenNode, LenNodePrecision> get_lia_for_not_contains(const Formula& not_conts, const AutAssignment& autass) {
        if(not_conts.get_predicates().size() == 0) {
            return { LenNode(LenFormulaType::TRUE), LenNodePrecision::PRECISE };
        }
        if(not_conts.get_predicates().size() > 1) {
            return { LenNode(LenFormulaType::FALSE), LenNodePrecision::UNDERAPPROX };
        }

        Predicate not_cont_orig = not_conts.get_predicates()[0];
        // remove variables with epsilon language
        Concat left {};
        Concat right {};
        std::copy_if(not_cont_orig.get_left_side().begin(), not_cont_orig.get_left_side().end(), std::back_inserter(left),
                [&](const BasicTerm& n){ return !autass.is_epsilon(n); });
        std::copy_if(not_cont_orig.get_right_side().begin(), not_cont_orig.get_right_side().end(), std::back_inserter(right),
                [&](const BasicTerm& n){ return !autass.is_epsilon(n); });
        Predicate not_cont(PredicateType::NotContains, {left, right});

        if(left == right) {
            return { LenNode(LenFormulaType::FALSE), LenNodePrecision::PRECISE };
        }

        // not contains to be solved
        
        CADiseqGen gen(not_cont, autass);
        ca::CA tag_aut = gen.construct_tag_aut();
        tag_aut.nfa.trim();

        STRACE("str-diseq",
            tout << "* Variable ordering: " << std::endl;
            tout << concat_to_string(gen.get_aut_matrix().get_var_order()) << std::endl << std::endl;
        );
        STRACE("str-diseq",
            tout << "* NFAs for variables: " << std::endl;
            for(const BasicTerm& bt : not_cont.get_set()) {
                tout << bt.to_string() << ":" << std::endl;
                autass.at(bt)->print_to_DOT(tout);
            }
            tout << std::endl;
        );
        STRACE("str-diseq",
            tout << "* Tag Automaton for not contains: " << not_cont.to_string() << std::endl;
            tag_aut.print_to_DOT(tout);
            tout << std::endl;
        );
        STRACE("str", tout << "CA LIA: finished" << std::endl; );

        // we include only those symbols occurring in the reduced tag automaton
        std::set<AtomicSymbol> ats;
        for(const auto& trans : tag_aut.nfa.delta.transitions()) {
            std::set<AtomicSymbol> sms = tag_aut.alph.get_symbol(trans.symbol);
            ats.insert(sms.begin(), sms.end());
        }

        parikh::ParikhImageNotContTag pi(tag_aut, ats);
        LenNode pi_formula = pi.get_not_cont_formula(not_cont);

        STRACE("str-diseq", tout << "* Resulting formula: " << std::endl << pi_formula << std::endl << std::endl; );

        return {pi_formula, LenNodePrecision::PRECISE};
    }

}

#endif