#ifndef Z3_STR_PARIKH_H_
#define Z3_STR_PARIKH_H_

#include <iostream>
#include <map>
#include <set>
#include <queue>
#include <string>
#include <memory>
#include <concepts>
#include <compare>

#include <mata/nfa/nfa.hh>
#include <mata/nfa/strings.hh>
#include <mata/nfa/builder.hh>

#include "formula.h"
#include "counter_automaton.h"
#include "formula_preprocess.h"

namespace smt::noodler::parikh {

using Transition = std::tuple<mata::nfa::State, mata::Symbol, mata::nfa::State>;
using TransitionCol = std::vector<std::vector<Transition>>;

/**
 * @brief Parikh image computation of NFA
 */
class ParikhImage {

private:
    mata::nfa::Nfa nfa;
    // variable gamma_q^I for each state q
    // gamma_q^I == 1 --> q is the first state of a run
    std::vector<BasicTerm> gamma_init {};
    // variable gamma_q^F for each state q
    // gamma_q^F == 1 --> q is the last state of a run
    std::vector<BasicTerm> gamma_fin {};
    // variable sigma_q for each state q
    // sigma_q = n <--> shortest path on a run from an initial state is n
    // sigma_q = -1 <--> q does not occur on the run
    std::vector<BasicTerm> sigma {};
    // variable for each transition 
    // counting the number times the transition was taken during the run
    std::map<Transition, BasicTerm> trans {};


protected:
    /**
     * computation of temporary formulae
     */
    /**
     * @brief Compute formula phi_init saying there is one initial state of a run. 
     * @return LenNode phi_init
     */
    LenNode compute_phi_init();
    /**
     * @brief Compute formula phi_fin saying there might be a final state as the last state of a run.
     * @return LenNode phi_fin 
     */
    LenNode compute_phi_fin();
    /**
     * @brief Compute formula phi_kirch ensuring that on a run the number of times we enter the state 
     * equals the number of states we leave the state (+/- one when the state is the first one or the last one).
     * @param succ_trans [q] = [(q,.,.), .... ]. Vector (idexed by states q) containing list of transitions with the source state being q  
     * @param prev_trans [q] = [(.,.,q), .... ]. Vector (idexed by states q) containing list of transitions with the target state being q 
     * @return LenNode phi_kirch
     */
    LenNode compute_phi_kirch(const TransitionCol& succ_trans, const TransitionCol& prev_trans);
    /**
     * @brief Compute formulae phi_span ensures connectedness of a run. Formula checks if there is a consistent 
     * spanning tree wrt a run. 
     * @param succ_trans [q] = [(q,.,.), .... ]. Vector (idexed by states q) containing list of transitions with the source state being q 
     * @param prev_trans [q] = [(.,.,q), .... ]. Vector (idexed by states q) containing list of transitions with the target state being q 
     * @return LenNode phi_span 
     */
    LenNode compute_phi_span(const TransitionCol& succ_trans, const TransitionCol& prev_trans);

public:
    ParikhImage(const mata::nfa::Nfa& nfa) : nfa(nfa) { } 

    /**
     * @brief Compute Parikh image of the nfa without the symbol mapping. 
     * The output is the number of transitions taken; not the number of symbols taken.
     * 
     * @return LenNode Parikh image 
     */
    virtual LenNode compute_parikh_image();

    const std::map<Transition, BasicTerm>& get_trans_vars() const {
        return this->trans;
    }

    virtual ~ParikhImage() { }
};


/**
 * @brief Parikh image computation of CA
 */
class ParikhImageCA : public ParikhImage {

private:
    ca::CA ca;
    // fresh variable for each AtomicSymbol. for symb, we use #symb to denote the corresponding variable
    std::map<ca::AtomicSymbol, BasicTerm> symbol_var {}; 
    // set of atomic symbols used in ca
    std::set<ca::AtomicSymbol> atomic_symbols {};


protected:
    /**
     * @brief Get the formula describing |L| != |R| where L != R is @p diseq.
     * 
     * @param diseq Disequation L != R
     * @return LenNode 
     */
    LenNode get_diseq_length(const Predicate& diseq);

    /**
     * @brief Generate LIA formula describing lengths of variables @p vars.
     * 
     * @param vars Variables
     * @return LenNode Length formula
     */
    LenNode get_var_length(const std::set<BasicTerm>& vars);

    /**
     * @brief Get the mismatch formula for each pair (i,j) of positions in @p diseq.
     * phi := OR( mismatch(i,j) where i is position of left of diseq and j is position of right of diseq )
     * 
     * @param diseq Disequation
     * @return LenNode phi
     */
    LenNode get_all_mismatch_formula(const Predicate& diseq);

    /**
     * @brief Get mismatch formula for particular positions @p i and @p j. 
     * 
     * @param i Position on the left side of @p diseq
     * @param j Position on the right side of @p diseq
     * @param diseq Diseq
     * @return LenNode mismatch(i,j)
     */
    LenNode get_mismatch_formula(size_t i, size_t j, const Predicate& diseq);

public:
    ParikhImageCA(const ca::CA& ca, const std::set<ca::AtomicSymbol>& atomic_symbols) : ParikhImage(ca.nfa), ca(ca), symbol_var(), atomic_symbols(atomic_symbols) { }

    /**
     * @brief Compute Parikh image with the free variables containing values of registers. 
     * Assumes that each register is set in each symbol of the CA alphabet.
     * @return LenNode phi_parikh
     */
    LenNode compute_parikh_image() override { 
        LenNode pi = ParikhImage::compute_parikh_image();
        LenNode sc = symbol_count_formula();

        return LenNode(LenFormulaType::AND, {
            pi, 
            sc
        });
    };

    /**
     * @brief Construct formula counting number of AtomicSymbol in each set on the transitions.
     * @return LenNode AND (#symb for each AtomicSymbol symb)
     */
    LenNode symbol_count_formula();

    /**
     * @brief Get Length formula for a disequation. 
     * phi := compute_parikh_image &&  get_var_length && (get_diseq_length || get_all_mismatch_formula)
     * 
     * @param diseq Diseq
     * @return LenNode phi
     */
    LenNode get_diseq_formula(const Predicate& diseq);
};

}

#endif