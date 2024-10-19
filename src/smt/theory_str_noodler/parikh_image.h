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
// Structure storing for each state a vector of transitions adjacent to this state.
// In particular TransitionStateVector[state] is a vector of transitions with source state being state
using TransitionStateVector = std::vector<std::vector<Transition>>;

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
    LenNode compute_phi_kirch(const TransitionStateVector& succ_trans, const TransitionStateVector& prev_trans);
    /**
     * @brief Compute formulae phi_span ensures connectedness of a run. Formula checks if there is a consistent
     * spanning tree wrt a run.
     * @param succ_trans [q] = [(q,.,.), .... ]. Vector (idexed by states q) containing list of transitions with the source state being q
     * @param prev_trans [q] = [(.,.,q), .... ]. Vector (idexed by states q) containing list of transitions with the target state being q
     * @return LenNode phi_span
     */
    LenNode compute_phi_span(const TransitionStateVector& succ_trans, const TransitionStateVector& prev_trans);

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

    const std::vector<BasicTerm>& get_gamma_init() const {
        return this->gamma_init;
    }

    const std::vector<BasicTerm>& get_gamma_fin() const {
        return this->gamma_fin;
    };

    const std::vector<BasicTerm>& get_sigma() const {
        return this->sigma;
    };

    void print_transition_var_labeling(std::ostream& output_stream) const;

    virtual ~ParikhImage() { }
};


/**
 * @brief Parikh image computation of Tag automaton for single disequation
 */
class ParikhImageDiseqTag : public ParikhImage {

protected:
    size_t number_of_states_in_row;

    ca::TagAut ca;

    // Maps every tag (e.g. <L, x>) to a corresponding #<L, x> variable representing
    // the number of times a tag has been seen in the underlying automaton.
    std::map<ca::AtomicSymbol, BasicTerm> tag_occurence_count_vars {};

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
    LenNode get_mismatch_formula(size_t i, size_t j, const Predicate& diseq, const LenNode& add_right = 0);

    /**
     * @brief Get formula describing that for selected symbols <R,1,sym> <R,2,sym'>
     * on the path we have that sym != sym'.
     *
     * @return LenNode Different mismatch symbol on the path
     */
    LenNode get_diff_symbol_formula();

public:
    ParikhImageDiseqTag(const ca::TagAut& ca, const std::set<ca::AtomicSymbol>& atomic_symbols, size_t number_of_states_in_row) :
        ParikhImage(ca.nfa),
        number_of_states_in_row(number_of_states_in_row),
        ca(ca),
        tag_occurence_count_vars(),
        atomic_symbols(atomic_symbols) { }

    /**
     * @brief Compute Parikh image with the free variables containing values of registers.
     * Assumes that each register is set in each symbol of the TagAut alphabet.
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
     * phi := compute_parikh_image &&  get_var_length && (get_diseq_length || (get_all_mismatch_formula && get_diff_symbol_formula))
     *
     * @param diseq Diseq
     * @return LenNode phi
     */
    LenNode get_diseq_formula(const Predicate& diseq);

    std::map<mata::Symbol, std::vector<LenNode>> group_sampling_transition_vars_by_symbol() const;

    LenNode express_string_length_preceding_supposed_mismatch(const std::vector<BasicTerm>& predicate_side, size_t supposed_mismatch_pos) const;
    std::pair<LenNode, size_t> express_mismatch_position(const std::vector<BasicTerm>& predicate_side, size_t mismatch_pos, size_t sample_order_label, const LenNode* offset_var = nullptr) const;
    LenNode count_register_stores_for_var_and_side(BasicTerm& var, char predicate_side_label) const;
    LenNode ensure_symbol_uniqueness_using_total_sum(std::map<mata::Symbol, std::vector<LenNode>>& symbol_to_register_sample_vars) const;
    LenNode ensure_symbol_uniqueness_using_implication(std::map<mata::Symbol, std::vector<LenNode>>& symbol_to_register_sample_vars) const;


};

typedef std::pair<mata::nfa::State, mata::nfa::State> StatePair;

/**
 * @brief Parikh image computation for tag automaton representing not contains.
 */
class ParikhImageNotContTag : public ParikhImageDiseqTag {

private:
    LenNode offset_var;

protected:
    /**
     * @brief Get the mismatch formula for each pair (i,j) of positions in @p not_cont.
     * phi := OR( mismatch(i,j,offset_var) where i is position of left of not_cont and j is position of right of not_cont ).
     * offset_var is added to the right side.
     *
     * @param not_cont Notcontains
     * @return LenNode phi
     */
    LenNode get_nt_all_mismatch_formula(const Predicate& not_cont);

public:
    ParikhImageNotContTag(const ca::TagAut& ca, const std::set<ca::AtomicSymbol>& atomic_symbols, size_t number_of_states_in_copy)
        : ParikhImageDiseqTag(ca, atomic_symbols, number_of_states_in_copy), offset_var(util::mk_noodler_var_fresh("offset_var")) { }

    /**
     * Create a formula asserting that |LHS| - |RHS| < offset_var.
     *
     * Assumes that the variables inside the underlying notContains will be present
     * in the overall notContains LIA formula, and that they in fact represent |x|.
     */
    LenNode mk_rhs_longer_than_lhs_formula(const Predicate& notContains);

    mata::nfa::State map_copy_state_into_its_origin(const mata::nfa::State state) const;

    /**
     * Given a @p parikh_image of the underlying tag automaton, group transitions that were
     * created using the same transition of the eps-concatenation as a template.
     *
     * For example, if the eps-concatenation contained (q, a, q'), then the tag automaton
     * will contain multiple transitions (q, <Tags>, q') (a bit over-simplified).
     *
     * Internally abuses the fact that there the state `p` and `p+K` for some fixed K is a copy
     * of the same state from the eps-concatenation.
     */
    std::unordered_map<StatePair, std::vector<LenNode>> group_isomorphic_transitions_across_copies(const std::map<Transition, BasicTerm>& parikh_image) const;

    /**
     * Create a formula asserting that @p parikh_image and @p other_parikh_image
     * encode the same run in the underlying eps-concatenation.
     */
    LenNode mk_parikh_images_encode_same_word_formula(const std::map<Transition, BasicTerm>& parikh_image, const std::map<Transition, BasicTerm>& other_image) const;

    LenNode get_not_cont_formula(const Predicate& not_cont);
    LenNode get_offset_var() const;
    LenNode existentially_quantify_all_parikh_vars(LenNode& formula);
};

}

#endif
