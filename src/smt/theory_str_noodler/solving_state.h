#ifndef _NOODLER_SOLVING_STATE_H_
#define _NOODLER_SOLVING_STATE_H_

#include <memory>
#include <deque>
#include <algorithm>

#include "params/theory_str_noodler_params.h"
#include "formula.h"
#include "aut_assignment.h"
#include "util.h"

namespace smt::noodler {

    /// A state of decision procedure that can lead to a solution
    struct SolvingState {

    private:
        
        /// @brief Apply substitutions from substitution_map directly to disequations.
        void apply_substitutions_to_disequations();

    public:
        // aut_ass[x] assigns variable x to some automaton while substitution_map[x] maps variable x to
        // the concatenation of variables for which x was substituted (i.e. its automaton is concatenation
        // of the automata from these variables). Each variable is either assigned in aut_ass or
        // substituted in substitution_map, but not both!
        AutAssignment aut_ass;
        std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;

        // set of inclusions (i.e. Predicate must be of type equations which we pretend is an inclusion) where we are trying to find aut_ass + substitution_map such that they hold
        std::set<Predicate> inclusions;
        // set of transducers which we want to smiplify so that we only have at most one var in input and at most one var in output
        std::set<Predicate> transducers;

        // set of inclusions/transducers from the previous sets that for sure are not on cycle in the inclusion graph
        // that would be generated from inclusions
        std::set<Predicate> predicates_not_on_cycle;

        // contains inclusions/transducers we need to process (for inclusions we want them to hold under aut_ass and substitution_map, for transducers we want to simplify them)
        std::deque<Predicate> predicates_to_process;

        // the variables that have length constraint on them in the rest of formula
        std::unordered_set<BasicTerm> length_sensitive_vars;

        // disequations postponed to be handled after finding stable solutions
        Formula postponed_disequations;

        // conversions local to this solving state
        std::vector<TermConversion> conversions;

        // length conjuncts generated while replacing disequalities in this state
        std::vector<LenNode> disequations_len_formula_conjuncts;

        // indicates whether this solving state has any siblings in the solving state tree
        bool has_siblings = false;

        SolvingState() = default;
        SolvingState(AutAssignment aut_ass,
                     std::deque<Predicate> predicates_to_process,
                     std::set<Predicate> inclusions,
                     std::set<Predicate> transducers,
                     std::set<Predicate> predicates_not_on_cycle,
                     std::unordered_set<BasicTerm> length_sensitive_vars,
                     std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map,
                     bool has_siblings,
                     Formula disequations = {},
                     std::vector<TermConversion> conversions = {})
                        : aut_ass(aut_ass),
                          substitution_map(substitution_map),
                          inclusions(inclusions),
                          transducers(transducers),
                          predicates_not_on_cycle(predicates_not_on_cycle),
                          predicates_to_process(predicates_to_process),
                          length_sensitive_vars(length_sensitive_vars),
                          postponed_disequations(disequations),
                          conversions(conversions),
                          has_siblings(has_siblings) {}

        /// pushes predicate to the beginning of predicates_to_process but only if it is not in it yet
        void push_front_unique(const Predicate &predicate) {
            if (std::find(predicates_to_process.begin(), predicates_to_process.end(), predicate) == predicates_to_process.end()) {
                predicates_to_process.push_front(predicate);
            }
        }

        /// pushes predicate to the end of predicates_to_process but only if it is not in it yet
        void push_back_unique(const Predicate &predicate) {
            if (std::find(predicates_to_process.begin(), predicates_to_process.end(), predicate) == predicates_to_process.end()) {
                predicates_to_process.push_back(predicate);
            }
        }

        /// pushes predicate either to the end or beginning of predicates_to_process (according to @p to_back) but only if it is not in it yet
        void push_unique(const Predicate &predicate, bool to_back) {
            if (to_back) {
                push_back_unique(predicate);
            } else {
                push_front_unique(predicate);
            }
        }

        /**
         * @brief Pushes predicates that depend on any variable in @p vars_to_check_dependency.
         * 
         * More concretely, it pushes all predicates whose right side (for inclusion) or inputs (for transducers)
         * contain some variable from @p vars_to_check_dependency.
         * It pushes the predicate only if it is not pushed already.
         * 
         * @param to_back whether to push to front or back to predicates_to_process
         */
        void push_dependent_predicates(std::set<BasicTerm> vars_to_check_dependency, bool to_back) {
            for (const Predicate &inclusion : inclusions) {
                if (is_dependent(vars_to_check_dependency, inclusion.get_right_set())) {
                    push_unique(inclusion, to_back);
                }
            }
            for (const Predicate &transducer : transducers) {
                if (is_dependent(vars_to_check_dependency, transducer.get_set_of_param(0))) {
                    push_unique(transducer, to_back);
                }
            }
        }

        /**
         * Pushes predicates that would depend on the given @p predicate in the inclusion graph for processing
         * 
         * More concretely, it pushes all predicates whose right side (for inclusion) or inputs (for transducers)
         * contain some variable from the left side/outputs of the given @p predicate.
         * It pushes the predicate only if it is not pushed already.
         */
        void push_dependent_predicates(const Predicate &predicate, bool to_back) {
            std::set<BasicTerm> vars_to_check_dependency;
            if (predicate.is_equation()) { // inclusion
                vars_to_check_dependency = predicate.get_left_set();
            } else {
                SASSERT(predicate.is_transducer());
                vars_to_check_dependency = predicate.get_set_of_param(1);
            }
            
            push_dependent_predicates(vars_to_check_dependency, to_back);
        }

        /**
         * @brief Adds all transducers that contain length vars on input and are not simple (they do not have one input and one output var, or output is literal) back to processing.
         * 
         * It pushes a transducer only if it is not pushed already.
         * Useful after calling substitute_vars().
         */
        void push_non_simple_transducers_to_processing() {
            for (const Predicate &transducer : transducers) {
                if (contains_length_var(transducer.get_input()) && (transducer.get_input().size() != 1 || transducer.get_output().size() != 1 || transducer.get_output()[0].is_literal())) {
                    push_unique(transducer, false);
                }
            }
        }

        /**
         * Checks whether @p predicate would be on cycle in the inclusion graph (can overapproximate
         * and say that predicate is on cycle even if it is not).
         */
        bool is_predicate_on_cycle(const Predicate &predicate) const {
            return !predicates_not_on_cycle.contains(predicate);
        }

        /**
         * Adds @p predicate to this solving state 
         * 
         * @param predicate Predicate to add
         * @param is_on_cycle Whether the predicate would be on cycle in the inclusion graph (if not sure, set to true)
         */
        void add_predicate(Predicate predicate, bool is_on_cycle = true) {
            if (!is_on_cycle) {
                predicates_not_on_cycle.insert(predicate);
            }
            if (predicate.is_equation()) { // inclusion
                inclusions.insert(std::move(predicate));
            } else {
                SASSERT(predicate.is_transducer());
                transducers.insert(std::move(predicate));
            }
        }

        /**
         * Adds inclusion with sides @p left_side and @p right_side to this solving state (i.e. we will start checking if
         * this inclusion should not be added to inclusion_to_process during the decision procedure).
         * 
         * @param left_side Left side of the new inclusion
         * @param right_side Right side of the new inclusion
         * @param is_on_cycle Whether the inclusion would be on cycle in the inclusion graph (if not sure, set to true)
         * @return The newly added inclusion
         */
        Predicate add_inclusion(std::vector<BasicTerm> left_side, std::vector<BasicTerm> right_side, bool is_on_cycle = true) {
            Predicate new_inclusion = Predicate::create_equation(std::move(left_side), std::move(right_side));
            add_predicate(new_inclusion, is_on_cycle);
            return new_inclusion;
        }

        /**
         * Adds transducer @p trans with ipnut variables in @p input and output variables in @p output to this solving state (i.e. we will start checking if
         * this transducer should not be added to inclusion_to_process during the decision procedure).
         * 
         * @param input Input variables
         * @param ouptut Output variables
         * @param is_on_cycle Whether the transducer would be on cycle in the inclusion graph (if not sure, set to true)
         * @return The newly added transducer predicate
         */
        Predicate add_transducer(std::shared_ptr<mata::nft::Nft> trans, std::vector<BasicTerm> input, std::vector<BasicTerm> output, bool is_on_cycle = true) {
            Predicate new_transducer = Predicate::create_transducer(trans, std::move(input), std::move(output));
            add_predicate(new_transducer, is_on_cycle);
            return new_transducer;
        }

        void remove_predicate(const Predicate &predicate) {
            if (predicate.is_equation()) { // inclusion
                inclusions.erase(predicate);
            } else {
                SASSERT(predicate.is_transducer());
                transducers.erase(predicate);
            }
            predicates_not_on_cycle.erase(predicate);
        }

        /**
         * @brief Get any predicate that has @p var on the right side (for inclusions) or input (for transducers) and save it to @p found_predicate
         * 
         * @return was such a predicate found?
         */
        bool get_predicate_with_var_on_right_side(const BasicTerm& var, Predicate& found_predicate) {
            for (const Predicate& inclusion : inclusions) {
                for (auto const& right_var : inclusion.get_right_set()) {
                    if (right_var == var) {
                        found_predicate = inclusion;
                        return true;
                    }
                }
            }
            for (const Predicate& transducer : transducers) {
                for (auto const& right_var : transducer.get_input()) {
                    if (right_var == var) {
                        found_predicate = transducer;
                        return true;
                    }
                }
            }
            return false;
        }

        /**
         * Check if the vector @p right_side_vars depends on @p left_side_vars, i.e. if some variable
         * (NOT literal) occuring in @p right_side_vars occurs also in @p left_side_vars
         */
        static bool is_dependent(const std::set<BasicTerm> &left_side_vars, const std::set<BasicTerm> &right_side_vars) {
            if (left_side_vars.empty()) {
                return false;
            }
            for (auto const &right_var : right_side_vars) {
                if (right_var.is_variable() && left_side_vars.contains(right_var)) {
                    return true;
                }
            }
            return false;
        }

        /**
         * @brief Substitutes variables from @p vars_to_substitute in predicates using substitution_map and removes unnnecessary nodes
         * 
         * Concretely, substitutes the variables of both sides of inclusions and vars in inputs/outputs of transducers,
         * both in the corresponding sets and in the worklist of predicates to process (if two nodes become equal, keeps only
         * one). Furthermore, it removes inclusions that have both sides equal after substitution.
         */
        void substitute_vars(const std::set<BasicTerm>& vars_to_substitute);

        /**
         * @brief Get under-approximation of the postponed disequations length formula. For each disquation L != R add to 
         * the resulting conjunction a formula |L| != |R|.
         * 
         * @return LenNode Postponed disequations length under-approximation 
         */
        LenNode get_disequations_underapprox_length_formula() const;

        /**
         * @brief Collect vars that are referenced by constraints stored directly in this state
         *        (e.g., postponed disequality-length conjuncts and conversions) and therefore
         *        must not be fully removed from substitution-related structures.
         */
        std::set<BasicTerm> get_vars_referenced_by_state_constraints() const;

        /// @brief Remove vars @p vars_to_remove (except those in @p vars_to_keep ) from the subtitution_map/aut_ass
        void remove_vars(const std::set<BasicTerm>& vars_to_remove, const std::set<BasicTerm>& vars_to_keep);

        /**
         * @brief Get the length constraints for variable @p var
         * 
         * If @p var is substituted by x1x2x3... then it creates
         * |var| = |x1| + |x2| + |x3| + ... otherwise, if @p var
         * has an automaton assigned, it creates length constraint
         * representing all possible lengths of words in the automaton.
         */
        LenNode get_lengths(const BasicTerm& var) const;

        /**
         * @brief Flattens substitution_map so that each var maps only to vars in aut_assignment
         *
         * For example, if we have substitution_map[x] = yz, substitution_map[y] = z, and z is in aut_assignment, then at the end
         * we will have substitution_map[x] = zz and substitution_map[y] = z
         */
        void flatten_substition_map();

        /**
         * @brief Checks if @p var is substituted by empty word
         */
        bool is_var_empty_word(const BasicTerm& var) { return (substitution_map.count(var) > 0 && substitution_map.at(var).empty()); }

        /**
         * @brief Get the vector of variables substituting @p var.
         * 
         * In the case that @p var is not substituted (it is mapped to automaton), we return { @p var }.
         * Useful especially after calling flatten_subtitution_map().
         */
        std::vector<BasicTerm> get_substituted_vars(const BasicTerm& var) const {
            if (substitution_map.count(var) > 0)
                return substitution_map.at(var);
            else
                return std::vector<BasicTerm>{var};
        }

        /**
         * @brief Get the assigned automata of variables in a @p concatenation of variables.
         * 
         * If @p group_non_length is true, we also concatenate automata of the sequences of non-length variables.
         * For example, for xyyxxzyz where y is length variable we will get 6 automata:
         *      - one for first x
         *      - second for first y
         *      - third for second y
         *      - fourth as a concatenation of automata for xxz
         *      - fifth for y
         *      - sixth for z
         * If @p group_non_length was false, we would get 8 automata, one for each variable.
         * 
         * Assumes that each variable in @p concatenation is assigned in aut_ass.
         * 
         * @return a pair where first item is the vector of automata and the second tells us for each automaton which variables were concatenated for it 
         */
        [[nodiscard]] std::pair<std::vector<std::shared_ptr<mata::nfa::Nfa>>,std::vector<std::vector<BasicTerm>>> get_automata_and_division_of_concatenation(const std::vector<BasicTerm>& concatenation, bool group_non_length);

        bool contains_length_var(const std::vector<BasicTerm>& vars) {
            for (const BasicTerm& var : vars) {
                if (length_sensitive_vars.contains(var)) {
                    return true;
                }
            }
            return false;
        }

        /**
         * @brief Processes inclusions from noodlification that are of the form where the right side var should be substituted by left side.
         * 
         * It assumes that left sides contain fresh variables, right sides are not substituted yet and all inclusions hold.
         * This function then takes each inclusions t_1 t_2 ... t_n ⊆ x where x is length var and substitutes substitution_map[x] = t_1 t_2 ... t_n.
         * It is possible that x is on the right side of two inclusions, the first one substitutes it and the second one is added into this SolvingState
         * and also it is added for processing.
         * There can be inclusions t_1 t_2 ... t_n ⊆ x y ... z where there are multiple variables on the right side, but all the variables on the right
         * side must be non-length (these variables are not substituted). Such inclusions are only added to SolvingState and not event for processing.
         * 
         * Furthermore, it updates all other predicates with the substitutions and adds non-simple transducers that are broken by this substitution for processing.
         * 
         * @param inclusions Inclusion to process
         * @param on_cycle Whether the inclusions should be on cycle or not
         * @return std::set<BasicTerm> The set of variables that were substituted
         */
        std::set<BasicTerm> process_substituting_inclusions_from_right(const std::vector<Predicate>& inclusions, bool on_cycle);

        /**
         * @brief Similar to process_substituting_inclusions_from_right but opposite (left var should be substituted by right side).
         * 
         * It assumes that right sides contain fresh variables and that all inclusion hold and are not substituted yet EXCEPT for those
         * that were replaced in process_substituting_inclusions_from_right (it is assumed that process_substituting_inclusions_from_right
         * is always called before this function).
         * Furthermore, all inclusions must be of form x ⊆ t_1 .. t_n where x is substituted even if it is not length var, therefore
         * we will have substitution_map[x] = t_1 t_2 ... t_n.
         * Again, if x was already substituted (either by some other inclusion in this function OR by some inclusion from process_substituting_inclusions_from_right)
         * then the inclusion is added to SolvingState and it is ALWAYS added for processing.
         * 
         * Furthermore, it updates all other predicates with the substitutions and adds non-simple transducers that are broken by the substitution for processing.
         * It also adds all dependent predicates to processing.
         * 
         * @param inclusions Inclusions to process
         * @param on_cycle Whether the inclusions should be on cycle or not
         * @return std::set<BasicTerm> The set of variables that were substituted
         */
        std::set<BasicTerm> process_substituting_inclusions_from_left(const std::vector<Predicate>& inclusions, bool on_cycle);


        /**
         * @brief Adds a new fresh var whose name starts with @p var_prefix, is length-aware if @p is_length is true and assigned to automaton @p nfa.
         * 
         * If @p optimize_literal is true and @p nfa accepts exactly one word, the resulting variable will be literal corresponding to this word instead
         * and @p var_prefix and @p is_length are ignored. This assumes that @p nfa is trimmed and reduced (or determinized and minimized), otherwise
         * the test for @p nfa to aaccept one word can return false even if it accepts one word.
         * 
         * @return The newly created variable. 
         */
        BasicTerm add_fresh_var(std::shared_ptr<mata::nfa::Nfa> nfa, std::string var_prefix, bool is_length, bool optimize_literal);

        /**
         * @brief Replaces the dummy symbol in transducers by all symbols from @p replacements
         * 
         * If @p replacements is empty, it only deletes dummy symbols from transducers.
         */
        void replace_dummy_symbol_in_transducers_with(std::set<mata::Symbol> replacements);

        /**
         * @brief Replace disequality L != R with equalities while updating this solving state.
         *
         * The method updates this state (automata assignment and length-sensitive vars),
         * It stores created disequality-related length constraints into
         * disequations_len_formula_conjuncts and stores needed to_code
         * conversions in this state's conversions.
         *
         * @param diseq Disequality to replace.
         * @return Vector with created equalities.
         */
        std::vector<Predicate> replace_disequality(const Predicate& diseq);

        /**
         * @brief Expand postponed disequations into equations and enqueue them.
         *
         * Each postponed disequation is replaced by equations via replace_disequality().
         * The resulting equations are added to this state and also pushed for processing.
         */
        void translate_postponed_disequations_to_equations();

        /**
         * @brief Run lightweight preprocessing focused on postponed disequations and
         *        detect whether they are immediately unsatisfiable in this state.
         *
         * This method runs a local FormulaPreprocessor over `postponed_disequations`
         * using the current `aut_ass`, `length_sensitive_vars` and any conversion
         * variables. If the preprocessor detects immediate unsatisfiability it
         * returns `l_false` and does not change this state. Otherwise the method
         * persists the preprocessor's simplified disequations and the refined
         * automata/length information back into this `SolvingState` (it updates
         * `postponed_disequations`, `aut_ass` and inserts any discovered length
         * variables into `length_sensitive_vars`) and returns `l_true`.
         *
         * @return `l_false` iff preprocessing proves some disequation branch unsat,
         *         `l_true` otherwise.
         */
        lbool preprocess_disequations_for_unsat(const theory_str_noodler_params& params);

        std::string DOT_name = "init";
        std::string set_new_DOT_name() {
            static size_t DOT_name_counter = 0;
            DOT_name = std::string("SolvingState") + std::to_string(DOT_name_counter);
            ++DOT_name_counter;
            return DOT_name;
        }
        std::string print_to_DOT() const;
    };
}

#endif
