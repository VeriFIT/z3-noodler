#ifndef _NOODLER_DECISION_PROCEDURE_H_
#define _NOODLER_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>
#include <functional>

#include "smt/params/theory_str_noodler_params.h"
#include "formula.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "formula_preprocess.h"
#include "ca_str_constr.h"

namespace smt::noodler {

    /**
     * @brief Preprocess options
     */
    enum struct PreprocessType {
        PLAIN,
        UNDERAPPROX
    };

    /**
     * @brief Abstract decision procedure. Defines interface for decision
     * procedures to be used within z3.
     */
    class AbstractDecisionProcedure {
    public:

        /**
         * @brief Initialize the computation (supposed to be called after preprocess)
         */
        virtual void init_computation() {
            throw std::runtime_error("Unimplemented");
        }

        /**
         * Do some preprocessing (can be called only before init_computation). Can
         * potentionally already solve the formula.
         * 
         * @param opt The type of preprocessing
         * @param len_eq_vars Equivalence class holding variables with the same length
         * @return lbool representing whether preprocessing solved the formula
         */
        virtual lbool preprocess(PreprocessType opt = PreprocessType::PLAIN, const BasicTermEqiv &len_eq_vars = {}) {
            throw std::runtime_error("preprocess unimplemented");
        }

        /**
         * Compute next solution and save the satisfiable solution.
         * @return True if there is a satisfiable element in the worklist.
         */
        virtual lbool compute_next_solution() {
            throw std::runtime_error("Not implemented");
        }

        /**
         * Get length constraints for the initial assignment (possibly modified by preprocessing).
         * If it is unsatisfiable, it means that there is no possible solution.
         */
        virtual LenNode get_initial_lengths(bool all_vars = false) {
            throw std::runtime_error("Unimplemented");
        }

        /**
         * Get length constraints for the solution. Assumes that we have some solution from
         * running compute_next_solution(), the solution is actually solution if the length
         * constraints hold.
         * 
         * The second element of the resulting pair marks whether the lennode is precise or
         * over/underapproximation.
         */
        virtual std::pair<LenNode, LenNodePrecision> get_lengths() {
            throw std::runtime_error("Unimplemented");
        }

        /**
         * @brief Get a vector of variables whose lengths are needed for generating the model of @p str_var
         */
        virtual std::vector<BasicTerm> get_len_vars_for_model(const BasicTerm& str_var) {
            throw std::runtime_error("Unimplemented");
        }

        /**
         * @brief Get string model for the string variable @p var
         * 
         * @param get_arith_model_of_var Returns either the length of a str variable or the value of the int variable in the model
         * @return the model for @p var 
         */
        virtual zstring get_model(BasicTerm var, const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
            throw std::runtime_error("Unimplemented");
        }

        /**
         * @brief Get the length sensitive variables
         */
        virtual const std::unordered_set<BasicTerm>& get_init_length_sensitive_vars() const {
            throw std::runtime_error("Unimplemented");
        }

        virtual ~AbstractDecisionProcedure()=default;
    };

    /// A state of decision procedure that can lead to a solution
    struct SolvingState {
        // aut_ass[x] assigns variable x to some automaton while substitution_map[x] maps variable x to
        // the concatenation of variables for which x was substituted (i.e. its automaton is concatenation
        // of the automata from these variables). Each variable is either assigned in aut_ass or
        // substituted in substitution_map, but not both!
        AutAssignment aut_ass;
        std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;

        // set of inclusions (i.e. Predicate must be of type equations which we pretend is an inclusion) where we are trying to find aut_ass + substitution_map such that they hold
        std::set<Predicate> inclusions;
        // set of transducers which we want to smiplify so that we only have one var on input and one var on output
        std::set<Predicate> transducers;

        // set of inclusions/transducers from the previous sets that for sure are not on cycle in the inclusion graph
        // that would be generated from inclusions
        std::set<Predicate> predicates_not_on_cycle;

        // contains inclusions/transducers we need to process (for inclusions we want them to hold under aut_ass and substitution_map, for transducers we want to simplify them)
        std::deque<Predicate> predicates_to_process;

        // the variables that have length constraint on them in the rest of formula
        std::unordered_set<BasicTerm> length_sensitive_vars;


        SolvingState() = default;
        SolvingState(AutAssignment aut_ass,
                     std::deque<Predicate> predicates_to_process,
                     std::set<Predicate> inclusions,
                     std::set<Predicate> predicates_not_on_cycle,
                     std::unordered_set<BasicTerm> length_sensitive_vars,
                     std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map)
                        : aut_ass(aut_ass),
                          substitution_map(substitution_map),
                          inclusions(inclusions),
                          predicates_not_on_cycle(predicates_not_on_cycle),
                          predicates_to_process(predicates_to_process),
                          length_sensitive_vars(length_sensitive_vars) {}

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
         * Checks whether @p predicate would be on cycle in the inclusion graph (can overapproximate
         * and say that predicate is on cycle even if it is not).
         */
        bool is_inclusion_on_cycle(const Predicate &predicate) {
            return (predicates_not_on_cycle.count(predicate) == 0);
        }

        /**
         * Adds @p predicate to this solving state 
         * 
         * @param predicate Predicate to add
         * @param is_on_cycle Whether the predicate would be on cycle in the inclusion graph (if not sure, set to true)
         */
        void add_predicate(const Predicate &predicate, bool is_on_cycle = true) {
            if (predicate.get_type() == PredicateType::Equation) {
                inclusions.insert(predicate);
            } else {
                SASSERT(predicate.get_type() == PredicateType::Transducer);
                transducers.insert(predicate);
            }
            if (!is_on_cycle) {
                predicates_not_on_cycle.insert(predicate);
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
        Predicate add_inclusion(const std::vector<BasicTerm> &left_side, const std::vector<BasicTerm> &right_side, bool is_on_cycle = true) {
            Predicate new_inclusion{PredicateType::Equation, std::vector<std::vector<BasicTerm>> {left_side, right_side}};
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
        Predicate add_transducer(std::shared_ptr<mata::nft::Nft> trans, const std::vector<BasicTerm> &input, const std::vector<BasicTerm> &output, bool is_on_cycle = true) {
            Predicate new_transducer{PredicateType::Transducer, std::vector<std::vector<BasicTerm>> {input, output}, trans};
            add_predicate(new_transducer, is_on_cycle);
            return new_transducer;
        }

        void remove_predicate(const Predicate &predicate) {
            if (predicate.get_type() == PredicateType::Equation) {
                inclusions.erase(predicate);
            } else {
                SASSERT(predicate.get_type() == PredicateType::Transducer);
                transducers.erase(predicate);
            }
            predicates_not_on_cycle.erase(predicate);
        }

        /**
         * Returns the vector of inclusions that would depend on the given @p inclusion in the inclusion graph.
         * That this all inclusions whose right side contain some variable from the left side of the given @p inclusion.
         * 
         * @param inclusion Inclusion whose dependencies we are looking for
         * @return The set of inclusions that depend on @p inclusion
         */
        std::vector<Predicate> get_dependent_inclusions(const Predicate &inclusion) {
            std::vector<Predicate> dependent_inclusions;
            auto left_vars_set = inclusion.get_left_set();
            for (const Predicate &other_inclusion : inclusions) {
                if (is_dependent(left_vars_set, other_inclusion.get_right_set())) {
                    dependent_inclusions.push_back(other_inclusion);
                }
            }
            return dependent_inclusions;
        }

        /**
         * @brief Get any inclusion that has @p var on the right side and save it to @p found inclusion
         * 
         * @return was such an inclusion found?
         */
        bool get_inclusion_with_var_on_right_side(const BasicTerm& var, Predicate& found_inclusion) {
            for (const Predicate &inclusion : inclusions) {
                for (auto const &right_var : inclusion.get_right_set()) {
                    if (right_var == var) {
                        found_inclusion = inclusion;
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

        // substitutes vars and merge same nodes + delete copies of the merged nodes from the predicates_to_process (and also nodes that have same sides are deleted)
        void substitute_vars(std::unordered_map<BasicTerm, std::vector<BasicTerm>> &substitution_map);

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
        std::vector<BasicTerm> get_substituted_vars(const BasicTerm& var) {
            if (substitution_map.count(var) > 0)
                return substitution_map.at(var);
            else
                return std::vector<BasicTerm>{var};
        }
    };

    class DecisionProcedure : public AbstractDecisionProcedure {
    protected:
        // counter of noodlifications
        unsigned noodlification_no = 0;

        // a deque containing states of decision procedure, each of them can lead to a solution
        std::deque<SolvingState> worklist;

        /// State of a found satisfiable solution set when one is computed using
        ///  compute_next_solution() or after preprocess()
        SolvingState solution;

        // initial length vars, formula, automata assignment and substitution map, can be updated by preprocessing, used for initializing the decision procedure
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        Formula formula;
        AutAssignment init_aut_ass;
        std::unordered_map<BasicTerm, std::vector<BasicTerm>> init_substitution_map;
        // contains to/from_code/int conversions
        std::vector<TermConversion> conversions;

        // disequations that are supposed to be solved after a stable solution is found
        Formula disequations;
        // not contains that are supposed to be solved after a stable solution is found
        Formula not_contains_tag;

        // the length formula from preprocessing, get_lengths should create conjunct with it
        LenNode preprocessing_len_formula = LenNode(LenFormulaType::TRUE,{});
        // keeps the length formulas from replace_disequality(), they need to hold for solution to be satisfiable (get_lengths should create conjunct from them)
        std::vector<LenNode> disequations_len_formula_conjuncts;

        const theory_str_noodler_params& m_params;

        /**
         * @brief Replace disequality L != R with equalities and a length constraint saved in disequations_len_formula_conjuncts.
         * 
         * @param diseq Disequality to replace
         * @return Vector with created equalities
         */
        std::vector<Predicate> replace_disequality(Predicate diseq);

        void process_inclusion(const Predicate& inclusion_to_process, SolvingState& solving_state);
        void process_transducer(const Predicate& transducer_to_process, SolvingState& solving_state);

        /**
         * @brief Gets the formula encoding to_code/from_code/to_int/from_int conversions
         */
        std::pair<LenNode, LenNodePrecision> get_formula_for_conversions();

        /**
         * @brief Initialize disquation for TagAut-based handling. Assumed to be called during 
         * the decision procedure initialization.
         */
        void init_ca_diseq(const Predicate& diseq);

        /**
         * @brief Gets the formula encoding handling disequations using TAG aut
         */
        LenNode get_formula_for_ca_diseqs();

        /**
         * @brief Gets the formula encoding handling not contains using TAG aut
         */
        std::pair<LenNode, LenNodePrecision> get_formula_for_not_contains();

        /**
         * Returns the code var version of @p var used to encode to_code/from_code in get_formula_for_conversions
         */
        BasicTerm code_version_of(const BasicTerm& var) {
            return BasicTerm(BasicTermType::Variable, var.get_name() + "!to_code");
        }

        /**
         * Returns the int var version of @p var used to encode to_int/from_int in get_formula_for_conversions
         */
        BasicTerm int_version_of(const BasicTerm& var) {
            return BasicTerm(BasicTermType::Variable, var.get_name() + "!to_int");
        }

        /**
         * Gets the pair of variable sets (code_subst_vars, int_subst_vars) where code_subst_vars
         * contains all vars s_i, such that there exists "c = to_code(s)" or "s = from_code(c)"
         * in conversions where s is substituted by s_1 ... s_i ... s_n in the solution.
         * The set int_subst_vars is defined similarly, but for "i = to_int(s)" or "s = from_int(i)"
         * conversions.
         */
        std::pair<std::set<BasicTerm>,std::set<BasicTerm>> get_vars_substituted_in_conversions();

        /**
         * @brief Get the formula for to_code/from_code substituting variables
         * 
         * It basically succinctly encodes `code_version_of(s) = to_code(w_s)` for each s in @p code_subst_vars and w_c \in solution.aut_ass.at(s) while
         * keeping the correspondence between |s| and |w_s|
         */
        LenNode get_formula_for_code_subst_vars(const std::set<BasicTerm>& code_subst_vars);

        /**
         * @brief Get the formula encoding that arithmetic variable @p var is any of the numbers encoded by some interval word from @p interval_words
         */
        LenNode encode_interval_words(const BasicTerm& var, const std::vector<interval_word>& interval_words);

        /**
         * @brief Get the formula for to_int/from_int substituting variables
         * 
         * It basically succinctly encodes `int_version_of(s) = to_int(w_s)` for each s in @p int_subst_vars and w_s \in solution.aut_ass.at(s) while
         * keeping the correspondence between |s|, |w_s|, and code_version_of(s).
         * Note that for w_s = "", we do not put int_version_of(s) = -1 but we instead force that it is NOT -1 (so that get_formula_for_int_conversion
         * can handle this case correctly).
         * 
         * @param int_subst_vars to_int/from_int substituting variables for which we create formulae
         * @param code_subst_vars to_code/from_code substituting variables (needed only if int_subst_vars and code_subst_vars are not disjoint)
         * @param[out] int_subst_vars_to_possible_valid_lengths will map each var from int_subst_vars into a vector of lengths of all possible numbers for var (also 0 if there is empty string)
         * @param underapproximating_length For the case that we need to underapproximate, this variable sets the length up to which we underapproximate
         * @return The formula + precision of the formula (can be precise or underapproximation)
         */
        std::pair<LenNode, LenNodePrecision> get_formula_for_int_subst_vars(const std::set<BasicTerm>& int_subst_vars, const std::set<BasicTerm>& code_subst_vars, std::map<BasicTerm,std::vector<unsigned>>& int_subst_vars_to_possible_valid_lengths);

        /**
         * @brief Get the formula encoding to_code/from_code conversion
         */
        LenNode get_formula_for_code_conversion(const TermConversion& conv);

        /**
         * @brief Get the formula encoding to_int/from_int conversion
         * 
         * @param int_subst_vars_to_possible_valid_lengths maps each var from int_subst_vars into a vector of lengths of all possible numbers for var (also 0 if there is empty string)
         */
        LenNode get_formula_for_int_conversion(const TermConversion& conv, const std::map<BasicTerm,std::vector<unsigned>>& int_subst_vars_to_possible_valid_lengths);

        /**
         * Formula containing all not_contains predicate (nothing else)
         */
        Formula not_contains{};

        ////////////////////////////////////////////////////////////////
        //////////////////// FOR MODEL GENERATION //////////////////////
        ////////////////////////////////////////////////////////////////

        // inclusions that resulted from preprocessing, we use them to generate model (we can pretend that they were all already refined)
        std::vector<Predicate> inclusions_from_preprocessing;

        // see get_vars_substituted_in_conversions() for what these sets mean, we save them so that we can use them in model generation
        std::set<BasicTerm> code_subst_vars;
        std::set<BasicTerm> int_subst_vars;
        
        bool is_model_initialized = false;
        /**
         * @brief Initialize model from solution
         * 
         * @param get_arith_model_of_var Returns either the length of a str variable or the value of the int variable in the model
         */
        void init_model(const std::function<rational(BasicTerm)>& get_arith_model_of_var);

        // keeps already computed models
        std::map<BasicTerm,zstring> model_of_var;
        // vars for which we already called get_model() at least once (used for cyclicity detection, will be removed when get_model() can handle cycles in inclusions)
        std::set<BasicTerm> vars_whose_model_we_are_computing;

        /**
         * @brief Update the model and its language in the solution of the variable @p var to @p computed_model
         * 
         * @param var The variable whose lang/model should be updated
         * @param computed_model The model computed for @p var
         * @return the computed model 
         */
        zstring update_model_and_aut_ass(BasicTerm var, zstring computed_model) {
            model_of_var[var] = computed_model;
            if (solution.aut_ass.contains(var)) {
                solution.aut_ass[var] = std::make_shared<mata::nfa::Nfa>(AutAssignment::create_word_nfa(computed_model));
            }
            STRACE("str-model-res", tout << "Model for " << var << ": " << computed_model << std::endl);
            return computed_model;
        };

    public:

        /**
         * Initialize a new decision procedure that can solve word equations
         * (equalities of concatenations of string variables) with regular constraints
         * (variables belong to some regular language represented by automaton) while
         * keeping the length dependencies between variables (for the variables that
         * occur in some length constraint in the rest of the formula).
         * 
         * @param formula encodes the string formula (including equations, not contains)
         * @param init_aut_ass gives regular constraints (maps each variable from @p equalities to some NFA), assumes all NFAs are non-empty
         * @param init_length_sensitive_vars the variables that occur in length constraints in the rest of formula
         * @param par Parameters for Noodler string theory.
         * @param conversions Contains to/from_code/int conversions (x,y,conversion) where x = conversion(y)
         */
        DecisionProcedure(
             Formula formula, AutAssignment init_aut_ass,
             std::unordered_set<BasicTerm> init_length_sensitive_vars,
             const theory_str_noodler_params &par,
             std::vector<TermConversion> conversions
        ) : init_length_sensitive_vars(init_length_sensitive_vars),
            formula(formula),
            init_aut_ass(init_aut_ass),
            conversions(conversions),
            m_params(par) {
            
        }
        
        /**
         * Do some preprocessing (can be called only before init_computation). Can
         * potentionally already solve the formula. If it solves the formula as sat
         * it is still needed to check for lengths.
         * 
         * @param opt The type of preprocessing
         * @param len_eq_vars Equivalence class holding variables with the same length
         * @return lbool representing whether preprocessing solved the formula
         */
        lbool preprocess(PreprocessType opt = PreprocessType::PLAIN, const BasicTermEqiv &len_eq_vars = {}) override;

        void init_computation() override;
        lbool compute_next_solution() override;

        LenNode get_initial_lengths(bool all_vars = false) override;

        std::pair<LenNode, LenNodePrecision> get_lengths() override;

        std::vector<BasicTerm> get_len_vars_for_model(const BasicTerm& str_var) override;

        zstring get_model(BasicTerm var, const std::function<rational(BasicTerm)>& get_arith_model_of_var) override;

        /**
         * @brief Get the length sensitive variables
         */
        const std::unordered_set<BasicTerm>& get_init_length_sensitive_vars() const override {
            return this->init_length_sensitive_vars;
        }
    };
}

#endif
