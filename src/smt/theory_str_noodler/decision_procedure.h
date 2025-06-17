#ifndef _NOODLER_DECISION_PROCEDURE_H_
#define _NOODLER_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>
#include <functional>

#include "params/theory_str_noodler_params.h"
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
         * @param arith_model Returns either the length of a str variable or the value of the int variable in the model
         * @return the model for @p var 
         */
        virtual zstring get_model(BasicTerm var, const std::map<BasicTerm,rational>& arith_model) {
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
        // set of transducers which we want to smiplify so that we only have at most one var in input and at most one var in output
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
                     std::set<Predicate> transducers,
                     std::set<Predicate> predicates_not_on_cycle,
                     std::unordered_set<BasicTerm> length_sensitive_vars,
                     std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map)
                        : aut_ass(aut_ass),
                          substitution_map(substitution_map),
                          inclusions(inclusions),
                          transducers(transducers),
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
         * @brief Adds all transducers that are not simple (that do not have one input and one output var) back to processing.
         * 
         * It pushes a transducer only if it is not pushed already.
         * Useful after calling substitute_vars().
         */
        void push_non_simple_transducers_to_processing() {
            for (const Predicate &transducer : transducers) {
                if (transducer.get_input().size() != 1 || transducer.get_output().size() != 1 || transducer.get_input()[0].is_literal() || transducer.get_input()[1].is_literal()) {
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

        // substitutes vars and merge same nodes + delete copies of the merged nodes from the predicates_to_process (and also inclusions that have same sides are deleted)

        /**
         * @brief Substitutes variables from @p vars_to_substitute in predicates using substitution_map and removes unnnecessary nodes
         * 
         * Concretely, substitutes the variables of both sides of inclusions and vars in inputs/outputs of transducers,
         * both in the corresponding sets and in the worklist of predicates to process (if two nodes become equal, keeps only
         * one). Furthermore, it removes inclusions that have both sides equal after substitution.
         */
        void substitute_vars(const std::set<BasicTerm>& vars_to_substitute);

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
         * This function then takes each inclusions t_1 t_2 ... t_n ⊆ x where x is length var  and substitutes substitution_map[x] = t_1 t_2 ... t_n.
         * It is possible that x is on the right side of two inclusions, the first one substitutes it and the second one is added into this SolvingState
         * and also it is added for processing.
         * There can be inclusions t_1 t_2 ... t_n ⊆ x y ... z where there are multiple variables on the right side, but all the variables on the right
         * side must be non-length (these variables are not substituted). Such inclusions are only added to SolvingState and not event for processing.
         * 
         * Furthermore, it updates all other predicates with the substitutions and adds non-simple transducers that are broken by this substitution for processing.
         * 
         * @param inclusions Inclusion to process
         * @param on_cycle Whether the inclusions should be on cycle or not
         */
        void process_substituting_inclusions_from_right(const std::vector<Predicate>& inclusions, bool on_cycle);

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
         */
        void process_substituting_inclusions_from_left(const std::vector<Predicate>& inclusions, bool on_cycle);


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

        std::string DOT_name = "init";
        std::string set_new_DOT_name() {
            static size_t DOT_name_counter = 0;
            DOT_name = std::string("SolvingState") + std::to_string(DOT_name_counter);
            ++DOT_name_counter;
            return DOT_name;
        }
        std::string print_to_DOT() const;
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

        // length vars that occur as input/output of some transducer formula
        std::set<BasicTerm> length_vars_with_transducers;

        // disequations that are supposed to be solved after a stable solution is found
        Formula disequations;
        // not contains that are supposed to be solved after a stable solution is found
        Formula not_contains_tag;

        // the length formula from preprocessing, get_lengths should create conjunct with it
        LenNode preprocessing_len_formula = LenNode(LenFormulaType::TRUE,{});
        // keeps the length formulas from replace_disequality(), they need to hold for solution to be satisfiable (get_lengths should create conjunct from them)
        std::vector<LenNode> disequations_len_formula_conjuncts;

        // see get_vars_substituted_in_conversions() for what these sets mean (used in get_length() and in model generation)
        std::set<BasicTerm> code_subst_vars;
        std::set<BasicTerm> int_subst_vars;

        std::set<BasicTerm> code_subst_vars_handled_by_parikh;

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

        void push_to_worklist(SolvingState solving_state, bool to_back) {
            std::string old_DOT_name = solving_state.DOT_name;
            solving_state.set_new_DOT_name();
            STRACE(str_noodle_dot, tout << solving_state.print_to_DOT() << std::endl << old_DOT_name << " -> " << solving_state.DOT_name << ";\n");
            if (to_back) {
                worklist.push_back(std::move(solving_state));
            } else {
                worklist.push_front(std::move(solving_state));
            }
        }

        unsigned num_of_popped_elements = 0;
        SolvingState pop_from_worklist() {
            SolvingState element_to_process = std::move(worklist.front());
            worklist.pop_front();
            STRACE(str_noodle_dot, tout << element_to_process.DOT_name << " -> " << element_to_process.DOT_name << " [penwidth=0,dir=none,label=" << num_of_popped_elements << "];\n";);
            ++num_of_popped_elements;
            return element_to_process;
        }

        /**
         * @brief Get the (parikh) formula encoding lengths and code-point conversions of variables in transducers
         * 
         * Assumes that code_subst_vars and int_subst_vars are computed already.
         * It also updates length_vars_with_transducers and code_subst_vars_handled_by_parikh
         */
        LenNode get_formula_for_transducers();

        /**
         * @brief Get the formula encoding lengths of variables based on solution
         * It ignores the length vars that are in tranducers, as formula for these
         * should be in get_formula_for_transducers(). For the normal length
         * vars it either creates formula |x| = |x_1| + ... + |x_n| if
         *   solution.subtitution_map[x] = x_1 ... x_n
         * or it creates the formula from lasso construction of automaton
         *   solution.aut_ass[x]
         * 
         */
        LenNode get_formula_for_len_vars();

        /**
         * @brief Gets the formula encoding to_code/from_code/to_int/from_int conversions
         * 
         * Assumes that code_subst_vars and int_subst_vars are computed already.
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
         * If s is not substituted (it maps to automaton), then it is added to code_subst_vars instead.
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

        std::vector<std::pair<mata::nft::Nft,std::vector<BasicTerm>>> transducers_with_vars_on_tapes;
        
        bool is_model_initialized = false;
        /**
         * @brief Initialize model from solution
         * 
         * @param arith_model Returns either the length of a str variable or the value of the int variable in the model
         */
        void init_model(const std::map<BasicTerm,rational>& arith_model);

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
            SASSERT(!model_of_var.contains(var) || model_of_var.at(var) == computed_model);
            model_of_var[var] = computed_model;
            if (solution.aut_ass.contains(var)) {
                solution.aut_ass[var] = std::make_shared<mata::nfa::Nfa>(AutAssignment::create_word_nfa(computed_model));
            }
            STRACE(str_model_res, tout << "Model for " << var << ": " << computed_model << std::endl);
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

        zstring get_model(BasicTerm var, const std::map<BasicTerm,rational>& arith_model) override;

        /**
         * @brief Get the length sensitive variables
         */
        const std::unordered_set<BasicTerm>& get_init_length_sensitive_vars() const override {
            return this->init_length_sensitive_vars;
        }
    };
}

#endif
