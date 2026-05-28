#ifndef _NOODLER_DECISION_PROCEDURE_H_
#define _NOODLER_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>
#include <functional>

#include "params/theory_str_noodler_params.h"
#include "formula.h"
#include "solving_state.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "formula_preprocess.h"
#include "ca_str_constr.h"
#include "conversion_handler.h"

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

        virtual ~AbstractDecisionProcedure()=default;
    };

    class DecisionProcedure : public AbstractDecisionProcedure {
    protected:
        // counter of noodlifications
        unsigned noodlification_no = 0;

        // a deque containing states of decision procedure, each of them can lead to a solution
        std::deque<SolvingState> worklist;
        // if a solving state has nothing to process, it can lead to solution, we keep these solving states here instead of worklist so we can process them immediately
        std::vector<SolvingState> possible_solutions;

        /// State of a found satisfiable solution set when one is computed using
        ///  compute_next_solution() or after preprocess()
        SolvingState solution;

        // initial length vars, formula, automata assignment and substitution map, can be updated by preprocessing, used for initializing the decision procedure
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        Formula formula;
        AutAssignment init_aut_ass;
        std::unordered_map<BasicTerm, std::vector<BasicTerm>> init_substitution_map;
        ConversionHandler conversion_handler;
        ast_manager& m;

        // length vars that occur as input/output of some transducer formula
        std::set<BasicTerm> length_vars_with_transducers;

        // disequations that are supposed to be solved after a stable solution is found
        Formula disequations;
        // not contains that are supposed to be solved after a stable solution is found
        Formula not_contains_tag;

        // the length formula from preprocessing, get_lengths should create conjunct with it
        LenNode preprocessing_len_formula = LenNode(LenFormulaType::TRUE,{});

        // remembers whether the input formula passed to init_computation() contained any disequation
        bool input_contains_disequations = false;

        std::set<BasicTerm> code_subst_vars_handled_by_parikh;

        const theory_str_noodler_params& m_params;

        /// @brief We save here all string variables that exist before the decision procedure is run (useful for removing variables created in decision procedure, @sa SolvingState::remove_vars())
        std::set<BasicTerm> initial_variables;

        /// @brief Sets initial_variables by collecting all variables from @p f, @p state (aut_ass, length_sensitive_vars, conversions), and inclusions_from_preprocessing.
        void set_initial_variables(const Formula& f, const SolvingState& state);

        void process_inclusion(const Predicate& inclusion_to_process, SolvingState& solving_state);
        void process_transducer(const Predicate& transducer_to_process, SolvingState& solving_state);

        bool is_worklist_empty() {
            return (worklist.empty() && possible_solutions.empty());
        }

        void push_to_worklist(SolvingState solving_state, bool to_back) {
            std::string old_DOT_name = solving_state.DOT_name;
            solving_state.set_new_DOT_name();
            STRACE(str_noodle_dot, tout << solving_state.print_to_DOT() << std::endl << old_DOT_name << " -> " << solving_state.DOT_name << ";\n");
            if (solving_state.predicates_to_process.empty()) {
                possible_solutions.push_back(std::move(solving_state));
            } else {
                if (to_back) {
                    worklist.push_back(std::move(solving_state));
                } else {
                    worklist.push_front(std::move(solving_state));
                }
            }
        }

        unsigned num_of_popped_elements = 0;
        SolvingState pop_from_worklist() {
            SolvingState element_to_process;
            if (!possible_solutions.empty()) {
                element_to_process = std::move(possible_solutions.back());
                possible_solutions.pop_back();
            } else {
                element_to_process = std::move(worklist.front());
                worklist.pop_front();
            }
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
         * Formula containing all not_contains predicate (nothing else)
         */
        Formula not_contains{};

        ////////////////////////////////////////////////////////////////
        //////////////////// FOR MODEL GENERATION //////////////////////
        ////////////////////////////////////////////////////////////////

        // inclusions that resulted from preprocessing, we use them to generate model (we can pretend that they were all already refined)
        std::vector<Predicate> inclusions_from_preprocessing;

        /// Keeps transducer with parikh information needed to compute model
        struct TransducerParikhInformation {
            mata::nft::Nft nft; // the transducer
            std::vector<BasicTerm> vars_on_tapes; // each tape of the transducer represent some length variable
            std::map<mata::nft::State, BasicTerm> state_to_gamma_init; // states of the transducer are mapped to parikh variable representing that the solution starts in the given state
            std::map<mata::nft::Transition, BasicTerm> transition_to_var; // transitions of the transducer are mapped to parikh variables representing how often we need to pass it (vars can be shared)

            /// Get all parikh vars connected with the transducer
            std::set<BasicTerm> get_all_parikh_vars() const {
                std::set<BasicTerm> parikh_vars;
                for (const auto& [_state, var] : state_to_gamma_init) {
                    parikh_vars.insert(var);
                }
                for (const auto& [_trans, var] : transition_to_var) {
                    parikh_vars.insert(var);
                }
                return parikh_vars;
            }

            /// Given an @p arith_model (maps gamma_init vars to numbers), we get all states that be an initial state (their gamma_init var is equal to 1)
            std::set<mata::nft::State> get_potentional_initial_states(const std::map<BasicTerm,rational>& arith_model) const {
                std::set<mata::nft::State> potentional_initial_states;
                for (const auto& [state, var] : state_to_gamma_init) {
                    if (arith_model.at(var) == 1) {
                        potentional_initial_states.insert(state);
                    }
                }
                return potentional_initial_states;
            }

            /// Given an @p arith_model (maps transition vars to numbers), we return a mapping that maps transitions to a (possibly shared) number representing how many times a transition need to be taken
            std::map<mata::nft::Transition,std::shared_ptr<unsigned>> get_transition_to_value(const std::map<BasicTerm,rational>& arith_model) const {
                std::map<BasicTerm, std::shared_ptr<unsigned>> var_to_value;
                std::map<mata::nft::Transition,std::shared_ptr<unsigned>> result;
                for (const auto& [trans, var] : transition_to_var) {
                    if (!var_to_value.contains(var)) {
                        var_to_value[var] = std::make_shared<unsigned>(arith_model.at(var).get_unsigned());
                    }
                    result[trans] = var_to_value.at(var);
                }
                return result;
            }

            /// Replaces transitions with dummy symbol in @c nft and @c transition_to_var by new transitions with the symbols from @p set_of_symbols_to_replace_dummy_symbol_with and maps them to the same var
            void replace_dummy_symbol(const std::set<mata::Symbol>& set_of_symbols_to_replace_dummy_symbol_with) {
                if (set_of_symbols_to_replace_dummy_symbol_with.empty()) { return; }
                if (set_of_symbols_to_replace_dummy_symbol_with.size() > 1) {
                    // TODO fix this? if we had more dummy symbols, for code-points vars, we can only have transitions with the correct code-point value
                    util::throw_error("We cannot replace dummy symbol by more than one symbol in transducers yet");
                }
                util::replace_dummy_symbol_in_transducer_with(nft, set_of_symbols_to_replace_dummy_symbol_with);
                std::vector<std::pair<mata::nft::Transition, BasicTerm>> new_elements;
                for (auto it = transition_to_var.begin(); it != transition_to_var.end();) {
                    if (it->first.symbol == util::get_dummy_symbol()) {
                        for (mata::Symbol s : set_of_symbols_to_replace_dummy_symbol_with) {
                            new_elements.emplace_back(mata::nft::Transition{it->first.source, s, it->first.target}, it->second);
                        }
                        it = transition_to_var.erase(it);
                    } else {
                        ++it;
                    }
                }
                transition_to_var.insert(new_elements.begin(), new_elements.end());
            }
        };

        /// Transducers that combine multiple length variables
        std::vector<TransducerParikhInformation> transducers_with_parikh_information;
        
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
             std::vector<TermConversion> conversions,
             ast_manager& m
        ) : init_length_sensitive_vars(init_length_sensitive_vars),
            formula(formula),
            init_aut_ass(init_aut_ass),
            conversion_handler(conversions, par.m_underapprox_length),
            m(m),
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
        /**
         * Same as compute_next_solution, but checks length constraints while running
         * to potentionally skip processing some noodles which are found unsat.
         *
         * @param check_lens length check function; the boolean argument indicates whether
         *                   the formula should be added to the blocking formula (true) or
         *                   only satisfiability should be checked without blocking (false).
         *
         * @return first: True if there is a satisfiable element in the worklist.
         *         second: if any solving states were skipped (the length check was unsat)
         */
        std::pair<lbool, bool> compute_next_solution_with_len_checks(
            std::function<lbool(bool)> check_lens
        );

        LenNode get_initial_lengths(bool all_vars = false) override;

        std::pair<LenNode, LenNodePrecision> get_lengths() override;

        std::vector<BasicTerm> get_len_vars_for_model(const BasicTerm& str_var) override;

        zstring get_model(BasicTerm var, const std::map<BasicTerm,rational>& arith_model) override;
    };
}

#endif
