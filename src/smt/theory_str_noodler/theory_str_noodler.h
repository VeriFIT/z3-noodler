/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3.
Eternal glory to Yu-Fang.
*/

#ifndef _THEORY_STR_NOODLER_H_
#define _THEORY_STR_NOODLER_H_

#include <functional>
#include <list>
#include <set>
#include <stack>
#include <map>
#include <memory>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "aut_assignment.h"
#include "formula.h"
#include "inclusion_graph.h"
#include "decision_procedure.h"
#include "expr_solver.h"
#include "quant_lia_solver.h"
#include "util.h"
#include "expr_cases.h"
#include "regex.h"
#include "var_union_find.h"
#include "nielsen_decision_procedure.h"
#include "counter_automaton.h"
#include "length_decision_procedure.h"
#include "unary_decision_procedure.h"

#include "smt/params/smt_params.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_noodler_params.h"
#include "smt/smt_kernel.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"

/**
 * NOTE: way how to print z3 formula in smt2 format (including the declaration)
 * ast_pp_util utl(m);
 * utl.collect(formula);
 * utl.display_decls(std::cout);
 * utl.display_assert(std::cout, formula);
 */

namespace smt::noodler {

    // FIXME add high level explanation of how this works (length vars are got from init_search_eh, predicates are translated in relevant_eh, final_check_eh does this and that etc)
    // FIXME a lot of stuff in this class comes from trau/z3str3 we still need to finish cleaning
    class theory_str_noodler : public theory {
    protected:

        /**
         * Structure for storing items for the loop protection.
         */
        struct stored_instance {
            expr_ref lengths; // length formula 
            bool initial_length; // was the length formula obtained from the initial length checking?
            // TODO we could also keep here the decision procedure and immediately get the model when loop protection gets sat
        };

        /**
         * @brief Statistics for noodler.
         */

        struct DecProcStats {
            unsigned num_solved_preprocess = 0; // number of instances solved by preprocessing of the procedure
            unsigned num_start = 0; // number of times the procedure was started (after preprocessing)
            unsigned num_finish = 0; // number of times the procedure gave an answer (no undef)
        };

        int m_scope_level = 0;
        const theory_str_noodler_params& m_params;
        th_rewriter m_rewrite;
        arith_util m_util_a;
        seq_util m_util_s;

        // equivalence of z3 terms based on their length (terms are equiv if their length is for sure the same)
        var_union_find var_eqs;

        // variables whose lengths are important
        obj_hashtable<expr> len_vars;

        // used in final_check_eh, maps noodler string variables to z3 string variables
        // AND int variables to predicates they represent (see handle_conversion)
        std::map<BasicTerm, expr_ref> var_name;

        // mapping predicates and function to variables that they substitute to
        obj_map<expr, expr*> predicate_replace;

        // TODO what are these?
        std::vector<app_ref> axiomatized_len_axioms;
        obj_hashtable<expr> axiomatized_terms;
        obj_hashtable<expr> axiomatized_persist_terms;
        obj_hashtable<expr> propagated_string_theory; // expressions that were already processed by string_theory_propagation (to avoid looping)
        obj_hashtable<expr> m_has_length;          // is length applied
        expr_ref_vector     m_length;             // length applications themselves
        std::vector<std::pair<expr_ref, stored_instance>> axiomatized_instances;

        // TODO what are these?
        vector<std::pair<obj_hashtable<expr>,std::vector<app_ref>>> len_state;
        obj_map<expr, unsigned> bool_var_int;
        obj_hashtable<expr> bool_var_state;

        using expr_pair = std::pair<expr_ref, expr_ref>;
        using expr_pair_flag = std::tuple<expr_ref, expr_ref, bool>;

        // mapping of quantifier quards (quantified variables) to z3 vars. z3 represents variables using indices. 
        std::map<std::string, unsigned> quantif_vars {};

        // constraints that are (possibly) to be processed in final_check_eh (added either in relevant_eh or ?assign_eh?)
        // they also need to be popped and pushed in pop_scope_eh and push_scope_eh)
        scoped_vector<expr_pair> m_word_eq_todo; // pair contains left and right side of the word equality
        scoped_vector<expr_pair> m_word_diseq_todo; // pair contains left and right side of the word disequality
        scoped_vector<expr_pair> m_lang_eq_todo; //pair contains left and right side of the language equality
        scoped_vector<expr_pair> m_lang_diseq_todo; // pair contains left and right side of the language disequality
        scoped_vector<expr_pair> m_not_contains_todo; // first element should not contain the second one
        scoped_vector<expr_pair_flag> m_membership_todo; // contains the variable and reg. lang. + flag telling us if it is negated (false -> negated)
        // contains pair of variables (e,s), where we have one of e = str.to_code(s), e = str.from_code(s),
        // e = str.to_int(s), or e = str.from_int(s), based on the conversion type
        scoped_vector<TermConversion> m_conversion_todo;

        // during final_check_eh, we call remove_irrelevant_constr which chooses from previous sets of
        // todo constraints and check if they are relevant for current SAT assignment => if they are
        // they are added to one of these sets
        vector<expr_pair> m_word_eq_todo_rel; // pair contains left and right side of the word equality
        vector<expr_pair> m_word_diseq_todo_rel; // pair contains left and right side of the word disequality
        vector<expr_pair_flag> m_lang_eq_or_diseq_todo_rel; // contains left and right side of the language (dis)equality and a flag - true -> equality, false -> diseq
        vector<expr_pair> m_not_contains_todo_rel; // first element should not contain the second one
        vector<expr_pair_flag> m_membership_todo_rel; // contains the variable and reg. lang. + flag telling us if it is negated (false -> negated)
        // we cannot decide relevancy of to_code, from_code, to_int and from_int, so we assume everything in m_conversion_todo is relevant => no _todo_rel version

        // TODO: the following three things should probably be done differently
        // true if last run of final_check_eh was sat (if it is true, then final_check_eh always return sat)
        bool last_run_was_sat = false;
        // the length formula from the last run that was sat
        expr_ref sat_length_formula;
        // the scope at which the last run was sat (so if we pop behind this scope, we have to forget that the last run was sat)
        int scope_with_last_run_was_sat = -1;

        unsigned num_of_solving_final_checks = 0; // number of final checks that lead to solving string formula (i.e. not solved by loop protection nor by language (dis)equalities)
        std::map<std::string, DecProcStats> statistics {
            {"underapprox", {0, 0, 0}}, // underapprox of the stabilization-based procedure
            {"stabilization", {0, 0, 0}}, // stabilization-based procedure
            {"nielsen", {0 ,0 ,0}}, // nielsen procedure
            {"length", {0 ,0 ,0}}, // length-based procedure
            {"unary", {0 ,0 ,0}}, // unary decision procedure
            {"single-memb-heur", {0 ,0 ,0}}, // membership heuristic
            {"multi-memb-heur", {0 ,0 ,0}}, // multiple memberhip heuritstic
        };

        // we need this because part of Z3 is written like C, and statistic takes 'const char*', which has to be kept somewhere
        std::map<std::string, std::vector<const char*>> statistics_bullshit_names {
            {"underapprox", {"str-num-proc-underapprox-start", "str-num-proc-underapprox-finish", "str-num-proc-underapprox-solved-preprocess"}}, // underapprox of the stabilization-based procedure
            {"stabilization", {"str-num-proc-stabilization-start", "str-num-proc-stabilization-finish", "str-num-proc-stabilization-solved-preprocess"}}, // stabilization-based procedure
            {"nielsen", {"str-num-proc-nielsen-start", "str-num-proc-nielsen-finish", "str-num-proc-nielsen-solved-preprocess"}}, // nielsen procedure
            {"length", {"str-num-proc-length-start", "str-num-proc-length-finish", "str-num-proc-length-solved-preprocess"}}, // length-based procedure
            {"unary", {"str-num-proc-unary-start", "str-num-proc-unary-finish", "str-num-proc-unary-solved-preprocess"}}, // unary decision procedure
            {"single-memb-heur", {"str-num-proc-single-memb-heur-start", "str-num-proc-single-memb-heur-finish", "str-num-proc-single-memb-heur-solved-preprocess"}}, // membership heuristic
            {"multi-memb-heur", {"str-num-proc-multi-memb-heur-start", "str-num-proc-multi-memb-heur-finish", "str-num-proc-multi-memb-heur-solved-preprocess"}}, // multiple memberhip heuritstic
        };

        // Stuff for model generation
        std::set<BasicTerm> relevant_vars; // vars that are in the formula used in decision procedure (we cannot used dec_proc to generate models for those that are not in here)
        std::shared_ptr<AbstractDecisionProcedure> dec_proc = nullptr; // keeps the decision procedure that returned sat
        // classes for creating model dependencies, see their usage in mk_value
        class noodler_var_value_proc; // for noodler vars used in decision procedure
        class str_var_value_proc; // for string vars (whose length is important) that are not used in decision procedure
        class concat_var_value_proc; // for concatenation

    public:
        char const * get_name() const override { return "noodler"; }
        theory_str_noodler(context& ctx, ast_manager & m, theory_str_noodler_params const & params);
        void display(std::ostream& os) const override;
        theory *mk_fresh(context * newctx) override { return alloc(theory_str_noodler, *newctx, get_manager(), m_params); }
        void init() override;
        theory_var mk_var(enode *n) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        bool internalize_atom(app *atom, bool gate_ctx) override;
        bool internalize_term(app *term) override;
        void init_search_eh() override;
        void relevant_eh(app *n) override;
        void assign_eh(bool_var v, bool is_true) override;
        void new_eq_eh(theory_var, theory_var) override;
        void new_diseq_eh(theory_var, theory_var) override;
        bool can_propagate() override;
        void propagate() override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void restart_eh() override;
        void reset_eh() override;
        final_check_status final_check_eh() override;
        model_value_proc *mk_value(enode *n, model_generator& mg) override;
        void init_model(model_generator& m) override;
        void finalize_model(model_generator& mg) override;
        lbool validate_unsat_core(expr_ref_vector& unsat_core) override;

        /**
         * @brief Collect statistics (called at the end of the run)
         * 
         * @param st 
         */
        void collect_statistics(::statistics & st) const override;

        // FIXME ensure_enode is non-virtual function of theory, why are we redegfining it?
        enode* ensure_enode(expr* e);

        void add_length_axiom(expr* n);
        /**
         * @brief Add special axioms for conversions.
         */
        void add_conversion_num_axioms();
        /**
         * @brief Add special axioms for length (in)equations.
         */
        bool add_len_num_axioms(expr* ex);

        /**
         * @brief Get concatenation of e1 and e2
         */
        expr_ref mk_concat(expr* e1, expr* e2);

        /**
         * @brief Creates literal representing that n is empty string
         */
        literal mk_eq_empty(expr* n);

        bool has_length(expr *e) const { return m_has_length.contains(e); }
        void enforce_length(expr* n);

        ~theory_str_noodler() {}

    protected:
        expr_ref mk_sub(expr *a, expr *b);

        literal mk_literal(expr *e);
        bool_var mk_bool_var(expr *e);

        /**
         * @brief Create a fresh Z3 int variable with a given @p name followed by a unique suffix.
         *
         * @param name Infix of the name (rest is added to get a unique name)
         */
        expr_ref mk_int_var_fresh(const std::string& name) {
            app* fresh_var = m.mk_fresh_const(name, m_util_a.mk_int(), true); // need to be skolem, because it seems they are not printed for models
            return expr_ref(fresh_var, m);
        }
        
        /**
         * @brief Create a fresh Z3 string variable with a given @p name followed by a unique suffix.
         *
         * @param name Infix of the name (rest is added to get a unique name)
         */
        expr_ref mk_str_var_fresh(const std::string& name) {
            app* fresh_var = m.mk_fresh_const(name, m_util_s.mk_string_sort(), true); // need to be skolem, because it seems they are not printed for models
            return expr_ref(fresh_var, m);
        }

        /**
         * @brief Get Z3 int var with exact given @p name
         *
         * @param name Name of the var
         */
        expr_ref mk_int_var(const std::string& name) {
            // quantified int variables we need to create as z3 variables. If they are created as skolem const, the quantification is 
            // ignored (because everything there is a constant).
            // WARNING: currently, we do not support occurrences of variables with the same name in different 
            // scopes (both quantified and free)
            auto it = this->quantif_vars.find(name);
            if(it != this->quantif_vars.end()) {
                return expr_ref(m.mk_var(it->second, m_util_a.mk_int()), m);
            }
            app* var = m.mk_skolem_const(symbol(name.c_str()), m_util_a.mk_int()); // need to be skolem, because it seems they are not printed for models
            return expr_ref(var, m);
        }

        /**
         * @brief Get Z3 string var with exact given @p name
         *
         * @param name Name of the var
         */
        expr_ref mk_str_var(const std::string& name) {
            app* var = m.mk_skolem_const(symbol(name.c_str()), m_util_s.mk_string_sort()); // need to be skolem, because it seems they are not printed for models
            return expr_ref(var, m);
        }

        /**
         * @brief Transforms LenNode to the z3 formula
         * 
         * Uses mapping var_name, those variables v that are mapped are assumed to be string variables
         * and will be transformed into (str.len v) while other variables (which are probably created
         * during preprocessing/decision procedure) are taken as int variables.
         */
        expr_ref len_node_to_z3_formula(const LenNode& len_formula);

        /**
         * @brief Adds @p e as a theory axiom (i.e. to SAT solver).
         * 
         * @param e Axiom to add, probably should be a predicate.
         * 
         * TODO Nobody probably knows what happens in here.
         */
        void add_axiom(expr *e);
        /**
         * @brief Adds a new clause of literals from @p ls.
         * 
         * TODO Nobody probably knows what happens in here, and it is a bit different than the other add_axiom
         */
        void add_axiom(std::vector<literal> ls);

        // methods for rewriting different predicates into something simpler that we can handle
        void handle_char_at(expr *e);
        void handle_substr(expr *e);
        void handle_substr_int(expr *e);
        void handle_index_of(expr *e);
        void handle_replace(expr *e);
        void handle_replace_re(expr *e);
        void handle_prefix(expr *e);
        void handle_suffix(expr *e);
        void handle_not_prefix(expr *e);
        void handle_not_suffix(expr *e);
        void handle_contains(expr *e);
        void handle_not_contains(expr *e);
        void handle_in_re(expr *e, bool is_true);
        void handle_is_digit(expr *e);
        void handle_conversion(expr *e);
        void handle_lex_leq(expr *e);
        void handle_lex_lt(expr *e);
        void handle_replace_all(expr *e);
        void handle_replace_re_all(expr *e);

        // methods for assigning boolean values to predicates
        void assign_not_contains(expr *e);

        void set_conflict(const literal_vector& ls);

        /**
         * @brief Construct a formula representing current conjunction of atomic string constraints currently 
         * solved in final_check (atoms that are not relevant are omited). It includes (dis)equations, regexes, 
         * and notcontains.
         * 
         * @return expr_ref Conjunction of atomic string constraints
         */
        expr_ref construct_refinement();

        /**
         * @brief Introduce string axioms for a formula @p ex. 
         * 
         * @param ex Formula whose terms should be inspected.
         * @param init Is it an initial string formula (formula from input)?
         * @param neg Is the formula under negation?
         * @param var_lengths Introduce lengths axioms for variables of the form x = eps -> |x| = 0? 
         */
        void string_theory_propagation(expr * ex, bool init = false, bool neg = false, bool var_lengths = false);
        void propagate_concat_axiom(enode * cat);
        void propagate_basic_string_axioms(enode * str, bool var_lengths = false);

        /**
         * Creates theory axioms that hold iff either any of the negated assumption from @p neg_assumptions holds,
         * or string term @p s does not occur in @p x@p s other than at the end. I.e. we are checking
         * (not-negated assumptions) -> (string term @p s does not occur in @p x@p s other than at the end)
         * 
         * It does it by checking that s does not occur anywhere in xs reduced by one character (i.e. xs[0:-2])
         * 
         * Translates to the following theory axioms:
         * not(s = eps) -> neg_assumptions || s = s1.s2
         * not(s = eps) -> neg_assumptions || s2 in re.allchar (is a single character)
         * not(s = eps) -> neg_assumptions || not(contains(x.s1, s))
         * (s = eps) && (x != eps) -> neg_assumptions
         * 
         * For the case that s is a string literal, we do not add the two first axioms and we take s1 = s[0:-2].
         * 
         * @param neg_assumptions Negated assumptions that have to hold for checking tightest prefix
         */
        void tightest_prefix(expr* s, expr* x, std::vector<literal> neg_assumptions);

        /// @brief Returns the model_value_proc for string variable @p str_expr based on whether it is used in dec_proc or not
        model_value_proc* model_of_string_var(app* str_var);

        /******************* FINAL_CHECK_EH HELPING FUNCTIONS *********************/

        /**
         * @brief Adds string constraints from *_todo that are relevant for SAT checking to *_todo_rel.
         */
        void remove_irrelevant_constr();

        /**
        Convert (dis)equation @p ex to the instance of Predicate. As a side effect updates mapping of
        variables (BasicTerm) to the corresponding z3 expr.
        @param ex Z3 expression to be converted to Predicate.
        @return Instance of predicate
        */
        Predicate conv_eq_pred(app* expr);

        /**
         * @brief Check if the given equation is a temporary equations that was added 
         * among axioms during axiomatization in handle_replace_all. These equalities
         * are there due to length axioms inferring and proper handling of variable 
         * substitution. We want to discard them as they make the instances artificially harder: 
         * x = replace_all(...) || x = y --> we might get in final_check x = y && tmp = replace_all(...)
         * in final_check we include only those transducer constraints that are present in remaining 
         * constraints (ignoring tmp = replace_all(...)).
         * 
         * @param ex Equation
         * @return true <-> is temporary transducer constraint
         */
        bool is_tmp_transducer_eq(app* const ex);

        /**
         * @brief Creates noodler formula containing relevant word equations and disequations
         * 
         * @param alph Set of symbols of the current instance (for transducer constraints)
         */
        Formula get_formula_from_relevant(const std::set<mata::Symbol>& alph);
        /**
         * @brief Get all symbols used in relevant word (dis)equations and memberships
         */
        std::set<mata::Symbol> get_symbols_from_relevant();
        /**
         * Get automata assignment for formula @p instance using relevant memberships in m_membership_todo_rel.
         * As a side effect updates mapping of variables (BasicTerm) to the corresponding z3 expr.
         * @param instance Formula containing (dis)equations
         * @param noodler_alphabet Set of symbols occuring in the formula and memberships
         */
        [[nodiscard]] AutAssignment create_aut_assignment_for_formula(
                const Formula& instance,
                const std::set<mata::Symbol>& noodler_alphabet
        );
        /**
         * Get initial length variables as a set of @c BasicTerm from their expressions.
         */
        std::unordered_set<BasicTerm> get_init_length_vars(AutAssignment& ass);
        /**
         * @brief Get the conversions (to/from_int/code) with noodler variables
         * 
         * Side effect: string variables in conversions which are not mapped in the automata
         * assignment @p ass will be mapped to sigma* after this.
         */
        std::vector<TermConversion> get_conversions_as_basicterms(AutAssignment &ass, const std::set<mata::Symbol>& noodler_alphabet);

        /**
         * Solves relevant language (dis)equations from m_lang_eq_or_diseq_todo_rel. If some of them
         * does not hold, returns false and also blocks it in the SAT assignment.
         */
        bool solve_lang_eqs_diseqs();
        /**
         * Solve the problem using underapproximating decision procedure, if it returns l_true,
         * the original formula is SAT, otherwise we need to run normal decision procedure.
         */
        lbool solve_underapprox(const Formula& instance, const AutAssignment& aut_ass,
                                const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                                std::vector<TermConversion> conversions);

        /**
         * @brief Check if the length formula @p len_formula is satisfiable with the existing length constraints.
         * 
         * @param[out] unsat_core If this parameter is NOT nullptr, the LIA solver stores here unsat core of 
         * the current @p len_formula. If the parameter is nullptr, the unsat core is not computed.
         */
        lbool check_len_sat(expr_ref len_formula, expr_ref* unsat_core=nullptr);

        /**
         * @brief Blocks current SAT assignment for given @p len_formula
         * 
         * @param len_formula Length formula corresponding to the current instance
         * @param add_axiomatized Add item to the vector of axiomatized instances (for the loop protection)
         * @param init_lengths Was the length formula obtained from the initial length checking (for the fool protection)
         * 
         * TODO explain better
         */
        void block_curr_len(expr_ref len_formula, bool add_axiomatized = true, bool init_lengths = false);

        /**
         * @brief Checks if the current instance is suitable for Nielsen decision procedure.
         * 
         * @param instance Current instance converted to Formula
         * @param init_length_sensitive_vars Length variables
         * @return true <-> suitable for Nielsen-based decision procedure
         */
        bool is_nielsen_suitable(const Formula& instance, const std::unordered_set<BasicTerm>& init_length_sensitive_vars) const;

        /**
         * @brief Check if the current instance is suitable for underapproximation.
         * 
         * @param instance Current instance converted to Formula
         * @param aut_ass Current automata assignment
         * @param convs String-Int conversions
         * @return true <-> suitable for underapproximation
         */
        bool is_underapprox_suitable(const Formula& instance, const AutAssignment& aut_ass, const std::vector<TermConversion>& convs) const;

        /**
         * @brief Checks if the relevant predicates are suitable for multiple membership heuristic
         * 
         * Multiple membership heuristic is used when we have formula containing only memberships.
         * We then only need to compute intersection from the regular languages and check if it is not empty.
         * The heuristics sorts the regexes by expected complexity of computing nfa, and iteratively computes
         * the intersection, so that if the formula is unsat, we do not need to build all automata.
         * Furthermore, for all regexes that should be complemented, we compute their union and then check
         * the inclusion with the intersection from the previous step, i.e., we have:
         * L_1 \cap ... \cap L_m \cap \neg L_{m+1} \cap ... \cap \neg L_n = L \cap \neg (L_{m+1} \cup ... \cup L_n)
         *                                                                = L \cap \neg L'
         * where L = L_1 \cap ... \cap L_m, and L' = L_{m+1} \cup ... \cup L_n.
         * We then want to check if L \cap \neg L' is empty (unsat), which is the same as asking if L is subset of L'.
         */
        bool is_mult_membership_suitable();

        /**
         * @brief Wrapper for running the Nielsen transformation.
         * 
         * @param instance Formula instance
         * @param aut_assignment Current automata assignment
         * @param init_length_sensitive_vars Length sensitive variables
         * @return lbool Outcome of the procedure
         */
        lbool run_nielsen(const Formula& instance, const AutAssignment& aut_assignment, const std::unordered_set<BasicTerm>& init_length_sensitive_vars);

        /**
         * @brief Wrapper for running the length-based decision procedure. 
         * 
         * @param instance Formula instance
         * @param aut_assignment Current automata assignment
         * @param init_length_sensitive_vars Length sensitive variables
         * @return lbool Outcome of the procedure
         */
        lbool run_length_proc(const Formula& instance, const AutAssignment& aut_assignment, const std::unordered_set<BasicTerm>& init_length_sensitive_vars);

        /**
         * @brief Wrapper for running the mulitple membership query heuristics.
         * 
         * Check is_mult_membership_suitable() for explanation.
         * 
         * @return lbool Outcome of the heuristic procedure.
         */
        lbool run_mult_membership_heur();
        
        /**
         * @brief Wrapper for running the loop protection.
         * 
         * @return lbool Outcome of the loop protection
         */
        lbool run_loop_protection();

        /**
         * @brief Run length-based satisfiability checking.
         * 
         * @param instance Current instance converted to Formula
         * @param aut_ass Current automata assignment
         * @param init_length_sensitive_vars Length sensitive variables
         * @param conversions String <-> Int conversions
         * @return lbool Outcome of the procedure.
         */
        lbool run_length_sat(const Formula& instance, const AutAssignment& aut_ass,
                                const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                                std::vector<TermConversion> conversions);

        /**
         * @brief This function should always be called after decision procedure decides SAT with non-trivial length formula
         * 
         * It pushes the length formula into Z3, so that we can generate correct model.
         * 
         * @param length_formula - formula with which we got sat
         */
        void sat_handling(expr_ref length_formula);

        /***************** FINAL_CHECK_EH HELPING FUNCTIONS END *******************/
    };
}

#endif /* _THEORY_STR_NOODLER_H_ */
