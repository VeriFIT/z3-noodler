#ifndef _NOODLER_LENGTH_DECISION_PROCEDURE_H_
#define _NOODLER_LENGTH_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>

#include "params/theory_str_noodler_params.h"

#include "formula.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "formula_preprocess.h"
#include "decision_procedure.h"

namespace smt::noodler {

    /**
     * @brief Pool of variable constraints
     * 
     */
    class ConstraintPool : public std::map<BasicTerm, class VarConstraint> {
    private:
        std::map<zstring, BasicTerm> lit_conversion {};

    public:
        void add_to_pool(const Predicate& pred);

        const std::map<zstring, BasicTerm> get_lit_conversion() const {
            return this->lit_conversion;
        }

        static zstring generate_lit_alias(const BasicTerm& lit, std::map<zstring, BasicTerm>& lit_conversion) {
            zstring new_lit_name = util::mk_noodler_var_fresh("lit").get_name();
            lit_conversion.emplace(std::make_pair(new_lit_name, lit));
            return new_lit_name;
        }
    };

    /**
     * @brief Type for storing batch of equations of the form 
     * x = y1 y2 ... 
     * x = z1 z2 ...
     * It represents constraints on the variable x (_name). We call it constraints on variable x.
     */
    class VarConstraint {
    private:
        zstring _name; // name of the constrained variable
        std::vector<Concat> _constr_eqs;	// All sides of equations on the opposite side of this variable
        std::vector<zstring> _lits; // Literals occuring explicitly and in contained variables
        std::vector<std::pair<zstring, zstring>> _alignments;   // All literals, that should be aligned
        lbool is_parsed;
        // variables occurring in the variable constraint
        std::set<BasicTerm> vars {};
        // set of block vars that are dependant on the current block. 
        // In a block graph they are successors of the current block.
        std::set<BasicTerm> depend_on_block_var {};

        /**
         * @brief Check if @p side is of the form [_name]
         * 
         * @param side Concatenation
         * @return @p side == [_name] 
         */
        bool check_side(const Concat& side);

        /**
         * @brief Emplace concatenation to the var constraint
         * 
         * @param c Concatenation
         * @param lit_conversion Occurrences of literals (unique names for the same literals) 
         */
        void emplace(const Concat& c, std::map<zstring, BasicTerm>& lit_conversion);

        /**
         * @brief Generate LIA formula b_x(var_name) = b_x(last) + |last| if last is not undef otherwise b(t) = 0
         * Expressing that the begin of var_name is directly after last. We need to convert |last| to |lit_conversion[last]| if last is literal. Otherwise |last| is interpreted as number of characters of the temporary literal name.
         * 
         * @param var_name Variable name
         * @param last Variable/Literal preceeding var_name
         * @param lit_conversion Literal conversion 
         * @return LenNode 
         */
        LenNode generate_begin(const zstring& var_name, const BasicTerm& last, const std::map<zstring, BasicTerm>& lit_conversion) const;

        /**
         * @brief Generate the LIA formula b_x(lit) = b_from(lit) + b_x(from) where 
         * x is the current constrained variable _name
         * 
         * Corresponds to the case when x = ... y ... && y = ... lit ....
         * then b_x(lit) = b_y(lit) + b_x(y)
         * 
         * @param lit Literal
         * @param from Source constrained variable
         * @return LenNode Len formula
         */
        LenNode generate_begin(const zstring& lit, const zstring& from) const;

        /**
         * @brief Generate LIA formula of the form |x| = |y_1| + ... where 
         * x = _name and y_1 ... is in @p side_len
         * 
         * @param side_len Concatenation of variables
         * @return LenNode Length formula
         */
        LenNode generate_side_eq(const std::vector<LenNode>& side_len) const;

        /**
         * @brief Generate LIA formula aligning literals @p l1 and @p l2
         * 
         * @param l1 Literal 1
         * @param l2 Literal 1
         * @param conv Occurrences of literals (unique names for the same literals)  
         * @return LenNode 
         */
        LenNode align_literals(const zstring& l1, const zstring& l2, const std::map<zstring, BasicTerm>& conv) const;

         /**
         * @brief Compare first n characters of l1 with last n characters of l2 (e.g. l1=banana, l2=ababa, n=2 -> [ba]nana, aba[ba] -> true)
         * 
         * @return bool match of substrings
         */
        static bool zstr_comp(const zstring& l1_val, const zstring& l2_val, unsigned n);
    public:
        VarConstraint() : _name(), is_parsed(l_false) {};
        VarConstraint(zstring name) : _name(std::move(name)), is_parsed (l_false) {};

        /**
         * @brief Add predicate to the the var constraint. Do not check if a equation side matches 
         * the variable name _name.
         * 
         * @param pred Predicate Predicate to be added
         * @param[out] lit_conversion Occurrences of literals (unique names for the same literals) 
         */
        void add(const Predicate& pred, std::map<zstring, BasicTerm>& lit_conversion);
        std::string to_string() const;

        /**
         * @brief Get literals occurring in the variable constrain and transitively in all var constraints in 
         * the system containing the variable in a side of current var constraint.
         * 
         * @return const std::vector<zstring>& Literals
         */
        // !!! Must be called after parse !!!
        const std::vector<zstring>& get_lits() const;

        /**
         * @brief Get variables occurring inside the var constraint
         * 
         * @return const std::set<BasicTerm> Variables
         */
        const std::set<BasicTerm> get_vars() const {
            return this->vars;
        }

        /**
         * @brief parse var constraint
         * 
         * @param pool all var constraints
         * @param conv conversions for literals
         * @return bool success
         */
        bool parse(ConstraintPool& pool);
        
        /**
         * @brief Get length constraints generated by the batch of equations contraining x.
         * 
         * @param pool Pool of constraints on variables.
         * @return LenNode Length constraints on the current variable constraint
         */
        LenNode get_lengths(const ConstraintPool& pool) const;

        /**
         * @brief Get LIA formula saying that literals matching the same variables do not share any part.
         * Assumes that the var constraints contain @p multi_var.
         * 
         * @param pool Pool of var constraints
         * @param multi_var Variable with multiple occurrences
         * @param source_var Variable whose var constraints contains also the variable @p multi_var
         * @return LenNode LIA formula
         */
        LenNode get_multi_var_lia(const ConstraintPool& pool, const BasicTerm& multi_var, const BasicTerm& source_var) const;

        std::vector<Concat> get_side_eqs() const { return this->_constr_eqs; }

        std::set<BasicTerm> get_dependencies() const { return this->depend_on_block_var; }
    };

    /**
     * @brief Structure for a representation of a block model. 
     * Block are equations of the form x = R_i. A model of these equations can be computed from 
     * a model of x @p solution. 
     */
    struct BlockModel {
        zstring solution; // model of the block variable
        std::set<BasicTerm> terms {}; // other terms occurring in the equational block.
    };

    /**
     * @brief Model generation module for the length decision procedure.
     */
    class LengthProcModel {
    private:
        std::vector<BasicTerm> length_vars {};
        std::map<BasicTerm, zstring> model {};
        // model for each block variable
        std::map<BasicTerm, BlockModel> block_models {};
        // each literal has a fresh name --> we need to convert them back in the generation
        std::map<zstring, BasicTerm> lit_conversion {};
        SubstitutionMap subst_map {};
        AutAssignment aut_ass {};
        // blocks
        ConstraintPool block_pool;
        // set of multi vars (we assume at most one multi var)
        std::set<BasicTerm> multi_var_set{};

    protected:
       /**
         * @brief Get model for variable from its automata assignment (respecting the computed length). 
         * 
         * @param var Variable
         * @param arith_model Length model of variables
         * @return zstring Word from automaton corresponding to @p var.
         */
        zstring assign_aut_ass_var(const BasicTerm& var, const std::map<BasicTerm,rational>& arith_model);

        /**
         * @brief Assign model for variable @p var s.t. it is not in the block system but it is in the 
         * substitution map.
         * 
         * @param var Variable from the substitution map for getting a model
         * @param arith_model Length model of variables
         * @return zstring Model of @p var
         */
        zstring assign_subst_map_var(const BasicTerm& var, const std::map<BasicTerm,rational>& arith_model);

        /**
         * @brief Get skeleton from block represented by @p block_var for the mutli var @p multi_var.
         * 
         * @param block_var Block variable
         * @param multi_var Multi var
         * @param arith_model Length model of variables
         * @return std::vector<long> Skeleton
         */
        std::vector<long> get_multivar_skeleton(const BasicTerm& block_var, const BasicTerm& multi_var, const std::map<BasicTerm,rational>& arith_model);

        /**
         * @brief Get model for the multi var @p multi_var.
         * 
         * @param multi_var Multi var
         * @param arith_model Length model of variables
         * @return zstring Model of @p multi_var
         */
        zstring get_multivar_model(const BasicTerm& multi_var, const std::map<BasicTerm,rational>& arith_model);

        /**
         * @brief Assign free variables. Variables that are free in the system (meaning that they are not in 
         * the block system neither in substitution map) are assigned according to their length.
         * 
         * @param arith_model Length model of variables
         */
        void assign_free_vars(const std::map<BasicTerm,rational>& arith_model);

        /**
         * @brief Create models for variables in the substitution map (created in preprocessing).  
         * 
         * @param arith_model Length model of variables
         */
        void assign_subst_map_vars(const std::map<BasicTerm,rational>& arith_model);

        /**
         * @brief Assign model to multi var. So far we support only a single multi var (checked in the 
         * compute_next_solution).
         * 
         * @param arith_model Length model of variables
         */
        void assign_multi_vars(const std::map<BasicTerm,rational>& arith_model);

        /**
         * @brief Generate models for variable in the block given by @p block_var.
         * 
         * @param block_var Block var
         * @param block_model Block model to be set
         * @param arith_model Length model of variables
         */
        void generate_block_models(const BasicTerm& block_var, BlockModel& block_model, const std::map<BasicTerm,rational>& arith_model);


    public:
        /**
         * @brief Default constructor
         */
        LengthProcModel() : LengthProcModel(ConstraintPool{}, {}, {}, {}) {};

        /**
         * @brief Create model generation module for the given instance.
         * 
         * @param block_pool Blocks
         * @param subst Substitution map from preprocessing
         * @param aut_ass Automata assignment after preprocessing
         * @param multi_var_set Set of multi vars
         */
        LengthProcModel(const ConstraintPool& block_pool, const SubstitutionMap& subst, const AutAssignment& aut_ass, const std::set<BasicTerm>& multi_var_set);

        /**
         * @brief Compute model for each variable in the system. 
         * 
         * @param arith_model Length model of variables
         */
        void compute_model(const std::map<BasicTerm,rational>& arith_model); 

        /**
         * @brief Is the model initialized
         * 
         * @return true <-> initialized
         */
        bool is_initialized() const { return !this->model.empty(); }

        /**
         * @brief Add length variable to the model generation (those variables are assigned in the model generation).
         * 
         * @param var Variable
         */
        void add_len_var(const BasicTerm& var) {
            this->length_vars.push_back(var);
        }

        /**
         * @brief Get already computed assignment of variable @p bt.
         * 
         * @param bt Variable
         * @return zstring String assignment
         */
        zstring get_var_model(const BasicTerm& bt) { return this->model.at(bt); }

        /**
         * @brief Get length variables that are relevant for model of @p str_var in the current model generators.
         * In fact we overapproximate and for each variable @p str_var we return all variables occurring 
         * in the model generators.
         * 
         * @param str_var String variable
         * @return std::vector<BasicTerm> Relevant variables (including temporary int variables) 
         */
        std::vector<BasicTerm> get_len_vars_for_model(const BasicTerm& str_var) { return this->length_vars; };

    };

    /**
     * @brief Length-based decision procedure.
     * 
     */
    class LengthDecisionProcedure : public AbstractDecisionProcedure {
    private:
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        Formula formula;
        AutAssignment init_aut_ass;
        const theory_str_noodler_params& m_params;

        // the length formula from preprocessing, get_lengths should create conjunct with it
        LenNode preprocessing_len_formula = LenNode(LenFormulaType::TRUE,{});
        std::vector<LenNode> computed_len_formula {};
        std::vector<LenNode> implicit_len_formula {};

        // pool of variable constraints
        ConstraintPool pool {};
        // model generation module
        LengthProcModel len_model;
        // substitution map from preprocessing
        SubstitutionMap subst_map {};

    protected:
        /**
         * @brief Check whether the preprocessed formula can be solved using the length-based procedure. 
         * It checks and stores multiple occurrences of variables @p multi_vars (do not include the constrained variables).
         * It also checks if formula contains equations only. 
         * 
         * @param[out] multi_vars Variables with multiple occurrences 
         * @return lbool l_under <-> the formula is out of the fragment
         */
        lbool check_formula(std::set<BasicTerm>& multi_vars);
    
    public:
        LenNodePrecision precision = LenNodePrecision::PRECISE;

        /**
         * Initialize a new decision procedure that can solve language (dis)equality constraints.
         * 
         * @param equalities encodes the language equations
         * @param init_aut_ass gives regular constraints (maps each variable from @p form to some NFA)
         * @param init_length_sensitive_vars the variables that occur in length constraints in the rest of formula
         * @param par Parameters for Noodler string theory.
         */
        LengthDecisionProcedure(const Formula &form, AutAssignment init_aut_ass,
                           const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                           const theory_str_noodler_params& par
         ) : init_length_sensitive_vars{ init_length_sensitive_vars },
             formula { form },
             init_aut_ass{ init_aut_ass },
             m_params(par),
             len_model() { 
        }

        lbool compute_next_solution() override;

        LenNode get_initial_lengths(bool all_vars = false) override {
            return LenNode(LenFormulaType::TRUE);
        }
        std::pair<LenNode, LenNodePrecision> get_lengths() override;
        void init_computation() override { };

        lbool preprocess(PreprocessType opt = PreprocessType::PLAIN, const BasicTermEqiv &len_eq_vars = {}) override;

        static bool is_suitable(const Formula &form, const AutAssignment& init_aut_ass);

        const Formula& get_formula() const {
            return this->formula;
        } 

         /**
         * @brief Get string model based on integer constraints.
         * 
         * @param var Variable whose model is obtained.
         * @param arith_model LIA model.
         * @return zstring String model of @p var
         */
        zstring get_model(BasicTerm var, const std::map<BasicTerm,rational>& arith_model) override;

        /**
         * @brief Get length variables that are relevant for model of @p str_var. 
         * 
         * @param str_var String variable
         * @return std::vector<BasicTerm> Relevant variables (including temporary int variables) 
         */
        std::vector<BasicTerm> get_len_vars_for_model(const BasicTerm& str_var) override;

        /**
         * @brief Get the length sensitive variables
         */
        const std::unordered_set<BasicTerm>& get_init_length_sensitive_vars() const override {
            return this->init_length_sensitive_vars;
        }
    };
}

#endif
