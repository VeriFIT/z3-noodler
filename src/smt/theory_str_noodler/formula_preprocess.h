
#ifndef Z3_STR_FORMULA_PREPROCESS_H_
#define Z3_STR_FORMULA_PREPROCESS_H_

#include <iostream>
#include <map>
#include <set>
#include <queue>
#include <string>

#include <mata/nfa/nfa.hh>

#include "util/trace.h"
#include "params/theory_str_noodler_params.h"

#include "formula.h"
#include "aut_assignment.h"
#include "var_union_find.h"
#include "util.h"

namespace smt::noodler {

    //----------------------------------------------------------------------------------------------------------------------------------

    /**
     * @brief Remove from the container @p st all items satisfying the predicate @p pred.
     *
     * @tparam T Container type
     * @tparam P Predicate type
     * @param st Set
     * @param pred predicate
     */
    template<typename T, typename P>
    void remove_if(T& st, P pred) {
        for(auto it{st.begin()}; it != st.end();) {
            if(pred(*it))
                it = st.erase(it);
            else
                it++;
        }
    }

    /**
     * @brief Set difference
     *
     * @tparam T type of sets
     * @param t1 First set
     * @param t2 Second set
     * @return @p t1 \ @p t2
     */
    template<typename T>
    std::set<T> set_difference(const std::set<T>& t1, const std::set<T>& t2) {
        std::set<T> diff;
        std::set_difference(t1.begin(), t1.end(), t2.begin(), t2.end(),
            std::inserter(diff, diff.begin()));
        return diff;
    }

    template<typename T>
    bool set_disjoint(const std::unordered_set<T>& t1, const std::set<T>& t2) {
        if (t1.size() < t2.size()) {
            for(const auto& t : t1) {
                if(t2.contains(t))
                    return false;
            }
        } else {
            for(const auto& t : t2) {
                if(t1.contains(t))
                    return false;
            }
        }
        return true;
    }

    template<typename T, typename S, typename P>
    std::set<S> set_map(const std::set<T>& st, P pred) {
        std::set<S> ret;
        std::transform (st.begin(), st.end(), std::inserter(ret, ret.begin()), pred);
        return ret;
    }

    template<typename T>
    bool is_subset(const std::set<T>& s1, const std::set<T>& s2) {
        return std::includes(s2.begin(), s2.end(), s1.begin(), s1.end());
    }

    template<typename T>
    bool is_subvector(const std::vector<T>& vec, const std::vector<T>& check) { // insufficient
        return std::search(vec.begin(), vec.end(), check.begin(), check.end()) != vec.end();
    }

    template<typename T, typename P>
    std::set<T> set_filter(std::set<T>& st, P pred) {
        std::set<T> ret;
        std::copy_if (st.begin(), st.end(), std::inserter(ret, ret.begin()), pred );
        return ret;
    }

    template<typename T>
    void map_increment(std::map<T, unsigned>& mp, const T& val) {
         auto iter = mp.find(val);
        if(iter != mp.end()) {
            iter->second++;
        } else {
            mp[val] = 1;
        }
    }

    template<typename T, typename P>
    void map_set_insert(std::map<T, std::set<P>>& mp, const T& key, const P& val) {
        auto iter = mp.find(key);
        if(iter != mp.end()) {
            iter->second.insert(val);
        } else {
            mp[key] = std::set<P>({val});
        }
    }

    //----------------------------------------------------------------------------------------------------------------------------------

    using ConcatGraphEdges = std::map<std::pair<BasicTerm,BasicTerm>, unsigned>;
    using SubstitutionMap = std::unordered_map<BasicTerm, std::vector<BasicTerm>>;

    /**
     * @brief Concatenation graph. Oriented graph where each term (literal/variable) is node and two terms
     * t1 and t2 are connected by a labelled oriented edge (t1 -> t2) if t1.t2 occurs in some equation.
     * Moreover each edge is labelled by the number of occurrences of such concatenation in the formula.
     */
    class ConcatGraph {
    public:
        ConcatGraphEdges edges;
        std::map<BasicTerm, std::set<BasicTerm>> pred;
        std::map<BasicTerm, std::set<BasicTerm>> succ;

    public:
        ConcatGraph() : edges(), pred(), succ() { };
        ConcatGraph(const ConcatGraph&) = default;

        void add_edge(const BasicTerm& from, const BasicTerm& to) {
            map_increment(this->edges, {from, to});
            map_set_insert(this->pred, to, from);
            map_set_insert(this->succ, from, to);
        };

        unsigned get_edge_cost(const BasicTerm& from, const BasicTerm& to) const {
            return this->edges.at({from, to});
        };

        std::set<BasicTerm> get_succ(const BasicTerm& t) const {
            return this->succ.at(t);
        };


        bool is_init(const BasicTerm& t) const { return t.get_name() == ""; };

        /**
         * @brief Special node s (variable with empty name) denoting beginning and end of a concatenation. If there is
         * an edge between this special node s->t, t is at the beginning of some equation. If there is an edge t->s,
         * t is at the end of an equation.
         *
         * @return Special node (called init).
         */
        BasicTerm init() const { return BasicTerm(BasicTermType::Variable, "");  };

        /**
         * @brief Returns nodes (variables) having only one sucessor and moreover having more than one
         * predecessors (or a predecessor is init node) .
         *
         * @return Set of BasicTerms (variable terms).
         */
        std::set<BasicTerm> get_init_vars() const {
            std::set<BasicTerm> ret;
            for(const auto& pr : this->succ) {
                if(is_init(pr.first))   continue;
                if(pr.second.size() > 1)    continue;
                if(!pr.first.is_variable())    continue;

                std::set<BasicTerm> pred_set = this->pred.at(pr.first);
                if(pred_set.size() > 1)
                    ret.insert(pr.first);
                if(pred_set.size() == 1 && is_init(*pred_set.begin()))
                    ret.insert(pr.first);
                if(pred_set.size() == 1 && this->succ.at(*pred_set.begin()).size() > 1)
                    ret.insert(pr.first);
            }
            return ret;
        }
    };

    //----------------------------------------------------------------------------------------------------------------------------------

    /**
     * @brief Representation of a variable/literal in a predicate
     */
    struct VarNode {
        BasicTerm term; /// variable or literal
        size_t pred_index; /// index of predicate in which term occurs
        /**
         * @brief Position of term in the predicate with index pred_index
         * 
         * The absolute value denotes the position of the side (starting with 1 not 0),
         * where negative values means it occurs in params[0] (left side for (dis)eqautions)
         * and positive means in params[1] (right side for (dis)equations)
         */
        int position;

        VarNode(BasicTerm term, const size_t eq_index, const int position): term{ std::move(term) }, pred_index{ eq_index }, position{ position } {}
        VarNode(const VarNode& other) = default;
        VarNode(VarNode &&) = default;

        VarNode& operator=(const VarNode&) = default;

        bool operator==(const VarNode& other) const {
            return term == other.term && pred_index == other.pred_index && position == other.position;
        }

        bool operator<(const VarNode& other) const {
            if(position == other.position) {
                if(pred_index == other.pred_index) {
                    if(term == other.term) return false;
                    return term < other.term;
                }
                return pred_index < other.pred_index;
            }
            return position < other.position;
        }

        std::string to_string() const {
            std::string ret;
            ret += "( " + term.to_string() + ";" + std::to_string(pred_index) + ";" + std::to_string(position) + ")";
            return ret;
        };
    };
    //----------------------------------------------------------------------------------------------------------------------------------

    using VarMap = std::map<BasicTerm, std::set<VarNode>>;
    using VarNodeSymDiff = std::pair<std::set<VarNode>, std::set<VarNode>>;
    using Concat = std::vector<BasicTerm>;
    using SepEqsGather = std::vector<std::pair<std::map<BasicTerm, unsigned>, unsigned>>;
    using Dependency = std::map<size_t, std::set<size_t>>;

    /**
     * @brief Class representing a formula with efficient handling of variable occurrences.
     */
    class FormulaVar {

    private:
        std::map<size_t, Predicate> predicates; // formula
        std::set<Predicate> allpreds; // all predicates in a set
        VarMap varmap; // mapping of a variable name to a set of its occurrences in the formula
        size_t input_size; // number of equations in the input formula
        size_t max_index; // maximum occupied index

    protected:
        void update_varmap(const Predicate& pred, size_t index);

    public:

        FormulaVar(const Formula& conj);

        std::string to_string() const;

        const std::set<VarNode>& get_var_occurr(const BasicTerm& var) const { return this->varmap.at(var); };
        bool var_occurs(const BasicTerm& var) const { return (this->varmap.contains(var) && this->varmap.at(var).size() > 0); };
        const Predicate& get_predicate(size_t index) const { return this->predicates.at(index); };
        const std::map<size_t, Predicate>& get_predicates() const { return this->predicates; };
        const std::set<Predicate>& get_predicates_set() const { return this->allpreds; };
        const VarMap& get_varmap() const { return this->varmap; };
        void get_side_regulars(std::vector<std::pair<size_t, Predicate>>& out) const;
        void get_simple_eqs(std::vector<std::pair<size_t, Predicate>>& out) const;
        size_t get_max_index() const { return this->max_index; }
        bool contains_simple_eqs() const { std::vector<std::pair<size_t, Predicate>> out; get_simple_eqs(out); return out.size() > 0;  }

        std::set<VarNode> get_var_positions(const Predicate& pred, size_t index, bool incl_lit=false) const;
        void update_var_positions_side(const std::vector<BasicTerm>& side, std::set<VarNode>& res, size_t index, bool incl_lit=false, int mult=1) const;

        /// Returns the side of the predicate denoted by the position of @p var_node
        const Concat& get_side_of_var_node(const VarNode& var_node) const {
            if (var_node.position > 0) {
                return get_predicate(var_node.pred_index).get_params()[1];
            } else {
                return get_predicate(var_node.pred_index).get_params()[0];
            }
        }

        bool single_occurr(const std::set<BasicTerm>& items) const;
        bool is_side_regular(const Predicate& p, Predicate& out) const;
        /**
         * @brief Is equation simple (equation of the form X=Y)
         *
         * @param p Equation
         * @return Is simple?
         */
        bool is_simple_eq(const Predicate& p) const { return p.is_equation() && p.get_left_side().size() == 1 && p.get_right_side().size() == 1; };

        void remove_predicate(size_t index);
        int add_predicate(const Predicate& pred, int index = -1);
        void add_predicates(const std::set<Predicate>& preds);

        void replace(const Concat& find, const Concat& replace);
        void clean_varmap();
        void clean_predicates();

        /**
         * @brief Increment index pointing to a side (taking into account that left side has negative numbers
         * from 1 and right side positive numbers from 1).
         *
         * @param val Index
         * @param incr Increment
         * @return @p incr th successor of @p val
         */
        static int increment_side_index(int val, size_t incr) { return val > 0 ? val + incr : val - incr; };
    };

    //----------------------------------------------------------------------------------------------------------------------------------

    using TermReplaceMap = std::map<BasicTerm, std::set<Concat>>;

    /**
     * @brief Class for formula preprocessing.
     */
    class FormulaPreprocessor {

    private:
        FormulaVar formula;
        unsigned fresh_var_cnt;

        // same meaning as in SolvingState (see decision_procedure.h)
        AutAssignment aut_ass;
        SubstitutionMap substitution_map;

        // keeps equations that were removed during preprocessing as inclusions that are needed to generate model
        // (the variables on the right should be propagated from the left variables during model generation)
        std::vector<Predicate> removed_inclusions_for_model;

        LenNode len_formula;
        std::unordered_set<BasicTerm> len_variables;
        std::unordered_set<BasicTerm> conversion_vars; // all conversion vars should always be also in len vars, also it should not contain literals

        const theory_str_noodler_params& m_params;

        Dependency dependency;

    protected:
        void update_reg_constr(const BasicTerm& var, const std::vector<BasicTerm>& upd);
        bool propagate_regular_eqs(const std::set<VarNode>& diff1, const std::set<VarNode>& diff2, Predicate& new_pred) const;
        VarNodeSymDiff get_eq_sym_diff(const Concat& cat1, const Concat& cat2) const;
        bool generate_identities_suit(const VarNodeSymDiff& diff, Predicate& new_pred) const;
        ConcatGraph get_concat_graph() const;
        bool is_var_eps(const BasicTerm& t) const { assert(t.is_variable()); return this->aut_ass.is_epsilon(t); };

        BasicTerm create_fresh_var();
        void get_concat_gather(const Concat& concat, SepEqsGather& res) const;
        void separate_eq(const Predicate& eq, const SepEqsGather& gather_left, SepEqsGather& gather_right, std::set<Predicate>& res) const;

        void gather_extended_vars(Predicate::EquationSideType side, std::set<BasicTerm>& res);

        bool same_length(const BasicTermEqiv& ec, const BasicTerm&t1, const BasicTerm& t2) const;
        
        bool add_var_separator(const Concat& side, std::map<BasicTerm, std::set<BasicTerm>>& container);
        bool propagate_var_separators(const BasicTerm& dest, const BasicTerm& src, std::map<BasicTerm, std::map<BasicTerm, std::set<BasicTerm>>>& separators);
        Concat flatten_concat(const Concat& con, std::map<BasicTerm, std::set<Concat>>& replace_map) const;
        bool can_unify(const Concat& con1, const Concat& con2, const std::function<bool(const Concat&, const Concat&)> &check) const;
        TermReplaceMap construct_replace_map() const;


    public:
        FormulaPreprocessor(Formula conj, AutAssignment ass, std::unordered_set<BasicTerm> lv, const theory_str_noodler_params &par, std::unordered_set<BasicTerm> conversion_vars) :
            formula(conj),
            fresh_var_cnt(0),
            aut_ass(ass),
            len_formula(LenFormulaType::AND, { } ),
            len_variables(lv),
            conversion_vars(conversion_vars),
            m_params(par),
            dependency() { };

        const FormulaVar& get_formula() const { return this->formula; };
        std::string to_string() const { return this->formula.to_string(); };
        void get_regular_sublists(std::map<Concat, unsigned>& res) const;
        void get_eps_terms(std::set<BasicTerm>& res) const;
        const AutAssignment& get_aut_assignment() const { return this->aut_ass; }
        const SubstitutionMap& get_substitution_map() const { return this->substitution_map; }
        const Dependency& get_dependency() const { return this->dependency; }
        Dependency get_flat_dependency() const;
        void add_to_len_formula(LenNode len_to_add) { len_formula.succ.push_back(std::move(len_to_add)); }
        const LenNode& get_len_formula() const { return this->len_formula; }
        const std::unordered_set<BasicTerm>& get_len_variables() const { return this->len_variables; }
        const std::vector<Predicate>& get_removed_inclusions_for_model() const {return this->removed_inclusions_for_model; }

        Formula get_modified_formula() const;

        void remove_regular();
        void propagate_variables();
        void propagate_eps();
        void generate_identities();
        void reduce_regular_sequence(unsigned mn);
        void separate_eqs();
        void remove_extension();
        void remove_trivial();
        void skip_len_sat();
        void underapprox_languages();
        void generate_equiv(const BasicTermEqiv& ec);
        void infer_alignment();
        void common_prefix_propagation();
        void common_suffix_propagation();
        void conversions_validity(std::vector<TermConversion>& conversions);
        bool has_unsat_transducers();

        void underapprox_var_language(const BasicTerm& var);
        void refine_languages();

        /// @brief Reduces automata in aut_ass for only variables that are needed (length, conversion vars or occur in the formula)
        void reduce_automata();

        void reduce_diseqalities();

        bool contains_unsat_literals();
        bool contains_unsat_eqs_or_diseqs();
        bool can_unify_contain(const Concat& left, const Concat& right) const;
         /**
         * @brief Check if it is possible to syntactically unify not contains terms. If they are included (in the sense of vectors) the 
         * not(contain) is unsatisfiable.
         * 
         * @param prep FormulaPreprocessor
         * @return true -> can be unified 
         */
        bool can_unify_not_contains();

        /**
         * @brief Construct constraints to get rid of not_contains predicates.
         * @return false -> unsatisfiable constaint; true if it is not evident
         */
        bool replace_not_contains();

        void simplify_not_contains_to_equations();

        /**
         * @brief Replace all occurrences of find with replace. Warning: do not modify the automata assignment.
         *
         * @param find Find
         * @param replace Replace
         */
        void replace(const Concat& find, const Concat& replace) { this->formula.replace(find, replace); };
        /**
         * @brief Update predicate with the given index.
         *
         * @param index Index of the predicate to be updated
         * @param pred New predicate
         */
        void update_predicate(size_t index, const Predicate& pred) {
            this->formula.remove_predicate(index);
            this->formula.add_predicate(pred, index);
        }
        void clean_varmap() { this->formula.clean_varmap(); };

        std::string print_info(bool print_nfas = false);
    };


    static std::string concat_to_string(const Concat& cat) {
        std::string ret;
        for(const BasicTerm& t : cat) {
            ret += t.to_string() + " ";
        }
        return ret;
    }

    static std::string set_term_to_string(const std::set<BasicTerm>& st) {
        std::string ret;
        for(const BasicTerm& t : st) {
            ret += t.to_string() + " ";
        }
        return ret;
    }


} // Namespace smt::noodler.

#endif //Z3_STR_FORMULA_PREPROCESS_H_
