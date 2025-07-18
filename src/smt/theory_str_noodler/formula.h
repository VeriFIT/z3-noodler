/**
 * @brief Create basic representation of firnzkae.
 *
 * Each equation or inequation consists of a left and right side of the equation which hold a vector of basic equation
 *  terms.
 * Each term is of one of the following types:
 *     - Literal,
 *     - Variable, or
 *     - operation such as IndexOf, Length, etc.
 */

#ifndef Z3_NOODLER_FORMULA_H
#define Z3_NOODLER_FORMULA_H

#include <utility>
#include <vector>
#include <stdexcept>
#include <memory>
#include <cassert>
#include <unordered_map>
#include <string>
#include <string_view>
#include <set>
#include <map>
#include <unordered_set>
#include <iostream>
#include <mata/nft/nft.hh>

#include "util/zstring.h"
#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"

namespace smt::noodler {
    enum struct PredicateType {
        Equation,
        Inequation,
        NotContains,
        Transducer, 
    };

    [[nodiscard]] static std::string to_string(PredicateType predicate_type) {
        switch (predicate_type) {
            case PredicateType::Equation:
                return "Equation";
            case PredicateType::Inequation:
                return "Inequation";
            case PredicateType::NotContains:
                return "Notcontains";
            case PredicateType::Transducer:
                return "Transducer";
        }

        throw std::runtime_error("Unhandled predicate type passed to to_string().");
    }

    enum struct BasicTermType {
        Variable,
        Literal,
        Length,
    };

    [[nodiscard]] static std::string to_string(BasicTermType term_type) {
        switch (term_type) {
            case BasicTermType::Variable:
                return "Variable";
            case BasicTermType::Literal:
                return "Literal";
            case BasicTermType::Length:
                return "Length";
        }

        throw std::runtime_error("Unhandled basic term type passed to to_string().");
    }

    class BasicTerm {
    public:
        explicit BasicTerm(BasicTermType type): type(type) {}
        BasicTerm(BasicTermType type, zstring name): type(type), name(std::move(name)) {}

        [[nodiscard]] BasicTermType get_type() const { return type; }
        [[nodiscard]] bool is_variable() const { return type == BasicTermType::Variable; }
        [[nodiscard]] bool is_literal() const { return type == BasicTermType::Literal; }
        [[nodiscard]] bool is(BasicTermType term_type) const { return type == term_type; }

        [[nodiscard]] zstring get_name() const { return name; }
        void set_name(zstring new_name) { name = std::move(new_name); }

        [[nodiscard]] bool equals(const BasicTerm& other) const {
            return type == other.get_type() && name == other.get_name();
        }

        [[nodiscard]] std::string to_string() const;

        struct HashFunction {
            size_t operator() (const BasicTerm& basic_term) const {
                size_t row_hash = std::hash<BasicTermType>()(basic_term.type);
                size_t col_hash = basic_term.name.hash() << 1;
                return row_hash ^ col_hash;
            }
        };

    private:
        BasicTermType type;
        // name of the variable, or the given literal
        zstring name;
    }; // Class BasicTerm.

    [[nodiscard]] static std::string to_string(const BasicTerm& basic_term) {
        return basic_term.to_string();
    }


    static std::ostream& operator<<(std::ostream& os, const BasicTerm& basic_term) {
        os << basic_term.to_string();
        return os;
    }

    static bool operator==(const BasicTerm& lhs, const BasicTerm& rhs) { return lhs.equals(rhs); }
    static bool operator!=(const BasicTerm& lhs, const BasicTerm& rhs) { return !(lhs == rhs); }
    static bool operator<(const BasicTerm& lhs, const BasicTerm& rhs) {
        if (lhs.get_type() < rhs.get_type()) {
            return true;
        } else if (lhs.get_type() > rhs.get_type()) {
            return false;
        }
        // Types are equal. Compare names.
        if (lhs.get_name() < rhs.get_name()) {
            return true;
        }
        return false;
    }
    static bool operator>(const BasicTerm& lhs, const BasicTerm& rhs) { return !(lhs < rhs); }

    [[nodiscard]] static std::string to_string(const std::vector<BasicTerm>& vec, const std::string& delimiter = " ") {
        if(vec.empty()) return "";
        std::string ret = vec[0].to_string();
        for(size_t i = 1; i < vec.size(); i++) {
            ret += delimiter + vec[i].to_string();
        }
        return ret;
    }

    static std::ostream& operator<<(std::ostream& os, const std::vector<BasicTerm>& vec) {
        os << to_string(vec);
        return os;
    }

    //----------------------------------------------------------------------------------------------------------------------------------

    /**
     * @brief Length formula precision
     */
    enum struct LenNodePrecision {
        PRECISE,
        UNDERAPPROX,
        OVERAPPROX,
    };

    /**
     * Given two precisions p0 and p1 of formulae for certain parts of the current SAT branch (e.g. only not-contains predicates), compute the precision of the result.
     * 
     * For example, we have: `not-contains(x, y) AND x != z`, where:
     *    - we (p0=)overapproximate the not-contains to {a, b, c, d} whereas the real set of models is {a, b}
     *    - we have (p1=)precise solutions of the disequation {a, c} (to the disequation)
     * So taking a conjunction of the overapproximation+precise formula for disequation, we have the resulting precision result=overapproximation as
     *  Models of the conjunction using approximations: {a, b, c, d} && {a, c} = {a, c}
     *  Models of the real formula, if we could compute it: {a, b} && {a, c} = {a}
     */
    LenNodePrecision get_resulting_precision_for_conjunction(const LenNodePrecision& p0, const LenNodePrecision& p1);

    enum struct LenFormulaType {
        PLUS,
        MINUS,
        TIMES,
        EQ,
        NEQ, // not equal
        NOT,
        LEQ, // <=
        LT, // <
        LEAF, // int or variable (use LenNode(int) or LenNode(BasicTerm) constructors)
        AND,
        OR,
        TRUE,
        FALSE,
        EXISTS, // existential quantifier
        FORALL, // quantifier for all
    };

    struct LenNode {
        LenFormulaType type;
        BasicTerm atom_val;
        std::vector<struct LenNode> succ;

        LenNode(rational k) : type(LenFormulaType::LEAF), atom_val(BasicTermType::Length, zstring(k)), succ() { };
        LenNode(int k) : LenNode(rational(k)) { };
        LenNode(BasicTerm val) : type(LenFormulaType::LEAF), atom_val(val), succ() { };
        LenNode(LenFormulaType tp, std::vector<struct LenNode> s = {}) : type(tp), atom_val(BasicTerm(BasicTermType::Length)), succ(s) { };
    };

    static std::ostream& operator<<(std::ostream& os, const LenNode& node) {
        auto children_iterator = node.succ.begin(); // Some nodes, e.g., quantifiers would like to consume successor nodes
        bool was_opening_parenthesis_emitted = true;

        switch (node.type)
        {
        case LenFormulaType::TRUE:
            return (os << "true");
        case LenFormulaType::FALSE:
            return (os << "false");
        case LenFormulaType::LEAF: {
            zstring name = node.atom_val.get_name();
            // Make sure that we print negative numbers in a valid SMT2 format
            if (node.atom_val.is(BasicTermType::Length)) {
                if (name[0] == '-') {
                    os << "(- " << name.encode().substr(1) << ")";
                    return os;
                }
            }
            return (os << node.atom_val.get_name());
        }
        case LenFormulaType::NOT:
            return os << "(not" << node.succ.at(0) << ")";
        case LenFormulaType::LEQ:
            return os << "(<= " << node.succ.at(0) << " " << node.succ.at(1) << ")";
        case LenFormulaType::LT:
            return os << "(< " << node.succ.at(0) << " " << node.succ.at(1) << ")";
        case LenFormulaType::EQ:
            return os << "(= " << node.succ.at(0) << " " << node.succ.at(1) << ")";
        case LenFormulaType::NEQ:
            return os << "(not (= " << node.succ.at(0) << " " << node.succ.at(1) << "))";
        case LenFormulaType::PLUS:
            if (node.succ.size() > 1) {
                os << "(+";
            } else {
                was_opening_parenthesis_emitted = false;
            }
            break;
        case LenFormulaType::MINUS:
            os << "(-";
            break;
        case LenFormulaType::TIMES:
            os << "(*";
            break;
        case LenFormulaType::AND:
            if (node.succ.size() > 1) {
                os << "(and";
            } else {
                was_opening_parenthesis_emitted = false;
            }
            break;
        case LenFormulaType::OR:
            if (node.succ.size() > 1) {
                os << "(or";
            } else {
                was_opening_parenthesis_emitted = false;
            }
            break;
        case LenFormulaType::FORALL: {
            const auto& quantified_var = *children_iterator;
            children_iterator++;

            os << "(forall (( " << quantified_var << " Int))";
            break;
        }
        case LenFormulaType::EXISTS: {
            const auto& quantified_var = *children_iterator;
            children_iterator++;
            os << "(exists (( " << quantified_var << " Int))";
            break;
        }
        default:
            UNREACHABLE();
        }

        for (; children_iterator != node.succ.end(); children_iterator++) {
            const auto& child = *children_iterator;
            os << " " << child;
        }

        if (was_opening_parenthesis_emitted) {
            os << ")";
        }
        return os;
    }
    /**
     * Recursively collect all free variables in the given formula.
     */
    std::set<BasicTerm> collect_free_vars(const LenNode& formula);

    /**
     * Write the given formula as SMT2 to the given @p out_stream, including preamble.
     */
    void write_len_formula_as_smt2(const LenNode& formula, std::ostream& out_stream);

    /**
     * Apply the given substitution. Variables are assumed to be named uniquely in the formula.
     */
    LenNode substitute_free_vars_for_concrete_values(const LenNode& formula, const std::map<BasicTerm, int> values);

    //----------------------------------------------------------------------------------------------------------------------------------

    class Predicate {
    private:
        PredicateType type;
        std::vector<std::vector<BasicTerm>> params;
        // transducer for the case of PredicateType::Transducer where params[0] is input and params[1] is output
        std::shared_ptr<mata::nft::Nft> transducer = nullptr;
    public:
        enum struct EquationSideType { // can be used also for disequations
            Left,
            Right,
        };

        Predicate() : type(PredicateType::Equation) {}
        explicit Predicate(const PredicateType type): type(type), params(), transducer() {
            if (is_two_sided()) {
                params.resize(2);
                params.emplace_back();
                params.emplace_back();
            }
        }

        explicit Predicate(const PredicateType type, std::vector<std::vector<BasicTerm>> par): type(type), params(par), transducer() {
            assert(!is_two_sided() || params.size() == 2);
        }

        explicit Predicate(const PredicateType type, std::vector<std::vector<BasicTerm>> par, std::shared_ptr<mata::nft::Nft> trans) : 
            type(type),
            params(par),
            transducer(trans) {
            assert(type == PredicateType::Transducer);
            assert(trans->num_of_levels == 2);
        }


        static Predicate create_equation(std::vector<BasicTerm> left_side, std::vector<BasicTerm> right_side) {
            return Predicate{PredicateType::Equation, {std::move(left_side), std::move(right_side)}};
        }

        static Predicate create_disequation(std::vector<BasicTerm> left_side, std::vector<BasicTerm> right_side) {
            return Predicate{PredicateType::Inequation, {std::move(left_side), std::move(right_side)}};
        }

        static Predicate create_transducer(std::shared_ptr<mata::nft::Nft> trans, std::vector<BasicTerm> input, std::vector<BasicTerm> output) {
            return Predicate{PredicateType::Transducer, {std::move(input), std::move(output)}, trans};
        }

        static Predicate create_not_contains(std::vector<BasicTerm> haystick, std::vector<BasicTerm> needle) {
            return Predicate{PredicateType::NotContains, {std::move(haystick), std::move(needle)}};
        }

        [[nodiscard]] PredicateType get_type() const { return type; }
        [[nodiscard]] bool is_equation() const { return type == PredicateType::Equation; }
        [[nodiscard]] bool is_inequation() const { return type == PredicateType::Inequation; }
        [[nodiscard]] bool is_not_cont() const { return type == PredicateType::NotContains; }
        [[nodiscard]] bool is_eq_or_ineq() const { return is_equation() || is_inequation(); }
        [[nodiscard]] bool is_transducer() const { return is(PredicateType::Transducer); }
        [[nodiscard]] bool is_two_sided() const { return is_equation() || is_inequation() || is_not_cont() || is_transducer(); }
        [[nodiscard]] bool is(const PredicateType predicate_type) const { return predicate_type == this->type; }

        [[nodiscard]] const std::vector<std::vector<BasicTerm>>& get_params() const { return this->params; }

        /// get left side of (dis)equation 
        [[nodiscard]] std::vector<BasicTerm>& get_left_side() {
            assert(is_eq_or_ineq());
            return params[0];
        }

        /// get left side of (dis)equation 
        [[nodiscard]] const std::vector<BasicTerm>& get_left_side() const {
            assert(is_eq_or_ineq());
            return params[0];
        }

        /// get right side of (dis)equation 
        [[nodiscard]] std::vector<BasicTerm>& get_right_side() {
            assert(is_eq_or_ineq());
            return params[1];
        }

        /// get right side of (dis)equation 
        [[nodiscard]] const std::vector<BasicTerm>& get_right_side() const {
            assert(is_eq_or_ineq());
            return params[1];
        }

        /// set right side of (dis)equation 
        void set_left_side(const std::vector<BasicTerm> &new_left_side) {
            assert(is_eq_or_ineq());
            params[0] = new_left_side;
        }

        /// set left side of (dis)equation 
        void set_left_side(std::vector<BasicTerm> &&new_left_side) {
            assert(is_eq_or_ineq());
            params[0] = std::move(new_left_side);
        }

        /// set right side of (dis)equation 
        void set_right_side(const std::vector<BasicTerm> &new_right_side) {
            assert(is_eq_or_ineq());
            params[1] = new_right_side;
        }

        /// general get_param(int) for arbitrary predicate type
        [[nodiscard]] const std::vector<BasicTerm>& get_param(size_t param) const {
            return this->params[param];
        }

        /// set right side of (dis)equation 
        void set_right_side(std::vector<BasicTerm> &&new_right_side) {
            assert(is_eq_or_ineq());
            params[1] = std::move(new_right_side);
        }

        /// get input of transducer
        [[nodiscard]] std::vector<BasicTerm>& get_input() {
            assert(is_transducer());
            return params[0];
        }

        /// get input of transducer
        [[nodiscard]] const std::vector<BasicTerm>& get_input() const {
            assert(is_transducer());
            return params[0];
        }

        /// get output of transducer
        [[nodiscard]] std::vector<BasicTerm>& get_output() {
            assert(is_transducer());
            return params[1];
        }

        /// get output of transducer
        [[nodiscard]] const std::vector<BasicTerm>& get_output() const {
            assert(is_transducer());
            return params[1];
        }

        /// set input of transducer
        void set_input(const std::vector<BasicTerm> &new_input) {
            assert(is_transducer());
            params[0] = new_input;
        }

        /// set input of transducer
        void set_input(std::vector<BasicTerm> &&new_input) {
            assert(is_transducer());
            params[0] = std::move(new_input);
        }

        /// set output of transducer
        void set_output(const std::vector<BasicTerm> &new_output) {
            assert(is_transducer());
            params[1] = new_output;
        }

        /// set output of transducer
        void set_output(std::vector<BasicTerm> &&new_output) {
            assert(is_transducer());
            params[1] = std::move(new_output);
        }

        /// get haystack of notcontains
        [[nodiscard]] std::vector<BasicTerm>& get_haystack() {
            assert(is_not_cont());
            return params[0];
        }

        /// get haystack of notcontains
        [[nodiscard]] const std::vector<BasicTerm>& get_haystack() const {
            assert(is_not_cont());
            return params[0];
        }

        /// get needle of notcontains
        [[nodiscard]] std::vector<BasicTerm>& get_needle() {
            assert(is_not_cont());
            return params[1];
        }

        /// get needle of notcontains
        [[nodiscard]] const std::vector<BasicTerm>& get_needle() const {
            assert(is_not_cont());
            return params[1];
        }

        /// set haystack of transducer
        void set_haystack(const std::vector<BasicTerm> &new_haystack) {
            assert(is_not_cont());
            params[0] = new_haystack;
        }

        /// set haystack of transducer
        void set_haystack(std::vector<BasicTerm> &&new_haystack) {
            assert(is_not_cont());
            params[0] = std::move(new_haystack);
        }

        /// set needle of transducer
        void set_needle(const std::vector<BasicTerm> &new_needle) {
            assert(is_not_cont());
            params[1] = new_needle;
        }

        /// set needle of transducer
        void set_needle(std::vector<BasicTerm> &&new_needle) {
            assert(is_not_cont());
            params[1] = std::move(new_needle);
        }


        /// get set of all variables/literals occuring in the predicate
        [[nodiscard]] std::set<BasicTerm> get_set() const {
            std::set<BasicTerm> ret;
            for(const auto& side : this->params) {
                for(const BasicTerm& t : side)
                    ret.insert(t);
            }
            return ret;
        }

        /// get set of all variables/literals occuring in the paramater at @p index
        [[nodiscard]] std::set<BasicTerm> get_set_of_param(std::vector<std::vector<BasicTerm>>::size_type index) const {
            std::set<BasicTerm> ret;
            for(const BasicTerm& t : this->params[index]) {
                ret.insert(t);
            }
            return ret;
        }

        /// get set ofleft side variables/literals of (dis)equation 
        [[nodiscard]] std::set<BasicTerm> get_left_set() const {
            assert(is_eq_or_ineq());
            return get_set_of_param(0);
        }

        /// get set of right side variables/literals of (dis)equation 
        [[nodiscard]] std::set<BasicTerm> get_right_set() const {
            assert(is_eq_or_ineq());
            return get_set_of_param(1);
        }

        /// get set of input variables/literals of transducer
        [[nodiscard]] std::set<BasicTerm> get_input_set() const {
            assert(is_transducer());
            return get_set_of_param(0);
        }

        /// get set of output variables/literals of transducer
        [[nodiscard]] std::set<BasicTerm> get_output_set() const {
            assert(is_transducer());
            return get_set_of_param(1);
        }

        /// get set of haystack variables/literals of notcontains
        [[nodiscard]] std::set<BasicTerm> get_haystack_set() const {
            assert(is_not_cont());
            return get_set_of_param(0);
        }


        /// get set of needle variables/literals of notcontains
        [[nodiscard]] std::set<BasicTerm> get_needle_set() const {
            assert(is_not_cont());
            return get_set_of_param(1);
        }

        /// get set of only variables in the predicate
        [[nodiscard]] std::set<BasicTerm> get_vars() const;

        /// get set of only variables on @p side of (dis)equation
        [[nodiscard]] std::set<BasicTerm> get_side_vars(EquationSideType side) const;

        /**
         * @brief Check if the predicate contains only constant strings.
         */
        bool is_str_const() const {
            for(const auto& side : this->params) {
                for(const BasicTerm& t : side)
                    if(!t.is_literal()) return false;
            }
            return true;
        }

        /**
         * @brief Get the length formula of the equation. For an equation X1 X2 X3 ... = Y1 Y2 Y3 ...
         * creates a formula |X1|+|X2|+|X3|+ ... = |Y1|+|Y2|+|Y3|+ ...
         *
         * @return LenNode Root of the length formula
         */
        LenNode get_formula_eq() const {

            auto plus_chain = [&](const std::vector<BasicTerm>& side) {
                std::vector<LenNode> ops;
                if(side.size() == 0) {
                    return LenNode(BasicTerm(BasicTermType::Length, "0"));
                }
                if(side.size() == 1) {
                    return LenNode(side[0]);
                }
                for(const BasicTerm& t : side) {
                    LenNode n = LenNode(t);
                    ops.push_back(n);
                }
                return LenNode(LenFormulaType::PLUS, ops);
            };

            assert(is_eq_or_ineq());
            LenNode left = plus_chain(this->params[0]);
            LenNode right = plus_chain(this->params[1]);
            LenNode eq = LenNode(LenFormulaType::EQ, {left, right});

            if(is_inequation()) {
                eq =  LenNode(LenFormulaType::NOT, {eq});
            }

            return eq;
        }

        /// get @p side of (dis)equation 
        std::vector<BasicTerm>& get_side(EquationSideType side);

        /// get @p side of (dis)equation 
        [[nodiscard]] const std::vector<BasicTerm>& get_side(EquationSideType side) const;

        /// get predicate with switched sides (for (dis)equations and transducers), transducers also invert
        [[nodiscard]] Predicate get_switched_sides_predicate() const {
            assert(is_two_sided());
            // for transducers we need to invert tapes, i.e., T(x,y) iff T^{-1}(y,x)
            if(is_transducer()) {
                auto nft_inverse = std::make_shared<mata::nft::Nft>(mata::nft::invert_levels(*transducer));
                return Predicate::create_transducer(nft_inverse, get_output(), get_input());
            }
            return Predicate{ type, { get_right_side(), get_left_side() } };
        }

        /**
         * @brief Replace BasicTerm @p find in the given concatenation
         *
         * @param concat Concatenation to be searche/replaced
         * @param find  Find
         * @param replace Replace
         * @param res Result
         * @return Does the concatenation contain at least one occurrence of @p find ?
         */
        static bool replace_concat(
                const std::vector<BasicTerm>& concat,
                const std::vector<BasicTerm>& find,
                const std::vector<BasicTerm>& replace,
                std::vector<BasicTerm>& res) {
            bool modif = false;
            for(auto it = concat.begin(); it != concat.end(); ) {
                if(std::equal(it, it+find.size(), find.begin(), find.end())) {
                    res.insert(res.end(), replace.begin(), replace.end());
                    modif = true;
                    it += find.size();
                } else {
                    res.push_back(*it);
                    it++;
                }
            }
            return modif;
        }

        /**
         * @brief Replace BasicTerm @p find in the predicate (do not modify the current one).
         *
         * @param find Find
         * @param replace Replace
         * @param res Where to store the modified predicate
         * @return Does the predicate contain at least one occurrence of @p find ?
         */
        bool replace(const std::vector<BasicTerm>& find, const std::vector<BasicTerm>& replace, Predicate& res) const {
            std::vector<std::vector<BasicTerm>> new_params;
            bool modif = false;
            for(const std::vector<BasicTerm>& p : this->params) {
                std::vector<BasicTerm> res_vec;
                bool r = Predicate::replace_concat(p, find, replace, res_vec);
                new_params.push_back(res_vec);
                modif = modif || r;
            }
            res = Predicate(this->type, new_params);
            res.transducer = this->transducer;
            return modif;
        }

        /**
         * Decide whether the @p side contains multiple occurrences of a single variable (with a same name).
         * 
         * @param side Side to check.
         * @return True if there are multiple occurrences of a single variable. False otherwise.
         */
        [[nodiscard]] bool mult_occurr_var_side(EquationSideType side) const;

        void replace(void* replace_map) {
            (void) replace_map;
            throw std::runtime_error("unimplemented");
        }

        void remove(void* terms_to_remove) {
            (void) terms_to_remove;
            throw std::runtime_error("unimplemented");
        }

        /**
         * @brief Count number of variables and sum of lengths of all literals
         * (represented by literal "" in the map).
         *
         * @param side Side of the term
         * @return std::map<BasicTerm, unsigned> Number of variables / sum of lits lengths
         */
        std::map<BasicTerm, unsigned> variable_count(const Predicate::EquationSideType side) const;

        /**
         * @brief Split literals into literals consisting of a single symbol.
         *
         * @return Predicate Modified predicate where each literal is a symbol.
         */
        Predicate split_literals() const;

        /**
         * @brief Strong equality. For the case of transducer predicates the transducers
         * are compared for identity (not just the indentity of pointers).
         * 
         * @param other Other predicate
         * @return true Is strongly equal
         */
        bool strong_equals(const Predicate& other) const;

        bool operator==(const Predicate& other) const {
            return (type == other.type && params == other.params && transducer == other.transducer);
        }

        std::strong_ordering operator<=>(const Predicate& other) const {
            if (type < other.type) {
                return std::strong_ordering::less;
            } else if (type > other.type) {
                return std::strong_ordering::greater;
            }
    
            // Types are equal. Compare data.
            if (params < other.params) {
                return std::strong_ordering::less;
            } else if (params > other.params) {
                return std::strong_ordering::greater;
            }

            if (transducer < other.transducer) {
                return std::strong_ordering::less;
            } else if (transducer > other.transducer) {
                return std::strong_ordering::greater;
            }

            return std::strong_ordering::equal;
        }

        [[nodiscard]] std::string to_string() const;

        struct HashFunction {
            size_t operator()(const Predicate& predicate) const {
                size_t res{};
                size_t row_hash = std::hash<PredicateType>()(predicate.type);
                for(const auto& pr : predicate.get_params()) {
                    for(const BasicTerm& term : pr) {
                        size_t col_hash = BasicTerm::HashFunction()(term) << 1;
                        res ^= col_hash;
                    }
                }
                return row_hash ^ res;
            }
        };

        /**
         * @brief Get the transducer shared pointer (for the transducer predicates only).
         * 
         * @return std::shared_ptr<mata::nft::Nft> Transducer
         */
        const std::shared_ptr<mata::nft::Nft>& get_transducer() const {
            assert(is_transducer());
            return transducer;
        }
        std::shared_ptr<mata::nft::Nft>& get_transducer() {
            assert(is_transducer());
            return transducer;
        }
    }; // Class Predicate.

    [[nodiscard]] static std::string to_string(const Predicate& predicate) {
        return predicate.to_string();
    }

    static std::ostream& operator<<(std::ostream& os, const Predicate& predicate) {
        os << predicate.to_string();
        return os;
    }

    //----------------------------------------------------------------------------------------------------------------------------------

    class Formula {
    private:
        std::vector<Predicate> predicates;
    public:
        std::vector<Predicate>& get_predicates() { return predicates; }
        const std::vector<Predicate>& get_predicates() const { return predicates; }

        // TODO: Use std::move for both add functions?
        void add_predicate(Predicate predicate) { predicates.push_back(std::move(predicate)); }

        std::string to_string() const {
            std::string ret;
            for(const Predicate& p : this->predicates) {
                ret += p.to_string() + "\n";
            }
            return ret;
        }

        /**
         * @brief Extract and remove predicate of the type @p type from the formula.
         * The predicates of the type @p type are stored in the output @p extracted
         * It removes the extracted predicates from the current formula.
         *
         * @param type Predicate type
         * @param[out] extracted Where to store extracted predicates
         */
        void extract_predicates(PredicateType type, Formula& extracted) {
            std::vector<Predicate> new_predicates {};
            for(const Predicate& pred : this->predicates) {
                if(pred.get_type() == type) {
                    extracted.add_predicate(pred);
                } else {
                    new_predicates.emplace_back(pred);
                }
            }
            this->predicates = new_predicates;
        }

        /**
         * @brief Does the Formula contain a predicate of a type @p type ?
         *
         * @param type Type of the predicate.
         * @return true <-> Formula contains predicate of type @p type.
         */
        bool contains_pred_type(PredicateType type) const {
            for(const Predicate& pred : this->predicates) {
                if(pred.get_type() == type) {
                    return true;
                }
            }
            return false;
        }

        /**
         * @brief Get union of variables from all predicates
         *
         * @return std::set<BasicTerm> Variables
         */
        std::set<BasicTerm> get_vars() const {
            std::set<BasicTerm> ret;
            for(const auto& p : this->predicates) {
                auto vars = p.get_vars();
                ret.insert(vars.begin(), vars.end());
            }
            return ret;
        }

        /**
         * @brief Check whether a formula is quadratic.
         *
         * @return true <-> quadratic
         */
        bool is_quadratic() const {
            std::map<BasicTerm, unsigned> occur_map;

            auto upd = [&occur_map] (const std::vector<BasicTerm>& vc) {
                for(const BasicTerm& bt : vc) {
                    if(!bt.is_variable()) continue;
                    occur_map[bt]++;
                }
            };
            for(const Predicate& pred : this->predicates) {
                if(!pred.is_equation()) {
                    return false;
                }
                upd(pred.get_right_side());
                upd(pred.get_left_side());
            }
            for(const auto& pr : occur_map) {
                if(pr.second > 2)
                    return false;
            }
            return true;
        }

        /**
         * @brief Check whether all predicates match the given type.
         *
         * @param tp Predicate type
         * @return true <-> All predicates are of type @p tp
         */
        bool all_of_type(PredicateType tp) {
            for(const Predicate& pred : this->predicates) {
                if(pred.get_type() != tp) {
                    return false;
                }
            }
            return true;
        }

        /**
         * @brief Replace in all predicates
         *
         * @param find What to find
         * @param replace What to replace
         * @return Formula Modified formula according to the replace
         */
        Formula replace(const std::vector<BasicTerm>& find, const std::vector<BasicTerm>& replace) const {
            Formula ret;
            for(const Predicate& pred : this->predicates) {
                Predicate res;
                pred.replace(find, replace, res);
                ret.add_predicate(res);
            }
            return ret;
        }

        /**
         * @brief Split literals into literals consisting of a single symbol.
         *
         * @return Formula Modified formula where each literal is a symbol.
         */
        Formula split_literals() const {
            Formula new_formula;
            for(const Predicate& pred : this->predicates) {
                new_formula.add_predicate(pred.split_literals());
            }
            return new_formula;
        }
    }; // Class Formula.

    static bool operator==(const Formula& lhs, const Formula& rhs) { return lhs.get_predicates() == rhs.get_predicates(); }
    static bool operator!=(const Formula& lhs, const Formula& rhs) { return !(lhs == rhs); }
    static bool operator<(const Formula& lhs, const Formula& rhs) {
       return lhs.get_predicates() < rhs.get_predicates();
    }
    static bool operator>(const Formula& lhs, const Formula& rhs) { return !(lhs < rhs); }

    // Conversions of strings to ints/code values and vice versa
    enum class ConversionType {
        TO_CODE,
        FROM_CODE,
        TO_INT,
        FROM_INT,
    };

    // Term conversion: to_int/from_int/to_code/from_code
    struct TermConversion {
        ConversionType type;
        BasicTerm string_var;
        BasicTerm int_var;

        TermConversion(ConversionType type, BasicTerm string_var, BasicTerm int_var) : type(type), string_var(std::move(string_var)), int_var(std::move(int_var)) {}
    };

    inline std::string get_conversion_name(ConversionType type) {
        switch (type)
        {
        case ConversionType::TO_CODE:
            return "to_code";
        case ConversionType::FROM_CODE:
            return "from_code";
        case ConversionType::TO_INT:
            return "to_int";
        case ConversionType::FROM_INT:
            return "from_int";

        default:
            UNREACHABLE();
            return "";
        }
    }

    /**
     * Context (other formulae) in which a formula is to be used.
     */
    struct LenFormulaContext {
        ast_manager& manager;
        arith_util&  arith_utilities;
        seq_util  &  seq_utilities;

        /**
         * Maps quantified variable names to the quantifier-depth of the corresponding quantifier.
         *
         * Necessary to correctly compute de Brujin sequences for the indices, which facilitate
         * the binding between a quantifier and a new variable.
         */
        std::map<std::string, unsigned>& quantified_vars;
        std::map<BasicTerm, expr_ref>&   known_z3_exprs;

        int current_quantif_depth = 0;  // To compute de Brujin numbers for quantified variables
    };

    /**
     * Convert given len_node into z3's expression.
     * 
     * The function accepts a context (collections of references to managers/utils) to allow
     * for easier unit testing. If embedded in theory_str_noodler, one would have to instantiate
     * and setup a lot of things just to check whether a formula instance is being correctly converted.
     * 
     * @note: The function does not correctly handle nested quantifiers when variables have the same names.
     * 
     * @param ctx Collection of references to managers and utils used during the conversion.
     */
    expr_ref convert_len_node_to_z3_formula(LenFormulaContext &ctx, const LenNode &node);

    /**
     * Helper function to construct quantifier expressions when converting len_nodes into z3's expressions.
     */
    expr_ref construct_z3_expr_for_len_node_quantifier(LenFormulaContext& ctx, const LenNode& node, enum quantifier_kind quantif_kind);


} // Namespace smt::noodler.

namespace std {
    template<>
    struct hash<smt::noodler::Predicate> {
        inline size_t operator()(const smt::noodler::Predicate& predicate) const {
            size_t accum = smt::noodler::Predicate::HashFunction()(predicate);
            return accum;
        }
    };

    template<>
    struct hash<smt::noodler::BasicTerm> {
        inline size_t operator()(const smt::noodler::BasicTerm& basic_term) const {
            size_t accum = smt::noodler::BasicTerm::HashFunction()(basic_term);
            return accum;
        }
    };
}

#endif //Z3_NOODLER_FORMULA_H
