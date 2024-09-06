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

#include "util/zstring.h"

namespace smt::noodler {
    enum struct PredicateType {
        Equation,
        Inequation,
        NotContains,
    };

    [[nodiscard]] static std::string to_string(PredicateType predicate_type) {
        switch (predicate_type) {
            case PredicateType::Equation:
                return "Equation";
            case PredicateType::Inequation:
                return "Inequation";
            case PredicateType::NotContains:
                return "Notcontains";
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

    //----------------------------------------------------------------------------------------------------------------------------------

    /**
     * @brief Length formula precision
     */
    enum struct LenNodePrecision {
        PRECISE,
        UNDERAPPROX,
        OVERAPPROX,
    };

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
        case LenFormulaType::LEAF:
            return (os << node.atom_val.get_name());
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
     * Write the given formula as SMT2 to the given @p out_stream, including preable.
     */
    void write_len_formula_as_smt2(const LenNode& formula, std::ostream& out_stream);

    //----------------------------------------------------------------------------------------------------------------------------------

    class Predicate {
    public:
        enum struct EquationSideType {
            Left,
            Right,
        };

        Predicate() : type(PredicateType::Equation) {}
        explicit Predicate(const PredicateType type): type(type) {
            if (is_equation() || is_inequation()) {
                params.resize(2);
                params.emplace_back();
                params.emplace_back();
            }
        }

        explicit Predicate(const PredicateType type, std::vector<std::vector<BasicTerm>> par):
            type(type),
            params(par)
            { }

        [[nodiscard]] PredicateType get_type() const { return type; }
        [[nodiscard]] bool is_equation() const { return type == PredicateType::Equation; }
        [[nodiscard]] bool is_inequation() const { return type == PredicateType::Inequation; }
        [[nodiscard]] bool is_not_cont() const { return type == PredicateType::NotContains; }
        [[nodiscard]] bool is_eq_or_ineq() const { return is_equation() || is_inequation(); }
        [[nodiscard]] bool is_two_sided() const { return is_equation() || is_inequation() || is_not_cont(); }
        [[nodiscard]] bool is_predicate() const { return !is_eq_or_ineq(); }
        [[nodiscard]] bool is(const PredicateType predicate_type) const { return predicate_type == this->type; }

        const std::vector<std::vector<BasicTerm>>& get_params() const { return this->params; }

        std::vector<BasicTerm>& get_left_side() {
            assert(is_two_sided());
            return params[0];
        }

        [[nodiscard]] const std::vector<BasicTerm>& get_left_side() const {
            assert(is_two_sided());
            return params[0];
        }

        std::vector<BasicTerm>& get_right_side() {
            assert(is_two_sided());
            return params[1];
        }

        [[nodiscard]] const std::vector<BasicTerm>& get_right_side() const {
            assert(is_two_sided());
            return params[1];
        }

        void set_left_side(const std::vector<BasicTerm> &new_left_side) {
            assert(is_two_sided());
            params[0] = new_left_side;
        }

        void set_left_side(std::vector<BasicTerm> &&new_left_side) {
            assert(is_two_sided());
            params[0] = std::move(new_left_side);
        }

        void set_right_side(const std::vector<BasicTerm> &new_right_side) {
            assert(is_two_sided());
            params[1] = new_right_side;
        }

        void set_right_side(std::vector<BasicTerm> &&new_right_side) {
            assert(is_two_sided());
            params[1] = std::move(new_right_side);
        }

        std::set<BasicTerm> get_set() const {
            std::set<BasicTerm> ret;
            for(const auto& side : this->params) {
                for(const BasicTerm& t : side)
                    ret.insert(t);
            }
            return ret;
        }

        std::set<BasicTerm> get_left_set() const {
            assert(is_eq_or_ineq());
            std::set<BasicTerm> ret;
            for(const BasicTerm& t : this->params[0])
                ret.insert(t);
            return ret;
        }

        std::set<BasicTerm> get_right_set() const {
            assert(is_eq_or_ineq());
            std::set<BasicTerm> ret;
            for(const BasicTerm& t : this->params[1])
                ret.insert(t);
            return ret;
        }

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

            LenNode left = plus_chain(this->params[0]);
            LenNode right = plus_chain(this->params[1]);
            LenNode eq = LenNode(LenFormulaType::EQ, {left, right});

            if(is_inequation()) {
                eq =  LenNode(LenFormulaType::NOT, {eq});
            }

            return eq;
        }

        std::vector<BasicTerm>& get_side(EquationSideType side);

        [[nodiscard]] const std::vector<BasicTerm>& get_side(EquationSideType side) const;

        [[nodiscard]] Predicate get_switched_sides_predicate() const {
            assert(is_eq_or_ineq());
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
            return modif;
        }

        /**
         * Get unique variables on both sides of an (in)equation.
         * @return Variables in the (in)equation.
         */
        [[nodiscard]] std::set<BasicTerm> get_vars() const;

        /**
         * Get unique variables on a single @p side of an (in)equation.
         * @param[in] side (In)Equation side to get variables from.
         * @return Variables in the (in)equation on specified @p side.
         */
        [[nodiscard]] std::set<BasicTerm> get_side_vars(EquationSideType side) const;

        /**
         * Decide whether the @p side contains multiple occurrences of a single variable (with a same name).
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

        [[nodiscard]] bool equals(const Predicate& other) const;

        [[nodiscard]] std::string to_string() const;

        struct HashFunction {
            size_t operator()(const Predicate& predicate) const {
                size_t res{};
                size_t row_hash = std::hash<PredicateType>()(predicate.type);
                for (const auto& term: predicate.get_left_side()) {
                    size_t col_hash = BasicTerm::HashFunction()(term) << 1;
                    res ^= col_hash;
                }
                for (const auto& term: predicate.get_right_side()) {
                    size_t col_hash = BasicTerm::HashFunction()(term) << 1;
                    res ^= col_hash;
                }
                return row_hash ^ res;
            }
        };

        // TODO: Additional operations.

    private:
        PredicateType type;
        std::vector<std::vector<BasicTerm>> params;

        // TODO: Add additional attributes such as cost, etc.
    }; // Class Predicate.

    [[nodiscard]] static std::string to_string(const Predicate& predicate) {
        return predicate.to_string();
    }

    static std::ostream& operator<<(std::ostream& os, const Predicate& predicate) {
        os << predicate.to_string();
        return os;
    }

    static bool operator==(const Predicate& lhs, const Predicate& rhs) { return lhs.equals(rhs); }
    static bool operator!=(const Predicate& lhs, const Predicate& rhs) { return !(lhs == rhs); }
    static bool operator<(const Predicate& lhs, const Predicate& rhs) {
        if (lhs.get_type() < rhs.get_type()) {
            return true;
        } else if (lhs.get_type() > rhs.get_type()) {
            return false;
        }
        // Types are equal. Compare data.
        if (lhs.get_params() < rhs.get_params()) {
            return true;
        }
        return false;
    }
    static bool operator>(const Predicate& lhs, const Predicate& rhs) { return !(lhs < rhs); }

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
