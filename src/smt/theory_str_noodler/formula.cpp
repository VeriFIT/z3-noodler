
#include "formula.h"

namespace smt::noodler {
    std::set<BasicTerm> Predicate::get_vars() const {
        assert(is_eq_or_ineq());
        std::set<BasicTerm> vars;
        for (const auto& side: params) {
            for (const auto &term: side) {
                if (term.is_variable()) {
                    bool found{false};
                    for (const auto &var: vars) {
                        if (var == term) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) { vars.insert(term); }
                }
            }
        }
        return vars;
    }

    std::set<BasicTerm> Predicate::get_side_vars(const Predicate::EquationSideType side) const {
        assert(is_eq_or_ineq());
        std::set<BasicTerm> vars;
        std::vector<BasicTerm> side_terms;
        switch (side) {
            case EquationSideType::Left:
                side_terms = get_left_side();
                break;
            case EquationSideType::Right:
                side_terms = get_right_side();
                break;
            default:
                throw std::runtime_error("unhandled equation side_terms type");
                break;
        }

        for (const auto &term: side_terms) {
            if (term.is_variable()) {
                bool found{false};
                for (const auto &var: vars) {
                    if (var == term) {
                        found = true;
                        break;
                    }
                }
                if (!found) { vars.insert(term); }
            }
        }
        return vars;
    }

    bool Predicate::mult_occurr_var_side(const Predicate::EquationSideType side) const {
        assert(is_eq_or_ineq());
        const auto terms_begin{ get_side(side).cbegin() };
        const auto terms_end{ get_side(side).cend() };
        for (auto term_iter{ terms_begin }; term_iter < terms_end; ++term_iter) {
            if (term_iter->is_variable()) {
                for (auto term_iter_following{ term_iter + 1}; term_iter_following < terms_end;
                     ++term_iter_following) {
                    if (*term_iter == *term_iter_following) {
                        return true;
                        // TODO: How to handle calls of predicates?
                    }
                }
            }
        }
        return false;
    }

    std::string Predicate::to_string() const {
        switch (type) {
            case PredicateType::Default: {
                return "Default (missing type and data)";
            }
            case PredicateType::Equation: {
                std::string result{ "Equation:" };
                for (const auto& item: get_left_side()) {
                    result += " " + item.to_string();
                }
                result += " =";
                for (const auto& item: get_right_side()) {
                    result += " " + item.to_string();
                }
                return result;
            }

            case PredicateType::Inequation: {
                std::string result{ "Inequation:" };
                for (const auto& item: get_left_side()) {
                    result += " " + item.to_string();
                }
                result += " !=";
                for (const auto& item: get_right_side()) {
                    result += " " + item.to_string();
                }
                return result;
            }

                // TODO: Implement prints for other predicates.

            case PredicateType::Contains: {
                break;
            }
        }

        throw std::runtime_error("Unhandled predicate type passed as 'this' to to_string().");
    }

    bool Predicate::equals(const Predicate &other) const {
        if (type == other.type) {
            if (is_eq_or_ineq()) {
                return params[0] == other.params[0] && params[1] == other.params[1];
            }
            return true;
        }
        return false;
    }

    const std::vector<BasicTerm> &Predicate::get_side(const Predicate::EquationSideType side) const {
        assert(is_eq_or_ineq());
        switch (side) {
            case EquationSideType::Left:
                return params[0];
                break;
            case EquationSideType::Right:
                return params[1];
                break;
            default:
                throw std::runtime_error("unhandled equation side type");
                break;
        }
    }

    std::vector<BasicTerm> &Predicate::get_side(const Predicate::EquationSideType side) {
        assert(is_eq_or_ineq());
        switch (side) {
            case EquationSideType::Left:
                return params[0];
                break;
            case EquationSideType::Right:
                return params[1];
                break;
            default:
                throw std::runtime_error("unhandled equation side type");
                break;
        }
    }

    std::string BasicTerm::to_string() const {
        switch (type) {
            case BasicTermType::Literal: {
                std::string result{};
                if (!name.empty()) {
                    result += "\"" + name.encode() + "\"";
                }
                return result;
            }
            case BasicTermType::Variable:
                return name.encode();
            case BasicTermType::Length:
            case BasicTermType::Substring:
            case BasicTermType::IndexOf:
                return name.encode() + " (" + noodler::to_string(type) + ")";
                // TODO: Decide what will have names and when to use them.
        }

        throw std::runtime_error("Unhandled basic term type passed as 'this' to to_string().");
    }
} // Namespace smt::noodler.
