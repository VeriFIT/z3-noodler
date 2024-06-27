
#include "formula.h"

namespace smt::noodler {
    std::set<BasicTerm> Predicate::get_vars() const {
        std::set<BasicTerm> vars;
        for (const auto& side: params) {
            for (const auto &term: side) {
                if (term.is_variable()) {
                    vars.insert(term);
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

    Predicate Predicate::split_literals() const {
        const auto& split_concat = [&](const std::vector<BasicTerm>& con) {
            std::vector<BasicTerm> ret;
            for(const BasicTerm& bt : con) {
                if(bt.is_literal()) {
                    zstring name = bt.get_name();
                    for(size_t i = 0; i < name.length(); ++i) {
                        ret.emplace_back(BasicTerm(BasicTermType::Literal, zstring(name[i])));
                    }
                } else {
                    ret.push_back(bt);
                }
            }
            return ret;
        };

        std::vector<std::vector<BasicTerm>> new_pars;
        for(const auto& par : this->params) {
            new_pars.push_back(split_concat(par));
        }
        return Predicate(this->get_type(), new_pars);
    }

    std::string Predicate::to_string() const {
        switch (type) {
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

            case PredicateType::NotContains: {
                std::string result{ "Notcontains " };
                for (const auto& item: params[0]) {
                    result += " " + item.to_string();
                }
                result += " ,";
                for (const auto& item: params[1]) {
                    result += " " + item.to_string();
                }
                return result;
            }
        }

        throw std::runtime_error("Unhandled predicate type passed as 'this' to to_string().");
    }

    bool Predicate::equals(const Predicate &other) const {
        if (type == other.type) {
            if (is_two_sided()) {
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

    std::map<BasicTerm, unsigned> Predicate::variable_count(const Predicate::EquationSideType side) const {
        std::map<BasicTerm, unsigned> occurr;
        BasicTerm litTerm(BasicTermType::Literal, "");
        unsigned lits = 0;
        for(const BasicTerm& b : this->get_side(side)) {
            if(b.is_variable()) {
                occurr[b]++;
            } else {
                lits += b.get_name().length();
            }
        }
        occurr[litTerm] = lits;
        return occurr;
    }

    std::string BasicTerm::to_string() const {
        switch (type) {
            case BasicTermType::Literal: {
                return ("\"" + name.encode() + "\"");
            }
            case BasicTermType::Variable:
                return name.encode();
            case BasicTermType::Length:
                return name.encode() + " (" + noodler::to_string(type) + ")";
                // TODO: Decide what will have names and when to use them.
        }

        throw std::runtime_error("Unhandled basic term type passed as 'this' to to_string().");
    }
} // Namespace smt::noodler.
