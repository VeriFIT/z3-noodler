#ifndef Z3_STR_COUNTER_AUT_H_
#define Z3_STR_COUNTER_AUT_H_

#include <iostream>
#include <map>
#include <set>
#include <queue>
#include <string>
#include <memory>
#include <concepts>
#include <compare>

#include <mata/nfa/nfa.hh>
#include <mata/nfa/strings.hh>
#include <mata/nfa/builder.hh>

#include "formula.h"
#include "util.h"

namespace smt::noodler::ca {

    template <typename T>
    requires std::strict_weak_order<std::less<T>, T const&, T const&>
    class StructAlphabet {

    private:
        std::map<T, mata::Symbol> alph_symb_mata {};
        std::map<mata::Symbol, T> alph_mata_symb {};

    public:

        StructAlphabet() : alph_symb_mata(), alph_mata_symb() { }

        mata::Symbol add_symbol(const T& symb) {
            mata::Symbol new_symbol = this->alph_symb_mata.size();
            auto iter = this->alph_symb_mata.find(symb);
            if (iter != this->alph_symb_mata.end()) {
                return iter->second;
            } else {
                this->alph_symb_mata[symb] = new_symbol;
                this->alph_mata_symb[new_symbol] = symb;
                return new_symbol;
            }
        };

        void insert(const mata::Symbol mata_symb, const T& symb) {
            this->alph_symb_mata[symb] = mata_symb;
            this->alph_mata_symb[mata_symb] = symb;
        }

        mata::Symbol get_mata_symbol(const T& symb) const {
            return this->alph_symb_mata.at(symb);
        }

        const T& get_symbol(const mata::Symbol symb) const {
            return this->alph_mata_symb.at(symb);
        }

        std::set<T> get_all_symbols() const {
            std::set<T> ret;
            for (const auto& [key,val] : this->alph_symb_mata) {
                ret.insert(key);
            }
            return ret;
        }

    };

    /**
     * @brief Symbols of the form <mark, var, label, symbol>
     */
    struct AtomicSymbol {
        char mark; // 0 = L; 1 = P; 2 = R
        BasicTerm var; // variable from string constraint
        char label; // 0 = missing value
        mata::Symbol symbol; // symbol (used for the R-case)

        bool operator<(const AtomicSymbol& as) const {
            auto cmp = mark <=> as.mark ;
            if(cmp < 0) {
                return true;
            } else if (cmp > 0) {
                return false;
            } else {
                cmp = label <=> as.label;
                if(cmp < 0) {
                    return true;
                } else if (cmp > 0) {
                    return false;
                } else {
                    cmp = symbol <=> as.symbol;
                    if(cmp < 0) {
                        return true;
                    } else if (cmp > 0) {
                        return false;
                    } else {
                        return var < as.var;
                    }
                }
            }
        }
        bool operator==(const AtomicSymbol&) const = default;

        std::string to_string() const {
            std::string ret;
            std::string marks[3] = {"L", "P", "R"};
            std::string var_escape = var.is_literal() ? "\\\"" + var.get_name().encode() + "\\\"" : var.to_string();

            std::string label_str = label == 0 ? "" : "," + std::to_string(int(label));
            std::string symbol_str = mark == 2 ? "," + std::to_string(symbol) : "";
            std::string var_str = mark <= 2 ? "," + var_escape : "";

            ret = "<" + marks[size_t(mark)] + var_str + label_str + symbol_str + ">";
            return ret;
        }
    };

    using CounterAlphabet = StructAlphabet<std::set<AtomicSymbol>>;

    /**
     * @brief Counter Automaton
     */
    struct CA {
        // underlying nfa
        mata::nfa::Nfa nfa;
        // structured alphabed with registe updates
        CounterAlphabet alph;
        // variable ordering
        std::vector<BasicTerm> var_order {};

        std::string symbol_to_string(const std::set<AtomicSymbol>& sym) const {
            std::string ret;
            for(const AtomicSymbol& as : sym) {
                ret += as.to_string() + " ";
            }
            return ret;
        }

        // taken and modified from Mata
        void print_to_DOT(std::ostream &output) const {
            output << "digraph finiteAutomaton {" << std::endl
                        << "node [shape=circle];" << std::endl;

            for (mata::nfa::State final_state: nfa.final) {
                output << final_state << " [shape=doublecircle];" << std::endl;
            }

            const size_t delta_size = nfa.delta.num_of_states();
            for (mata::nfa::State source = 0; source != delta_size; ++source) {
                for (const mata::nfa::SymbolPost &move: nfa.delta[source]) {
                    output << source << " -> {";
                    for (mata::nfa::State target: move.targets) {
                        output << target << " ";
                    }
                    output << "} [label=\"" << symbol_to_string(alph.get_symbol(move.symbol)) << "\"];" << std::endl;
                }
            }

            output << "node [shape=none, label=\"\"];" << std::endl;
            for (mata::nfa::State init_state: nfa.initial) {
                output << "i" << init_state << " -> " << init_state << ";" << std::endl;
            }

            output << "}" << std::endl;
        }
    };

    
}


#endif