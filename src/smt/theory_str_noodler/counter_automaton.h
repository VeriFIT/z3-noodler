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

    /**
     * @brief Structured alphabet. Performs mapping between mata symbols
     * and particular symbols T.
     *
     * @tparam T Symbol type
     */
    template <typename T>
    requires std::strict_weak_order<std::less<T>, T const&, T const&>
    class StructAlphabet {

    private:
        std::map<T, mata::Symbol> alph_symb_mata {};
        std::map<mata::Symbol, T> alph_mata_symb {};

    public:

        StructAlphabet() : alph_symb_mata(), alph_mata_symb() { }

        mata::Symbol add_symbol(const T& symb) {
            // Speculate: if the given @p symb is not in the map, then this will be its handle
            mata::Symbol new_symbol = this->alph_symb_mata.size();

            // Use .emplace to avoid doing another lookup to store the value if is not present in the map
            const auto& [map_bucket, did_emplace_insert_new] = this->alph_symb_mata.emplace(symb, new_symbol);

            if (did_emplace_insert_new) {
                // Create the reverse mapping
                this->alph_mata_symb[new_symbol] = symb;
            }

            return map_bucket->second;  // The bucket's value (.second) is correct regardless of previous existence
        }

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
     * <L,var> counts the length of a string assignment of variable var
     * <P,var,i> counts the i-th mismatch in variable var (i=label)
     * <R,x,i,symb> captures i-th mismatch symbol (i=label)
     */
    struct AtomicSymbol {
        enum class TagType : uint8_t {
            LENGTH         = 0, // <L, x>
            MISMATCH_POS   = 1, // <P, var, mismatch_idx>
            REGISTER_STORE = 2, // <R, var, mismatch_idx, alphabet_symbol>
            COPY_PREVIOUS  = 3, // <C, var, mismatch_idx>
        };


        TagType      type;
        BasicTerm    var;    // variable from string constraint
        char         label;  // 0 = missing value
        mata::Symbol symbol; // symbol (used for the R-case)

        bool operator<(const AtomicSymbol& other_symbol) const {
            auto cmp = type <=> other_symbol.type ;
            if (cmp < 0) {
                return true;
            } else if (cmp > 0) {
                return false;
            } else {
                cmp = label <=> other_symbol.label;
                if (cmp < 0) {
                    return true;
                } else if (cmp > 0) {
                    return false;
                } else {
                    cmp = symbol <=> other_symbol.symbol;
                    if (cmp < 0) {
                        return true;
                    } else if (cmp > 0) {
                        return false;
                    } else {
                        return var < other_symbol.var;
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
            std::string symbol_str = type == TagType::REGISTER_STORE ? "," + std::to_string(symbol) : "";
            std::string var_str = type <= TagType::REGISTER_STORE ? "," + var_escape : "";

            ret = "<" + marks[size_t(type)] + var_str + label_str + symbol_str + ">";
            return ret;
        }

        static AtomicSymbol create_l_symbol(const BasicTerm& var) {
            return AtomicSymbol{TagType::LENGTH, var, 0, 0};
        }

        static AtomicSymbol create_p_symbol(const BasicTerm& var, char label) {
            return AtomicSymbol{TagType::MISMATCH_POS, var, label, 0};
        }

        static AtomicSymbol create_r_symbol(const BasicTerm& var, char label, mata::Symbol symbol) {
            return AtomicSymbol{TagType::REGISTER_STORE, var, label, symbol};
        }

    private:
        // private constructor; the AtomicSymbol should be constructed using functions create*
        AtomicSymbol(TagType mrk, const BasicTerm& vr, char lbl, mata::Symbol symb ) : type(mrk), var(vr), label(lbl), symbol(symb) {}
    };

    using CounterAlphabet = StructAlphabet<std::set<AtomicSymbol>>;

    /**
     * @brief Tag automaton: an automaton with special symbols consisting of sets of tags present on its transition edges.
     */
    struct TagAut {
        // underlying nfa
        mata::nfa::Nfa nfa;
        // Structured alphabet providing bi-directional between sets of tags and their corresponding Mata handles that are actually used by mata
        CounterAlphabet alph;
        // variable ordering
        std::vector<BasicTerm> var_order {};

        // Debugging: color states in the tag automaton according to the variable it originates in
        std::unordered_map<mata::nfa::State, uint64_t> node_color_map;

        size_t num_of_states_in_row;

        std::string symbol_to_string(const std::set<AtomicSymbol>& sym) const {
            std::string ret;
            for(const AtomicSymbol& as : sym) {
                ret += as.to_string() + " ";
            }
            return ret;
        }

        // taken and modified from Mata
        void print_to_dot(std::ostream &output) const {
            const char* color_table[] = {
                "gray", // DEFAULT
                "red",
                "green",
                "blue",
                "yellow",
                "purple",
            };

            const size_t state_cnt = nfa.delta.num_of_states();

            // Collect all used states so we do not create notes for needless states
            // #Optimize(mhecko): maybe bit_set could be faster
            std::unordered_set<mata::nfa::State> used_states;
            for (mata::nfa::State source_state = 0; source_state < state_cnt; ++source_state) {
                for (const mata::nfa::SymbolPost &move: nfa.delta[source_state]) {
                    for (mata::nfa::State target_state: move.targets) {
                        used_states.insert(source_state);
                        used_states.insert(target_state);
                    }
                }
            }

            output << "digraph finiteAutomaton {" << std::endl
                        << "node [shape=circle];" << std::endl;

            for (mata::nfa::State state = 0; state < state_cnt; state++) {
                if (!used_states.contains(state)) continue;

                bool is_final = nfa.final.contains(state);
                auto color_val_it = this->node_color_map.find(state);
                uint64_t color_idx = (color_val_it == this->node_color_map.end()) ? 0 : color_val_it->second;
                color_idx = color_idx >= sizeof(color_table) ? 0 : color_idx; // Reset if overflow

                const char* shape = is_final ? "doublecircle" : "circle";
                const char* color = color_table[color_idx];

                output << "node_" << state << "[style=filled, fillcolor=" << color << ", shape=" << shape << ", label=" << state << "];\n";
            }


            for (mata::nfa::State source = 0; source != state_cnt; ++source) {
                for (const mata::nfa::SymbolPost &move: nfa.delta[source]) {
                    output << "node_" << source << " -> {";
                    for (mata::nfa::State target: move.targets) {
                        output << "node_" << target << " ";
                    }
                    output << "} [label=\"" << symbol_to_string(alph.get_symbol(move.symbol)) << "\"];" << std::endl;
                }
            }

            output << "node [shape=none, label=\"\"];" << std::endl;
            for (mata::nfa::State init_state: nfa.initial) {
                output << "i" << init_state << " -> " << "node_" << init_state << ";" << std::endl;
            }

            output << "}" << std::endl;
        }

        std::set<ca::AtomicSymbol> gather_used_symbols() {
            std::set<AtomicSymbol> atomic_symbols;
            for (const auto& trans : this->nfa.delta.transitions()) {
                std::set<AtomicSymbol> sms = this->alph.get_symbol(trans.symbol);
                atomic_symbols.insert(sms.begin(), sms.end());
            }
            return atomic_symbols;
        }

    };


}


#endif
