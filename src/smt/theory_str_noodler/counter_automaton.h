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

#include "util.h"
#include "formula.h"

/**
 * Exapands to two if statements terminating the function containing the macro early.
 *
 * Insert two ifs that make the code containing this macro return true if (cmp_expr < 0) and false if (cmp_expr > 0)
 * @Note: when cmp_expr == 0, the control flow goes/falls through the inserted branches.
 */
#define INSERT_LEXICOGRAPHIC_BRANCH_ON_CMP_RESULT(cmp_expr) \
    {                                       \
        if ((cmp_expr) < 0)      return true;  \
        else if ((cmp_expr) > 0) return false; \
    }

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

        bool has_mata_symbol_for(const T& symbol) const {
            return (this->alph_symb_mata.find(symbol) != this->alph_symb_mata.end());
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
            REGISTER_STORE = 2, // <R, disequation, side, mismatch_idx, alphabet_symbol>
            COPY_PREVIOUS  = 3, // <C, var, disequation, side, mismatch_idx>
        };

        enum class PredicateSide : uint8_t {
            LEFT  = 0,
            RIGHT = 1,
        };

        TagType       type;
        BasicTerm     var;       // variable from string constraint
        int           predicate_idx; // Negative values mean that we only deal with one predicate
        PredicateSide predicate_side;
        size_t        copy_idx;  // What level of the tag automaton is this tag located
        mata::Symbol  symbol;    // Symbol stored during sampling transition (tag with type REGISTER_STORE)

        // Lexicographical order on (type, copy_idx, disequation_idx, predicate_side, symbol, var)
        bool operator<(const AtomicSymbol& other_symbol) const {
            INSERT_LEXICOGRAPHIC_BRANCH_ON_CMP_RESULT(type           <=> other_symbol.type);
            INSERT_LEXICOGRAPHIC_BRANCH_ON_CMP_RESULT(copy_idx       <=> other_symbol.copy_idx);
            INSERT_LEXICOGRAPHIC_BRANCH_ON_CMP_RESULT(predicate_idx  <=> other_symbol.predicate_idx);
            INSERT_LEXICOGRAPHIC_BRANCH_ON_CMP_RESULT(predicate_side <=> other_symbol.predicate_side);
            INSERT_LEXICOGRAPHIC_BRANCH_ON_CMP_RESULT(symbol         <=> other_symbol.symbol);
            return var < other_symbol.var;
        }
        bool operator==(const AtomicSymbol&) const = default;

        bool is_mutating_registers() const {
            return (this->type == TagType::REGISTER_STORE || this->type == TagType::COPY_PREVIOUS);
        }

        std::string to_string() const {
            std::string var_escape = var.is_literal() ? "\\\"" + var.get_name().encode() + "\\\"" : var.to_string();

            switch (this->type) {
                case TagType::LENGTH: {
                    return "<L, " + var_escape + ">";
                }
                case TagType::MISMATCH_POS: { // <P, var, copy_idx>
                    return "<P, " + var_escape + ", " + std::to_string(this->copy_idx) + ">";
                }
                case TagType::REGISTER_STORE: { // <R, var, disequation, side, mismatch_idx, alphabet_symbol>
                    std::stringstream string_builder;
                    string_builder << "<R, "
                                   << var_escape + ", ";
                    if (this->predicate_idx >= 0) {
                        string_builder << this->predicate_idx << "-"
                                       << (this->predicate_side == PredicateSide::LEFT ? "L" : "R")
                                       << ", ";
                    }
                    string_builder << copy_idx << ", " << this->symbol << ">";
                    return string_builder.str();
                }
                case TagType::COPY_PREVIOUS: { // <C, var, disequation, side, mismatch_idx>
                    std::stringstream string_builder;
                    string_builder << "<C, " << var_escape << ", "
                                   << "Pred" << this->predicate_idx << "-"
                                   << (this->predicate_side == PredicateSide::LEFT ? "L" : "R")
                                   << ", " << this->copy_idx << ">";
                    return string_builder.str();
                }
                default: {
                    assert(false);
                    return "??";
                }
            }
        }

        static AtomicSymbol create_l_symbol(const BasicTerm& var) {
            return AtomicSymbol{TagType::LENGTH, var, 0, PredicateSide::LEFT, 0,  0};
        }

        static AtomicSymbol create_p_symbol(const BasicTerm& var, size_t copy_idx) {
            return AtomicSymbol{TagType::MISMATCH_POS, var, 0, PredicateSide::LEFT, copy_idx, 0};
        }

        /**
         * Create mismatch-sampling symbol for a single disequation. When deciding multiple disequations, use
         * create_r_symbol_with_predicate_info.
         */
        static AtomicSymbol create_r_symbol(const BasicTerm& var, size_t copy_idx, mata::Symbol symbol) {
            return AtomicSymbol{TagType::REGISTER_STORE, var, /* predicate_idx */-1, PredicateSide::LEFT, copy_idx, symbol};
        }

        static AtomicSymbol create_r_symbol_with_predicate_info(size_t predicate_idx, const BasicTerm& var, PredicateSide side, size_t copy_idx, mata::Symbol symbol) {
            AtomicSymbol tag(
                TagType::REGISTER_STORE,
                var,
                predicate_idx,
                side,
                copy_idx,
                symbol
            );

            return tag;
        }

        static AtomicSymbol create_c_symbol(const BasicTerm& var, int predicate_idx, PredicateSide side, size_t copy_idx) {
            // Create a Copy tag of the form: <C, x, h, k, i -> i+1> with the following semantics
            // the mismatch letter for _h_-th disequation and its _k_-th side is in variable _x_
            // and it is seen when transitioning from i-th copy. The symbol is the same as the one
            // sampled in previous sampling transition.
            return AtomicSymbol{TagType::COPY_PREVIOUS, var, predicate_idx, side, copy_idx, 0};
        }

    private:
        // private constructor; the AtomicSymbol should be constructed using functions create*
        AtomicSymbol(TagType tag_type, const BasicTerm& var, int predicate_idx, PredicateSide side, size_t copy_idx, mata::Symbol symb )
            : type(tag_type), var(var), predicate_idx(predicate_idx), predicate_side(side), copy_idx(copy_idx), symbol(symb) {}
        AtomicSymbol(TagType tag_type, int predicate_idx, PredicateSide side, size_t copy_idx, mata::Symbol symb )
            : type(tag_type), var(BasicTermType::Variable, "dummy"), predicate_idx(predicate_idx), predicate_side(side), copy_idx(copy_idx), symbol(symb) {}
    };

    using TagSet = std::set<AtomicSymbol>;
    using CounterAlphabet = StructAlphabet<TagSet>;

    /**
     * Metadata about states of a tag automaton, allowing better debugging enabling testing.
     */
    struct TagAutStateMetadata {
        std::vector<size_t> var_info;  // What variable does the state belong to
        std::vector<size_t> levels;    // In what copy does the state reside

        /**
         * Maps states to integers so that two states with the same value are copies of the same state.
         *
         * Underlying nfa is created by copying one NFA multiple times. This
         * field tells if two states are the same because they are a copy of the
         * same state.
         */
        std::vector<size_t> where_is_state_copied_from;
    };

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

        TagAutStateMetadata metadata;

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

        // For some reason we cannot pull parikh_image.h, remake the Transition alias
        typedef std::tuple<mata::nfa::State, mata::Symbol, mata::nfa::State> TransitionTuple;

        // taken and modified from Mata
        void print_to_dot(std::ostream &output, const std::map<TransitionTuple, BasicTerm>& transition_vars = {}) const {
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
                    for (mata::nfa::State target: move.targets) {
                        TransitionTuple transition = std::make_tuple(source, move.symbol, target);
                        auto var_labeling_transition_it = transition_vars.find(transition);

                        output << "node_" << source << " -> "
                               << "node_" << target << " "
                               << " [label=\"" << symbol_to_string(alph.get_symbol(move.symbol));

                        if (var_labeling_transition_it != transition_vars.end()) {
                            output << " (" << var_labeling_transition_it->second << ")";
                        }
                        output << "\"];\n";
                    }
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

namespace std {
    std::ostream& operator<<(std::ostream& out_stream, const smt::noodler::ca::TagSet& tag_set);
}

#endif
