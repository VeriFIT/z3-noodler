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
    requires std::totally_ordered<T>
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

        mata::Symbol get_mata_symbol(const T& symb) {
            return this->alph_symb_mata.at(symb);
        }

        const T& get_symbol(const mata::Symbol symb) {
            return this->alph_mata_symb.at(symb);
        }

    };

    using CounterAlphabet = StructAlphabet<std::vector<int>>;

    /**
     * @brief Counter Automaton
     */
    struct CA {
        // underlying nfa
        mata::nfa::Nfa nfa;
        // structured alphabed with registe updates
        CounterAlphabet alph;
        // number of registers
        size_t registers;
    };

    
}


#endif