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
    using CA = std::pair<mata::nfa::Nfa, CounterAlphabet>;
    using Transition = std::tuple<mata::nfa::State, mata::Symbol, mata::nfa::State>;


    static LenNode compute_parikh_image(const CA& ca) {
        const auto& [nfa, alph] = ca;
        // pool of fresh variables
        std::vector<BasicTerm> gamma_init {};
        std::vector<BasicTerm> gamma_fin {};
        std::vector<BasicTerm> sigma {};
        // mapping of transitions to concrete variables
        std::map<Transition, BasicTerm> trans {};

        LenNode phi_init(LenFormulaType::AND);
        LenNode sum(LenFormulaType::PLUS);
        for(size_t state = 0; state < nfa.num_of_states(); state++) {
            // create fresh vars
            gamma_init.push_back(util::mk_noodler_var_fresh("gamma_init"));
            if(nfa.initial.contains(state)) {
                // 0 <= gamma_init[state] <= 1
                sum.succ.emplace_back(gamma_init[state]);
                phi_init.succ.emplace_back( LenNode(LenFormulaType::AND, {
                    LenNode(LenFormulaType::LEQ, {0, gamma_init[state]}),
                    LenNode(LenFormulaType::LEQ, {gamma_init[state], 1})
                }) );
            } else {
                // gamma_init[state] == 0
                phi_init.succ.emplace_back( LenNode(LenFormulaType::EQ, {0, gamma_init[state]}) );
            }
        }
        // sum gamma_init[state] for state is initial == 1
        // exactly one initial state is selected
        phi_init.succ.emplace_back( LenNode(LenFormulaType::EQ, {sum, 1}) );

        return phi_init;
    }

    
}


#endif