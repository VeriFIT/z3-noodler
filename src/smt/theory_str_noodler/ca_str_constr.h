#ifndef Z3_STR_CA_CONSTR_H_
#define Z3_STR_CA_CONSTR_H_

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
#include "counter_automaton.h"
#include "aut_assignment.h"

namespace smt::noodler::ca {


    static LenNode get_lia_for_disequations(const Formula& diseqs, const AutAssignment& autass) {
        return LenNode(LenFormulaType::FALSE);
    }

}

#endif