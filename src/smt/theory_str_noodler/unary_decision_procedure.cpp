
#include "unary_decision_procedure.h"

namespace smt::noodler {
    zstring UnaryDecisionProcedure::get_model(BasicTerm var, const std::map<BasicTerm,rational>& arith_model) {
        zstring smb(unsigned(this->symbol));
        zstring ass = "";
        rational length = arith_model.at(var);
        for(rational i(0); i < length; i++) {
            ass = ass + smb;
        }
        return ass;
    }

}
