
#pragma once

#include "util/params.h"

struct theory_str_noodler_params {
   
    bool m_underapproximation = false;
    bool m_preprocess_red = false;
    bool m_preprocess_nft = true;
    bool m_homomorphism_heuristic = true;
    bool m_loop_protect = false;
    bool m_try_nielsen = false;
    bool m_try_length_proc = false;
    bool m_try_memb_heur = false;
    bool m_try_unary_proc = false;
    unsigned m_underapprox_length = 5;
    bool is_underapprox = false;
    bool m_produce_models = false;
    bool is_overapprox = false;
    bool m_ca_constr = false;
    bool m_postpone_diseqs_stabilization = true;
    bool m_try_premature_len_checks = true;
    bool m_enable_warnings = false;

    /** @brief Whether to use regex engine semantics when generating ECMA regex constraints.
    *
    *  If true, the regex is implicitly wrapped in Sigma*, allowing to match substrings (like in regex engines).
    *  If false, the regex must match the entire string.
    */
    bool m_ecma_engine_semantics = false;

    theory_str_noodler_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }

    void updt_params(params_ref const & p);
    void display(std::ostream & out) const;
};

