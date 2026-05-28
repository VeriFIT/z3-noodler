
#include "params/theory_str_noodler_params.h"
#include "params/smt_params_helper.hpp"
#include "util/gparams.h"

void theory_str_noodler_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_underapproximation = p.str_underapprox();
    m_preprocess_red = p.str_preprocess_red();
    m_preprocess_nft = p.str_preprocess_nft();
    m_homomorphism_heuristic = p.str_homomorphism_heuristic();
    m_loop_protect = p.str_loop_protect();
    m_try_nielsen = p.str_try_nielsen();
    m_try_length_proc = p.str_try_length_proc();
    m_try_memb_heur = p.str_try_membership_heur();
    m_try_unary_proc = p.str_try_unary_proc();
    m_underapprox_length = p.str_underapprox_length();
    m_ca_constr = p.str_ca_constr();
    m_ecma_engine_semantics = p.str_ecma_engine_semantics();
    m_postpone_diseqs_stabilization = p.str_postpone_diseqs_stabilization();
    m_try_premature_len_checks = p.str_try_premature_length_checks();
    m_enable_warnings = p.str_enable_warnings();
    m_produce_models = gparams::get_ref().get_bool("model", false);
}

#define DISPLAY_PARAM(X) out << #X"=" << X << std::endl;

void theory_str_noodler_params::display(std::ostream & out) const {
    DISPLAY_PARAM(m_underapproximation);
    DISPLAY_PARAM(m_preprocess_red);
    DISPLAY_PARAM(m_preprocess_nft);
    DISPLAY_PARAM(m_homomorphism_heuristic);
    DISPLAY_PARAM(m_loop_protect);
    DISPLAY_PARAM(m_try_nielsen);
    DISPLAY_PARAM(m_try_length_proc);
    DISPLAY_PARAM(m_try_memb_heur);
    DISPLAY_PARAM(m_try_unary_proc);
    DISPLAY_PARAM(m_underapprox_length);
    DISPLAY_PARAM(m_produce_models);
    DISPLAY_PARAM(m_ca_constr);
    DISPLAY_PARAM(m_ecma_engine_semantics);
    DISPLAY_PARAM(m_postpone_diseqs_stabilization);
    DISPLAY_PARAM(m_enable_warnings);
}
