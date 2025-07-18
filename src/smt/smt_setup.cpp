/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_setup.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-24.

Revision History:

--*/
#include "smt/smt_context.h"
#include "smt/smt_setup.h"
#include "ast/static_features.h"
#include "smt/theory_arith.h"
#include "smt/theory_lra.h"
#include "smt/theory_dense_diff_logic.h"
#include "smt/theory_diff_logic.h"
#include "smt/theory_utvpi.h"
#include "smt/theory_array.h"
#include "smt/theory_array_full.h"
#include "smt/theory_bv.h"
#include "smt/theory_intblast.h"
#include "smt/theory_datatype.h"
#include "smt/theory_recfun.h"
#include "smt/theory_dummy.h"
#include "smt/theory_dl.h"
#include "smt/theory_seq_empty.h"
#include "smt/theory_seq.h"
#include "smt/theory_char.h"
#include "smt/theory_special_relations.h"
#include "smt/theory_sls.h"
#include "smt/theory_pb.h"
#include "smt/theory_fpa.h"
#include "smt/theory_str.h"
#include "smt/theory_polymorphism.h"
#include "smt/theory_str_noodler/theory_str_noodler.h"

namespace smt {

    setup::setup(context & c, smt_params & params):
        m_context(c),
        m_manager(c.get_manager()),
        m_params(params),
        m_already_configured(false) {
    }

    void setup::operator()(config_mode cm) {
        TRACE(internalize, tout << "setup " << &m_context << "\n";);
        SASSERT(m_context.get_scope_level() == 0);
        SASSERT(!m_already_configured);
        // if (m_params.m_mbqi && m_params.m_model_compact) {
        //    warning_msg("ignoring MODEL_COMPACT=true because it cannot be used with MBQI=true");
        //    m_params.m_model_compact = false;
        // }
        TRACE(setup, tout << "configuring logical context, logic: " << m_logic << " " << cm << "\n";);
        
        m_already_configured = true;
        
        switch (cm) {
        case CFG_BASIC: setup_unknown(); break;
        case CFG_LOGIC: setup_default(); break;
        case CFG_AUTO:  setup_auto_config(); break;
        }
        setup_card();
        setup_sls();
    }

    void setup::setup_default() {
        if (m_logic == "QF_UF") 
            setup_QF_UF();
        else if (m_logic == "QF_RDL")
            setup_QF_RDL();
        else if (m_logic == "QF_IDL")
            setup_QF_IDL();
        else if (m_logic == "QF_UFIDL")
            setup_QF_UFIDL();
        else if (m_logic == "QF_LRA")
            setup_QF_LRA();
        else if (m_logic == "QF_LIA")
            setup_QF_LIA();
        else if (m_logic == "QF_UFLIA")
            setup_QF_UFLIA();
        else if (m_logic == "QF_UFLRA")
            setup_QF_UFLRA();
        else if (m_logic == "QF_AX")
            setup_QF_AX();
        else if (m_logic == "QF_AUFLIA")
            setup_QF_AUFLIA();
        else if (m_logic == "QF_BV")
            setup_QF_BV();
        else if (m_logic == "QF_AUFBV")
            setup_QF_AUFBV();
        else if (m_logic == "QF_ABV")
            setup_QF_AUFBV();
        else if (m_logic == "QF_UFBV")
            setup_QF_AUFBV();
        else if (m_logic == "QF_BVRE")
            setup_QF_BVRE();
        else if (m_logic == "AUFLIA")
            setup_AUFLIA();
        else if (m_logic == "AUFLIRA")
            setup_AUFLIRA();
        else if (m_logic == "AUFNIRA")
            setup_AUFNIRA();
        else if (m_logic == "AUFLIA+")
            setup_AUFLIA();
        else if (m_logic == "AUFLIA-")
            setup_AUFLIA();
        else if (m_logic == "AUFLIRA+")
            setup_AUFLIRA();
        else if (m_logic == "AUFLIRA-")
            setup_AUFLIRA();
        else if (m_logic == "AUFNIRA+")
            setup_AUFLIRA();
        else if (m_logic == "AUFNIRA-")
            setup_AUFLIRA();
        else if (m_logic == "UFNIA")
            setup_UFNIA();
        else if (m_logic == "UFLRA")
            setup_UFLRA();
        else if (m_logic == "LRA")
            setup_LRA();
        else if (m_logic == "QF_FP")
            setup_QF_FP();
        else if (m_logic == "QF_FPBV" || m_logic == "QF_BVFP")
            setup_QF_FPBV();
        else if (m_logic == "QF_S" || m_logic == "QF_SLIA" || m_logic == "QF_SNIA")
            setup_QF_S();
        else if (m_logic == "QF_DT")
            setup_QF_DT();
        else
            setup_unknown();
    }

    void setup::setup_auto_config() {
        static_features    st(m_manager);
        IF_VERBOSE(100, verbose_stream() << "(smt.configuring)\n";);
        TRACE(setup, tout << "setup, logic: " << m_logic << "\n";);
        // HACK: do not collect features for QF_BV and QF_AUFBV... since they do not use them...
        if (m_logic == "QF_BV") {
            setup_QF_BV();
        }
        else if (m_logic == "QF_AUFBV" || m_logic == "QF_ABV" || m_logic == "QF_UFBV") {
            setup_QF_AUFBV();
        }
        else {
            IF_VERBOSE(100, verbose_stream() << "(smt.collecting-features)\n";);
            ptr_vector<expr> fmls;
            m_context.get_asserted_formulas(fmls);
            st.collect(fmls.size(), fmls.data());
            TRACE(setup, st.display_primitive(tout););
            IF_VERBOSE(1000, st.display_primitive(verbose_stream()););
            if (m_logic == "QF_UF") 
                setup_QF_UF(st);
            else if (m_logic == "QF_RDL")
                setup_QF_RDL(st);
            else if (m_logic == "QF_IDL")
                setup_QF_IDL(st);
            else if (m_logic == "QF_UFIDL")
                setup_QF_UFIDL(st);
            else if (m_logic == "QF_LRA")
                setup_QF_LRA(st);
            else if (m_logic == "QF_LIA")
                setup_QF_LIA(st);
            else if (m_logic == "QF_UFLIA")
                setup_QF_UFLIA(st);
            else if (m_logic == "QF_UFLRA")
                setup_QF_UFLRA();
            else if (m_logic == "QF_AX")
                setup_QF_AX(st);
            else if (m_logic == "QF_BVRE")
                 setup_QF_BVRE();
            else if (m_logic == "QF_AUFLIA")
                setup_QF_AUFLIA(st);
            else if (m_logic == "QF_S" || m_logic == "QF_SLIA" || m_logic == "QF_SNIA")
                setup_QF_S();
            else if (m_logic == "AUFLIA")
                setup_AUFLIA(st);
            else if (m_logic == "AUFLIRA")
                setup_AUFLIRA();
            else if (m_logic == "AUFNIRA")
                setup_AUFNIRA();
            else if (m_logic == "AUFLIA+")
                setup_AUFLIA();
            else if (m_logic == "AUFLIA-")
                setup_AUFLIA();
            else if (m_logic == "AUFLIRA+")
                setup_AUFLIRA();
            else if (m_logic == "AUFLIRA-")
                setup_AUFLIRA();
            else if (m_logic == "AUFNIRA+")
                setup_AUFLIRA();
            else if (m_logic == "AUFNIRA-")
                setup_AUFLIRA();
            else if (m_logic == "UFNIA")
                setup_UFNIA();
            else if (m_logic == "QF_DT")
                setup_QF_DT();
            else if (m_logic == "LRA")
                setup_LRA();
            else 
                setup_unknown(st);
        }
    }

    static void check_no_arithmetic(static_features const & st, char const * logic) {
        if (st.m_num_arith_ineqs > 0 || st.m_num_arith_terms > 0 || st.m_num_arith_eqs > 0) 
            throw default_exception("Benchmark constrains arithmetic, but specified logic does not support it.");
    }

    void setup::setup_QF_UF() {
        m_params.setup_QF_UF();
    }

    void setup::setup_QF_DT() {
        setup_QF_UF();
        setup_datatypes();
        setup_recfuns();
    }

    void setup::setup_QF_BVRE() {
        setup_QF_BV();
        setup_QF_LIA();
        setup_seq();
    }

    void setup::setup_QF_UF(static_features const & st) {        
        check_no_arithmetic(st, "QF_UF");
        setup_QF_UF();
        TRACE(setup,
              tout << "st.m_num_theories: " << st.m_num_theories << "\n";
              tout << "st.m_num_uninterpreted_functions: " << st.m_num_uninterpreted_functions << "\n";);
    }

    void setup::setup_QF_RDL() {
        m_params.setup_QF_RDL();
        setup_mi_arith();
    }

    static bool is_in_diff_logic(static_features const & st) {
        return 
            st.m_num_arith_eqs == st.m_num_diff_eqs && 
            st.m_num_arith_terms == st.m_num_diff_terms && 
            st.m_num_arith_ineqs == st.m_num_diff_ineqs;
    }

    static bool is_diff_logic(static_features const & st) {
        return 
            is_in_diff_logic(st) && 
            (st.m_num_diff_ineqs > 0 || st.m_num_diff_eqs > 0 || st.m_num_diff_terms > 0)
            ;
    }

    static void check_no_uninterpreted_functions(static_features const & st, char const * logic) {
        if (st.m_num_uninterpreted_functions != 0)
            throw default_exception("Benchmark contains uninterpreted function symbols, but specified logic does not support them.");
    }

    void setup::setup_QF_RDL(static_features & st) {
        if (!is_in_diff_logic(st))
            throw default_exception("Benchmark is not in QF_RDL (real difference logic).");
        if (st.m_has_int)
            throw default_exception("Benchmark has integer variables but it is marked as QF_RDL (real difference logic).");
        TRACE(setup, tout << "setup_QF_RDL(st)\n";);
        check_no_uninterpreted_functions(st, "QF_RDL");
        m_params.m_relevancy_lvl       = 0;
        m_params.m_arith_eq2ineq       = true;
        m_params.m_arith_reflect       = false;
        m_params.m_arith_propagate_eqs = false;
        m_params.m_nnf_cnf             = false;
        if (st.is_dense()) {
            m_params.m_restart_strategy = RS_GEOMETRIC;
            m_params.m_restart_adaptive = false;
            m_params.m_phase_selection  = PS_CACHING;
        }
        // The smi theories use fixed size integers instead of rationals.
        // They have support for epsilons for modeling strict inequalities, but they
        // cannot handle rational numbers.
        // It is only safe to use them when the input does not contain rational numbers.
        // Moreover, if model construction is enabled, then rational numbers may be needed
        // to compute the actual value of epsilon even if the input does not have rational numbers.
        // Example: (x < 1) and (x > 0)
        if (m_manager.proofs_enabled()) {
            m_context.register_plugin(alloc(smt::theory_mi_arith, m_context));
        }
        else {
            if (m_params.m_arith_auto_config_simplex || st.m_num_uninterpreted_constants > 4 * st.m_num_bool_constants 
                || st.m_num_ite_terms > 0 /* theory_rdl and theory_frdl do not support ite-terms */) {
                // if (!st.m_has_rational && !m_params.m_model && st.arith_k_sum_is_small()) {
                //   TRACE(rdl_bug, tout << "using theory_smi_arith\n";);
                //    m_context.register_plugin(alloc(smt::theory_smi_arith, m_context));
                // }
                // else {
                TRACE(rdl_bug, tout << "using theory_mi_arith\n";);
                //setup_lra_arith();
                m_context.register_plugin(alloc(smt::theory_mi_arith, m_context));
                // }
            }
            else {
                m_params.m_arith_bound_prop           = bound_prop_mode::BP_NONE;
                m_params.m_arith_propagation_strategy = arith_prop_strategy::ARITH_PROP_AGILITY;
                m_params.m_arith_add_binary_bounds    = true;
                if (!st.m_has_rational && !m_params.m_model && st.arith_k_sum_is_small())
                    m_context.register_plugin(alloc(smt::theory_frdl, m_context));
                else
                    m_context.register_plugin(alloc(smt::theory_rdl, m_context));
            }
        }
    }

    void setup::setup_QF_IDL() {
        TRACE(setup, tout << "setup_QF_IDL()\n";);
        m_params.setup_QF_IDL();
        setup_lra_arith();
    }

    void setup::setup_QF_IDL(static_features & st) {
        if (!is_in_diff_logic(st))
            throw default_exception("Benchmark is not in QF_IDL (integer difference logic).");
        if (st.m_has_real)
            throw default_exception("Benchmark has real variables but it is marked as QF_IDL (integer difference logic).");
        TRACE(setup, tout << "setup QF_IDL, m_arith_k_sum: " << st.m_arith_k_sum << " m_num_diff_terms: " << st.m_num_arith_terms << "\n";
              st.display_primitive(tout););
        TRACE(setup, tout << "setup_QF_IDL(st)\n";);
        check_no_uninterpreted_functions(st, "QF_IDL");
        m_params.m_relevancy_lvl       = 0;
        m_params.m_arith_eq2ineq       = true;
        m_params.m_arith_reflect       = false;
        m_params.m_arith_propagate_eqs = false;
        m_params.m_arith_small_lemma_size = 30;
        m_params.m_nnf_cnf             = false;
        if (st.m_num_uninterpreted_constants > 5000)
            m_params.m_relevancy_lvl   = 2;
        else if (st.m_cnf && !st.is_dense())
            m_params.m_phase_selection = PS_CACHING_CONSERVATIVE2;
        else
            m_params.m_phase_selection = PS_CACHING;
        if (st.is_dense() && st.m_num_bin_clauses + st.m_num_units == st.m_num_clauses) {
            m_params.m_restart_adaptive    = false;
            m_params.m_restart_strategy    = RS_GEOMETRIC;
        }
        if (st.m_cnf && st.m_num_units == st.m_num_clauses) {
            // the problem is just a big conjunction... using randomization to deal with crafted benchmarks
            m_params.m_random_initial_activity = IA_RANDOM;
        }

        TRACE(setup, 
              tout << "RELEVANCY: " << m_params.m_relevancy_lvl << "\n";
              tout << "ARITH_EQ_BOUNDS: " << m_params.m_arith_eq_bounds << "\n";);

        if (m_manager.proofs_enabled()) {
            m_context.register_plugin(alloc(smt::theory_mi_arith, m_context));
        }
        else if (!m_params.m_arith_auto_config_simplex && st.is_dense()) {
            TRACE(setup, tout << "using dense diff logic...\n";);
            m_params.m_phase_selection = PS_CACHING_CONSERVATIVE;
            if (st.arith_k_sum_is_small())
                m_context.register_plugin(alloc(smt::theory_dense_si, m_context));
            else
                m_context.register_plugin(alloc(smt::theory_dense_i, m_context));
    
        }
        else {
            // if (st.arith_k_sum_is_small()) {
            //    TRACE(setup, tout << "using small integer simplex...\n";
            //    m_context.register_plugin(alloc(smt::theory_si_arith, m_context));
            // }
            // else {
            TRACE(setup, tout << "using big integer simplex...\n";);
            m_context.register_plugin(alloc(smt::theory_i_arith, m_context));
            // }
        }
    }

    void setup::setup_QF_UFIDL() {
        TRACE(setup, tout << "setup_QF_UFIDL()\n";);
        m_params.setup_QF_UFIDL();
        setup_lra_arith();
    }

    void setup::setup_QF_UFIDL(static_features & st) {
        TRACE(setup, tout << "setup_QF_UFIDL(st)\n";);
        if (st.m_has_real)
            throw default_exception("Benchmark has real variables but it is marked as QF_UFIDL (uninterpreted functions and difference logic).");
        m_params.m_relevancy_lvl    = 0;
        m_params.m_arith_reflect    = false;
        m_params.m_nnf_cnf          = false;
        if (st.m_num_uninterpreted_functions == 0) {
            m_params.m_arith_eq2ineq        = true;
            m_params.m_arith_propagate_eqs  = false;
            if (st.is_dense()) {
                m_params.m_arith_small_lemma_size = 128;
                m_params.m_lemma_gc_half          = true;
                m_params.m_restart_strategy       = RS_GEOMETRIC;
                
                if (m_manager.proofs_enabled()) {
                    m_context.register_plugin(alloc(smt::theory_mi_arith, m_context));
                }
                else if (st.arith_k_sum_is_small())
                    m_context.register_plugin(alloc(smt::theory_dense_si, m_context));
                else
                    m_context.register_plugin(alloc(smt::theory_dense_i, m_context));
                return;
            }
        }
        m_params.m_arith_eq_bounds  = true;
        // m_params.m_phase_selection  = PS_THEORY;
        m_params.m_restart_strategy = RS_GEOMETRIC;
        m_params.m_restart_factor   = 1.5;
        m_params.m_restart_adaptive = false;
        if (m_manager.proofs_enabled()) {
            m_context.register_plugin(alloc(smt::theory_mi_arith, m_context));
        }
        // else if (st.arith_k_sum_is_small())
        //   m_context.register_plugin(alloc(smt::theory_dense_si, m_context));
        else
            m_context.register_plugin(alloc(smt::theory_i_arith, m_context));
    }

    void setup::setup_QF_LRA() {
        TRACE(setup, tout << "setup_QF_LRA()\n";);
        m_params.setup_QF_LRA();
        setup_lra_arith();
    }

    void setup::setup_QF_LRA(static_features const & st) {
        check_no_uninterpreted_functions(st, "QF_LRA");
        m_params.setup_QF_LRA(st);
        setup_lra_arith();
    }

    void setup::setup_QF_LIRA(static_features const& st) {
        setup_mi_arith();
    }

    void setup::setup_QF_LIA() {
        TRACE(setup, tout << "setup_QF_LIA(st)\n";);
        m_params.setup_QF_LIA();
        setup_lra_arith();
    }

    void setup::setup_QF_LIA(static_features const & st) {
        check_no_uninterpreted_functions(st, "QF_LIA");
        TRACE(setup, tout << "QF_LIA setup\n";);
        m_params.setup_QF_LIA(st);
        setup_lra_arith();
    }

    void setup::setup_QF_UFLIA() {
        setup_lra_arith();
        m_params.setup_QF_UFLIA();
    }

    void setup::setup_QF_UFLIA(static_features & st) {
        if (st.m_has_real)
            throw default_exception("Benchmark has real variables but it is marked as QF_UFLIA (uninterpreted functions and linear integer arithmetic).");
        setup_QF_UFLIA();
        if (st.m_has_bv) 
            setup_QF_BV();
    }

    void setup::setup_QF_UFLRA() {
        m_params.setup_QF_UFLRA();
        setup_lra_arith();
    }

    void setup::setup_QF_BV() {
        TRACE(setup, tout << "qf-bv\n";);
        m_params.setup_QF_BV();
        setup_bv();
    }

    void setup::setup_QF_AUFBV() {
        m_params.setup_QF_AUFBV();
        setup_bv();
        setup_arrays();
    }

    void setup::setup_QF_AX() {
        TRACE(setup, tout << "QF_AX\n";);
        m_params.setup_QF_AX();
        setup_arrays();
    }

    void setup::setup_QF_AX(static_features const & st) {
        m_params.setup_QF_AX(st);
        setup_arrays();
    }

    void setup::setup_QF_AUFLIA() {
        TRACE(QF_AUFLIA, tout << "no static features\n";);
        m_params.setup_QF_AUFLIA();
        setup_i_arith();
        setup_arrays();
    }

    void setup::setup_QF_AUFLIA(static_features const & st) {
        m_params.setup_QF_AUFLIA(st);
        setup_i_arith();
        setup_arrays();
    }

    void setup::setup_AUFLIA(bool simple_array) {
        TRACE(setup, tout << "AUFLIA\n";);
        m_params.setup_AUFLIA(simple_array);
        TRACE(setup, tout << "max_eager_multipatterns: " << m_params.m_qi_max_eager_multipatterns << "\n";);
        m_context.register_plugin(alloc(smt::theory_i_arith, m_context));
        setup_arrays();
    }

    void setup::setup_AUFLIA(static_features const & st) {
        if (st.m_has_real)
            throw default_exception("Benchmark has real variables but it is marked as AUFLIA (arrays, uninterpreted functions and linear integer arithmetic).");
        m_params.setup_AUFLIA(st);
        setup_AUFLIA();
    }

    void setup::setup_AUFLIRA(bool simple_array) {
        TRACE(setup, tout << "AUFLIRA\n";);
        m_params.setup_AUFLIRA(simple_array);
        setup_mi_arith();
        setup_arrays(); 
    }

    void setup::setup_UFNIA() {
        setup_AUFLIA();
    }

    void setup::setup_UFLRA() {
        setup_AUFLIRA();
    }

    void setup::setup_AUFLIAp() {
        setup_AUFLIA();
    }

    void setup::setup_AUFNIRA() {
        setup_AUFLIRA();
    }

    void setup::setup_LRA() {
        m_params.setup_LRA();
        setup_mi_arith();
    }

    void setup::setup_QF_FP() {
        setup_QF_BV();
        m_context.register_plugin(alloc(smt::theory_fpa, m_context));
    }

    void setup::setup_QF_FPBV() {
        setup_QF_BV();
        m_context.register_plugin(alloc(smt::theory_fpa, m_context));
    }

    void setup::setup_QF_S() {
        if (m_params.m_string_solver == "z3str3") {
            setup_str();
        }
        else if (m_params.m_string_solver == "seq") {
            setup_unknown();
        }
        else if (m_params.m_string_solver == "char") {
            setup_QF_BV();
            setup_char();
        }
        else if (m_params.m_string_solver == "noodler") {
            setup_arith();
            setup_str_noodler();
        }
        else if (m_params.m_string_solver == "auto") {
            setup_unknown();
        }
 
        else if (m_params.m_string_solver == "empty") {
            setup_seq();
        }
        else if (m_params.m_string_solver == "none") {
            // don't register any solver.
        }
        else {
            throw default_exception("invalid parameter for smt.string_solver, valid options are 'z3str3', 'seq', 'auto', 'noodler'");
        }
    }

    bool is_arith(static_features const & st) {
        return st.m_num_arith_ineqs > 0 || st.m_num_arith_terms > 0 || st.m_num_arith_eqs > 0;
    }

    void setup::setup_i_arith() {
        if (arith_solver_id::AS_OLD_ARITH == m_params.m_arith_mode) {
            m_context.register_plugin(alloc(smt::theory_i_arith, m_context));
        }
        else {
            setup_lra_arith();
        }
    }

    void setup::setup_lra_arith() {
        if (m_params.m_arith_mode == arith_solver_id::AS_OLD_ARITH)
            m_context.register_plugin(alloc(smt::theory_mi_arith, m_context));
        else
            m_context.register_plugin(alloc(smt::theory_lra, m_context));
    }

    void setup::setup_mi_arith() {
        switch (m_params.m_arith_mode) {
        case arith_solver_id::AS_OPTINF:
            m_context.register_plugin(alloc(smt::theory_inf_arith, m_context));            
            break;
        case arith_solver_id::AS_NEW_ARITH:
            setup_lra_arith();
            break;
        default:
            m_context.register_plugin(alloc(smt::theory_mi_arith, m_context));
            break;
        }
    }

    void setup::setup_arith() {
        static_features    st(m_manager);
        IF_VERBOSE(100, verbose_stream() << "(smt.collecting-features)\n";);
        ptr_vector<expr> fmls;
        m_context.get_asserted_formulas(fmls);
        st.collect(fmls.size(), fmls.data());
        IF_VERBOSE(1000, st.display_primitive(verbose_stream()););
        bool fixnum = st.arith_k_sum_is_small() && m_params.m_arith_fixnum;
        bool int_only = !st.m_has_rational && !st.m_has_real && m_params.m_arith_int_only;
        auto mode = m_params.m_arith_mode;
        if (m_logic == "QF_LIA") {
            mode = arith_solver_id::AS_NEW_ARITH;
        }
        switch(mode) {
        case arith_solver_id::AS_NO_ARITH:
            m_context.register_plugin(alloc(smt::theory_dummy, m_context, m_manager.mk_family_id("arith"), "no arithmetic"));
            break;
        case arith_solver_id::AS_DIFF_LOGIC:
            m_params.m_arith_eq2ineq  = true;
            if (fixnum) {
                if (int_only)
                    m_context.register_plugin(alloc(smt::theory_fidl, m_context));
                else
                    m_context.register_plugin(alloc(smt::theory_frdl, m_context));
            }
            else {
                if (int_only)
                    m_context.register_plugin(alloc(smt::theory_idl, m_context));
                else
                    m_context.register_plugin(alloc(smt::theory_rdl, m_context));
    }
            break;
        case arith_solver_id::AS_DENSE_DIFF_LOGIC:
            m_params.m_arith_eq2ineq  = true;
            if (fixnum) {
                if (int_only)
                    m_context.register_plugin(alloc(smt::theory_dense_si, m_context));
                else
                    m_context.register_plugin(alloc(smt::theory_dense_smi, m_context));
            }
            else {
                if (int_only)
                    m_context.register_plugin(alloc(smt::theory_dense_i, m_context));
                else
                    m_context.register_plugin(alloc(smt::theory_dense_mi, m_context));
            }
            break;
        case arith_solver_id::AS_UTVPI:
            m_params.m_arith_eq2ineq  = true;
            if (int_only)
                m_context.register_plugin(alloc(smt::theory_iutvpi, m_context));
            else
                m_context.register_plugin(alloc(smt::theory_rutvpi, m_context));
            break;
        case arith_solver_id::AS_OPTINF:
            m_context.register_plugin(alloc(smt::theory_inf_arith, m_context));            
            break;
        case arith_solver_id::AS_OLD_ARITH:
            if (m_params.m_arith_int_only && int_only)
                m_context.register_plugin(alloc(smt::theory_i_arith, m_context));
            else
                m_context.register_plugin(alloc(smt::theory_mi_arith, m_context));
            break;
        case arith_solver_id::AS_NEW_ARITH:
            setup_lra_arith();
            break;
        default:
            m_context.register_plugin(alloc(smt::theory_mi_arith, m_context));
            break;
        }
    }

    void setup::setup_bv() {
        family_id bv_fid = m_manager.mk_family_id("bv");
        if (m_context.get_theory(bv_fid))
            return;
        switch (m_params.m_bv_solver) {
        case 2:
            m_context.register_plugin(alloc(smt::theory_intblast, m_context));
            setup_lra_arith();
            return;
        default:
            break;
        }
        switch (m_params.m_bv_mode) {
        case BS_NO_BV:
            m_context.register_plugin(alloc(smt::theory_dummy, m_context, bv_fid, "no bit-vector"));
            break;
        case BS_BLASTER:
            m_context.register_plugin(alloc(smt::theory_bv, m_context));
            break;
        }
    }

    void setup::setup_arrays() {
        switch(m_params.m_array_mode) {
        case AR_NO_ARRAY:
            m_context.register_plugin(alloc(smt::theory_dummy, m_context, m_manager.mk_family_id("array"), "no array"));
            break;
        case AR_SIMPLE:
            m_context.register_plugin(alloc(smt::theory_array, m_context));
            break;
        case AR_MODEL_BASED:
             throw default_exception("The model-based array theory solver is deprecated");
            break;
        case AR_FULL:
            m_context.register_plugin(alloc(smt::theory_array_full, m_context));
            break;
        }
    }

    void setup::setup_datatypes() {
        TRACE(datatype, tout << "registering theory datatype...\n";);
        m_context.register_plugin(alloc(theory_datatype, m_context));
    }

    void setup::setup_recfuns() {
        TRACE(recfun, tout << "registering theory recfun...\n";);
        theory_recfun * th = alloc(theory_recfun, m_context);
        m_context.register_plugin(th);
    }

    void setup::setup_dl() {
        m_context.register_plugin(mk_theory_dl(m_context));
    }

    void setup::setup_seq_str(static_features const & st) {
        // check params for what to do here when it's ambiguous
        if (m_params.m_string_solver == "z3str3") {
            setup_str();
        } 
        else if (m_params.m_string_solver == "seq") {
            setup_seq();
        } 
        else if (m_params.m_string_solver == "empty") {
            setup_seq();
        }
        else if (m_params.m_string_solver == "noodler") {
            setup_str_noodler();
        }
        else if (m_params.m_string_solver == "none") {
            // don't register any solver.
        }
        else if (m_params.m_string_solver == "auto") {
            if (st.m_has_seq_non_str) {
                setup_seq();
            } 
            else {
                setup_str();
            }
        } 
        else {
            throw default_exception("invalid parameter for smt.string_solver, valid options are 'z3str3', 'seq', 'auto', 'noodler'");
        }
    }

    void setup::setup_card() {
        m_context.register_plugin(alloc(theory_pb, m_context));
    }

    void setup::setup_sls() {
        if (m_params.m_sls_enable)
            m_context.register_plugin(alloc(theory_sls, m_context));
    }

    void setup::setup_fpa() {
        setup_bv();
        m_context.register_plugin(alloc(theory_fpa, m_context));
    }

    void setup::setup_str() {
        setup_arith();
        m_context.register_plugin(alloc(theory_str, m_context, m_manager, m_params));
    }

    void setup::setup_str_noodler() {
        m_context.register_plugin(alloc(noodler::theory_str_noodler, m_context, m_manager, m_params));
    }

    void setup::setup_seq() {
        m_context.register_plugin(alloc(smt::theory_seq, m_context));
        setup_char();
    }

    void setup::setup_char() {
        m_context.register_plugin(alloc(smt::theory_char, m_context));        
    }

    void setup::setup_special_relations() {
        m_context.register_plugin(alloc(smt::theory_special_relations, m_context, m_manager));
    }

    void setup::setup_polymorphism() {
        if (m_manager.has_type_vars())
            m_context.register_plugin(alloc(theory_polymorphism, m_context));
    }

    void setup::setup_unknown() {
        static_features st(m_manager);
        ptr_vector<expr> fmls;
        m_context.get_asserted_formulas(fmls);
        st.collect(fmls.size(), fmls.data());
        TRACE(setup, tout << "setup_unknown\n";);
        setup_arith();
        setup_arrays();
        setup_bv();
        setup_datatypes();
        setup_recfuns();
        setup_dl();
        setup_seq_str(st);
        setup_fpa();
        setup_special_relations();
        setup_polymorphism();
        setup_relevancy(st);
    }

    //
    // quantifier free problems with bit-vectors should always use relevancy = 0
    // there are some other cases where relevancy propagation is harmful.
    //
    void setup::setup_relevancy(static_features& st) {
        // the case split queue has been constructed by now.
        // it is not safe to disable relevancy if the case split stragegy is relevancy-dependent.
        if (m_params.m_case_split_strategy == CS_RELEVANCY || 
            m_params.m_case_split_strategy == CS_RELEVANCY_ACTIVITY || 
            m_params.m_case_split_strategy == CS_RELEVANCY_GOAL)
            return;

        if (st.m_has_bv && !st.m_has_fpa && st.m_num_quantifiers == 0)
             m_params.m_relevancy_lvl = 0;           
    }

    void setup::setup_unknown(static_features & st) {
        TRACE(setup, tout << "setup_unknown\n";);
        if (st.m_num_quantifiers > 0) {
            if (st.m_has_real)
                setup_AUFLIRA(false);
            else 
                setup_AUFLIA(false);
            setup_datatypes();
            setup_bv();
            setup_dl();
            setup_seq_str(st);
            setup_fpa();
            setup_recfuns();
            setup_special_relations();
            setup_polymorphism();
            return;
        }

        TRACE(setup,
              tout << "num non UF theories: " << st.num_non_uf_theories() << "\n";
              tout << "num theories: " << st.num_theories() << "\n";
              tout << "is_diff_logic: " << is_diff_logic(st) << "\n";
              tout << "is_arith: " << is_arith(st) << "\n";
              tout << "has UF: " << st.has_uf() << "\n";
              tout << "has real: " << st.m_has_real << "\n";
              tout << "has int: " << st.m_has_int << "\n";
              tout << "has bv: " << st.m_has_bv << "\n";
              tout << "has fpa: " << st.m_has_fpa << "\n"; 
              tout << "has arrays: " << st.m_has_arrays << "\n";);

        if (st.num_non_uf_theories() == 0) {           
            setup_QF_UF(st);
            return;
        }

        if (st.num_theories() == 1 && is_diff_logic(st)) {
            if (st.m_has_real && !st.m_has_int)
                setup_QF_RDL(st);
            else if (!st.m_has_real && st.m_has_int)
                setup_QF_IDL(st);
            else
                setup_unknown();
            return;
        }
        
        if (st.num_theories() == 2 && st.has_uf() && is_diff_logic(st)) {
            if (!st.m_has_real && st.m_has_int)
                setup_QF_UFIDL(st);
            else
                setup_unknown();
            return;
        }
        
        if (st.num_theories() == 1 && is_arith(st)) {
            if ((st.m_has_int && st.m_has_real) || (st.m_num_non_linear != 0)) 
                setup_QF_LIRA(st);
            else if (st.m_has_real)
                setup_QF_LRA(st);
            else
                setup_QF_LIA(st);
            return;
        }

        if (st.num_theories() == 2 && st.has_uf() && is_arith(st)) {
            if (!st.m_has_real && st.m_num_non_linear == 0)
                setup_QF_UFLIA(st);
            else if (!st.m_has_int && st.m_num_non_linear == 0) 
                setup_QF_UFLRA();
            else
                setup_unknown();
            return;
        }

        if (st.num_theories() == 1 && st.m_has_bv) {
            setup_QF_BV();
            return;
        }

        if (st.num_theories() == 1 && st.m_has_fpa) {
            setup_QF_FP();
            return;
        }

        if (st.num_theories() == 2 && st.m_has_fpa && st.m_has_bv) {
            setup_QF_FPBV();
            return;
        }

        if (st.num_theories() == 1 && st.m_has_arrays) {
            setup_QF_AX(st);
            return;
        }

        if (st.num_theories() == 2 && st.has_uf() && st.m_has_arrays && !st.m_has_ext_arrays && st.m_has_bv) {
            setup_QF_AUFBV();
            return;
        }

        if (st.num_theories() == 2 && st.has_uf() && st.m_has_arrays && st.m_has_int) {
            setup_QF_AUFLIA(st);
            return;
        }

        setup_unknown();
    }

};


