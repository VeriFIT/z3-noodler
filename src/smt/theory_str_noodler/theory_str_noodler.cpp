/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3.
Eternal glory to Yu-Fang.
*/

#include <algorithm>
#include <sstream>
#include <iostream>
#include <cmath>

#include "ast/ast_pp.h"
#include "smt/smt_context.h"
#include "smt/theory_lra.h"
#include "smt/theory_arith.h"
#include "smt/smt_context.h"
#include "ast/seq_decl_plugin.h"
#include "ast/reg_decl_plugins.h"

#include "decision_procedure.h"
#include "theory_str_noodler.h"
#include "memb_heuristics_procedures.h"

namespace smt::noodler {

    theory_str_noodler::theory_str_noodler(context& ctx, ast_manager & m, theory_str_noodler_params const & params):
        theory(ctx, ctx.get_manager().mk_family_id("seq")),
        m_params(params),
        m_rewrite(m),
        m_util_a(m),
        m_util_s(m),
        var_eqs(m_util_a),
        m_length(m),
        axiomatized_instances(),
        sat_length_formula(m)  {
    }

    void theory_str_noodler::display(std::ostream &os) const {
        os << "theory_str display" << std::endl;
    }

    void theory_str_noodler::init() {
        theory::init();
        STRACE(str, tout << "init" << std::endl;);
    }

    enode *theory_str_noodler::ensure_enode(expr *e) {
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        enode *n = ctx.get_enode(e);
        ctx.mark_as_relevant(n);
        return n;
    }

    theory_var theory_str_noodler::mk_var(enode *const n) {
        if (!m_util_s.is_seq(n->get_expr()) &&
            !m_util_s.is_re(n->get_expr())) {
            return null_theory_var;
        }
        if (is_attached_to_var(n)) {
            return n->get_th_var(get_id());
        } else {
            theory_var v = theory::mk_var(n);
            get_context().attach_th_var(n, this, v);
            get_context().mark_as_relevant(n);
            return v;
        }
    }


    bool theory_str_noodler::internalize_atom(app *const atom, const bool gate_ctx) {
        (void) gate_ctx;
        STRACE(str, tout << "internalize_atom: gate_ctx is " << gate_ctx << ", "
                           << mk_pp(atom, get_manager()) << '\n';);
        context &ctx = get_context();
        if (ctx.b_internalized(atom)) {
            STRACE(str, tout << "done before\n";);
            return true;
        }
        return internalize_term(atom);
    }

    bool theory_str_noodler::internalize_term(app *const term) {
        context &ctx = get_context();

        if (m_util_s.str.is_in_re(term)) {
            if (!ctx.e_internalized(term->get_arg(0))) {
                ctx.internalize(term->get_arg(0), false);
                enode* enode = ctx.get_enode(term->get_arg(0));
                mk_var(enode);
            }
        }
        if (ctx.e_internalized(term)) {
            enode *e = ctx.get_enode(term);
            mk_var(e);
            return true;
        }
        for (auto arg : *term) {
            mk_var(ensure_enode(arg));
        }
        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            //We do not want to mark as relevant because it involves
            // irrelevant RE solutions comming from the underlying SAT solver.
            //ctx.mark_as_relevant(bv);
        }

        enode *e = nullptr;
        if (ctx.e_internalized(term)) {
            e = ctx.get_enode(term);
        } else {
            e = ctx.mk_enode(term, false, m.is_bool(term), true);
        }
        mk_var(e);
        if (!ctx.relevancy()) {
            relevant_eh(term);
        }
        return true;
    }

    void theory_str_noodler::apply_sort_cnstr(enode *n, sort *s) {
        mk_var(n);
    }

    void theory_str_noodler::collect_statistics(::statistics & st) const {
        STRACE(str, tout << "collecting statistics" << std::endl;);
        st.update("noodler-final_checks", num_of_solving_final_checks);
        for (const auto& [heur_name, heur_stats] : this->statistics) {
            st.update(statistics_bullshit_names.at(heur_name)[0], heur_stats.num_start);
            st.update(statistics_bullshit_names.at(heur_name)[1], heur_stats.num_finish);
            st.update(statistics_bullshit_names.at(heur_name)[2], heur_stats.num_solved_preprocess);
        }
    }

    void theory_str_noodler::init_search_eh() {
        STRACE(str, tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        context &ctx = get_context();
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        for (unsigned i = 0; i < nFormulas; ++i) {
            STRACE(str_init_formula, tout << "Initial asserted formula " << i << ": " << expr_ref(ctx.get_asserted_formula(i), m) << std::endl;);
            expr *ex = ctx.get_asserted_formula(i);
            this->input_has_quantifiers |= util::has_quantifiers(m, ex);
            if (!add_len_num_axioms(ex)) {
                obj_hashtable<app> lens;
                util::get_len_exprs(ctx.get_asserted_formula(i), m_util_s, m, lens);
                for (app* const a : lens) {
                    expr* len_arg;
                    VERIFY(m_util_s.str.is_length(a, len_arg));
                    mark_expression_as_length(len_arg);
                }
            }
            ctx.mark_as_relevant(ex);
            string_theory_propagation(ex, true, false);  
        }
        // it seems that for quantified formulae, the model generation infrastructure is necessary for 
        // the solving (even though the model is not requested). Probably it has something to do with 
        // model-based quantifier instantiation.
        if(this->input_has_quantifiers) {
            const_cast<theory_str_noodler_params&>(m_params).m_produce_models = true;
        }
        add_conversion_num_axioms();
        STRACE(str, tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_str_noodler::string_theory_propagation(expr *ex, bool init, bool neg, bool var_lengths) {
        STRACE(str, tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        STRACE(str_propagation, tout << mk_pp(ex, get_manager()) << std::endl;);

        context &ctx = get_context();
        if (!ctx.e_internalized(ex)) {
            // expr might be in a logical context (e.g., and, or, not)
            ctx.internalize(ex, true);
        }
        //We do not mark the expression as relevant since we do not want bias a
        //fresh SAT solution by the newly added theory axioms.
        // enode *n = ctx.get_enode(expr);
        // ctx.mark_as_relevant(n);

        if(m.is_not(ex)) {
            neg = !neg;
        }

        // TODO weird, we have to do it because inequations are handled differently as equations, and they might not have been set as relevant
        if(init && m.is_eq(ex) && neg) {
            ctx.mark_as_relevant(m.mk_not(ex));
        }
        // we need to propagate all string predicates (including their negated forms) before the actual solve (in init_search), because we need to ensure these axioms are 
        // generated only once on the decision level 0 (if they are generated on a higher level, they can cause looping for some reason)
        if(init && (
                m_util_s.str.is_prefix(ex) ||
                m_util_s.str.is_suffix(ex) ||
                m_util_s.str.is_contains(ex) ||
                m_util_s.str.is_is_digit(ex) ||
                m_util_s.str.is_lt(ex)
                // we cannot do it for conversions because otherwise all conversions become relevant and there is a degradation on benchmarks
                // (this degradation should not happen for other predicates, because they are transformed into simpler atoms such as equation, regular membership... whose relevancy we can check when it is needed)
            )) {
            if(neg) ctx.mark_as_relevant(m.mk_not(ex));
            else ctx.mark_as_relevant(ex);
        }

        // in the initialization phase, we need to mark all string terms as relevant. We want to 
        // prevent the situation when the string functions/predicates are axiomatized 
        // on higher decision level than 0 (otherwise the axioms are lost).
        // String propagation of the input formula works on level 0.
        if(init && (
            m_util_s.str.is_index(ex) ||
            m_util_s.str.is_at(ex) ||
            m_util_s.str.is_extract(ex) ||
            m_util_s.str.is_replace(ex) ||
            m_util_s.str.is_replace_all(ex) ||
            m_util_s.str.is_replace_re_all(ex) ||
            m_util_s.str.is_replace_re(ex) ||
            m_util_s.str.is_update(ex) ||
            m_util_s.str.is_trim(ex) ||
            m_util_s.str.is_delete(ex)
        )) {
            ctx.mark_as_relevant(ex);
        }

        // Check if we already axiomatized the expr
        if (propagated_string_theory.contains(ex)) {
            return;
        }     
        propagated_string_theory.insert(ex);

        sort *expr_sort = ex->get_sort();
        sort *str_sort = m_util_s.str.mk_string_sort();

        if (expr_sort == str_sort) {
            enode *n = ctx.get_enode(ex);
            propagate_basic_string_axioms(n, var_lengths);
            if (is_app(ex) && m_util_s.str.is_concat(to_app(ex))) {
                propagate_concat_axiom(n);
            }
        }
        // if expr is an application, recursively inspect all arguments
        if (is_app(ex) && !m_util_s.str.is_length(ex)) {
            app *term = to_app(ex);
            unsigned num_args = term->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                string_theory_propagation(term->get_arg(i), init, neg, var_lengths);
            }
        }

        STRACE(str, tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    // for concatenation xy create axiom |xy| = |x| + |y| where x, y are some string expressions
    void theory_str_noodler::propagate_concat_axiom(enode *cat) {
        STRACE(str, tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        app *a_cat = cat->get_expr();
        SASSERT(m_util_s.str.is_concat(a_cat));
        ast_manager &m = get_manager();

        // build LHS
        expr_ref len_xy(m);
        len_xy = m_util_s.str.mk_length(a_cat);
        SASSERT(len_xy);

        // build RHS: start by extracting x and y from Concat(x, y)
        SASSERT(a_cat->get_num_args() == 2);
        app *a_x = to_app(a_cat->get_arg(0));
        app *a_y = to_app(a_cat->get_arg(1));
        expr_ref len_x(m);
        len_x = m_util_s.str.mk_length(a_x);
        SASSERT(len_x);

        expr_ref len_y(m);
        len_y = m_util_s.str.mk_length(a_y);
        SASSERT(len_y);

        // now build len_x + len_y
        expr_ref len_x_plus_len_y(m);
        len_x_plus_len_y = m_util_a.mk_add(len_x, len_y);
        SASSERT(len_x_plus_len_y);

        STRACE(str_concat,
            tout << "[Concat Axiom] " << mk_pp(len_xy, m) << " = " << mk_pp(len_x, m) << " + " << mk_pp(len_y, m)
                 << std::endl;
        );

        // finally assert equality between the two subexpressions
        app_ref eq(m.mk_eq(len_xy, len_x_plus_len_y), m);
        SASSERT(eq);
        add_axiom(eq);
        this->axiomatized_len_axioms.push_back(eq);
        STRACE(str, tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_str_noodler::propagate_basic_string_axioms(enode *str, bool var_lengths) {
        context &ctx = get_context();
        ast_manager &m = get_manager();

        {
            sort *a_sort = str->get_expr()->get_sort();
            sort *str_sort = m_util_s.str.mk_string_sort();
            if (a_sort != str_sort) {
                STRACE(str,
                       tout << "WARNING: not setting up string axioms on non-string term " << mk_pp(str->get_expr(), m)
                            << std::endl;);
                return;
            }
        }

        // TESTING: attempt to avoid a crash here when a variable goes out of scope
        if (str->get_iscope_lvl() > ctx.get_scope_level()) {
            STRACE(str, tout << "WARNING: skipping axiom setup on out-of-scope string term" << std::endl;);
            return;
        }

        // generate a stronger axiom for constant strings
        app_ref a_str(str->get_expr(), m);

        // len(str) = |str| for explicit string str
        if (m_util_s.str.is_string(a_str)) {

            expr_ref len_str(m_util_s.str.mk_length(a_str), m);
            SASSERT(len_str);

            zstring strconst;
            m_util_s.str.is_string(str->get_expr(), strconst);
            unsigned int l = strconst.length();
            expr_ref len(m_util_a.mk_numeral(rational(l), true), m);

            expr_ref eq(m.mk_eq(len_str, len), m);
            add_axiom(eq);
            return;
        } else if(!m.is_ite(a_str)) {
            // axiom |t| >= 0 where t is a string term
            { 
                // build LHS
                expr_ref len_str(m);
                len_str = m_util_s.str.mk_length(a_str);
                SASSERT(len_str);
                // build RHS
                expr_ref zero(m);
                zero = m_util_a.mk_numeral(rational(0), true);
                SASSERT(zero);
                // build LHS >= RHS and assert
                app_ref lhs_ge_rhs(m_util_a.mk_ge(len_str, zero), m);
                ctx.internalize(lhs_ge_rhs, false);
                SASSERT(lhs_ge_rhs);

                add_axiom({mk_literal(lhs_ge_rhs)});
                this->axiomatized_len_axioms.push_back(lhs_ge_rhs);
            }
            // axiom |t| <= 0 -> t = eps; if var_lengths is set add also t = eps -> |t| = 0
            {
                // build LHS of iff
                expr_ref len_str(m);
                len_str = m_util_s.str.mk_length(a_str);
                SASSERT(len_str);
                expr_ref zero(m);
                zero = m_util_a.mk_numeral(rational(0), true);
                SASSERT(zero);
                expr_ref lhs(m);
                lhs = m_util_a.mk_le(len_str, zero);
                SASSERT(lhs);
                // build RHS of iff
                expr_ref empty_str(m);
                empty_str = m_util_s.str.mk_empty(a_str->get_sort());
                SASSERT(empty_str);
                expr_ref rhs(m);
                rhs = m.mk_eq(a_str, empty_str);
                ctx.internalize(rhs, false);
                ctx.internalize(lhs, false);
                SASSERT(rhs);
                // build LHS <=> RHS and assert
                add_axiom(m.mk_or(m.mk_not(lhs), rhs));
                // generate also the other implication
                if(var_lengths) {
                    add_axiom(m.mk_or(m.mk_not(rhs), lhs));
                }
            }
        } else {
            // INFO do nothing if ite, because this function is called only in string_theory_propagation where ite is processed
        }
    }

    void theory_str_noodler::add_length_axiom(expr *n) {
        app_ref ln(m_util_a.mk_ge(n, m_util_a.mk_int(0)), m);
        ctx.internalize(ln, false);
        add_axiom(ln);
        this->axiomatized_len_axioms.push_back(ln);
    }

    void theory_str_noodler::relevant_eh(app *const n) {
        STRACE(str, tout << "relevant: " << mk_pp(n, get_manager()) << " with family id " << n->get_family_id() << ", sort " << n->get_sort()->get_name() << " and decl kind " << n->get_decl_kind() << std::endl;);

        if (m_util_s.str.is_length(n)) { // str.len
            add_length_axiom(n);

            expr *arg;
            VERIFY(m_util_s.str.is_length(n, arg));
            // FIXME what is this? is it important? can we delete this?
            if (!has_length(arg) && get_context().e_internalized(arg)) {
                enforce_length(arg);
            }

            // Small hack for issue #327
            // It seems when there are bitvectors (even if unrelated to strings), relevant_eh is not called for string variables/uninterpreted functions.
            // However, relevant_eh still called for (str.len f) where f is the string variable/uninterpreted function.
            // By doing the following, we will therefore mark the string variable as relevant for us.
            // Note that ctx.mark_as_relevant is not enough, we need to call relevant_eh directly.
            relevant_eh(to_app(arg));

        } else if(m_util_s.str.is_lt(n)) { // str.<
            handle_lex_lt(n);
        } else if(m_util_s.str.is_le(n)) { // str.<=
            UNREACHABLE(); // should be rewritten to str.< by the rewriter
        } else if (m_util_s.str.is_at(n)) { // str.at
            handle_char_at(n);
        } else if (m_util_s.str.is_extract(n)) { // str.substr
            handle_substr(n);
        } else if(m_util_s.str.is_prefix(n)) { // str.prefixof
            handle_prefix(n);
            handle_not_prefix(n);
        } else if(m_util_s.str.is_suffix(n)) { // str.suffixof
            handle_suffix(n);
            handle_not_suffix(n);
        } else if(m_util_s.str.is_contains(n)) { // str.contains
            handle_contains(n);
            handle_not_contains(n);
        } else if (m_util_s.str.is_index(n)) { // str.indexof
            handle_index_of(n);
        } else if (m_util_s.str.is_replace(n)) { // str.replace
            handle_replace(n);
        } else if(m_util_s.str.is_replace_all(n)) { // str.replace_all
            handle_replace_all(n);
        } else if(m_util_s.str.is_replace_re(n)) { // str.replace_re
            handle_replace_re(n);
        } else if(m_util_s.str.is_replace_re_all(n)) { // str.replace_re_all
            handle_replace_re_all(n);
        } else if(m_util_s.str.is_update(n)) {
            handle_update(n);
        } else if(m_util_s.str.is_trim(n)) {
            handle_trim(n);
        } else if(m_util_s.str.is_delete(n)) {
            handle_delete(n);
        } else if (m_util_s.str.is_is_digit(n)) { // str.is_digit
            handle_is_digit(n);
        } else if (
            m_util_s.str.is_stoi(n) || // str.to_int
            m_util_s.str.is_itos(n) || // str.from_int
            m_util_s.str.is_stor(n) || // str.to_real
            m_util_s.str.is_rtos(n) || // str.from_real
            m_util_s.str.is_to_code(n) || // str.to_code
            m_util_s.str.is_from_code(n) // str.from_code
        ) {
            handle_conversion(n);
        } else if (util::is_str_variable(n, m_util_s)) {
            BasicTerm var_for_n = util::get_variable_basic_term(n);
            SASSERT(!var_name.contains(var_for_n) || var_name.at(var_for_n) == n);
            var_name.insert({util::get_variable_basic_term(n), expr_ref(n, m)});
        } else if (
            m_util_s.str.is_concat(n) || // str.++
            m_util_s.re.is_to_re(n) || // str.to_re
            m_util_s.str.is_in_re(n) || // str.in_re
            m_util_s.is_re(n) || // one of re. command (re.none, re.all, re.comp, ...), or possibly RegLan variable
            m_util_s.str.is_string(n) // string literal
        ) {
            // we do not need to handle these, concatenation is handled in the decision procedure (it is a basic term)
            // and everything else will be handled during final_check_eh
        } else {
            // if we got here it means that we got some uninterpreted string function (i.e. probably user declared), we just replace it with a fresh string variable
            expr* e = n;
            if (!axiomatized_persist_terms.contains(e)) {
                axiomatized_persist_terms.insert(e);
                expr_ref fresh = mk_str_var_fresh("uninter");
                predicate_replace.insert(e, fresh.get());
                add_axiom({mk_eq(fresh, e, false)});
            }
        }

        if (initial_len_expressions.contains(n)) {
            SASSERT(predicate_replace.find(n));
            len_vars.insert(predicate_replace[n]);
        }
    }

    /*
    ensure that all elements in equivalence class occur under an application of 'length'
    */
    void theory_str_noodler::enforce_length(expr *e) {
        enode *n = ensure_enode(e);
        enode *n1 = n;
        do {
            expr *o = n->get_expr();
            // TODO is this needed? what happens if we get ite, it does not do anything
            if (!has_length(o) && !m.is_ite(o)) {
                expr_ref len = expr_ref(m_util_s.str.mk_length(o), m);
                add_length_axiom(len);
            }
            n = n->get_next();
        } while (n1 != n);
    }

    void theory_str_noodler::assign_eh(bool_var v, const bool is_true) {
        ast_manager &m = get_manager();
        STRACE(str, tout << "assign enter\n";);
        STRACE(str_assign, tout << "assign: bool_var #" << v << " is " << is_true << ", "
                            << mk_pp(get_context().bool_var2expr(v), m) << "@ scope level:" << m_scope_level << '\n';);
        context &ctx = get_context();
        expr *e = ctx.bool_var2expr(v);
        expr *e1 = nullptr, *e2 = nullptr;
        if (m_util_s.str.is_prefix(e, e1, e2)) {
            // already handled in relevant_eh. It suffices to handle is_prefix only once as it is fully 
            // axiomatized using basic string constraints ((dis)equations, regexes, and lengths)
        } else if (m_util_s.str.is_suffix(e, e1, e2)) {
            // already handled in relevant_eh. It suffices to handle is_suffix only once as it is fully 
            // axiomatized using basic string constraints ((dis)equations, regexes, and lengths)
        } else if (m_util_s.str.is_contains(e, e1, e2)) {
            // notcontains cannot be fully axiomatized. We need to add it among string constraints solved later in final_check 
            // (it is not sufficient to add it only once at the beginning of the solver run as it max occurr in different SAT assignments).
            if (!is_true) {
                assign_not_contains(e);
            }
        } else if(m_util_s.str.is_le(e) || m_util_s.str.is_lt(e)) {
            // handled in relevant_eh
        } else if (m_util_s.str.is_in_re(e)) {
            // regexes are not axiomatized. We store them to be solved later in final_check
            handle_in_re(e, is_true);
        } else if(m.is_bool(e)) {
            ensure_enode(e);
            TRACE(str_assign, tout << "bool literal " << mk_pp(e, m) << " " << is_true << "\n" );
        } else {
            TRACE(str_assign, tout << "unhandled literal " << mk_pp(e, m) << "\n";);
            UNREACHABLE();
        }
    }

    void theory_str_noodler::new_eq_eh(theory_var x, theory_var y) {
        // get the expressions for left and right side of equation
        expr_ref l{get_enode(x)->get_expr(), m};
        expr_ref r{get_enode(y)->get_expr(), m};

        STRACE(str, tout << "new_eq: " << l <<  " = " << r << std::endl;);

        app* equation = m.mk_eq(l, r);

        // TODO explain what is happening here
        if(!ctx.e_internalized(equation)) {
            ctx.mark_as_relevant(equation);
        }

        if(m_util_s.is_re(l) && m_util_s.is_re(r)) { // language equation
            m_lang_eq_todo.push_back({l, r});
        } else { // word equation
            // mk_eq_atom can check if equation trivially holds (by having the
            // same thing on both sides) or not (by having two distintict
            // string literals)
            app* equation_atom = ctx.mk_eq_atom(l, r);
            if (m.is_false(equation_atom)) {
                // if we have two distinct literals, we immediately stop by not allowing this equation
                add_axiom({mk_literal(m.mk_not(equation))});
            } else if (!m.is_true(equation_atom)) {
                // if equation is not trivially true, we add it for later check
                m_word_eq_todo.push_back({l, r});

                // Optimization: If equation holds, then the lengths of both sides must be the same.
                // We do this only if the equation (or its inverse) is already for sure relevant,
                // otherwise adding the axiom might make the equation relevant (even though it is not).
                // Used for quick check for arith solver, to immediately realise that sides cannot be
                // ever equal based on lengths.
                // This does NOT add the variables from the equation to len_vars.
                if (ctx.is_relevant(equation) || ctx.is_relevant(m.mk_eq(r, l))) {
                    literal l_eq_r = mk_literal(equation);    //mk_eq(l, r, false);
                    literal len_l_eq_len_r = mk_eq(m_util_s.str.mk_length(l), m_util_s.str.mk_length(r), false);
                    add_axiom({~l_eq_r, len_l_eq_len_r});
                }
            }
        }
    }

    void theory_str_noodler::new_diseq_eh(theory_var x, theory_var y) {
        // get the expressions for left and right side of disequation
        const expr_ref l{get_enode(x)->get_expr(), m};
        const expr_ref r{get_enode(y)->get_expr(), m};

        app* equation = m.mk_eq(l, r);
        app* disequation = m.mk_not(equation);

        // This is to handle the case containing ite inside disequations
        // TODO explain better
        if(!ctx.e_internalized(equation)) {
            STRACE(str, tout << "relevanting: " << mk_pp(disequation, m) << std::endl;);
            ctx.mark_as_relevant(disequation);
        }
        ctx.internalize(disequation, false);

        if(m_util_s.is_re(l) && m_util_s.is_re(r)) { // language disequation
            m_lang_diseq_todo.push_back({l, r});
        } else { // word disequation
            // mk_eq_atom can check if equation trivially holds (by having the
            // same thing on both sides) or not (by having two distintict
            // string literals)
            app* equation_atom = ctx.mk_eq_atom(l, r);
            if (m.is_true(equation_atom)) {
                // if equation trivially holds (i.e. this disequation does not),
                // we immediately stop by always forcing it
                add_axiom({mk_literal(equation)});
            } else if (!m.is_false(equation_atom)) {
                // if equation is not trivially false, we add it for later check
                m_word_diseq_todo.push_back({l, r});
            }
        }

        STRACE(str,
            tout << ctx.find_assignment(equation) << " " << ctx.find_assignment(disequation) << std::endl
                 << "new_diseq: " << l << " != " << r
                 << " @" << m_scope_level<< " " << ctx.get_bool_var(equation) << " "
                 << ctx.is_relevant(disequation) << ":" << ctx.is_relevant(equation) << std::endl;
        );
    }

    bool theory_str_noodler::can_propagate() {
        return false;
    }

    void theory_str_noodler::propagate() {
    }

    void theory_str_noodler::push_scope_eh() {
        theory::push_scope_eh();
        m_scope_level += 1;
        m_word_eq_todo.push_scope();
        m_lang_eq_todo.push_scope();
        m_lang_diseq_todo.push_scope();
        m_word_diseq_todo.push_scope();
        m_membership_todo.push_scope();
        m_not_contains_todo.push_scope();
        m_conversion_todo.push_scope();
        var_eqs.push_scope();
        STRACE(str, tout << "push_scope: " << m_scope_level << '\n';);
    }

    void theory_str_noodler::pop_scope_eh(const unsigned num_scopes) {
        // remove all axiomatized terms
        axiomatized_terms.reset();
        propagated_string_theory.reset();
        m_scope_level -= num_scopes;
        m_word_eq_todo.pop_scope(num_scopes);
        m_lang_eq_todo.pop_scope(num_scopes);
        m_lang_diseq_todo.pop_scope(num_scopes);
        m_word_diseq_todo.pop_scope(num_scopes);
        m_membership_todo.pop_scope(num_scopes);
        m_not_contains_todo.pop_scope(num_scopes);
        m_conversion_todo.pop_scope(num_scopes);
        var_eqs.pop_scope(num_scopes);
        m_rewrite.reset();
        // for incremental solving, we assume (TODO: should be done differently?) that if we added another assert, then pop must have been called and the satisfiability of the last run does not matter
        if (m_scope_level < scope_with_last_run_was_sat) {
            last_run_was_sat = false;
            scope_with_last_run_was_sat = -1;
        }
        STRACE(str,
            tout << "pop_scope: " << num_scopes << " (back to level " << m_scope_level << ")\n";);

        theory::pop_scope_eh(num_scopes);
    }
    
    void theory_str_noodler::restart_eh() {
        STRACE(str, tout << "restart\n");
    }

    void theory_str_noodler::reset_eh() {
        theory::reset_eh();
        STRACE(str, tout << "reset" << '\n';);
    }

    expr_ref theory_str_noodler::mk_sub(expr *a, expr *b) {
        ast_manager &m = get_manager();

        expr_ref result(m_util_a.mk_sub(a, b), m);
        m_rewrite(result);
        return result;
    }

    literal theory_str_noodler::mk_literal(expr *const e) {
        ast_manager &m = get_manager();
        context &ctx = get_context();
        expr_ref ex{e, m};
        // simplify the expression. This was commented before and it caused 
        // problems at some point, I am not pretty sure of what kind.
        m_rewrite(ex);

        // since ex might be different to e, propagate basic string axioms
        string_theory_propagation(ex, true);

        if (!ctx.e_internalized(ex)) {
            ctx.internalize(ex, false);
        }
        enode *const n = ctx.get_enode(ex);
        ctx.mark_as_relevant(n);
        return ctx.get_literal(ex);
    }

    bool_var theory_str_noodler::mk_bool_var(expr *const e) {
        ast_manager &m = get_manager();
        STRACE(str, tout << "mk_bool_var: " << mk_pp(e, m) << '\n';);
        if (!m.is_bool(e)) {
            return null_bool_var;
        }
        context &ctx = get_context();
        SASSERT(!ctx.b_internalized(e));
        const bool_var &bv = ctx.mk_bool_var(e);
        ctx.set_var_theory(bv, get_id());
        ctx.set_enode_flag(bv, true);
        return bv;
    }

    void theory_str_noodler::add_axiom(expr *const e) {
        STRACE(str_axiom, tout << "add_axiom expr: " << mk_pp(e, get_manager()) << std::endl;);

        if (!axiomatized_terms.contains(e)) {
            axiomatized_terms.insert(e);
            if (e == nullptr || get_manager().is_true(e)) return;
            context &ctx = get_context();
            if (!ctx.b_internalized(e)) {
                ctx.internalize(e, false);
            }
            ctx.internalize(e, false);
            literal l{ctx.get_literal(e)};
            ctx.mark_as_relevant(l);
            ctx.mk_th_axiom(get_id(), 1, &l);
        }
    }

    void theory_str_noodler::add_axiom(std::vector<literal> ls) {
        STRACE(str_axiom,
            tout << "add_axiom literals:" << std::endl;
            literal_vector lv;
            for (const auto &l : ls) {
                if (l != null_literal && l != false_literal) {
                    lv.push_back(l);
                }
            }
            ctx.display_literals_verbose(tout, lv) << "\n-----------------------------\n";
        );
        literal_vector lv;
        for (const auto &l : ls) {
            if (l != null_literal && l != false_literal) {
                ctx.mark_as_relevant(l);
                lv.push_back(l);
            }
        }
        if (lv.empty()) {
            return;
        }
        ctx.mk_th_axiom(get_id(), lv);
    }

    /**
     * @brief Handle str.at(s,i)
     *
     * We set str.at(s,i) = v where v is fresh. 
     * Translates to the following theory axioms in the general case:
     * 0 <= i < |s| -> s = xvy
     * 0 <= i < |s| -> v in re.allchar
     * 0 <= i < |s| -> |v| = 1 (not completely neccessary, helps z3)
     * 0 <= i < |s| -> |x| = i
     * i < 0 -> v = eps
     * i >= |s| -> v = eps
     * 
     * Special cases:
     *  - when s is a one letter string literal
     *  - when i is some small non-negative integer
     *  - when i = num + |s| where num is some small negative integer
     *
     * @param e str.at(s, i)
     */
    void theory_str_noodler::handle_char_at(expr *e) {
        if (axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        STRACE(str, tout << "handle char_at: " << mk_pp(e, m) << '\n';);

        expr *s = nullptr, *i = nullptr;
        VERIFY(m_util_s.str.is_at(e, s, i));

        expr_ref v = get_fresh_var_for_string_function("at", e);
        expr_ref v_in_allchar(m_util_s.re.mk_in_re(v, m_util_s.re.mk_full_char(nullptr)), m);
        expr_ref zero(m_util_a.mk_int(0), m);
        expr_ref one(m_util_a.mk_int(1), m);
        literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero)); // i >= 0
        literal i_ge_len_s = mk_literal(m_util_a.mk_ge(mk_sub(i, m_util_s.str.mk_length(s)), zero)); // i >= |s|
        expr_ref emp(m_util_s.str.mk_empty(e->get_sort()), m); // empty string

        // SPECIAL CASES

        // the case where s is one letter string literal, i.e. (str.at "A" i)
        //   i = 0 -> v = "A"
        //   i != 0 -> v = eps
        if(zstring str; m_util_s.str.is_string(s, str) && str.length() == 1) { 
            // i = 0 -> v = "A"
            add_axiom({~mk_literal(m.mk_eq(i, m_util_a.mk_int(0))), mk_eq(v, s, false)});
            // i != 0 -> v = eps
            add_axiom({mk_literal(m.mk_eq(i, m_util_a.mk_int(0))), mk_eq(v, emp, false)});
            return;
        }

        const int MAX_SMALL_INT = 20; // threshold for small integers used in the next two cases (experimentally chosen)
        
        // the case where i is some small non-negative integer (the case where i is negative, i.e. the result is empty string, is handled by rewriter)
        //   i < |s| -> s = s[0].s[1]...s[i].at_right
        //   i < |s| -> v in allchar
        //   i < |s| -> |v| = 1
        //   |s| <= i -> v = eps
        if(rational num; m_util_a.is_numeral(i, num) && num.is_nonneg() && num < MAX_SMALL_INT) { // we want small integer, because otherwise we will create a lot of equations
            int val = num.get_int32();

            // y = s[0].s[1]. ... .s[val].at_right
            expr_ref y = mk_str_var_fresh("at_right");
            for(int j = val; j >= 0; j--) {
                // note that because we add s[j], handle_char_at will be called for each such j creating similar axioms for them
                y = m_util_s.str.mk_concat(m_util_s.str.mk_at(s, m_util_a.mk_int(j)), y);
            }
            string_theory_propagation(y);

            // i < |s| -> s = y
            add_axiom({i_ge_len_s, mk_eq(s, y, false)});
            // i < |s| -> v in allchar
            add_axiom({i_ge_len_s, mk_literal(v_in_allchar)});
            // i < |s| -> |v| = 1
            add_axiom({i_ge_len_s, mk_eq(one, m_util_s.str.mk_length(v), false) });
            // |s| <= i -> v = eps
            add_axiom({~i_ge_len_s, mk_eq(v, emp, false)});

            // Even though we use i<|s| above, we do not have to mark s as length expression, because if z3 decides that i<|s| holds,
            // then from s=s[0]...s[i].at_right we know that length of s is larger than i.
            // Similarly, if z3 decides that i>=|s| holds, we put s[i] = eps. This is correct, the only way for this to not hold is if
            // our computed s would be larger than i. Let assume we can compute such s. As we use all s[j], 0<=j<i, in the axioms,
            // all such s[j] become relevant and this function will be called for them. So for each j, z3 will decide whether j<|s| or j>=|s|.
            // If it decided j>=|s| for all j, then also for 0 we would have 0>=|s| which would force z3 to put |s|=0 but our computed s should
            // be larger than i, so this cannot happen. So there will be some j, where j<|s| let it be the largest one. Z3 will realise that |s|=j+1
            // and furthermore, there will be s=s[0]...s[j].at_right where from |s|=j+1 it will force |at_right|=0. So the computed s must have length
            // j+1 where i>=j+1.
            return;
        }

        // the case that i = num + |s| where num is some small negative integer (the case where num>=0, i.e. the result is empty string, is handled by rewriter)
        //   0 <= i -> s = at_left.s[num+|s|)].s[num+1+|s|)] ... .s[-1+|s|]
        //   0 <= i -> v in allchar
        //   0 <= i -> |v| = 1
        //   i < 0 -> v = eps
        if(rational num; expr_cases::is_num_plus_len(i, s, m, m_util_s, m_util_a, num) && num.is_neg() && num >-MAX_SMALL_INT) { // we want small integer, because otherwise we will create a lot of equations
            int val = num.get_int32();

            // y = at_left.s[val+|s|)].s[val+1+|s|]. ... .s[-1+|s|]
            expr_ref y = mk_str_var_fresh("at_left");
            for(int j = val; j < 0; j++) {
                // note that because we add s[j+|s|], handle_char_at will be called for each such j creating similar axioms for them
                y = m_util_s.str.mk_concat(y, m_util_s.str.mk_at(s, m_util_a.mk_add(m_util_a.mk_int(j), m_util_s.str.mk_length(s))));
            }
            string_theory_propagation(y);

            // 0 <= i -> s = y
            add_axiom({~i_ge_0, mk_eq(s, y, false)});
            // 0 <= i -> v in allchar
            add_axiom({~i_ge_0, mk_literal(v_in_allchar)});
            // 0 <= i -> |v| = 1
            add_axiom({~i_ge_0, mk_eq(one, m_util_s.str.mk_length(v), false) });
            // i < 0 -> v = eps
            add_axiom({i_ge_0, mk_eq(v, emp, false)});

            // We do not have to mark s as length expression, |s| is not used in the axioms above.
            return;
        }

        // GENERAL CASE

        // creating concatenation xvy
        expr_ref x = mk_str_var_fresh("at_left");
        expr_ref y = mk_str_var_fresh("at_right");
        expr_ref xvy(m_util_s.str.mk_concat(x, v, y), m);
        string_theory_propagation(xvy);

        expr_ref len_x(m_util_s.str.mk_length(x), m);
 
        // 0 <= i < |s| -> s = xvy
        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(s, xvy, false)});
        // 0 <= i < |s| -> v in re.allchar
        add_axiom({~i_ge_0, i_ge_len_s, mk_literal(v_in_allchar)});
        // 0 <= i < |s| -> |v| = 1
        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(one, m_util_s.str.mk_length(v), false)});
        // 0 <= i < |s| -> |x| = i
        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(i, len_x, false)});
        // i < 0 -> v = eps
        add_axiom({i_ge_0, mk_eq(v, emp, false)});
        // i >= |s| -> v = eps
        add_axiom({~i_ge_len_s, mk_eq(v, emp, false)});

        // mark s and x as length expressions as |s| and |x| are used in the axioms
        mark_expression_as_length(s);
        mark_expression_as_length(x);
    }

    /**
     * @brief Handle str.substr(s,i,l)
     *
     * We set str.substr(s,i,l) = v where v is fresh.
     * Translates to the following theory axioms:
     * l < 0 -> v = eps
     * i < 0 -> v = eps
     * i > |s| -> v = eps
     * s = eps -> v = eps
     * 0 <= i <= |s| -> x.v.y = s
     * 0 <= i -> |x| = i (as x is fresh, we do not need i <= |s|, for larger i, x will be ignored)
     * 0 <= i <= |s| && 0 <= l <= |s|-i -> |v| = l
     * 0 <= i <= |s| && |s|-i < l  -> |v| = |s|-i
     *
     * Special cases:
     *  - when s is a one letter string literal
     *  - the case (str.substr s 0 (1 + (str.indexof s t n))) with t a nonempty string literal
     *  - the case (str.substr s 0 (|s|-1))
     * 
     * There is also some special handling of x when i is either a numeral or of the form n+|s|
     * where n is a numeral. Furthermore, for l a numeral, there is special handlings of the
     * axioms for |v|.
     *
     * @param e str.substr(s, i, l)
     */
    void theory_str_noodler::handle_substr(expr *e) {
        if (axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        STRACE(str, tout << "handle substr: " << mk_pp(e, m) << '\n';);

        expr *s = nullptr, *i = nullptr, *l = nullptr;
        VERIFY(m_util_s.str.is_extract(e, s, i, l));

        expr_ref v = get_fresh_var_for_string_function("substr", e);

        expr_ref zero(m_util_a.mk_int(0), m);
        expr_ref one(m_util_a.mk_int(1), m);
        expr_ref eps(m_util_s.str.mk_string(""), m);
        expr_ref re_allchar(m_util_s.re.mk_full_char(nullptr), m);

        expr_ref lv(m_util_s.str.mk_length(v), m);
        expr_ref ls(m_util_s.str.mk_length(s), m);
        expr_ref ls_minus_i_minus_l(mk_sub(mk_sub(ls, i), l), m);

        literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
        literal i_le_ls = mk_literal(m_util_a.mk_le(mk_sub(i, ls), zero));
        literal ls_ge_l_plus_i = mk_literal(m_util_a.mk_ge(ls_minus_i_minus_l, zero));
        literal l_ge_0 = mk_literal(m_util_a.mk_ge(l, zero));
        literal s_is_empty = mk_eq(s, eps, false);

        const unsigned MAX_LOOPING = 50; // maximal looping allowed in regexes (if too large, the automata get too large)

        // SPECIAL CASES

        // the case where s is a string literal of length 1, i.e. (str.substr "A" i l)
        //   i != 0 -> v = eps
        //   l < 1 -> v = eps
        //   i = 0 && l >= 1 -> v = "A"
        if(zstring str_s; m_util_s.str.is_string(s, str_s) && str_s.length() == 1) {
            literal i_eq_0 = mk_literal(m_util_a.mk_eq(i, zero));
            literal l_ge_1 = mk_literal(m_util_a.mk_ge(l, one));

            // i != 0 -> v = eps
            add_axiom({i_eq_0, mk_eq(v, eps, false)});
            // l < 1 -> v = eps
            add_axiom({l_ge_1, mk_eq(v, eps, false)});
            // i = 0 && l >= 1 -> v = s
            add_axiom({~i_eq_0, ~l_ge_1, mk_eq(v, s, false)});
            return;
        }

        // the case (str.substr s 0 (1 + (str.indexof s t n))) with t a nonempty string literal
        //    - this case is very useful for pyex, try for example on QF_SLIA/20180523-Reynolds/pyex/peterc-pyex-doc-cav17-zz/httplib2/httplib2-entry-disposition/39783579d992a26f238877df4ca2ead6571ddafc66bf1b6d7fd58db0.smt2
        //    - if (str.indexof s t n) != -1 (i.e. t occurs somewhere in s starting from position n), then we can rewrite
        //           (str.substr s 0 (1 + (str.indexof s t n)))   to   (str.++ (str.substr s 0 (str.indexof s t n)) t[0])
        //    - we add axiom
        //         (str.indexof s t n) != -1 -> (str.substr s 0 (1 + (str.indexof s t n))) = (str.++ (str.substr s 0 (str.indexof s t n)) t[0])
        if(zstring indexof_find_string; m_util_a.is_zero(i) && expr_cases::is_one_add_indexof_string(l, s, m, m_util_s, m_util_a, indexof_find_string) && !indexof_find_string.empty()) {
            literal indexof_did_not_find = mk_eq(l, zero, false); // if (1 + (str.indexof s t n))==0, then t was not found in s from position n
            // we get the indexof expr by substracting 1 from l
            expr_ref indexof(m_util_a.mk_add(l, m_util_a.mk_int(-1)), m);
            m_rewrite(indexof);
            // (str.substr s 0 (str.indexof s t n))
            expr_ref new_substr(m_util_s.str.mk_substr(s, i, indexof), m);
            // t[0]
            expr_ref first_char_of_t(m_util_s.str.mk_string(indexof_find_string.extract(0,1)), m);
            // (str.++ (str.substr s 0 (str.indexof s t n)) t[0])
            expr_ref conc = mk_concat(new_substr, first_char_of_t);
            string_theory_propagation(conc);

            // (str.indexof s t n) != -1 -> (str.substr s 0 (1 + (str.indexof s t n))) = (str.++ (str.substr s 0 (str.indexof s t n)) t[0])
            add_axiom({indexof_did_not_find, mk_eq(e, conc, false)});
            return;
        }

        // the case (str.substr s 0 (|s|-1))
        //   s != eps -> s = vy
        //   s != eps -> y in re.allchar
        //   s != eps -> |y| = 1 (not completely neccessary, helps z3)
        //   s = eps -> v = eps
        if(rational num; m_util_a.is_zero(i) && expr_cases::is_num_plus_len(l, s, m, m_util_s, m_util_a, num) && num.is_minus_one()) {
            expr_ref y = mk_str_var_fresh("post_substr");
            expr_ref y_in_allchar(m_util_s.re.mk_in_re(y, m_util_s.re.mk_full_char(nullptr)), m);
            expr_ref ly(m_util_s.str.mk_length(y), m);
            expr_ref vy(m_util_s.str.mk_concat(v, y), m);
            string_theory_propagation(vy);

            // s != eps -> s = vy
            add_axiom({s_is_empty, mk_eq(s, vy, false)});
            // s != eps -> y in re.allchar
            add_axiom({s_is_empty, mk_literal(y_in_allchar)});
            // s != eps -> |y| = 1
            add_axiom({s_is_empty, mk_eq(ly, one, false)});
            // s = eps -> v = eps
            add_axiom({~s_is_empty, mk_eq(v, eps, false)});
            // update length variables
            mark_expression_as_length(s);
            this->var_eqs.add(expr_ref(l, m), v);
            return;
        }

        // GENERAL CASE

        // First the invalid cases
        // l < 0 -> v = eps
        add_axiom({l_ge_0, mk_eq(v, eps, false)});
        // i < 0 -> v = eps
        add_axiom({i_ge_0, mk_eq(v, eps, false)});
        // i > |s| -> v = eps
        add_axiom({i_le_ls, mk_eq(v, eps, false)});
        // s = eps -> v = eps
        add_axiom({~s_is_empty, mk_eq(v, eps, false)});

        // We will now create concatenation s=xvy for the valid case where v is the result of substr,
        // |x|=i and either |v|=l (if 0 <= l <= |s|-i) or |v|=|s|-i (if |s|-i < l)

        // Starting with x, we want to have |x| = i (but only if i >= 0) and put x in len vars.
        // Note that for i > |s| (invalid case), we do not care about x, so it can still be equal to i.
        // We can also handle some special cases in a better way.
        expr_ref x(m);
        if (m_util_a.is_zero(i)) {
            // if i=0 there is nothing before v in the concatenation, so x=eps
            x = eps;
        } else {
            x = mk_str_var_fresh("pre_substr");

            // stronger axioms: if i = t+n for some (positive) numeral n and expression t, then, if t>=0, we can split x to two parts x = x1.x2 where |x1|=t and |x2|=n
            //   t>=0 -> x2 in re.allchar^n
            //   t>=0 -> |x2| = n (not completely needed, helps z3)
            // these axioms are needed for pyex/full_str_int so x1 is in var_eqs with t
            if(expr *n, *t; m_util_a.is_add(i, n, t)) { // is i of the form t+n?
                if (rational n_value; m_util_a.is_numeral(n, n_value) && n_value.is_pos() && n_value <= MAX_LOOPING) {
                    unsigned n_value_unsigned = n_value.get_unsigned();

                    expr_ref x1 = x;
                    expr_ref x2 = mk_str_var_fresh("in_substr");
                    x = m_util_s.str.mk_concat(x1, x2);

                    // x2 in re.allchar^n
                    expr_ref x2_in_sigma_times_num(m_util_s.re.mk_in_re(x2, m_util_s.re.mk_loop_proper(re_allchar, n_value_unsigned, n_value_unsigned)), m);
                    literal t_ge_0 = mk_literal(m_util_a.mk_ge(t, zero)); // t>=0
                    // t>=0 -> x2 in re.allchar^n
                    add_axiom({~t_ge_0, mk_literal(x2_in_sigma_times_num)});
                    // t>=0 -> |x2| = n (not completely needed, helps z3)
                    add_axiom({~i_ge_0, ~i_le_ls, ~t_ge_0, mk_eq(m_util_s.str.mk_length(x2), n, false)});
                    // |x1| = t (we do not need to put it in an axiom, we will have that |x| = i later from which |x1| = t follows)
                    this->var_eqs.add(expr_ref(t, m), x1, false); // equivalence might not be precise (we need to check whether the equivalence holds in final_check).
                    // It is not precise because for t < 0 the equivalence does not hold
                }
            }

            // 0 <= i -> |x| = i
            add_axiom({~i_ge_0, mk_eq(m_util_s.str.mk_length(x), i, false)});
            this->var_eqs.add(expr_ref(i, m), x); // |x| = i, is not true for i <0, but because x is fresh and is used only in s=xvy, we only care about the situation where s=xvy is true, and in that case i>=0

            // Because we use |x| in the axiom, we should put it in length vars, however, if i is a (reasonably small) numeral
            // we can put x in re.allchar^i and then we do not have to add x to len vars as the length is restricted by the regex
            if (rational i_val; m_util_a.is_numeral(i, i_val) && i_val.is_pos() && i_val <= MAX_LOOPING) {
                unsigned i_val_unsigned = i_val.get_unsigned();
                expr_ref x_in_sigma_time_i(m_util_s.re.mk_in_re(x, m_util_s.re.mk_loop_proper(re_allchar, i_val_unsigned, i_val_unsigned)), m);
                // x in re.allchar^i
                add_axiom({mk_literal(x_in_sigma_time_i)});
            } else {
                mark_expression_as_length(x);
            }
        }

        // We now set the length of v:
        // 0 <= i <= |s| && 0 <= l <= |s|-i -> |v| = l
        add_axiom({~i_ge_0, ~i_le_ls, ~l_ge_0, ~ls_ge_l_plus_i, mk_eq(lv, l, false)});
        // 0 <= i <= |s| && |s|-i < l  -> |v| = |s|-i
        add_axiom({~i_ge_0, ~i_le_ls, ls_ge_l_plus_i, mk_eq(lv, mk_sub(ls, i), false)});
        // remember l=|v|
        this->var_eqs.add(expr_ref(l, m), v, false); // equivalence might not be precise (we need to check whether the equivalence holds in final_check)
        // It is not precise because in case where l > |s|-i, the length of v is |s|-i (not l).

        // We also need to put v in length variables, but not always. For this we nned to have y created.

        expr_ref y(m);
        // i+l >= |s|
        expr_ref post_bound(m_util_a.mk_ge(m_util_a.mk_add(i, l), m_util_s.str.mk_length(s)), m);
        m_rewrite(post_bound); // simplify
        if(m.is_true(post_bound)) {
            // If i + l >= |s|, we can set y to eps and we do not have to put v in length vars
            // as s=xv and the length of x is already handled by previous axioms (so v will be
            // automatically the rest of s).
            y = expr_ref(m_util_s.str.mk_string(""), m);
        } else {
            y = mk_str_var_fresh("post_substr");
            // If l is some (reasonably small) numeral, we can put
            //   - v in re.allchar^l, for the case 0 <= l <= |s|-i,
            //   - y=eps, for the case |s|-i < l.
            // Then we do not have to put v in length vars.
            if(rational l_val; m_util_a.is_numeral(l, l_val) && l_val.is_pos() && l_val <= MAX_LOOPING) {
                unsigned l_val_unsigned = l_val.get_unsigned();
                expr_ref substr_in(m_util_s.re.mk_in_re(v, m_util_s.re.mk_loop_proper(re_allchar, l_val_unsigned, l_val_unsigned)), m);
    
                // 0 <= i <= |s| && |s| < l + i  -> y = eps
                add_axiom({~i_ge_0, ~i_le_ls, ls_ge_l_plus_i, mk_eq(y, eps, false)});
                // 0 <= i <= |s| && 0 <= l <= |s| - i -> v in re.allchar^l
                add_axiom({~i_ge_0, ~i_le_ls, ~l_ge_0, ~ls_ge_l_plus_i, mk_literal(substr_in)});
            } else {
                 mark_expression_as_length(v);
            }
        }

        // We now create concatenation xvy and the main axiom
        expr_ref xvy(m_util_s.str.mk_concat(x, v, y), m);
        string_theory_propagation(xvy);

        // 0 <= i <= |s| -> xvy = s
        add_axiom({~i_ge_0, ~i_le_ls, mk_eq(xvy, s, false)});

        // mark s as length, as |s| is used in the axioms
        mark_expression_as_length(s);
    }

    /**
     * @brief Handling of str.replace(a,s,t) = v ... a where to replace, s what to find, t replacement.
     * Translates to the following theory axioms:
     * replace(a,s,t) = v
     * a = eps && s != eps -> v = a
     * (not(contains(a,s))) -> v = a
     * s = eps -> v = t.a
     * contains(a,s) && a != eps && s != eps -> a = x.s.y
     * contains(a,s) && a != eps && s != eps -> v = x.t.y
     * tighttestprefix(s, x, not(contains(a,s) && a != eps && s != eps))
     *
     * @param r replace term
     */
    void theory_str_noodler::handle_replace(expr *r) {
        if (axiomatized_persist_terms.contains(r)) { return; }
        axiomatized_persist_terms.insert(r);

        STRACE(str, tout << "handle replace: " << mk_pp(r, m) << '\n';);

        expr* a = nullptr, *s = nullptr, *t = nullptr;
        VERIFY(m_util_s.str.is_replace(r, a, s, t));

        expr_ref v = get_fresh_var_for_string_function("replace", r);

        expr_ref x = mk_str_var_fresh("replace_left");
        expr_ref y = mk_str_var_fresh("replace_right");
        expr_ref xty = mk_concat(x, mk_concat(t, y));
        expr_ref xsy = mk_concat(x, mk_concat(s, y));
        expr_ref eps(m_util_s.str.mk_string(""), m);
        literal a_emp = mk_eq_empty(a);
        literal s_emp = mk_eq_empty(s);

        // if s = t -> the result is unchanged
        add_axiom({~mk_eq(s, t, false), mk_eq(v, a,false)});
        // s = eps -> |v| = |a| + |t|
        add_axiom({~s_emp, mk_literal(m.mk_eq(m_util_s.str.mk_length(v), m_util_a.mk_add(m_util_s.str.mk_length(a), m_util_s.str.mk_length(t))))});

        // axioms for the case str.replace x (y.x) z
        expr* t1 = nullptr, *t2 = nullptr;
        if(m_util_s.str.is_concat(s, t1, t2) && (t1 == a || t2 == a)) {
            if(t1 == a) {
                add_axiom({~mk_eq_empty(t2), mk_eq(v, t,false)});
                add_axiom({mk_eq_empty(t2), mk_eq(v, a ,false)});
            } else {
                add_axiom({~mk_eq_empty(t1), mk_eq(v, t,false)});
                add_axiom({mk_eq_empty(t1), mk_eq(v, a,false)});
            }

            return;
        }

        expr* indexof = nullptr;
        if(expr_cases::is_replace_indexof(a, s, m, m_util_s, m_util_a, indexof)) {
            expr_ref minus_one(m_util_a.mk_int(-1), m);
            expr_ref eps(m_util_s.str.mk_string(""), m);
            literal ind_eq_m1 = mk_eq(indexof, minus_one, false);
            expr_ref len_a_m1(m_util_a.mk_sub(m_util_s.str.mk_length(a), m_util_a.mk_int(1)), m);
            expr_ref substr(m_util_s.str.mk_substr(a, m_util_a.mk_int(0), len_a_m1), m);

            // s = eps -> v = t.a
            add_axiom({~s_emp, mk_eq(v, mk_concat(t, a),false)});
            add_axiom({ind_eq_m1, mk_eq(v, mk_concat(substr, t),false)});
            add_axiom({~ind_eq_m1, mk_eq(v, eps, false)});
            return;
        }

        zstring str_a, str_b;
        // str.replace "A" s t where a = "A"
        if(m_util_s.str.is_string(a, str_a) && str_a.length() == 1) {
            // s = emp -> v = t.a
            // NOTE: we add it twice in different forms because Z3 for some reason ignores one of them sometimes, see https://github.com/VeriFIT/z3-noodler/pull/236
            add_axiom({~s_emp, mk_literal(m.mk_eq(v, mk_concat(t, a)))});
            add_axiom({mk_literal(m.mk_not(m.mk_eq(s, eps))), mk_literal(m.mk_eq(v, mk_concat(t, a)))});
            // s = a -> v = t
            // NOTE: if we use ~mk_eq(s, a), this diseqation does not become relevant
            add_axiom({mk_literal(m.mk_not(m.mk_eq(s, a))), mk_eq(v, t,false)});
            // add_axiom({~mk_eq(s, a, false), mk_eq(v, t,false)});
            // s != eps && s != a -> v = a
            add_axiom({mk_eq(s, a, false), s_emp, mk_eq(v, a,false)});
            

            // The following axioms are redundant in the sense of completeness, but in the nested replace calls 
            // they can relate the contains predicate from the general replace (and thence the SAT solver can help a lot).
            literal cnt = mk_literal(m_util_s.str.mk_contains(s, a));
            // strenghten not contains axiom with s = a
            add_axiom({~cnt, mk_literal(m.mk_not(m.mk_eq(s, a))), mk_eq(v, t,false)});
            add_axiom({cnt, s_emp, mk_eq(v, a,false)});
            ctx.force_phase(cnt);

            return;
        // str.replace "" s t where a = ""
        } else if(m_util_s.str.is_string(a, str_a) && str_a.length() == 0) {
            // s = emp -> v = t.a
            add_axiom({mk_literal(m.mk_not(m.mk_eq(s, eps))), mk_eq(v,t,false)});
            // s = emp -> v = t.a
            add_axiom({s_emp, mk_eq_empty(v)});
            return;
        }

        literal cnt = mk_literal(m_util_s.str.mk_contains(a, s));
        // a = eps && s != eps -> v = a
        add_axiom({~a_emp, s_emp, mk_eq(v, a, false)});
        // (not(contains(a,s))) -> v = a
        add_axiom({cnt, mk_eq(v, a, false)});

        // if both strings are explicit and cnt holds, extract exact lengths of the result.
        if(m_util_s.str.is_string(s, str_a) && m_util_s.str.is_string(t, str_b) && str_a.length() >= str_b.length()) {
            add_axiom({~cnt, mk_literal(m.mk_eq(m_util_s.str.mk_length(v), m_util_a.mk_sub(m_util_s.str.mk_length(a), m_util_a.mk_int(str_a.length() - str_b.length()) )))});
        }
        
        // s = eps -> v = t.a
        add_axiom({~s_emp, mk_eq(v, mk_concat(t, a),false)});
        // contains(a,s) && a != eps && s != eps -> a = x.s.y
        add_axiom({~cnt, a_emp, s_emp, mk_eq(a, xsy,false)});
        // contains(a,s) && a != eps && s != eps -> v = x.t.y
        add_axiom({~cnt, a_emp, s_emp, mk_eq(v, xty,false)});
        ctx.force_phase(cnt);
        // tighttestprefix(s, x, not(contains(a,s) && a != eps && s != eps))
        tightest_prefix(s, x, {~cnt, a_emp, s_emp});
    }

    /**
     * @brief Handling of str.indexof(t, s, offset) = indexof
     * Translates to the following theory axioms:
     * The case of offset = 0
     * not(contains(t,s)) -> indexof = -1
     * t = eps && s != eps -> indexof = -1
     * s = eps -> indexof = 0
     * contains(t, s) -> indexof >= 0
     * contains(t, s) && s != eps -> t = x.s.y
     * contains(t, s) && s != eps -> indexof = |x|
     * tightestprefix(s, x, not(contains(t, s) && s != eps))
     *
     * The case of offset > 0
     * not(contains(t,s)) -> indexof = -1
     * t = eps && s != eps -> indexof = -1
     * offset >= |t| && s != eps -> indexof = -1
     * offset > |t| -> indexof = -1
     * offset >= |t| && offset <= |t| && s = eps -> indexof = offset
     * offset >= 0 && offset < |t| -> t = xy
     * offset >= 0 && offset < |t| -> |x| = offset
     * offset >= 0 && offset < |t| && indexof(y,s,0) = -1 -> indexof = -1
     * offset >= 0 && offset < |t| && indexof(y,s,0) >= 0 -> offset + indexof(y,s,0) = indexof
     * offset < 0 -> indexof = -1
     *
     * @param i indexof term
     */
    void theory_str_noodler::handle_index_of(expr *i) {
        if (axiomatized_persist_terms.contains(i)) { return; }
        axiomatized_persist_terms.insert(i);

        STRACE(str, tout << "handle indexof: " << mk_pp(i, m) << '\n';);

        expr *s = nullptr, *t = nullptr, *offset = nullptr;
        VERIFY(m_util_s.str.is_index(i, t, s) || m_util_s.str.is_index(i, t, s, offset));

        expr_ref minus_one(m_util_a.mk_int(-1), m);
        expr_ref zero(m_util_a.mk_int(0), m);
        literal cnt = mk_literal(m_util_s.str.mk_contains(t, s));

        literal i_eq_m1 = mk_eq(i, minus_one, false);
        literal i_eq_0 = mk_eq(i, zero, false);
        literal s_eq_empty = mk_eq_empty(s);
        literal t_eq_empty = mk_eq_empty(t);

        // not(contains(t,s)) -> indexof = -1
        add_axiom({cnt, i_eq_m1});
        // t = eps && s != eps -> indexof = -1
        add_axiom({~t_eq_empty, s_eq_empty, i_eq_m1});

        if (!offset || m_util_a.is_zero(offset)) {
            expr_ref x = mk_str_var_fresh("index_left");
            expr_ref y = mk_str_var_fresh("index_right");
            expr_ref xsy(m_util_s.str.mk_concat(x, s, y), m);
            string_theory_propagation(xsy);

            expr_ref lenx(m_util_s.str.mk_length(x), m);
            // s = eps -> indexof = 0
            add_axiom({~s_eq_empty, i_eq_0});
            // contains(t, s) -> indexof >= 0
            add_axiom({~cnt, mk_literal(m_util_a.mk_ge(i, zero))});
            // contains(t, s) && s != eps -> t = x.s.y
            add_axiom({~cnt, s_eq_empty, mk_eq(t, xsy, false)});
            // contains(t, s) && s != eps -> indexof = |x|
            add_axiom({~cnt, s_eq_empty, mk_eq(i, lenx, false)});
            // tightestprefix(s, x, not(contains(t, s) && s != eps))
            tightest_prefix(s, x, {~cnt, s_eq_empty});

            if(expr_cases::is_indexof_at(s, t, m, m_util_s)) {
                add_axiom({mk_literal(m_util_a.mk_ge(i, zero))});
            }

            // update length variables
            this->len_vars.insert(x);
            this->var_eqs.add(expr_ref(i, m), x);

            expr_ref rest(m_util_a.mk_sub(m_util_a.mk_sub(m_util_s.str.mk_length(t), i), m_util_s.str.mk_length(s)), m);
            m_rewrite(rest);
            this->var_eqs.add(rest, y);

        } else {
            expr_ref len_t(m_util_s.str.mk_length(t), m);
            literal offset_ge_len = mk_literal(m_util_a.mk_ge(mk_sub(offset, len_t), zero));
            literal offset_le_len = mk_literal(m_util_a.mk_le(mk_sub(offset, len_t), zero));
            literal i_eq_offset = mk_eq(i, offset, false);
            // offset >= |t| && s != eps -> indexof = -1
            add_axiom({~offset_ge_len, s_eq_empty, i_eq_m1});
            // offset > |t| -> indexof = -1
            add_axiom({offset_le_len, i_eq_m1});
            // offset >= |t| && offset <= |t| && s = eps -> indexof = offset
            add_axiom({~offset_ge_len, ~offset_le_len, ~s_eq_empty, i_eq_offset});

            expr_ref x = mk_str_var_fresh("index_left_off");
            expr_ref y = mk_str_var_fresh("index_right_off");
            expr_ref xy(m_util_s.str.mk_concat(x, y), m);
            string_theory_propagation(xy);

            expr_ref indexof0(m_util_s.str.mk_index(y, s, zero), m);
            expr_ref offset_p_indexof0(m_util_a.mk_add(offset, indexof0), m);
            literal offset_ge_0 = mk_literal(m_util_a.mk_ge(offset, zero));
            // offset >= 0 && offset < |t| -> t = xy
            add_axiom({~offset_ge_0, offset_ge_len, mk_eq(t, xy, false)});
            // offset >= 0 && offset < |t| -> |x| = offset
            add_axiom({~offset_ge_0, offset_ge_len, mk_eq(m_util_s.str.mk_length(x), offset, false)});
            // offset >= 0 && offset < |t| && indexof(y,s,0) = -1 -> indexof = -1
            add_axiom({~offset_ge_0, offset_ge_len, ~mk_eq(indexof0, minus_one, false), i_eq_m1});
            // offset >= 0 && offset < |t| && indexof(y,s,0) >= 0 -> offset + indexof(y,s,0) = indexof
            add_axiom({~offset_ge_0, offset_ge_len, ~mk_literal(m_util_a.mk_ge(indexof0, zero)),
                            mk_eq(offset_p_indexof0, i, false)});
            // offset < 0 -> indexof = -1
            add_axiom({offset_ge_0, i_eq_m1});

            // update length variables
            mark_expression_as_length(t);
            this->len_vars.insert(x);
        }
    }

    void theory_str_noodler::tightest_prefix(expr* s, expr* x, std::vector<literal> neg_assumptions) {
        literal x_eq_emp = mk_eq_empty(x);

        zstring str;
        if (m_util_s.str.is_string(s, str)) {
            if (str.length() == 0) {
                // s == epsilon, i.e. we only need to add '(s = eps) && (x != eps) -> neg_assumptions'
                // where we know that (s = eps) is true
                neg_assumptions.push_back(x_eq_emp);
                add_axiom(neg_assumptions);
            } else {
                // s != epsilon, we only need 'not(s = eps) -> neg_assumptions || not(contains(x.s1, s))'
                // where s1=s[0:-2] and we know that not(s = eps) is true
                expr_ref s1(m_util_s.str.mk_string(str.extract(0, str.length()-1)), m);
                neg_assumptions.push_back(~mk_literal(m_util_s.str.mk_contains(mk_concat(x, s1), s)));
                add_axiom(neg_assumptions);
            }
        } else {
            // s is not string literal, we need to add all 4 theory axioms

            // we set (s = eps) for the first 3 theory axioms
            literal s_eq_emp = mk_eq_empty(s);
            neg_assumptions.push_back(s_eq_emp);

            // not(s = eps) -> neg_assumptions || s = s1.s2
            expr_ref s1 = mk_str_var_fresh("tightest_prefix_first");
            expr_ref s2 = mk_str_var_fresh("tightest_prefix_last");
            expr_ref s1s2 = mk_concat(s1, s2);
            neg_assumptions.push_back(mk_literal(m.mk_eq(s, s1s2)));
            add_axiom(neg_assumptions);

            // not(s = eps) -> neg_assumptions || s2 in re.allchar (is a single character)
            expr_ref re(m_util_s.re.mk_in_re(s2, m_util_s.re.mk_full_char(nullptr)), m);
            neg_assumptions.back() = mk_literal(re);
            add_axiom(neg_assumptions);

            // not(s = eps) -> neg_assumptions || not(contains(x.s1, s))
            neg_assumptions.back() = ~mk_literal(m_util_s.str.mk_contains(mk_concat(x, s1), s));
            add_axiom(neg_assumptions);

            // (s = eps) && (x != eps) -> neg_assumptions
            // we need to change (s = eps) to not(s = eps)
            neg_assumptions[neg_assumptions.size() - 2] = ~s_eq_emp;
            neg_assumptions.back() = x_eq_emp;
            add_axiom(neg_assumptions);
        }
    }

    /**
     * @brief Handle replace_re. Just store the instance. It is solved using transducer 
     * constraints in the final_check.
     * 
     * @param e replace_re term
     */
    void theory_str_noodler::handle_replace_re(expr *e) {
        if (axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        STRACE(str, tout << "handle replace_re: " << mk_pp(e, m) << '\n';);

        expr *s = nullptr, *R = nullptr, *t = nullptr;
        VERIFY(m_util_s.str.is_replace_re(e, s, R, t));

        expr_ref v = get_fresh_var_for_string_function("replace_re", e);
    }

    /**
     * @brief Handle replace_all. Just store the instance. It is solved using transducer 
     * constraints in the final_check.
     * 
     * @param e replace_all
     */
    void theory_str_noodler::handle_replace_all(expr *e) {
        if (axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        STRACE(str, tout << "handle replace_all: " << mk_pp(e, m) << '\n';);

        expr *s = nullptr, *i = nullptr, *l = nullptr;
        VERIFY(m_util_s.str.is_replace_all(e, s, i, l));

        expr_ref v = get_fresh_var_for_string_function("replace_all", e);
    }

    /**
     * @brief Handle replace_re_all. Just store the instance. It is solved using transducer 
     * constraints in the final_check.
     * 
     * @param e replace_re_all
     */
    void theory_str_noodler::handle_replace_re_all(expr *e) {
        if (axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        STRACE(str, tout << "handle replace_re_all: " << mk_pp(e, m) << '\n';);

        expr *s = nullptr, *i = nullptr, *l = nullptr;
        VERIFY(m_util_s.str.is_replace_re_all(e, s, i, l));

        expr_ref v = get_fresh_var_for_string_function("replace_re_all", e);
    }

    /**
     * @brief Handling of str.update(w, i, r)
     * Starts replacing characters in w at index i with characters in r
     * The resulting string will always have the same length as w,
     * meaning if r is too long to fit into w, it will get truncated
     * (e.g. str.update("aaaa", 2, "bbbb") = "aabb")
     *
     * 0 <= i < |w| && |r| > 0  ->  str.update(w, i, r) = u1 u2 u3
     * 0 <= i < |w| && |r| > 0  ->  w = u1 x u3
     * 0 <= i < |w| && |r| > 0  ->  |u1| = i
     * 0 <= i < |w| && |r| > 0  ->  |x| = |u2|
     * 0 <= i < |w| && |r| > 0  ->  r = u2 y
     * 0 <= i < |w| && |r| > 0 && |r| >  |w| - i  ->  |u2| = |w| - i
     * 0 <= i < |w| && |r| > 0 && |r| <= |w| - i  ->  |u2| = |r|
     *
     * i < 0   -> str.update(w, i, r) = w;
     * i >=|w| -> str.update(w, i, r) = w;
     * |r| <= 0 -> str.update = w (not completely necessary, helps z3)
     *
     * @param e The str.update(w, i, r) term
     */
    void theory_str_noodler::handle_update(expr *e) {
        if (axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        expr *w = nullptr, *i = nullptr, *r = nullptr;
        VERIFY(m_util_s.str.is_update(e, w, i, r));

        expr_ref x = mk_str_var_fresh("update_removing");
        expr_ref y = mk_str_var_fresh("update_overflow");
        expr_ref u1 = mk_str_var_fresh("update_left");
        expr_ref u2 = mk_str_var_fresh("update_center");
        expr_ref u3 = mk_str_var_fresh("update_right");

        expr_ref result = get_fresh_var_for_string_function("update", e);

        expr_ref u1_x_u3 = mk_concat(u1, mk_concat(x, u3));
        expr_ref u2_y = mk_concat(u2, y);
        expr_ref u1_u2_u3 = mk_concat(u1, mk_concat(u2, u3));

        expr_ref zero(m_util_a.mk_int(0), m);

        // |r| > |w| - i
        literal will_overflow = mk_literal(m_util_a.mk_gt(mk_sub(m_util_s.str.mk_length(r), m_util_a.mk_sub(m_util_s.str.mk_length(w), i)), zero));
        // i >= 0
        literal i_ge_zero = mk_literal(m_util_a.mk_ge(i, zero));
        // i < |w|
        literal i_lt_len_w = mk_literal(m_util_a.mk_lt(mk_sub(i, m_util_s.str.mk_length(w)), zero));
        // |r| <= 0
        literal r_len_le_zero = mk_literal(m_util_a.mk_le(m_util_s.str.mk_length(r), zero));

        // 0 <= i < |w| && |r| > 0  ->  str.update(w, i, r) = u1 u2 u3
        add_axiom({~i_ge_zero, ~i_lt_len_w, r_len_le_zero, mk_eq(u1_u2_u3, result, false)});
        // 0 <= i < |w| && |r| > 0  ->  w = u1 x u3
        add_axiom({~i_ge_zero, ~i_lt_len_w, r_len_le_zero, mk_eq(u1_x_u3, w, false)});
        // 0 <= i < |w| && |r| > 0  ->  |u1| = i
        add_axiom({~i_ge_zero, ~i_lt_len_w, r_len_le_zero, mk_eq(i, m_util_s.str.mk_length(u1), false)});
        // 0 <= i < |w| && |r| > 0  ->  |x| = |u2|
        add_axiom({~i_ge_zero, ~i_lt_len_w, r_len_le_zero, mk_eq(m_util_s.str.mk_length(x), m_util_s.str.mk_length(u2), false)});
        // 0 <= i < |w| && |r| > 0  ->  r = u2 y
        add_axiom({~i_ge_zero, ~i_lt_len_w, r_len_le_zero, mk_eq(u2_y, r, false)});
        // 0 <= i < |w| && |r| > 0 && |r| >  |w| - i ->  |u2| = |w| - i
        add_axiom({~i_ge_zero, ~i_lt_len_w, r_len_le_zero, ~will_overflow, mk_eq(m_util_s.str.mk_length(u2), m_util_a.mk_sub(m_util_s.str.mk_length(w), i), false)});
        // 0 <= i < |w| && |r| > 0 && |r| <= |w| - i ->  |u2| = |r|
        add_axiom({~i_ge_zero, ~i_lt_len_w, r_len_le_zero, will_overflow, mk_eq(m_util_s.str.mk_length(u2), m_util_s.str.mk_length(r) , false)});

        // i < 0   -> str.update(w, i, r) = w;
        add_axiom({i_ge_zero, mk_eq(result, w, false)});
        // i >=|w| -> str.update(w, i, r) = w;
        add_axiom({i_lt_len_w, mk_eq(result, w, false)});
        // |r| <= 0 -> str.update = w (not completely necessary, helps z3)
        add_axiom({~r_len_le_zero, mk_eq(result, w, false)});

        mark_expression_as_length(u1);
        mark_expression_as_length(x);
        mark_expression_as_length(u2);
        mark_expression_as_length(r);
        mark_expression_as_length(w);
    }

    /**
     * @brief Handling of str.trim(w)
     * Trims the whitespace at the edges of w
     *
     * str.trim(w) = u
     * w = tl u tr
     * tl, tr ∈ WS*
     * u ∈ (Σ\WS)* + (Σ\WS)Σ*(Σ\WS) (u must not start and end with whitespace)
     * WS = " " + "\f" + "\n" + "\r" + "\t" + "\v"
     *
     * @param e The str.trim(w) term
     */
    void theory_str_noodler::handle_trim(expr *e) {
        if (axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        expr *w = nullptr;
        VERIFY(m_util_s.str.is_trim(e, w));

        expr_ref tl = mk_str_var_fresh("trim_left");
        expr_ref tr = mk_str_var_fresh("trim_right");

        expr_ref u = get_fresh_var_for_string_function("trim", e);

        expr_ref tl_u_tr = mk_concat(tl, mk_concat(u, tr));

        // WS = " " + "\f" + "\n" + "\r" + "\t" + "\v"
        expr_ref whitespace_re(m_util_s.re.mk_to_re(m_util_s.str.mk_string(" ")), m);
        for (auto ws : { "\f", "\n", "\r", "\t", "\v" }) {
            whitespace_re = expr_ref(m_util_s.re.mk_union(
                        whitespace_re,
                        m_util_s.re.mk_to_re(m_util_s.str.mk_string(ws))), m);
        }
        // sigma \ WS
        expr_ref sigma_minus_ws(m_util_s.re.mk_diff(m_util_s.re.mk_full_char(nullptr), whitespace_re), m);
        // sigma*
        expr_ref sigma_star(m_util_s.re.mk_star(m_util_s.re.mk_full_char(nullptr)), m);
        // WS*
        expr_ref ws_star(m_util_s.re.mk_star(whitespace_re), m);
        // (sigma \ WS)* + ((sigma \ WS) . sigma_star . (sigma \ WS))
        expr_ref middle_regex(m_util_s.re.mk_union(
                    // u is either in (sigma\WS)* - covers if u is eps or one character long
                    m_util_s.re.mk_star(sigma_minus_ws),
                    // or u is in (sigma\WS)sigma*(sigma\WS) - sigma star surrounded with non whitespace characters
                    m_util_s.re.mk_concat(sigma_minus_ws, m_util_s.re.mk_concat(sigma_star, sigma_minus_ws))
                    ), m);


        // w = tl u tr
        add_axiom({mk_eq(w, tl_u_tr, false)});
        // tl is whitespace
        add_axiom({mk_literal(m_util_s.re.mk_in_re(tl, ws_star))});
        // tr is whitespace
        add_axiom({mk_literal(m_util_s.re.mk_in_re(tr, ws_star))});
        // u does not begin and end with whitespace characters
        add_axiom({mk_literal(m_util_s.re.mk_in_re(u, middle_regex))});
    }

    /**
     * @brief Handling of str.delete(w, i, l)
     * Deletes a substring of length l from w at index i
     *
     * l <= 0   ->  str.delete(w, i, l) = w
     * i <  0   ->  str.delete(w, i, l) = w
     * i >= |w| ->  str.delete(w, i, l) = w
     *
     * 0 <= i < |w| && l > 0 -> str.delete(w, i, l) = u1 u2
     * 0 <= i < |w| && l > 0 -> w = u1 x u2
     * 0 <= i < |w| && l > 0 -> |u1| = i
     * 0 <= i < |w| && l > 0 && i + l >= |w| -> u2 = ε
     * 0 <= i < |w| && l > 0 && i + l <  |w| -> |x| = l
     *
     * @param e The str.delete(w, i, l) term
     */
    void theory_str_noodler::handle_delete(expr *e) {
        if (axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        expr *w = nullptr, *i = nullptr, *l = nullptr;
        VERIFY(m_util_s.str.is_delete(e, w, i, l));

        STRACE(str, tout << "handle delete: " << mk_pp(e, m) << '\n';);

        expr_ref u1 = mk_str_var_fresh("delete_left");
        expr_ref u2 = mk_str_var_fresh("delete_right");
        expr_ref x = mk_str_var_fresh("delete_remove");

        expr_ref result = get_fresh_var_for_string_function("delete", e);

        expr_ref u1_x_u2 = mk_concat(u1, mk_concat(x, u2));
        expr_ref u1_u2 = mk_concat(u1, u2);

        expr_ref zero(m_util_a.mk_int(0), m);
        // i >= 0
        literal i_ge_zero = mk_literal(m_util_a.mk_ge(i, zero));
        // i < |w|
        literal i_lt_len_w = mk_literal(m_util_a.mk_lt(mk_sub(i, m_util_s.str.mk_length(w)), zero));
        // l > 0
        literal l_gt_zero = mk_literal(m_util_a.mk_gt(l, zero));
        // i + l >= |w|
        literal i_plus_l_ge_len_w = mk_literal(m_util_a.mk_ge(mk_sub(m_util_a.mk_add(i, l), m_util_s.str.mk_length(w)), zero));

        // l <= 0   ->  str.delete(w, i, l) = w
        add_axiom({l_gt_zero, mk_eq(result, w, false)});
        // i <  0   ->  str.delete(w, i, l) = w
        add_axiom({i_ge_zero, mk_eq(result, w, false)});
        // i >= |w| ->  str.delete(w, i, l) = w
        add_axiom({i_lt_len_w, mk_eq(result, w, false)});

        // 0 <= i < |w| && l > 0 -> str.delete(w, i, l) = u1 u2
        add_axiom({~i_ge_zero, ~i_lt_len_w, ~l_gt_zero, mk_eq(result, u1_u2, false)});
        // 0 <= i < |w| && l > 0 -> w = u1 x u2
        add_axiom({~i_ge_zero, ~i_lt_len_w, ~l_gt_zero, mk_eq(w, u1_x_u2, false)});
        // 0 <= i < |w| && l > 0 -> |u1| = i
        add_axiom({~i_ge_zero, ~i_lt_len_w, ~l_gt_zero, mk_eq(m_util_s.str.mk_length(u1), i, false)});
        // 0 <= i < |w| && l > 0 && i + l >= |w| -> u2 = ε
        add_axiom({~i_ge_zero, ~i_lt_len_w, ~l_gt_zero, ~i_plus_l_ge_len_w, mk_eq(u2, m_util_s.str.mk_string(""), false)});
        // 0 <= i < |w| && l > 0 && i + l <  |w| -> |x| = l
        add_axiom({~i_ge_zero, ~i_lt_len_w, ~l_gt_zero, i_plus_l_ge_len_w, mk_eq(l, m_util_s.str.mk_length(x), false)});

        mark_expression_as_length(w);
        mark_expression_as_length(u1);
        mark_expression_as_length(x);
    }

    expr_ref theory_str_noodler::mk_concat(expr* e1, expr* e2) {
        return expr_ref(m_util_s.str.mk_concat(e1, e2), m);
    }

    literal theory_str_noodler::mk_eq_empty(expr* _e) {
        context& ctx = get_context();
        expr_ref e(_e, m);
        SASSERT(m_util_s.is_seq(e));
        zstring s;
        if (m_util_s.str.is_empty(e)) {
            return true_literal;
        }
        expr_ref_vector concats(m);
        m_util_s.str.get_concat(e, concats);
        for (auto c : concats) {
            if (m_util_s.str.is_unit(c)) {
                return false_literal;
            }
            if (m_util_s.str.is_string(c, s) && s.length() > 0) {
                return false_literal;
            }
        }

        literal lit = mk_eq(e, m_util_s.str.mk_empty(e->get_sort()), false);
        ctx.mark_as_relevant(lit);
        return lit;
    }


    /**
     * @brief Handling of str.prefix(x, y) = e (x is a prefix of y)
     * Translates to the following theory axioms:
     * e -> y = x.v
     *
     * @param e prefix term
     */
    void theory_str_noodler::handle_prefix(expr *e) {
        if(axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        STRACE(str, tout << "handle prefix: " << mk_pp(e, m) << '\n';);

        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_prefix(e, x, y));

        expr * sub_str = nullptr, *sub_ind = nullptr, *sub_len = nullptr;
        rational val;
        zstring str;
        // handle the special case of the form (str.prefix "a" (str.substr s 5 2)) --> (str.at s 5) == "a"
        // TODO: move to the rewriter
        if(m_util_s.str.is_string(x, str) && str.length() == 1 && m_util_s.str.is_extract(y, sub_str, sub_ind, sub_len) && m_util_a.is_numeral(sub_ind) && m_util_a.is_numeral(sub_len, val) && val.get_int32() >= 1) {
            add_axiom({~mk_eq(x, m_util_s.str.mk_at(sub_str, sub_ind), false), mk_literal(e) });
            add_axiom({mk_eq(x, m_util_s.str.mk_at(sub_str, sub_ind), false), ~mk_literal(e) });
            return;
        }

        expr_ref fresh = mk_str_var_fresh("prefix");
        expr_ref xs(m_util_s.str.mk_concat(x, fresh), m);
        string_theory_propagation(xs);
        literal not_e = mk_literal(e);
        add_axiom({~not_e, mk_eq(y, xs, false)});
    }

    /**
     * @brief Handle not(prefix(x,y)); prefix(x,y) = @p e
     * Translates to the following theory axioms:
     * not(e) && |x| <= |y| -> x = p.mx.qx
     * not(e) && |x| <= |y| -> y = p.my.qy
     * not(e) && |x| <= |y| -> mx in re.allchar
     * not(e) && |x| <= |y| -> my in re.allchar
     * not(e) && |x| <= |y| -> mx != my
     *
     * @param e prefix term
     */
    void theory_str_noodler::handle_not_prefix(expr *e) {
        if(axiomatized_persist_terms.contains(m.mk_not(e))) { return; }
        axiomatized_persist_terms.insert(m.mk_not(e));

        STRACE(str, tout << "handle not(prefx): " << mk_pp(e, m) << '\n';);

        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_prefix(e, x, y));

        expr * sub_str = nullptr, *sub_ind = nullptr, *sub_len = nullptr;
        rational val;
        zstring str;
        // handle the special case of the form (not (str.prefix "a" (str.substr s 5 2))) <-> (str.at s 5) != "a"
        if(m_util_s.str.is_string(x, str) && str.length() == 1 && m_util_s.str.is_extract(y, sub_str, sub_ind, sub_len) && m_util_a.is_numeral(sub_ind) && m_util_a.is_numeral(sub_len, val) && val.get_int32() >= 1) {
            add_axiom({mk_eq(x, m_util_s.str.mk_at(sub_str, sub_ind), false), ~mk_literal(e) });
            add_axiom({~mk_eq(x, m_util_s.str.mk_at(sub_str, sub_ind), false), mk_literal(e) });
            return;
        }

        // handle the case not(prefix "ABC" y)
        if(m_util_s.str.is_string(x, str)) {
            expr_ref re(m_util_s.re.mk_in_re(y, m_util_s.re.mk_concat(
                m_util_s.re.mk_to_re(m_util_s.str.mk_string(str)),
                m_util_s.re.mk_star(m_util_s.re.mk_full_char(nullptr))
            ) ), m);
            literal lit_e = mk_literal(e);
            add_axiom({lit_e, ~mk_literal(re)});
            return;
        }
        // handle the case not(prefix x "ABC")
        if(m_util_s.str.is_string(y, str)) {
            literal lit_e = mk_literal(e);
            for(size_t i = 0; i <= str.length(); i++) {
                zstring substr = str.extract(0, i);
                add_axiom({lit_e, mk_literal(m.mk_not(m.mk_eq(x, m_util_s.str.mk_string(substr))))});
            }
            return;
        }
        // not(prefix x y) -> x != y  where y = at ...
        // not(prefix x y) -> x != eps
        if(m_util_s.str.is_at(y)) {
            literal lit_e = mk_literal(e);
            expr_ref eps(m_util_s.str.mk_string(""), m);
            add_axiom({ lit_e, mk_literal(m.mk_not(m.mk_eq(x,y))) });
            add_axiom({ lit_e, mk_literal(m.mk_not(m.mk_eq(x,eps))) });
            return;
        }

        expr_ref p = mk_str_var_fresh("nprefix_left");
        expr_ref mx = mk_str_var_fresh("nprefix_midx");
        expr_ref my = mk_str_var_fresh("nprefix_midy");
        expr_ref qx = mk_str_var_fresh("nprefix_rightx");
        expr_ref qy = mk_str_var_fresh("nprefix_righty");

        expr_ref pmx(m_util_s.str.mk_concat(p, mx), m);
        string_theory_propagation(pmx);
        expr_ref pmxqx(m_util_s.str.mk_concat(pmx, qx), m);
        string_theory_propagation(pmxqx);
        expr_ref pmy(m_util_s.str.mk_concat(p, my), m);
        string_theory_propagation(pmy);
        expr_ref pmyqy(m_util_s.str.mk_concat(pmy, qy), m);
        string_theory_propagation(pmyqy);

        // |x| <= |y|
        expr_ref len_x_gt_len_y(m);
        zstring s;
        if(m_util_s.str.is_string(x, s)) {
            len_x_gt_len_y = expr_ref{m_util_a.mk_ge(m_util_s.str.mk_length(y), m_util_a.mk_int(s.length())),m};
        } else {
            // we cannot put |x| <= |y| because lra solver gives up, we need to give it |y| - |x| >= 0 (there has to be a numeral on one side)
            len_x_gt_len_y = expr_ref{m_util_a.mk_ge(m_util_a.mk_sub(m_util_s.str.mk_length(y), m_util_s.str.mk_length(x)), m_util_a.mk_int(0)),m};
        }

        literal x_eq_pmq = mk_eq(x,pmxqx,false);
        literal y_eq_pmq = mk_eq(y,pmyqy,false);
        literal eq_mx_my = mk_literal(m.mk_not(ctx.mk_eq_atom(mx,my)));

        expr_ref rex(m_util_s.re.mk_in_re(mx, m_util_s.re.mk_full_char(nullptr)), m);
        expr_ref rey(m_util_s.re.mk_in_re(my, m_util_s.re.mk_full_char(nullptr)), m);

        literal lit_e = mk_literal(e);
        literal len_y_gt_len_x = mk_literal(m.mk_not(len_x_gt_len_y));
        // not(e) && |x| <= |y| -> x = p.mx.qx
        add_axiom({lit_e, len_y_gt_len_x, x_eq_pmq});
        // not(e) && |x| <= |y| -> y = p.my.qy
        add_axiom({lit_e, len_y_gt_len_x, y_eq_pmq});
        // not(e) && |x| <= |y| -> mx in re.allchar
        add_axiom({lit_e, len_y_gt_len_x, mk_literal(rex)});
        // not(e) && |x| <= |y| -> my in re.allchar
        add_axiom({lit_e, len_y_gt_len_x, mk_literal(rey)});
        // not(e) && |x| <= |y| -> mx != my
        add_axiom({lit_e, len_y_gt_len_x, eq_mx_my});

        // update length variables
        mark_expression_as_length(x);
        mark_expression_as_length(y);
        this->var_eqs.add(expr_ref(m_util_a.mk_int(1), m), expr_ref(my, m));
        this->var_eqs.add(expr_ref(m_util_a.mk_int(1), m), expr_ref(mx, m));
    }

    /**
     * @brief Handling of str.suffix(x, y) = e (x is a suffix of y)
     * Translates to the following theory axioms:
     * e -> y = v.x
     *
     * @param e suffix term
     */
    void theory_str_noodler::handle_suffix(expr *e) {
        if(axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        STRACE(str, tout << "handle suffix: " << mk_pp(e, m) << '\n';);

        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_suffix(e, x, y));

        expr_ref fresh = mk_str_var_fresh("suffix");
        expr_ref px(m_util_s.str.mk_concat(fresh, x), m);
        string_theory_propagation(px);
        literal not_e = mk_literal(e);
        add_axiom({~not_e, mk_eq(y, px, false)});
    }

    /**
     * @brief Handle not(suffix(x,y)); suffix(x,y) = @p e
     * Translates to the following theory axioms:
     * not(e) && |x| <= |y| -> x = px.mx.q
     * not(e) && |x| <= |y| -> y = py.my.q
     * not(e) && |x| <= |y| -> mx in re.allchar
     * not(e) && |x| <= |y| -> my in re.allchar
     * not(e) && |x| <= |y| -> mx != my
     *
     * @param e prefix term
     */
    void theory_str_noodler::handle_not_suffix(expr *e) {
        if(axiomatized_persist_terms.contains(m.mk_not(e))) { return; }
        axiomatized_persist_terms.insert(m.mk_not(e));

        STRACE(str, tout << "handle not(suffix): " << mk_pp(e, m) << '\n';);

        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_suffix(e, x, y));

        zstring str;
        // handle the case not(suffix "ABC" y)
        if(m_util_s.str.is_string(x, str)) {
            expr_ref re(m_util_s.re.mk_in_re(y, m_util_s.re.mk_concat(
                m_util_s.re.mk_star(m_util_s.re.mk_full_char(nullptr)),
                m_util_s.re.mk_to_re(m_util_s.str.mk_string(str))
            ) ), m);
            literal lit_e = mk_literal(e);
            add_axiom({lit_e, ~mk_literal(re)});
            return;
        }
        // handle the case not(suffix x "ABC")
        if(m_util_s.str.is_string(y, str)) {
            literal lit_e = mk_literal(e);
            str = str.reverse();
            for(size_t i = 0; i <= str.length(); i++) {
                zstring substr = str.extract(0, i);
                add_axiom({lit_e, mk_literal(m.mk_not(m.mk_eq(x, m_util_s.str.mk_string(substr))))});
            }
            return;
        }

        expr_ref q = mk_str_var_fresh("nsuffix_right");
        expr_ref mx = mk_str_var_fresh("nsuffix_midx");
        expr_ref my = mk_str_var_fresh("nsuffix_midy");
        expr_ref px = mk_str_var_fresh("nsuffix_leftx");
        expr_ref py = mk_str_var_fresh("nsuffix_lefty");

        expr_ref len_x_gt_len_y{m_util_a.mk_gt(m_util_a.mk_sub(m_util_s.str.mk_length(x),m_util_s.str.mk_length(y)), m_util_a.mk_int(0)),m};
        literal len_y_gt_len_x = mk_literal(len_x_gt_len_y);
        expr_ref pxmx(m_util_s.str.mk_concat(px, mx), m);
        string_theory_propagation(pxmx);
        expr_ref pxmxq(m_util_s.str.mk_concat(pxmx, q), m);
        string_theory_propagation(pxmxq);
        expr_ref pymy(m_util_s.str.mk_concat(py, my), m);
        string_theory_propagation(pymy);
        expr_ref pymyq(m_util_s.str.mk_concat(pymy, q), m);
        string_theory_propagation(pymyq);

        literal x_eq_pmq = mk_eq(x,pxmxq,false);
        literal y_eq_pmq = mk_eq(y,pymyq,false);
        literal eq_mx_my = mk_literal(m.mk_not(ctx.mk_eq_atom(mx,my)));
        literal lit_e = mk_literal(e);

        expr_ref rex(m_util_s.re.mk_in_re(mx, m_util_s.re.mk_full_char(nullptr)), m);
        expr_ref rey(m_util_s.re.mk_in_re(my, m_util_s.re.mk_full_char(nullptr)), m);

        // not(e) && |x| <= |y| -> x = px.mx.q
        add_axiom({lit_e, len_y_gt_len_x, x_eq_pmq});
        // not(e) && |x| <= |y| -> y = py.my.q
        add_axiom({lit_e, len_y_gt_len_x, y_eq_pmq});
        // not(e) && |x| <= |y| -> mx in re.allchar
        add_axiom({lit_e, len_y_gt_len_x, mk_literal(rex)});
        // not(e) && |x| <= |y| -> my in re.allchar
        add_axiom({lit_e, len_y_gt_len_x, mk_literal(rey)});
        // not(e) && |x| <= |y| -> mx != my
        add_axiom({lit_e, len_y_gt_len_x, eq_mx_my});

        // update length variables
        mark_expression_as_length(x);
        mark_expression_as_length(y);
        // my and mx are in the same length-equivalence class: 1
        this->var_eqs.add(expr_ref(m_util_a.mk_int(1), m), my);
        this->var_eqs.add(expr_ref(m_util_a.mk_int(1), m), mx);
    }

    /**
     * @brief Handle contains
     * Translates to the following theory axioms:
     * str.contains(x,y) -> x = pys
     *
     * @param e str.contains(x,y)
     */
    void theory_str_noodler::handle_contains(expr *e) {
        if(axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        STRACE(str, tout  << "handle contains: " << mk_pp(e, m) << std::endl;);

        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_contains(e, x, y));

        // if contains is of the form (str.contains (str.substr value2 0 (+ n (str.indexof value2 "A" 0))) "A"), derive simpler constraints
        expr * ind = nullptr;
        zstring str;
        if(expr_cases::is_contains_index(e, ind, m, m_util_s, m_util_a)) {
            expr_ref ind_eq(m.mk_eq( ind, m_util_a.mk_int(-1) ), m);
            expr_ref ind_leq(m_util_a.mk_le( ind, m_util_a.mk_int(-1) ), m);
            literal not_e = mk_literal(mk_not({e, m}));
            add_axiom({~mk_eq(ind, m_util_a.mk_int(-1), false), ~mk_literal(e) });
            add_axiom({mk_eq(ind, m_util_a.mk_int(-1), false), mk_literal(e) });
            return;
        // if constains is of the form (str.constains strX (str.at ...)) rewrite to a regular constaint ((str.at ...) \in union of chars of strX)
        // TODO: move to the rewriter
        } else if (m_util_s.str.is_at(y) && m_util_s.str.is_string(x, str) && str.length() > 0) {
            expr_ref re(m_util_s.re.mk_to_re(m_util_s.str.mk_string("")), m);
            for(size_t i = 0; i < str.length(); i++) {
                re = m_util_s.re.mk_union(re, m_util_s.re.mk_to_re(m_util_s.str.mk_string(str[i])));
            }
            expr_ref in_re(m_util_s.re.mk_in_re(y, re), m);
            literal not_e = mk_literal(mk_not({e, m}));
            add_axiom({not_e, mk_literal(in_re)});
            return;
        }

        expr_ref p = mk_str_var_fresh("contains_left");
        expr_ref s = mk_str_var_fresh("contains_right");
        expr_ref pys(m_util_s.str.mk_concat(m_util_s.str.mk_concat(p, y), s), m);

        string_theory_propagation(pys);
        literal not_e = mk_literal(mk_not({e, m}));
        add_axiom({not_e, mk_eq(x, pys, false)});
    }


    /**
     * @brief Heuristics for handling not contains: not(contains(s, t)).
     * So far only the case when t is a string literal is implemented.
     *
     * @param e contains term.
     */
    void theory_str_noodler::handle_not_contains(expr *e) {
        STRACE(str, tout  << "handle not(contains) " << mk_pp(e, m) << std::endl;);

        expr* cont = this->m.mk_not(e);
        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_contains(e, x, y));

        zstring s;
        if(m_util_s.str.is_string(y, s)) {
            expr_ref re(m_util_s.re.mk_in_re(x, m_util_s.re.mk_concat(m_util_s.re.mk_star(m_util_s.re.mk_full_char(nullptr)),
                m_util_s.re.mk_concat(m_util_s.re.mk_to_re(m_util_s.str.mk_string(s)),
                m_util_s.re.mk_star(m_util_s.re.mk_full_char(nullptr)))) ), m);
          
            add_axiom({mk_literal(e), ~mk_literal(re)});
            add_axiom({mk_literal(cont), mk_literal(re)});
        } else if(m_util_s.str.is_string(x, s) && s.length() <= 10) { // the number 10 is arbitrary, can be tuned (needs to be changed also in assign_not_contains)
            // for small string literals s, we can unroll all possible substrings of s and put that y cannot be any of them
            expr_ref re(m_util_s.re.mk_to_re(m_util_s.str.mk_string("")), m);
            for (unsigned i = 0; i < s.length(); i++) {
                for (unsigned j = i + 1; j <= s.length(); j++) {
                    expr_ref substr(m_util_s.re.mk_to_re(m_util_s.str.mk_string(s.extract(i, j - i))), m);
                    re = m_util_s.re.mk_union(re, substr);
                }
            }
            re = expr_ref(m_util_s.re.mk_in_re(y, re), m);
            add_axiom({mk_literal(e), ~mk_literal(re)});
        }
    }

    /**
     * @brief Handler for assigning boolean value to the not(contains) predicate.
     * 
     * @param e Not contains predicate
     */
    void theory_str_noodler::assign_not_contains(expr *e) {
        STRACE(str, tout  << "assign not(contains) " << mk_pp(e, m) << std::endl;);

        expr* cont = this->m.mk_not(e);
        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_contains(e, x, y));

        zstring s;
        // not(contains) was not axiomatized in handle_not_contains
        if(!m_util_s.str.is_string(y) && !(m_util_s.str.is_string(x, s) && s.length() <= 10)) {
            m_not_contains_todo.push_back({{x, m},{y, m}});
        }
    }

    /**
     * @brief Handle str.<
     * Translates to the following theory axioms.
     * 
     * not(x < y) -> x = y | y < x
     * x < y -> x != y
     * x < y -> not(y < x)
     * x < y & x = eps -> y != eps
     * x < y & x != eps -> x = u.v1.w1
     * x < y & x != eps -> y = u.v2.w2
     * x < y & x != eps -> v1 in re.allchar
     * x < y & x != eps -> v2 in re.allchar
     * x < y & x != eps -> to_code(v1) + k = to_code(v2) & k >= 1
     * @param e str.< predicate
     */
    void theory_str_noodler::handle_lex_lt(expr *e) {
        STRACE(str, tout  << "handle lessthan: " << mk_pp(e, m) << std::endl;);

        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_lt(e, x, y));
        expr_ref eps(m_util_s.str.mk_string(""), m);
        expr_ref x_eps(m.mk_eq(x, eps), m);
        expr_ref y_eps(m.mk_eq(y, eps), m);

        expr_ref lex_pre = mk_str_var_fresh("lex_pre");
        expr_ref lex_in_left = mk_str_var_fresh("lex_in_left");
        expr_ref lex_in_right = mk_str_var_fresh("lex_in_right");
        expr_ref lex_post_left = mk_str_var_fresh("lex_post_left");
        expr_ref lex_post_right = mk_str_var_fresh("lex_post_right");
        expr_ref px(m_util_s.str.mk_concat(m_util_s.str.mk_concat(lex_pre, lex_in_left), lex_post_left), m);
        expr_ref py(m_util_s.str.mk_concat(m_util_s.str.mk_concat(lex_pre, lex_in_right), lex_post_right), m);
        string_theory_propagation(px);
        string_theory_propagation(py);

        expr_ref x_px(m.mk_eq(x, px), m);
        expr_ref y_py(m.mk_eq(y, py), m);
        literal lit_e = mk_literal(e);
        literal lit_x_px = mk_literal(x_px);
        literal lit_y_py = mk_literal(y_py);
        
        expr_ref re_in_left(m_util_s.re.mk_in_re(lex_in_left, m_util_s.re.mk_full_char(nullptr)), m);
        expr_ref re_in_right(m_util_s.re.mk_in_re(lex_in_right, m_util_s.re.mk_full_char(nullptr)), m);
        expr_ref to_code_left(m_util_s.str.mk_to_code(lex_in_left), m);
        expr_ref to_code_right(m_util_s.str.mk_to_code(lex_in_right), m);
  
        // This is a dirty hack. If I add axiom to_code(v1) < to_code(v2), the LIA solver starts 
        // to solve a nonlinear problem (?). If I use to_code(v1) + k = to_code(v2) where k > 0, it works well.
        expr_ref vark = mk_int_var_fresh("lex_add");
        expr_ref to_code_lt(m.mk_eq(m_util_a.mk_add(to_code_left, vark), to_code_right), m);
        // k >= 1
        add_axiom({mk_literal(m_util_a.mk_ge(vark, m_util_a.mk_int(1)))});
        
        literal lit_x_eps = mk_literal(x_eps);
        literal lit_y_eps = mk_literal(y_eps);
        literal lit_e_switch = mk_literal(m_util_s.str.mk_lex_lt(y,x));

        // not(x < y) -> x = y | y < x
        add_axiom({lit_e, mk_eq(x,y,false), lit_e_switch});
        // x < y -> x != y
        add_axiom({~lit_e, ~mk_eq(x,y,false)});
        // x < y -> not(y < x)
        add_axiom({~lit_e, ~lit_e_switch});

        // x < y & x = eps -> y != eps
        add_axiom({~lit_e, ~lit_x_eps, ~lit_y_eps});
        // x < y & x != eps -> x = u.v1.w1
        add_axiom({~lit_e, lit_x_eps, lit_x_px});
        // x < y & x != eps -> y = u.v2.w2
        add_axiom({~lit_e, lit_x_eps, lit_y_py});
        // x < y & x != eps -> v1 in re.allchar
        add_axiom({~lit_e, lit_x_eps, mk_literal(re_in_left)});
        // x < y & x != eps -> v2 in re.allchar
        add_axiom({~lit_e, lit_x_eps, mk_literal(re_in_right)});
        // x < y & x != eps -> to_code(v1) + k = to_code(v2) & k >= 1
        add_axiom({~lit_e, lit_x_eps,  mk_literal(to_code_lt)});
    }

    void theory_str_noodler::handle_in_re(expr *const e, const bool is_true) {
        STRACE(str, tout  << "handle in_re " << mk_pp(e, m) << " " << is_true << std::endl;);

        expr *s = nullptr, *re = nullptr;
        VERIFY(m_util_s.str.is_in_re(e, s, re));

        app_ref re_constr(to_app(s), m);
        expr_ref re_atom(e, m);
        /// Check if @p re_constr is a simple variable. If not (it is, e.g., concatenation of string terms),
        /// this complex term T is replaced by a fresh variable X. The following axioms are hence added: X = T && X in RE.
        if(re_constr->get_num_args() != 0) {
            expr_ref var(m);
            if(this->predicate_replace.contains(re_constr)) {
                var = expr_ref(this->predicate_replace[re_constr], m);
            } else {
                var = mk_str_var_fresh("revar");
                this->predicate_replace.insert(re_constr.get(), var.get());
            }
            
            // app_ref fv(this->m_util_s.mk_skolem(this->m.mk_fresh_var_name(), 0, nullptr, this->m_util_s.mk_string_sort()), m);
            expr_ref eq_fv(mk_eq_atom(var.get(), s), m);
            expr_ref n_re(this->m_util_s.re.mk_in_re(var, re), m);
            expr_ref re_orig(e, m);

            // propagate_basic_string_axioms(ctx.get_enode(eq_fv));
            
            if(!is_true) {
                n_re = m.mk_not(n_re);
                re_orig = m.mk_not(re_orig);
            }
            add_axiom({mk_literal(eq_fv)});
            add_axiom({~mk_literal(re_orig), mk_literal(n_re)});
            
            re_constr = to_app(var); 
            re_atom = n_re;
        }

        expr_ref r{re, m};
        this->m_membership_todo.push_back(std::make_tuple(expr_ref(re_constr, m), r, is_true));
    }

    /**
     * @brief Handle is_digit
     * 
     * Translates into equivalence:
     * is_digit(s) <-> s \in [0-9]
     * 
     * @param e str.is_digit(s)
     * 
     * TODO: This probably makes is_digit always relevant.
     */
    void theory_str_noodler::handle_is_digit(expr *e) {
        if(axiomatized_persist_terms.contains(e)) { return; }
        axiomatized_persist_terms.insert(e);

        STRACE(str, tout << "handle is_digit: " << mk_pp(e, m) << '\n';);

        expr *s = nullptr;
        VERIFY(m_util_s.str.is_is_digit(e, s));
        // s \in [0-9]
        expr_ref s_in_digit(m_util_s.re.mk_in_re(s, m_util_s.re.mk_range(m_util_s.str.mk_string("0"), m_util_s.str.mk_string("9"))), m);
        // is_digit(s) -> s \in [0-9]
        add_axiom({~mk_literal(e), mk_literal(s_in_digit)});
        // ~is_digit(s) -> ~(s \in [0-9])
        add_axiom({mk_literal(e), ~mk_literal(s_in_digit)});
    }

    /**
     * @brief Add special axioms for conversions.
     * In particular, for n = to_int(x) generate n = to_int(x) -> x \in 0*to_string(n)).
     */
    void theory_str_noodler::add_conversion_num_axioms() {
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        for (unsigned i = 0; i < nFormulas; ++i) {
            expr *ex = ctx.get_asserted_formula(i);
            rational val;
            expr* to_int_arg = nullptr;
            if(expr_cases::is_to_int_num_eq(ex, m, m_util_s, m_util_a, to_int_arg, val) && val.is_nonneg()) {
                expr_ref re(m_util_s.re.mk_concat(m_util_s.re.mk_star(m_util_s.re.mk_to_re(m_util_s.str.mk_string("0"))), m_util_s.re.mk_to_re(m_util_s.str.mk_string(val.to_string()))), m);
                expr_ref in_re(m_util_s.re.mk_in_re(to_int_arg, re), m);
                add_axiom({~mk_literal(ex), mk_literal(in_re)});
            }
        }
    }

    /**
     * @brief Add special axioms for length (in)equations. In particular
     * - for (len s) == 10 create (len s) == 10 -> s \in \Sigma^10
     * - for (len s) <= 10 create (len s) <= 10 -> s \in re.loop(0, 10)
     * - for 10 <= (len s) create 10 <= (len s) -> s \in re.loop(10, \inf)
     * (len s) can be potentially any LIA formula where the "variables" are length constraints and there is no minus
     */
    bool theory_str_noodler::add_len_num_axioms(expr* ex) {
        // number bound for the conversion of length constraints into regex constraints.
        // For higher values this conversion could not be beneficial as we would work with 
        // big automata in the decision procedure.
        const int MAX_NUM = 64; 
        const unsigned MAX_VARS = 4;
        rational val;
        bool val_is_larger;
        expr_ref_vector len_arg(m);
        if(expr_cases::is_len_num_eq(ex, m, m_util_s, m_util_a, len_arg, val) && val < MAX_NUM) {
            if (val < 0) {
                // The sum of lengths should be equal negative number, which is not possible.
                // We cannot use the following line (that says this equation cannot hold), as it becomes inconsistent for Z3 (see https://github.com/VeriFIT/z3-noodler/issues/242),
                // instead it will be handled by the axioms saying that lengths need to be nonnegative.
                // add_axiom({~mk_literal(ex)});
                return true;
            } else if (val == 0) {
                // we know that concatenation of vars in len_arg must be empty string,
                // but it doesn't work for some reason, it resulted in some unknowns
                // even though decision procedure finished, so we better give up
                return false;
            } else if (len_arg.size() <= MAX_VARS) {
                expr_ref re(m_util_s.re.mk_full_char(nullptr), m);
                for(rational i{1}; i < val; i++) {
                    re = m_util_s.re.mk_concat(re, m_util_s.re.mk_full_char(nullptr));
                }
                expr_ref in_re(m_util_s.re.mk_in_re(m_util_s.str.mk_concat(len_arg, nullptr), re), m);
                add_axiom({~mk_literal(ex), mk_literal(in_re)});
                return true;
            }
        } else if(expr_cases::is_len_num_leq_or_geq(ex, m, m_util_s, m_util_a, len_arg, val, val_is_larger) && val < MAX_NUM) {
            if (val < 0) {
                if (val_is_larger) {
                    // The sum of lengths should be less than or equal than negative number, which is not possible.
                    // We cannot use the following line (that says this inequation cannot hold), as it becomes inconsistent for Z3 (see https://github.com/VeriFIT/z3-noodler/issues/242),
                    // instead it will be handled by the axioms saying that lengths need to be nonnegative.
                    // add_axiom({~mk_literal(ex)});
                }
                // if val is smaller than len_arg, then this expression just say that the length of len_arg is larger than minus number -> it is useless
                return true;
            } else if (val == 0) {
                if (val_is_larger) {
                    return false;
                }
                // if val is smaller than len_arg, then this expression just say that the length of len_arg is larger or equal than 0 -> it is useless
                return true;
            } else if (len_arg.size() <= MAX_VARS) {
                expr_ref re(
                    val_is_larger ? 
                        m_util_s.re.mk_loop(m_util_s.re.mk_full_char(nullptr), m_util_a.mk_int(0), m_util_a.mk_int(val)) :
                        m_util_s.re.mk_loop(m_util_s.re.mk_full_char(nullptr), m_util_a.mk_int(val)),
                    m
                );
                expr_ref in_re(m_util_s.re.mk_in_re(m_util_s.str.mk_concat(len_arg, nullptr), re), m);
                add_axiom({~mk_literal(ex), mk_literal(in_re)});
                return true;
            }
        }
        return false;
    }


    /**
     * @brief Handle to_code, from_code, to_int, from_int
     * 
     * Collects (and possibly creates) variables for the argument and result
     * of the term and puts them in m_conversion_todo.
     */
    void theory_str_noodler::handle_conversion(expr *conversion) {
        STRACE(str, tout  << "handle conversion " << mk_pp(conversion, m) << std::endl;);
        expr *arg = nullptr;
        rational width_for_rtos;

        ConversionType type;
        if (m_util_s.str.is_to_code(conversion, arg)) {
            type = ConversionType::TO_CODE;
        } else if (m_util_s.str.is_from_code(conversion, arg)) {
            type = ConversionType::FROM_CODE;
        } else if (m_util_s.str.is_stoi(conversion, arg)) {
            type = ConversionType::TO_INT;
        } else if (m_util_s.str.is_itos(conversion, arg)) {
            type = ConversionType::FROM_INT;
        } else if (m_util_s.str.is_stor(conversion, arg)) {
            type = ConversionType::TO_REAL;
        } else if (m_util_s.str.is_rtos(conversion)) {
            type = ConversionType::FROM_REAL;
            expr* width;
            VERIFY(m_util_s.str.is_rtos(conversion, arg, width));
            if (!m_util_a.is_numeral(width, width_for_rtos)) {
                util::throw_error("We cannot handle non-numeral width for str.to_real");
            }
        } else {
            UNREACHABLE();
            return;
        }
        bool tranforming_from = (type == ConversionType::FROM_CODE || type == ConversionType::FROM_INT || type == ConversionType::FROM_REAL);
        std::string name_of_type = get_conversion_name(type);

        // get the var for the argument
        BasicTerm var_for_arg(BasicTermType::Variable);
        if (tranforming_from) {
            // we create new fresh noodler var for the integer/real argument 
            var_for_arg = util::mk_noodler_var_fresh(name_of_type + "_argument");
            if (type == ConversionType::FROM_REAL) {
                // we make the var real for noodler (actually not needed, we add it to var_name anyway, so it will be replaced)
                var_for_arg = BasicTerm(BasicTermType::RealVariable, var_for_arg.get_name());
            }
            // to give equality for var_for_arg with arg, we save into var_name so that len formula we will create in decision procedure will replace the correct var with the correct expression
            // NOTE we cannnot put axiom var_for_arg == arg, this is ignored by Z3
            var_name.insert({var_for_arg, expr_ref(arg, m)});
        } else {
            // the argument has string type, we have to find the variable for it
            expr_ref z3_var_for_arg(m);
            if (m_util_s.str.is_string(arg)) {
                // it seems that Z3 rewriter handles the case where we tranform from string literal, so this should be unreachable
                UNREACHABLE();
                return;
            } else if (util::is_str_variable(arg, m_util_s)) {
                // we are converting directly from variable
                z3_var_for_arg = arg;
            } else if(this->predicate_replace.contains(arg)) {
                // argument is some function that already has a replacing variable
                z3_var_for_arg = this->predicate_replace[arg];
                // FIXME this equation should not really be here, whenever we add something to predicate_replace, we also add this equation.
                // However, conversions can be axiomatized on different level than 0 (other predicates are always on 0, see string_theory_propagation) and
                // the next branch adds something to predicate_replace with the equation, which can be lost after popping from the level in which we axiomatized.
                // This should be probably handled in a different way, see issue https://github.com/VeriFIT/z3-noodler/issues/175
                add_axiom({mk_literal(m.mk_eq(arg, z3_var_for_arg))});
            } else {
                // argument does not have a replacing variable (probably concatenation)
                // we need to create one
                z3_var_for_arg = mk_str_var_fresh(name_of_type + "_argument");
                add_axiom({mk_literal(m.mk_eq(arg, z3_var_for_arg))});
                this->predicate_replace.insert(arg, z3_var_for_arg);
            }
            var_for_arg = util::get_variable_basic_term(z3_var_for_arg);
            // we need exact solution for the argument, so that we can compute
            // the arithmetic formula for the result in final_check_eh
            len_vars.insert(z3_var_for_arg);
        }

        // create var for the result
        BasicTerm var_for_conversion(BasicTermType::Variable);
        if (tranforming_from) {
            expr_ref z3_var_for_conversion = mk_str_var_fresh(name_of_type + "_result");
            add_axiom({mk_literal(m.mk_eq(z3_var_for_conversion, conversion))});
            this->predicate_replace.insert(conversion, z3_var_for_conversion);
            len_vars.insert(z3_var_for_conversion); // we need exact solution for the result, to compute the arithmetic formula
            var_for_conversion = util::get_variable_basic_term(z3_var_for_conversion);

            // The range of from_* functions is bounded, we have to bound it also for the decision procedure
            app *epsilon = m_util_s.re.mk_epsilon(conversion->get_sort());
            app *zero = m_util_s.re.mk_to_re(m_util_s.str.mk_string("0"));
            app *nums_without_zero = m_util_s.re.mk_concat(
                m_util_s.re.mk_range(m_util_s.str.mk_string("1"), m_util_s.str.mk_string("9")),
                m_util_s.re.mk_star(m_util_s.re.mk_range(m_util_s.str.mk_string("0"), m_util_s.str.mk_string("9")))
            );
            app *all_nums = m_util_s.re.mk_union(zero, nums_without_zero);

            if (type == ConversionType::FROM_CODE) {
                // the result of str.from_code can only be either a char representing the code value, or empty string (if argument is out of range of any code value)
                app *sigma_eps = m_util_s.re.mk_union(epsilon, m_util_s.re.mk_full_char(nullptr));
                add_axiom({mk_literal(m_util_s.re.mk_in_re(z3_var_for_conversion, sigma_eps))});
            }

            if (type == ConversionType::FROM_INT) {
                // the result of str.from_int can only be either a decimal representation of a number without leading zeros, or empty string (if argument is negative)
                add_axiom({mk_literal(m_util_s.re.mk_in_re(z3_var_for_conversion, m_util_s.re.mk_union(all_nums, epsilon)))});

                // |from_int(x)| = 0 <-> x <= -1
                add_axiom({ mk_literal(m.mk_eq( m_util_s.str.mk_length(conversion), m_util_a.mk_int(0))), ~mk_literal(m_util_a.mk_le(arg, m_util_a.mk_int(-1))) });
                add_axiom({ ~mk_literal(m.mk_eq( m_util_s.str.mk_length(conversion), m_util_a.mk_int(0))), mk_literal(m_util_a.mk_le(arg, m_util_a.mk_int(-1))) });

                // As the result of from_int belongs to infinite language, it is very likely that we will have to underapproximate in the decision procedure.
                // The underapproximation maximum length of words used from this infinite language is given by m_params.m_underapprox_length, we therefore add
                //      argument < 10^m_underapprox_length => result \in .{0,m_underapprox_length}
                // This will force for the case that "argument < 10^m_underapprox_length", that we will not have to do any underapproximation and hopefully,
                // the case "argument >= 10^m_underapprox_length" will not happen .
                add_axiom({
                    ~mk_literal(m_util_a.mk_le(arg, m_util_a.mk_int(rational(10).expt(m_params.m_underapprox_length)-1))), // I rather use <= instead of <, LIA solver can have problems with that
                    mk_literal(m_util_s.re.mk_in_re(z3_var_for_conversion, m_util_s.re.mk_loop(m_util_s.re.mk_full_char(nullptr), m_util_a.mk_int(0), m_util_a.mk_int(m_params.m_underapprox_length))))
                });
            }

            if (type == ConversionType::FROM_REAL) {
                if (width_for_rtos > 0) {
                    app* digits_restricted_by_width = m_util_s.re.mk_loop(m_util_s.re.mk_range(m_util_s.str.mk_string("0"), m_util_s.str.mk_string("9")), m_util_a.mk_int(width_for_rtos), m_util_a.mk_int(width_for_rtos));
                    app* all_nums_with_decimal_part_restricted_by_width = m_util_s.re.mk_concat(all_nums, m_util_s.re.mk_concat(m_util_s.re.mk_to_re(m_util_s.str.mk_string(".")), digits_restricted_by_width));
                    // the result of str.from_real can only be either a decimal representation of a number without leading zeros (in the whole part) and width number of decimal digits, or empty string (if argument is negative)
                    add_axiom({mk_literal(m_util_s.re.mk_in_re(z3_var_for_conversion, m_util_s.re.mk_union(all_nums_with_decimal_part_restricted_by_width, epsilon)))});
                } else {
                    // the decimal part must be empty, so the result of str.from_real must be a whole number (or empty string)
                    add_axiom({mk_literal(m_util_s.re.mk_in_re(z3_var_for_conversion, m_util_s.re.mk_union(all_nums, epsilon)))});
                }

                // |from_real(x)| = 0 <-> x < 0
                add_axiom({ mk_literal(m.mk_eq( m_util_s.str.mk_length(conversion), m_util_a.mk_int(0))), mk_literal(m_util_a.mk_le(m_util_a.mk_real(0), arg)) });
                add_axiom({ ~mk_literal(m.mk_eq( m_util_s.str.mk_length(conversion), m_util_a.mk_int(0))), ~mk_literal(m_util_a.mk_le(m_util_a.mk_real(0), arg)) });

                // As the result of from_real belongs to infinite language, it is very likely that we will have to underapproximate in the decision procedure.
                // The underapproximation maximum length of words used from this infinite language is given by m_params.m_underapprox_length, we therefore add
                //      argument < 10^m_underapprox_length => result \in .{0,m_underapprox_length+1+width}
                // where we also add space for decimal dot (the +1) and decimal part (whose length is fixed by width)
                // This will force for the case that "argument < 10^m_underapprox_length", that we will not have to do any underapproximation and hopefully,
                // the case "argument >= 10^m_underapprox_length" will not happen .
                add_axiom({
                    ~mk_literal(m_util_a.mk_le(arg, m_util_a.mk_real(rational(10).expt(m_params.m_underapprox_length)-1))), // I rather use <= instead of <, LIA solver can have problems with that
                    mk_literal(m_util_s.re.mk_in_re(z3_var_for_conversion, m_util_s.re.mk_loop(m_util_s.re.mk_full_char(nullptr), m_util_a.mk_int(0), m_util_a.mk_int(rational(m_params.m_underapprox_length+1)+width_for_rtos))))
                });
            }
        } else {
            // we create new fresh noodler var for the integer/real result which we save into var_name so that
            // len formula we will create in decision procedure will replace the correct var with the correct expression
            var_for_conversion = util::mk_noodler_var_fresh(name_of_type + "_result");
            if (type == ConversionType::TO_REAL) { var_for_conversion = BasicTerm(BasicTermType::RealVariable, var_for_conversion.get_name()); } // probably not needed, we put it in var_name anyway, so its type does not matter
            var_name.insert({var_for_conversion, expr_ref(conversion, m)});

            // To help LIA solver, we give some bounds on the results of to_* functions
            if (type == ConversionType::TO_CODE) {
                // the result of str.to_code must be between -1 and zstring::max_char
                add_axiom({mk_literal(m_util_a.mk_le(m_util_a.mk_int(-1), conversion))});
                add_axiom({mk_literal(m_util_a.mk_le(conversion, m_util_a.mk_int(zstring::max_char())))});
            }

            if (type == ConversionType::TO_INT) {
                // the result of str.to_int cannot be any negative number other than -1
                add_axiom({mk_literal(m_util_a.mk_le(m_util_a.mk_int(-1), conversion))});

                expr *e1 = nullptr, *e2 = nullptr, *e3 = nullptr;
                rational r1;
                if (m_util_s.str.is_at(arg)) {
                    // argument is str.at(...) => result must be less than 10
                    add_axiom({mk_literal(m_util_a.mk_le(conversion, m_util_a.mk_int(9)))});
                } else if (m_util_s.str.is_extract(arg, e1, e2, e3) && m_util_a.is_numeral(e3, r1)) {
                    // argument is str.substr(?, ?, numeral) => result must be less than 10^numeral
                    rational ten_to_r1(1);
                    for (rational i(0); i < r1; ++i) {
                        ten_to_r1 = ten_to_r1 * 10;
                    }
                    add_axiom({mk_literal(m_util_a.mk_le(conversion, m_util_a.mk_int(ten_to_r1-1)))});
                }
            }

            if (type == ConversionType::TO_REAL) {
                // the result of str.to_real cannot be any negative number other than -1
                add_axiom({mk_literal(m_util_a.mk_le(m_util_a.mk_real(0), conversion)), mk_literal(m.mk_eq(m_util_a.mk_real(-1), conversion))});

                expr *e1 = nullptr, *e2 = nullptr, *e3 = nullptr;
                rational r1;
                if (m_util_s.str.is_at(arg)) {
                    // argument is str.at(...) => result must be less than 10
                    add_axiom({mk_literal(m_util_a.mk_le(conversion, m_util_a.mk_real(9)))});
                } else if (m_util_s.str.is_extract(arg, e1, e2, e3) && m_util_a.is_numeral(e3, r1)) {
                    // argument is str.substr(?, ?, numeral) => result must be less than 10^numeral
                    rational ten_to_r1(1);
                    for (rational i(0); i < r1; ++i) {
                        ten_to_r1 = ten_to_r1 * 10;
                    }
                    add_axiom({mk_literal(m_util_a.mk_le(conversion, m_util_a.mk_real(ten_to_r1-1)))});
                }
            }
        }

        // Add to todo
        if (tranforming_from) {
            if (type == ConversionType::FROM_REAL) {
                m_conversion_todo.push_back({type, var_for_conversion, var_for_arg, width_for_rtos});
            } else {
                m_conversion_todo.push_back({type, var_for_conversion, var_for_arg});
            }
        } else {
            m_conversion_todo.push_back({type, var_for_arg, var_for_conversion});
        }
    }

    void theory_str_noodler::set_conflict(const literal_vector& lv) {
        context& ctx = get_context();
        const auto& js = ext_theory_conflict_justification{
                get_id(), ctx, lv.size(), lv.data(), 0, nullptr, 0, nullptr};
        ctx.set_conflict(ctx.mk_justification(js));
        STRACE(str, ctx.display_literals_verbose(tout << "[Conflict]\n", lv) << '\n';);
    }

    void theory_str_noodler::mark_expression_as_length(expr *e) {
        if(m_util_s.str.is_string(e)) {
            return;
        }

        if(util::is_str_variable(e, m_util_s)) {
            len_vars.insert(e);
            return;
        }
        // quantified variables are handled in a different way (e.g., for quantifier 
        // instantiation the variable is replaced by a concrete term in final_check)
        if(is_var(e)) {
            return;
        }

        SASSERT(is_app(e));
        app* ex_app{ to_app(e) };
        if (m_util_s.str.is_concat(e)) {
            for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
                mark_expression_as_length(ex_app->get_arg(i));
            }
        } else {
            expr* rpl;
            if (predicate_replace.find(ex_app, rpl)) {
                mark_expression_as_length(rpl);
            } else {
                initial_len_expressions.insert(e);
            }
        }
    }
    
    void theory_str_noodler::print_len_vars(std::ostream& os) {
        os << "Current length vars:";
        for (expr* e : len_vars) {
            os << " " << mk_pp(e,m);
        }
        os << std::endl;
    }
}
