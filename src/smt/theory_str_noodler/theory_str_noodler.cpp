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
            if (!add_len_num_axioms(ex)) {
                obj_hashtable<app> lens;
                util::get_len_exprs(ctx.get_asserted_formula(i), m_util_s, m, lens);
                for (app* const a : lens) {
                    util::get_str_variables(a, this->m_util_s, m, this->len_vars, &this->predicate_replace);
                }
            }
            ctx.mark_as_relevant(ex);
            string_theory_propagation(ex, true, false);  
        }
        add_conversion_num_axioms();
        STRACE(str, tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_str_noodler::string_theory_propagation(expr *expr, bool init, bool neg, bool var_lengths) {
        STRACE(str, tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        STRACE(str_propagation, tout << mk_pp(expr, get_manager()) << std::endl;);

        context &ctx = get_context();

        if (!ctx.e_internalized(expr)) {
            // expr might be in a logical context (e.g., and, or, not)
            ctx.internalize(expr, true);
        }
        //We do not mark the expression as relevant since we do not want bias a
        //fresh SAT solution by the newly added theory axioms.
        // enode *n = ctx.get_enode(expr);
        // ctx.mark_as_relevant(n);

        if(m.is_not(expr)) {
            neg = !neg;
        }

        // TODO weird, we have to do it because inequations are handled differently as equations, and they might not have been set as relevant
        if(init && m.is_eq(expr) && neg) {
            ctx.mark_as_relevant(m.mk_not(expr));
        }
        // we need to propagate all string predicates (including their negated forms) before the actual solve (in init_search), because we need to ensure these axioms are 
        // generated only once on the decision level 0 (if they are generated on a higher level, they can cause looping for some reason)
        if(init && (
                m_util_s.str.is_prefix(expr) ||
                m_util_s.str.is_suffix(expr) ||
                m_util_s.str.is_contains(expr) ||
                m_util_s.str.is_is_digit(expr)
                // we cannot do it for conversions (and for string inequalities which lead to to_code conversions) because otherwise all conversions become relevant and there is a degradation on benchmarks
                // (this degradation should not happen for other predicates, because they are transformed into simpler atoms such as equation, regular membership... whose relevancy we can check when it is needed)
            )) {
            if(neg) ctx.mark_as_relevant(m.mk_not(expr));
            else ctx.mark_as_relevant(expr);
        }

        // Check if we already axiomatized the expr
        if (propagated_string_theory.contains(expr)) {
            return;
        }     
        propagated_string_theory.insert(expr);

        sort *expr_sort = expr->get_sort();
        sort *str_sort = m_util_s.str.mk_string_sort();

        if (expr_sort == str_sort) {
            enode *n = ctx.get_enode(expr);
            propagate_basic_string_axioms(n, var_lengths);
            if (is_app(expr) && m_util_s.str.is_concat(to_app(expr))) {
                propagate_concat_axiom(n);
            }
        }
        // if expr is an application, recursively inspect all arguments
        if (is_app(expr) && !m_util_s.str.is_length(expr)) {
            app *term = to_app(expr);
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
            STRACE(str_axiom, tout << "[ConstStr Axiom] " << mk_pp(a_str, m) << std::endl);

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
                STRACE(str_axiom, tout << "[Non-Zero Axiom] " << mk_pp(a_str, m) << std::endl);
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
                STRACE(str_axiom, tout << "string axiom 1: " << mk_ismt2_pp(lhs_ge_rhs, m) << std::endl;);

                add_axiom({mk_literal(lhs_ge_rhs)});
                this->axiomatized_len_axioms.push_back(lhs_ge_rhs);
            }
            // axiom |t| <= 0 -> t = eps; if var_lengths is set add also t = eps -> |t| = 0
            {
                STRACE(str_axiom, tout << "[Zero iff Empty Axiom] " << mk_pp(a_str, m) << std::endl);

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

            // FIXME what is this? is it important? can we delete this?
            expr *arg;
            if (m_util_s.str.is_length(n, arg) && !has_length(arg) && get_context().e_internalized(arg)) {
                enforce_length(arg);
            }
        } else if(m_util_s.str.is_lt(n)) { // str.<
            handle_lex_lt(n);
        } else if(m_util_s.str.is_le(n)) { // str.<=
            handle_lex_leq(n);
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
        } else if (m_util_s.str.is_is_digit(n)) { // str.is_digit
            handle_is_digit(n);
        } else if (
            m_util_s.str.is_stoi(n) || // str.to_int
            m_util_s.str.is_itos(n) || // str.from_int
            m_util_s.str.is_to_code(n) || // str.to_code
            m_util_s.str.is_from_code(n) // str.from_code
        ) {
            handle_conversion(n);
        } else if (
            m_util_s.str.is_concat(n) || // str.++
            m_util_s.re.is_to_re(n) || // str.to_re
            m_util_s.str.is_in_re(n) || // str.in_re
            m_util_s.is_re(n) || // one of re. command (re.none, re.all, re.comp, ...)
            util::is_str_variable(n, m_util_s) || // string variable
            // RegLan variables should never occur here, they are always eliminated by rewriter I think
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
        m_scope_level += 1;
        m_word_eq_todo.push_scope();
        m_lang_eq_todo.push_scope();
        m_lang_diseq_todo.push_scope();
        m_word_diseq_todo.push_scope();
        m_membership_todo.push_scope();
        m_not_contains_todo.push_scope();
        m_conversion_todo.push_scope();
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
        m_rewrite.reset();
        // for incremental solving, we assume (TODO: should be done differently?) that if we added another assert, then pop must have been called and the satisfiability of the last run does not matter
        if (m_scope_level < scope_with_last_run_was_sat) {
            last_run_was_sat = false;
            scope_with_last_run_was_sat = -1;
        }
        STRACE(str,
            tout << "pop_scope: " << num_scopes << " (back to level " << m_scope_level << ")\n";);
    }
    
    void theory_str_noodler::restart_eh() {
        STRACE(str, tout << "restart\n");
    }

    void theory_str_noodler::reset_eh() {
        // FIXME should here be something?
        STRACE(str, tout << "reset" << '\n';);
    }

    lbool theory_str_noodler::validate_unsat_core(expr_ref_vector &unsat_core) {
        return l_undef;
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
        STRACE(str_axiom, tout << __LINE__ << " " << __FUNCTION__ << mk_pp(e, get_manager()) << std::endl;);

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
            STRACE(str, ctx.display_literal_verbose(tout << "[Assert_e]\n", l) << '\n';);
        }
    }

    void theory_str_noodler::add_axiom(std::vector<literal> ls) {
        STRACE(str, tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        context &ctx = get_context();
        literal_vector lv;
        for (const auto &l : ls) {
            if (l != null_literal && l != false_literal) {
                ctx.mark_as_relevant(l);
                lv.push_back(l);
            }
        }
        ctx.mk_th_axiom(get_id(), lv, lv.size());
        STRACE(str_axiom, ctx.display_literals_verbose(tout << "[Assert_c]\n", lv) << '\n';);
        STRACE(str, tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
    }

    /**
     * @brief Handle str.at(s,i)
     *
     * Translates to the following theory axioms:
     * 0 <= i < |s| -> s = xvy
     * 0 <= i < |s| -> v in re.allchar
     * 0 <= i < |s| -> |x| = i
     * i < 0 -> v = eps
     * i >= |s| -> v = eps
     *
     * We store
     * str.at(s,i) = v
     *
     * @param e str.at(s, i)
     */
    void theory_str_noodler::handle_char_at(expr *e) {
        STRACE(str, tout << "handle-charat: " << mk_pp(e, m) << '\n';);
        if (axiomatized_persist_terms.contains(e))
            return;

        axiomatized_persist_terms.insert(e);
        ast_manager &m = get_manager();
        expr *s = nullptr, *i = nullptr, *res = nullptr;
        VERIFY(m_util_s.str.is_at(e, s, i));

        expr_ref fresh = mk_str_var_fresh("at");
        expr_ref re(m_util_s.re.mk_in_re(fresh, m_util_s.re.mk_full_char(nullptr)), m);
        expr_ref zero(m_util_a.mk_int(0), m);
        literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
        literal i_ge_len_s = mk_literal(m_util_a.mk_ge(mk_sub(i, m_util_s.str.mk_length(s)), zero));
        expr_ref emp(m_util_s.str.mk_empty(e->get_sort()), m);

        rational r;
        
        zstring str;
        // handle the case str.at "A" i
        if(m_util_s.str.is_string(s, str) && str.length() == 1) {
            add_axiom({~mk_literal(m.mk_eq(i, m_util_a.mk_int(0))), mk_eq(fresh, s, false)});
            add_axiom({mk_literal(m.mk_eq(i, m_util_a.mk_int(0))), mk_eq(fresh, emp, false)});
            add_axiom({mk_eq(fresh, e, false)});
            predicate_replace.insert(e, fresh.get());
            return;
        }
        if(m_util_a.is_numeral(i, r)) {
            int val = r.get_int32();

            expr_ref y = mk_str_var_fresh("at_right");

            for(int j = val; j >= 0; j--) {
                y = m_util_s.str.mk_concat(m_util_s.str.mk_at(s, m_util_a.mk_int(j)), y);
            }
            string_theory_propagation(y);

            add_axiom({i_ge_len_s, mk_eq(s, y, false)});
            add_axiom({i_ge_len_s, mk_literal(re)});
            add_axiom({i_ge_len_s, mk_eq(m_util_a.mk_int(1), m_util_s.str.mk_length(fresh), false) });
            add_axiom({mk_eq(fresh, e, false)});
            add_axiom({i_ge_0, mk_eq(fresh, emp, false)});
            add_axiom({~i_ge_len_s, mk_eq(fresh, emp, false)});

            predicate_replace.insert(e, fresh.get());
            return;
        }
        if(util::is_len_sub(i, s, m, m_util_s, m_util_a, res) && m_util_a.is_numeral(res, r)) {
            int val = r.get_int32();

            expr_ref y = mk_str_var_fresh("at_left");

            for(int j = val; j < 0; j++) {
                y = m_util_s.str.mk_concat(y, m_util_s.str.mk_at(s, m_util_a.mk_add(m_util_a.mk_int(j), m_util_s.str.mk_length(s))));
            }
            string_theory_propagation(y);

            add_axiom({~i_ge_0, mk_eq(s, y, false)});
            add_axiom({~i_ge_0, mk_eq(m_util_a.mk_int(1), m_util_s.str.mk_length(fresh), false) });
            add_axiom({mk_eq(fresh, e, false)});
            add_axiom({~i_ge_0, mk_literal(re)});
            add_axiom({i_ge_0, mk_eq(fresh, emp, false)});

            predicate_replace.insert(e, fresh.get());
            return;
        }

        expr_ref one(m_util_a.mk_int(1), m);
        expr_ref x = mk_str_var_fresh("at_left");
        expr_ref y = mk_str_var_fresh("at_right");
        expr_ref xey(m_util_s.str.mk_concat(x, m_util_s.str.mk_concat(fresh, y)), m);
        string_theory_propagation(xey);

        expr_ref len_x(m_util_s.str.mk_length(x), m);
 
        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(s, xey, false)});
        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(one, m_util_s.str.mk_length(fresh), false)});
        add_axiom({~i_ge_0, i_ge_len_s, mk_literal(re)});
        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(i, len_x, false)});
        add_axiom({i_ge_0, mk_eq(fresh, emp, false)});
        add_axiom({~i_ge_len_s, mk_eq(fresh, emp, false)});
        add_axiom({mk_eq(fresh, e, false)});

        // add the replacement charat -> v
        predicate_replace.insert(e, fresh.get());
        // update length variables
        util::get_str_variables(s, this->m_util_s, m, this->len_vars, &this->predicate_replace);
        this->len_vars.insert(x);
    }

    void theory_str_noodler::handle_substr_int(expr *e) {
        expr *s = nullptr, *i = nullptr, *l = nullptr;
        VERIFY(m_util_s.str.is_extract(e, s, i, l));

        rational r;
        if(!m_util_a.is_numeral(i, r)) {
            return;
        }

        expr_ref ls(m_util_s.str.mk_length(s), m);
        expr_ref ls_minus_i_l(mk_sub(mk_sub(ls, i), l), m);
        expr_ref zero(m_util_a.mk_int(0), m);
        expr_ref eps(m_util_s.str.mk_string(""), m);

        literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
        literal ls_le_i = mk_literal(m_util_a.mk_le(mk_sub(i, ls), zero));
        literal li_ge_ls = mk_literal(m_util_a.mk_ge(ls_minus_i_l, zero));
        literal l_ge_zero = mk_literal(m_util_a.mk_ge(l, zero));
        literal ls_le_0 = mk_literal(m_util_a.mk_le(ls, zero));
        
        expr* num_val, *ind_val;
        rational num_val_rat;
        if(r.is_zero() && expr_cases::is_indexof_add(l, s, m, m_util_s, m_util_a, num_val, ind_val) && m_util_a.is_numeral(num_val, num_val_rat) && num_val_rat.is_one()) {
            literal l_gt_zero = mk_literal(m_util_a.mk_le(l, zero));
            expr_ref v = mk_str_var_fresh("substr");
            expr_ref sub(m_util_a.mk_add(l, m_util_a.mk_int(-1)), m);
            m_rewrite(sub);
            expr_ref substr(m_util_s.str.mk_substr(s, i, sub), m);
            expr_ref conc = mk_concat(substr, ind_val);
            string_theory_propagation(conc);

            add_axiom({l_gt_zero, mk_eq(e, conc, false)});
            add_axiom({mk_eq(v, e, false)});

            // add the replacement substr -> v
            this->predicate_replace.insert(e, v.get());
            util::get_str_variables(s, this->m_util_s, m, this->len_vars);
            return;
        }

        expr_ref x(m_util_s.str.mk_string(""), m);
        expr_ref v = mk_str_var_fresh("substr");

        int val = r.get_int32();
        for(int v = 0; v < val; v++) {
            expr_ref var = mk_str_var_fresh("pre_substr");
            expr_ref re(m_util_s.re.mk_in_re(var, m_util_s.re.mk_full_char(nullptr)), m);
            x = m_util_s.str.mk_concat(x, var);
            add_axiom({~i_ge_0, ~ls_le_i, mk_literal(re)});
            // strenghtening the axiom to equivalence
            // for multiple substrs, the SAT solver keeps guessing re and ~re until all possibilities are covered. 
            // Now the choice of re is bound together with the substr axiom
            add_axiom({~mk_literal(re), i_ge_0});
            add_axiom({~mk_literal(re), ls_le_i});
            add_axiom({~i_ge_0, ~ls_le_i, mk_eq(m_util_s.str.mk_length(var), m_util_a.mk_int(1), false)});
        }

        expr_ref le(m_util_s.str.mk_length(v), m);
        expr_ref y = mk_str_var_fresh("post_substr");

        rational rl;
        expr * num_len;
        expr_ref xe(m_util_s.str.mk_concat(x, v), m);
        expr_ref xey(m_util_s.str.mk_concat(x, v, y), m);

        if(m_util_a.is_numeral(l, rl)) {
            int lval = rl.get_int32();
            expr_ref substr_re(m);
            for(int i = 0; i < lval; i++) {
                if(substr_re == nullptr) {
                    substr_re = m_util_s.re.mk_full_char(nullptr);
                } else {
                    substr_re = m_util_s.re.mk_concat(substr_re, m_util_s.re.mk_full_char(nullptr));
                }  
            }
            expr_ref substr_in(m_util_s.re.mk_in_re(v, substr_re), m);

            string_theory_propagation(xey);
            // 0 <= i <= |s| && 0 <= l <= |s| - i -> |v| = l
            add_axiom({~i_ge_0, ~ls_le_i, ~l_ge_zero, ~li_ge_ls, mk_eq(le, l, false)});
            // 0 <= i <= |s| && 0 <= l <= |s| - i -> |v| in substr_re
            add_axiom({~i_ge_0, ~ls_le_i, ~l_ge_zero, ~li_ge_ls, mk_literal(substr_in)});
            // 0 <= i <= |s| && |s| < l + i  -> s = x.v
            add_axiom({~i_ge_0, ~ls_le_i, li_ge_ls, mk_eq(y, eps, false)});
            // 0 <= i <= |s| && l < 0 -> v = eps
            add_axiom({~i_ge_0, ~ls_le_i, l_ge_zero, mk_eq(v, eps, false)});
            // 0 <= i <= |s| -> xey = s (e = v in fact)
            add_axiom({~i_ge_0, ~ls_le_i, mk_eq(xey, s, false)});
            // i < 0 -> v = eps
            add_axiom({i_ge_0, mk_eq(v, eps, false)});
            // |s| < 0 -> v = eps
            add_axiom({~ls_le_0, mk_eq(v, eps, false)});
            // i > |s| -> v = eps
            add_axiom({ls_le_i, mk_eq(v, eps, false)});
                // substr(s, i, n) = v
            add_axiom({mk_eq(v, e, false)});
             // add the replacement substr -> v
            this->predicate_replace.insert(e, v.get());
            // update length variables
            util::get_str_variables(s, this->m_util_s, m, this->len_vars);
            // add length |v| = l. This is not true entirely, because there could be a case that v = eps. 
            // but this case is handled by epsilon propagation preprocessing (this variable will not in the system
            // after that)
            this->var_eqs.add(expr_ref(l, m), v);
            return;

        } else if(util::is_len_sub(l, s, m, m_util_s, m_util_a, num_len) && m_util_a.is_numeral(num_len, rl) && rl == r) {
            xe = expr_ref(m_util_s.str.mk_concat(x, v), m);
            xey = expr_ref(m_util_s.str.mk_concat(x, v), m);
        } else if(m_util_a.is_zero(i) && util::is_len_sub(l, s, m, m_util_s, m_util_a, num_len) && m_util_a.is_numeral(num_len, rl)  && rl.is_minus_one()) {
            expr_ref substr_re(m_util_s.re.mk_full_char(nullptr), m);
            expr_ref substr_in(m_util_s.re.mk_in_re(y, substr_re), m);
            expr_ref ly(m_util_s.str.mk_length(y), m);

            literal l_ge_zero = mk_literal(m_util_a.mk_ge(l, zero));
            string_theory_propagation(xey);
            add_axiom({~l_ge_zero, mk_literal(substr_in)});
            add_axiom({~l_ge_zero, mk_eq(ly, m_util_a.mk_int(1), false)});
            add_axiom({~l_ge_zero, mk_eq(xey, s, false)});
            add_axiom({~l_ge_zero, mk_eq(le, l, false)});
            add_axiom({l_ge_zero, mk_eq(v, eps, false)});
            add_axiom({mk_eq(v, e, false)});
            this->predicate_replace.insert(e, v.get());
            // update length variables
            util::get_str_variables(s, this->m_util_s, m, this->len_vars);
            this->var_eqs.add(expr_ref(l, m), v);
            return;
        } else {
            expr_ref post_bound(m_util_a.mk_ge(m_util_a.mk_add(i, l), m_util_s.str.mk_length(s)), m);
            m_rewrite(post_bound); // simplify
            // if i + l >= |s|, we can set post_substr to eps
            if(m.is_true(post_bound)) {
                y = expr_ref(m_util_s.str.mk_string(""), m);
            }
            // 0 <= i <= |s| && 0 <= l <= |s| - i -> |v| = l
             add_axiom({~i_ge_0, ~ls_le_i, ~l_ge_zero, ~li_ge_ls, mk_eq(le, l, false)});
             // 0 <= i <= |s| && |s| < l + i  -> |v| = |s| - i
             add_axiom({~i_ge_0, ~ls_le_i, li_ge_ls, mk_eq(le, mk_sub(ls, i), false)});
             this->len_vars.insert(v);
        }

        string_theory_propagation(xe);
        string_theory_propagation(xey);
        // 0 <= i <= |s| -> xvy = s
        add_axiom({~i_ge_0, ~ls_le_i, mk_eq(xey, s, false)});
        // 0 <= i <= |s| && 0 <= l <= |s| - i -> |v| = l
        add_axiom({~i_ge_0, ~ls_le_i, ~l_ge_zero, ~li_ge_ls, mk_eq(le, l, false)});
        // 0 <= i <= |s| && l < 0 -> v = eps
        add_axiom({~i_ge_0, ~ls_le_i, l_ge_zero, mk_eq(v, eps, false)});
        // i < 0 -> v = eps
        add_axiom({i_ge_0, mk_eq(v, eps, false)});
        // not(0 <= l <= |s| - i) -> v = eps
        add_axiom({ls_le_i, mk_eq(v, eps, false)});
        // i > |s| -> v = eps
        add_axiom({~ls_le_0, mk_eq(v, eps, false)});
        // substr(s, i, n) = v
        add_axiom({mk_eq(v, e, false)});

        // add the replacement substr -> v
        this->predicate_replace.insert(e, v.get());
        // update length variables
        util::get_str_variables(s, this->m_util_s, m, this->len_vars);
        // add length |v| = l. This is not true entirely, because there could be a case that v = eps. 
        // but this case is handled by epsilon propagation preprocessing (this variable will not in the system
        // after that)
        this->var_eqs.add(expr_ref(l, m), v);
    }

    /**
     * @brief Handle str.substr(s,i,l)
     *
     * Translates to the following theory axioms:
     * 0 <= i <= |s| -> x.v.y = s
     * 0 <= i <= |s| -> |x| = i
     * 0 <= i <= |s| && 0 <= l <= |s| - i -> |v| = l
     * 0 <= i <= |s| && |s| < l + i  -> |v| = |s| - i
     * 0 <= i <= |s| && l < 0 -> v = eps
     * i < 0 -> v = eps
     * not(0 <= l <= |s| - i) -> v = eps
     * i > |s| -> v = eps
     *
     * We store
     * substr(s, i, n) = v
     *
     * @param e str.substr(s, i, l)
     */
    void theory_str_noodler::handle_substr(expr *e) {
        STRACE(str, tout << "handle-substr: " << mk_pp(e, m) << '\n';);
        if (axiomatized_persist_terms.contains(e))
            return;

        axiomatized_persist_terms.insert(e);

        ast_manager &m = get_manager();
        expr *s = nullptr, *i = nullptr, *l = nullptr;
        VERIFY(m_util_s.str.is_extract(e, s, i, l));

        expr_ref v = mk_str_var_fresh("substr");

        // Check if the substring is of the form str.substr x k 1 and rewrite to str.at x k
        rational num_l;
        if(m_util_a.is_numeral(l, num_l) && num_l == 1) {
            expr_ref at(m_util_s.str.mk_at(s, i), m);
            add_axiom({mk_eq(v, e, false)});
            add_axiom({mk_eq(v, at, false)});
            // set an additional constraint that v in eps union sigma
            expr_ref re(m_util_s.re.mk_in_re(v, m_util_s.re.mk_union( m_util_s.re.mk_to_re(m_util_s.str.mk_string("")),  m_util_s.re.mk_full_char(nullptr))) , m);
            add_axiom({mk_literal(re)});
            this->predicate_replace.insert(e, v.get());
            return;
        }

        // check the form str.substr "B" i l
        zstring str_s;
        if(m_util_s.str.is_string(s, str_s) && str_s.length() == 1) {
            expr_ref zero(m_util_a.mk_int(0), m);
            expr_ref one(m_util_a.mk_int(1), m);
            expr_ref eps(m_util_s.str.mk_string(""), m);

            literal i_eq_0 = mk_literal(m_util_a.mk_eq(i, zero));
            literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
            literal l_eq_0 = mk_literal(m_util_a.mk_eq(l, zero));
            literal i_ge_1 = mk_literal(m_util_a.mk_ge(i, one));
            literal l_ge_1 = mk_literal(m_util_a.mk_ge(l, one));
            literal l_ge_0 = mk_literal(m_util_a.mk_ge(l, zero));

            // i < 0 -> v = eps
            add_axiom({i_ge_0, mk_eq(v, eps, false)});
            // l < 0 -> v = eps
            add_axiom({l_ge_0, mk_eq(v, eps, false)});
            // l >= 0 && i = 0 && i >= 1 -> v = eps
            add_axiom({~l_ge_0, ~i_eq_0, ~l_ge_1, mk_eq(v, s, false)});
            // l >= 0 && i >= 1 -> v = eps
            add_axiom({~l_ge_0, ~i_ge_1, mk_eq(v, eps, false)});
            // l >= 0 && i = 0 && l < 1 -> v = eps
            add_axiom({~l_ge_0, ~i_eq_0, l_ge_1, mk_eq(v, eps, false)});
            // substr(s, i, l) = v
            add_axiom({mk_eq(v, e, false)});
            this->predicate_replace.insert(e, v.get());
            return;
        }
        // check the form str.substr "" x y --> str.substr "" x y == ""
        if(m_util_s.str.is_string(s, str_s) && str_s.length() == 0) {
            expr_ref eps(m_util_s.str.mk_string(""), m);
            add_axiom({mk_eq(v, eps, false)});
            add_axiom({mk_eq(v, e, false)});
            this->predicate_replace.insert(e, v.get());
            return;
        }

        expr* num = nullptr;
        expr* pred = nullptr;
        rational r;
        if(m_util_a.is_numeral(i)) {
            handle_substr_int(e);
            return;
        }

        expr_ref post_bound(m_util_a.mk_ge(m_util_a.mk_add(i, l), m_util_s.str.mk_length(s)), m);
        m_rewrite(post_bound); // simplify

        expr_ref xvar = mk_str_var_fresh("pre_substr");
        expr_ref x = xvar;
        expr_ref y = mk_str_var_fresh("post_substr");

        // if i + l >= |s|, we can set post_substr to eps
        if(m.is_true(post_bound)) {
            y = expr_ref(m_util_s.str.mk_string(""), m);
        }
        std::vector<expr_ref> vars;
        // if i is of the form i = n + ...., create pre_substr . in_substr1 ... in_substrn to be x
        if(m_util_a.is_add(i, num, pred) && m_util_a.is_numeral(num, r)) {
            for(int i = 0; i < r.get_int32(); i++) {
                expr_ref fv = mk_str_var_fresh("in_substr");
                x = m_util_s.str.mk_concat(x, fv);
                vars.push_back(fv);
            }    
        }
        expr_ref xe(m_util_s.str.mk_concat(x, v), m);
        expr_ref xey(m_util_s.str.mk_concat(x, v, y), m);

       
        expr_ref ls(m_util_s.str.mk_length(s), m);
        expr_ref lx(m_util_s.str.mk_length(x), m);
        expr_ref le(m_util_s.str.mk_length(v), m);
        expr_ref ls_minus_i_l(mk_sub(mk_sub(ls, i), l), m);
        expr_ref zero(m_util_a.mk_int(0), m);
        expr_ref eps(m_util_s.str.mk_string(""), m);

        literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
        literal ls_le_i = mk_literal(m_util_a.mk_le(mk_sub(i, ls), zero));
        literal li_ge_ls = mk_literal(m_util_a.mk_ge(ls_minus_i_l, zero));
        literal l_ge_zero = mk_literal(m_util_a.mk_ge(l, zero));
        literal ls_le_0 = mk_literal(m_util_a.mk_le(ls, zero));

        string_theory_propagation(xe);
        string_theory_propagation(xey);

        // create axioms in_substri is Sigma
        for(const expr_ref& val : vars) {
            expr_ref re(m_util_s.re.mk_in_re(val, m_util_s.re.mk_full_char(nullptr)), m);
            literal pred_ge = mk_literal(m_util_a.mk_ge(pred, m_util_a.mk_int(0)));
            add_axiom({~i_ge_0, ~ls_le_i, ~pred_ge, mk_literal(re)});
            add_axiom({~i_ge_0, ~ls_le_i, ~pred_ge, mk_eq(m_util_s.str.mk_length(val), m_util_a.mk_int(1), false)});
        }
        // 0 <= i <= |s| -> xvy = s
        add_axiom({~i_ge_0, ~ls_le_i, mk_eq(xey, s, false)});
        // 0 <= i <= |s| -> |x| = i
        add_axiom({~i_ge_0, ~ls_le_i, mk_eq(lx, i, false)});
        // 0 <= i <= |s| && 0 <= l <= |s| - i -> |v| = l
        add_axiom({~i_ge_0, ~ls_le_i, ~l_ge_zero, ~li_ge_ls, mk_eq(le, l, false)});
        // 0 <= i <= |s| && |s| < l + i  -> |v| = |s| - i
        add_axiom({~i_ge_0, ~ls_le_i, li_ge_ls, mk_eq(le, mk_sub(ls, i), false)});
        // 0 <= i <= |s| && l < 0 -> v = eps
        add_axiom({~i_ge_0, ~ls_le_i, l_ge_zero, mk_eq(v, eps, false)});
        // i < 0 -> v = eps
        add_axiom({i_ge_0, mk_eq(v, eps, false)});
        // not(0 <= l <= |s| - i) -> v = eps
        add_axiom({ls_le_i, mk_eq(v, eps, false)});
        // i > |s| -> v = eps
        add_axiom({~ls_le_0, mk_eq(v, eps, false)});
        // substr(s, i, n) = v
        add_axiom({mk_eq(v, e, false)});

        // add the replacement substr -> v
        this->predicate_replace.insert(e, v.get());
        // update length variables
        util::get_str_variables(s, this->m_util_s, m, this->len_vars);
        this->len_vars.insert(v);
        if(vars.size() > 0) {
            this->var_eqs.add(expr_ref(pred, m), xvar);
            this->var_eqs.add(expr_ref(l, m), v); 
            this->len_vars.insert(xvar);
        } else {
            this->var_eqs.add(expr_ref(i, m), x);
            this->len_vars.insert(x);
        }        
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
        STRACE(str, tout << "handle-replace: " << mk_pp(r, m) << '\n';);

        if(axiomatized_persist_terms.contains(r))
            return;

        axiomatized_persist_terms.insert(r);
        context& ctx = get_context();
        expr* a = nullptr, *s = nullptr, *t = nullptr;
        VERIFY(m_util_s.str.is_replace(r, a, s, t));

        expr_ref v = mk_str_var_fresh("replace");
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

            add_axiom({mk_eq(v, r, false)});
            predicate_replace.insert(r, v.get());
            return;
        }

        expr* indexof = nullptr;
        if(expr_cases::is_replace_indexof(a, s, m, m_util_s, m_util_a, indexof)) {
            expr_ref minus_one(m_util_a.mk_int(-1), m);
            expr_ref v = mk_str_var_fresh("replace");
            expr_ref eps(m_util_s.str.mk_string(""), m);
            literal ind_eq_m1 = mk_eq(indexof, minus_one, false);
            expr_ref len_a_m1(m_util_a.mk_sub(m_util_s.str.mk_length(a), m_util_a.mk_int(1)), m);
            expr_ref substr(m_util_s.str.mk_substr(a, m_util_a.mk_int(0), len_a_m1), m);


            // s = eps -> v = t.a
            add_axiom({~s_emp, mk_eq(v, mk_concat(t, a),false)});
            add_axiom({ind_eq_m1, mk_eq(v, mk_concat(substr, t),false)});
            add_axiom({~ind_eq_m1, mk_eq(v, eps, false)});
            add_axiom({mk_eq(v, r, false)});
            predicate_replace.insert(r, v.get());
            return;
        }

        zstring str_a, str_b;
        // str.replace "A" s t where a = "A"
        if(m_util_s.str.is_string(a, str_a) && str_a.length() == 1) {
            // s = emp -> v = t.a
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

            // replace(a,s,t) = v
            add_axiom({mk_eq(v, r, false)});
            predicate_replace.insert(r, v.get());
            return;
        // str.replace "" s t where a = ""
        } else if(m_util_s.str.is_string(a, str_a) && str_a.length() == 0) {
            // s = emp -> v = t.a
            add_axiom({mk_literal(m.mk_not(m.mk_eq(s, eps))), mk_eq(v,t,false)});
            // s = emp -> v = t.a
            add_axiom({s_emp, mk_eq_empty(v)});
            // replace(a,s,t) = v
            add_axiom({mk_eq(v, r, false)});
            predicate_replace.insert(r, v.get());
            return;
        }

        literal cnt = mk_literal(m_util_s.str.mk_contains(a, s));
        // replace(a,s,t) = v
        add_axiom({mk_eq(v, r, false)});
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

        predicate_replace.insert(r, v.get());
    }

    /**
     * @brief Handling of str.replace(s,R,t) = v ... s where to replace, R regex what to find, t replacement.
     * Translates to the following theory axioms (similar to handle_replace):
     * replace(s,R,t) = v
     * eps \in R -> v = t.s
     * s \not\in \Sigma*R\Sigma* -> v = s
     * s \in \Sigma*R\Sigma* && eps \not\in R -> (s = x.y.a.z && xy \not\in \Sigma*R\Sigma* && a \in \Sigma && ya \in R && v = x.t.z)
     *
     * @param e replace_re term
     */
    void theory_str_noodler::handle_replace_re(expr *e) {
        STRACE(str, tout << "handle-replace: " << mk_pp(e, m) << '\n';);

        if(axiomatized_persist_terms.contains(e))
            return;
        axiomatized_persist_terms.insert(e);

        context& ctx = get_context();
        expr *s = nullptr, *R = nullptr, *t = nullptr;
        VERIFY(m_util_s.str.is_replace_re(e, s, R, t));
        expr_ref v = mk_str_var_fresh("replace_re");
        expr_ref x = mk_str_var_fresh("replace_re_left");
        expr_ref y = mk_str_var_fresh("replace_re_middle");
        expr_ref a = mk_str_var_fresh("replace_re_middle_char");
        expr_ref z = mk_str_var_fresh("replace_re_right");
        expr_ref eps(m_util_s.str.mk_string(""), m);
        expr_ref xyaz = mk_concat(x, mk_concat(y, mk_concat(a, z)));
        expr_ref xy = mk_concat(x, y);
        expr_ref ya = mk_concat(y, a);
        expr_ref xtz = mk_concat(x, mk_concat(t, z));
        expr_ref ts = mk_concat(t, s);
        expr_ref sigma_star(m_util_s.re.mk_full_seq(R->get_sort()), m);
        // \Sigma*R\Sigma*
        expr_ref SRS(m_util_s.re.mk_concat(sigma_star, m_util_s.re.mk_concat(R, sigma_star)), m);
        // s \in \Sigma*R\Sigma*
        literal s_in_SRS = mk_literal(m_util_s.re.mk_in_re(s, SRS));
        // eps \in R
        literal eps_in_R = mk_literal(m_util_s.re.mk_in_re(eps, R));

        // eps \in R -> v = t.s
        add_axiom({~eps_in_R, mk_literal(m.mk_eq(v, ts))});

        // s \not\in \Sigma*R\Sigma* -> v = s
        add_axiom({s_in_SRS, mk_eq(v, s, false)});

        // s \in \Sigma*R\Sigma* && eps \not\in R -> (s = x.y.z && xy \not\in \Sigma*R\Sigma* && a \in \Sigma && ya \in R && v = x.t.z)
        add_axiom({~s_in_SRS, eps_in_R, mk_literal(m.mk_eq(s, xyaz))});
        add_axiom({~s_in_SRS, eps_in_R, mk_literal(m.mk_not(m_util_s.re.mk_in_re(xy, SRS)))});
        add_axiom({~s_in_SRS, eps_in_R, mk_literal(m_util_s.re.mk_in_re(a, m_util_s.re.mk_full_char(R->get_sort())))});
        add_axiom({~s_in_SRS, eps_in_R, mk_literal(m_util_s.re.mk_in_re(ya, R))});
        add_axiom({~s_in_SRS, eps_in_R, mk_eq(v, xtz, false)});
        
        add_axiom({mk_eq(v, e, false)});
        predicate_replace.insert(e, v.get());
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
        STRACE(str, tout << "handle-indexof: " << mk_pp(i, m) << '\n';);
        if(axiomatized_persist_terms.contains(i))
            return;

        axiomatized_persist_terms.insert(i);
        ast_manager &m = get_manager();
        expr *s = nullptr, *t = nullptr, *offset = nullptr;
        rational r;
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

        if (!offset || (m_util_a.is_numeral(offset, r) && r.is_zero())) {
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
            util::get_str_variables(t, this->m_util_s, m, this->len_vars);
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
     * @brief Handle replace_all. Just store the instance. It is solved using transducer 
     * constraints in the final_check.
     * 
     * @param e replace_all
     */
    void theory_str_noodler::handle_replace_all(expr *e) {
        STRACE(str, tout << "handle-replace-all: " << mk_pp(e, m) << '\n';);
        if (axiomatized_persist_terms.contains(e))
            return;

        axiomatized_persist_terms.insert(e);

        ast_manager &m = get_manager();
        expr *s = nullptr, *i = nullptr, *l = nullptr;
        VERIFY(m_util_s.str.is_replace_all(e, s, i, l));

        expr_ref v = mk_str_var_fresh("replace_all");
        // create equation for propagating length constraints
        // tmp = replace_all(...) => |tmp| = |replace_all(...)|
        add_axiom({mk_eq(v, e, false)});
        this->predicate_replace.insert(e, v.get());  
    }

    /**
     * @brief Handle replace_re_all. Just store the instance. It is solved using transducer 
     * constraints in the final_check.
     * 
     * @param e replace_re_all
     */
    void theory_str_noodler::handle_replace_re_all(expr *e) {
        STRACE(str, tout << "handle-replace-re-all: " << mk_pp(e, m) << '\n';);
        if (axiomatized_persist_terms.contains(e))
            return;

        axiomatized_persist_terms.insert(e);

        ast_manager &m = get_manager();
        expr *s = nullptr, *i = nullptr, *l = nullptr;
        VERIFY(m_util_s.str.is_replace_re_all(e, s, i, l));

        expr_ref v = mk_str_var_fresh("replace_all");
        // create equation for propagating length constraints
        // tmp = replace_all(...) => |tmp| = |replace_all(...)|
        add_axiom({mk_eq(v, e, false)});
        this->predicate_replace.insert(e, v.get());  
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
        if(axiomatized_persist_terms.contains(e))
            return;

        axiomatized_persist_terms.insert(e);
        ast_manager &m = get_manager();
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
        if(axiomatized_persist_terms.contains(m.mk_not(e)))
            return;

        axiomatized_persist_terms.insert(m.mk_not(e));
        ast_manager &m = get_manager();
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

        expr_ref len_x_gt_len_y(m);
        zstring s;
        if(m_util_s.str.is_string(x, s)) {
            len_x_gt_len_y = expr_ref{m_util_a.mk_ge(m_util_s.str.mk_length(y), m_util_a.mk_int(s.length())),m};
        } else {
            len_x_gt_len_y = expr_ref{m_util_a.mk_ge(m_util_s.str.mk_length(y), m_util_s.str.mk_length(x)),m};
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
        util::get_str_variables(x, this->m_util_s, m, this->len_vars, &this->predicate_replace);
        util::get_str_variables(y, this->m_util_s, m, this->len_vars, &this->predicate_replace);
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
        if(axiomatized_persist_terms.contains(e))
            return;

        axiomatized_persist_terms.insert(e);
        ast_manager &m = get_manager();
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
        if(axiomatized_persist_terms.contains(m.mk_not(e)))
            return;

        axiomatized_persist_terms.insert(m.mk_not(e));
        ast_manager &m = get_manager();
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
        util::get_str_variables(x, this->m_util_s, m, this->len_vars, &this->predicate_replace);
        util::get_str_variables(y, this->m_util_s, m, this->len_vars, &this->predicate_replace);
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
        if(axiomatized_persist_terms.contains(e))
            return;

        axiomatized_persist_terms.insert(e);
        STRACE(str, tout  << "handle contains " << mk_pp(e, m) << std::endl;);
        ast_manager &m = get_manager();
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
        expr* cont = this->m.mk_not(e);
        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_contains(e, x, y));

        STRACE(str, tout  << "handle not(contains) " << mk_pp(e, m) << std::endl;);
        zstring s;
        if(m_util_s.str.is_string(y, s)) {
            expr_ref re(m_util_s.re.mk_in_re(x, m_util_s.re.mk_concat(m_util_s.re.mk_star(m_util_s.re.mk_full_char(nullptr)),
                m_util_s.re.mk_concat(m_util_s.re.mk_to_re(m_util_s.str.mk_string(s)),
                m_util_s.re.mk_star(m_util_s.re.mk_full_char(nullptr)))) ), m);
          
            add_axiom({mk_literal(e), ~mk_literal(re)});
            add_axiom({mk_literal(cont), mk_literal(re)});
        } else if(m_util_s.str.is_string(x, s) && s.length() == 1) { // special case for not(contains "A" t)
            expr_ref re(m_util_s.re.mk_in_re(x, m_util_s.re.mk_to_re(m_util_s.str.mk_string(s)) ), m);
            add_axiom({mk_literal(e), ~mk_literal(re)});
        }
    }

    /**
     * @brief Handler for assigning boolean value to the not(contains) predicate.
     * 
     * @param e Not contains predicate
     */
    void theory_str_noodler::assign_not_contains(expr *e) {
        expr* cont = this->m.mk_not(e);
        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_contains(e, x, y));
        STRACE(str, tout  << "assign not(contains) " << mk_pp(e, m) << std::endl;);

        zstring s;
        // not(contains) was not axiomatized in handle_not_contains
        if(!m_util_s.str.is_string(y) && !(m_util_s.str.is_string(x, s) && s.length() == 1)) {
            m_not_contains_todo.push_back({{x, m},{y, m}});
        }
    }

    /**
     * @brief Handle str.<=
     * Translates to the following axiom
     * 
     * x <= y -> x = y | x < y
     * not(x <= y) -> y > x
     * @param e str.<= predicate
     */
    void theory_str_noodler::handle_lex_leq(expr *e) {
        STRACE(str, tout  << "handle str.<= " << mk_pp(e, m) << std::endl;);

        expr *x = nullptr, *y = nullptr;
        VERIFY(m_util_s.str.is_le(e, x, y));
      
        expr_ref e_lt(m_util_s.str.mk_lex_lt(x, y), m);
        expr_ref x_y(m.mk_eq(x,y), m);
        literal lit_e_lt = mk_literal(e_lt);
        literal lit_e = mk_literal(e);
        literal lit_x_y = mk_literal(x_y);
        literal lit_e_switch = mk_literal(m_util_s.str.mk_lex_lt(y, x));
        // x <= y -> x = y | x < y
        add_axiom({~lit_e, lit_e_lt, lit_x_y});
        // not(x <= y) -> y > x
        add_axiom({lit_e, lit_e_switch});
    }

    /**
     * @brief Handle str.<
     * Translates to the following theory axioms.
     * 
     * not(x < y) -> x = y | y < x
     * x < y & x = eps -> y != eps
     * x < y & x != eps -> x = u.v1.w1
     * x < y & x != eps -> y = u.v2.w2
     * x < y & x != eps -> v1 in re.allchar
     * x < y & x != eps -> v2 in re.allchar
     * x < y & x != eps -> to_code(v1) + k = to_code(v2) & k >= 1
     * @param e str.< predicate
     */
    void theory_str_noodler::handle_lex_lt(expr *e) {
        STRACE(str, tout  << "handle str.< " << mk_pp(e, m) << std::endl;);

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
        expr *s = nullptr, *re = nullptr;
        VERIFY(m_util_s.str.is_in_re(e, s, re));
        ast_manager& m = get_manager();
        STRACE(str, tout  << "handle_in_re " << mk_pp(e, m) << " " << is_true << std::endl;);

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
        if(axiomatized_persist_terms.contains(e))
            return;
        axiomatized_persist_terms.insert(e);

        expr *s = nullptr;
        VERIFY(m_util_s.str.is_is_digit(e, s));
        // s \in [0-9]
        expr *s_in_digit = m_util_s.re.mk_in_re(s, m_util_s.re.mk_range(m_util_s.str.mk_string("0"), m_util_s.str.mk_string("9")));
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
                add_axiom({~mk_literal(ex)});
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
                    add_axiom({~mk_literal(ex)});
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
        expr *arg = nullptr;

        ConversionType type;
        std::string name_of_type;
        if (m_util_s.str.is_to_code(conversion, arg)) {
            type = ConversionType::TO_CODE;
            name_of_type = "to_code";
        } else if (m_util_s.str.is_from_code(conversion, arg)) {
            type = ConversionType::FROM_CODE;
            name_of_type = "from_code";
        } else if (m_util_s.str.is_stoi(conversion, arg)) {
            type = ConversionType::TO_INT;
            name_of_type = "to_int";
        } else if (m_util_s.str.is_itos(conversion, arg)) {
            type = ConversionType::FROM_INT;
            name_of_type = "from_int";
        } else {
            UNREACHABLE();
            return;
        }
        bool tranforming_from = (type == ConversionType::FROM_CODE || type == ConversionType::FROM_INT);

        // get the var for the argument
        BasicTerm var_for_arg(BasicTermType::Variable);
        if (tranforming_from) {
            // we create new fresh noodler var for the integer argument which we save into var_name so that
            // len formula we will create in decision procedure will replace the correct var with the correct expression
            var_for_arg = util::mk_noodler_var_fresh(name_of_type + "_argument");
            var_name.insert({var_for_arg, expr_ref(arg, m)});
        } else {
            // for to_code and to_int, the argument has string type, we have to find the variable for it
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
            var_name.insert({var_for_arg, z3_var_for_arg}); // I have no idea why I am doing this, but it is probably important
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
            len_vars.insert(z3_var_for_conversion); // dunno if this is needed
            var_for_conversion = util::get_variable_basic_term(z3_var_for_conversion);
            var_name.insert({var_for_conversion, z3_var_for_conversion}); // I have no idea why I am doing this, but it is probably important

            // The range of from_* functions is bounded, we have to bound it also for the decision procedure
            if (type == ConversionType::FROM_CODE) {
                // the result of str.from_code can only be either a char representing the code value, or empty string (if argument is out of range of any code value)
                app *sigma_eps = m_util_s.re.mk_union(
                                                m_util_s.re.mk_epsilon(conversion->get_sort()),
                                                m_util_s.re.mk_full_char(nullptr)
                                            );
                add_axiom({mk_literal(m_util_s.re.mk_in_re(z3_var_for_conversion, sigma_eps))});
            }

            if (type == ConversionType::FROM_INT) {
                // the result of str.from_int can only be either a decimal representation of a number without leading zeros, or empty string (if argument is negative)
                app *zero = m_util_s.re.mk_to_re(m_util_s.str.mk_string("0")); // if argument == 0, the result will be 0
                app *nums_without_zero = m_util_s.re.mk_concat(
                                                m_util_s.re.mk_plus(m_util_s.re.mk_range(m_util_s.str.mk_string("1"), m_util_s.str.mk_string("9"))),
                                                m_util_s.re.mk_star(m_util_s.re.mk_range(m_util_s.str.mk_string("0"), m_util_s.str.mk_string("9")))
                                            ); // if argument > 0, the result will be of form [1-9]+[0-9]*
                app *epsilon = m_util_s.re.mk_epsilon(conversion->get_sort()); // if argument < 0, the result is empty string
                add_axiom({mk_literal(m_util_s.re.mk_in_re(z3_var_for_conversion, m_util_s.re.mk_union(m_util_s.re.mk_union(zero, nums_without_zero), epsilon)))});

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
        } else {
            // we create new fresh noodler var for the integer result which we save into var_name so that
            // len formula we will create in decision procedure will replace the correct var with the correct expression
            var_for_conversion = util::mk_noodler_var_fresh(name_of_type + "_result");
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
                    add_axiom({mk_literal(m_util_a.mk_le(conversion, m_util_a.mk_int(10)))});
                } else if (m_util_s.str.is_extract(arg, e1, e2, e3) && m_util_a.is_numeral(e3, r1)) {
                    // argument is str.substr(?, ?, numeral) => result must be less than 10^numeral
                    rational ten_to_r1(1);
                    for (rational i(0); i < r1; ++i) {
                        ten_to_r1 = ten_to_r1 * 10;
                    }
                    add_axiom({mk_literal(m_util_a.mk_le(conversion, m_util_a.mk_int(ten_to_r1)))});
                }
            }
        }

        // Add to todo
        if (tranforming_from) {
            m_conversion_todo.push_back({type, var_for_conversion, var_for_arg});
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

    expr_ref theory_str_noodler::construct_refinement() {
        context& ctx = get_context();

        ast_manager& m = get_manager();
        expr *refinement = nullptr;
        STRACE(str, tout << "[Constructing refinement]\n";);
        for (const auto& we : this->m_word_eq_todo_rel) {
            // we create the equation according to we
            expr *const e = ctx.mk_eq_atom(we.first, we.second);
            refinement = refinement == nullptr ? e : m.mk_and(refinement, e);
        }

        literal_vector ls;
        for (const auto& wi : this->m_word_diseq_todo_rel) {
            expr_ref e(m.mk_not(ctx.mk_eq_atom(wi.first, wi.second)), m);
            // e might not be internalized
            if(!ctx.e_internalized(e)) {
                ctx.internalize(e, false);
            }
            refinement = refinement == nullptr ? e : m.mk_and(refinement, e);
        }
        for (const auto& in : this->m_membership_todo_rel) {
            app_ref in_app(m_util_s.re.mk_in_re(std::get<0>(in), std::get<1>(in)), m);
            if(!std::get<2>(in)){
                in_app = m.mk_not(in_app);
                if(!ctx.e_internalized(in_app)) {
                    ctx.internalize(in_app, false);
                }
            }
            refinement = refinement == nullptr ? in_app : m.mk_and(refinement, in_app);
        }
        for(const auto& nc : this->m_not_contains_todo_rel) {
            app_ref nc_app(m.mk_not(m_util_s.str.mk_contains(nc.first, nc.second)), m);
            refinement = refinement == nullptr ? nc_app : m.mk_and(refinement, nc_app);
        }

        return expr_ref(refinement, m);
    }
}
