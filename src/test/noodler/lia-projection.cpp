#include <catch2/catch_test_macros.hpp>

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "params/smt_params.h"
#include "smt/smt_context.h"
#include "smt/smt_kernel.h"
#include "smt/theory_str_noodler/lia_solver.h"

using namespace smt::noodler;

TEST_CASE("collect_arith_projection", "[noodler]") {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    smt_params params;
    sort* int_sort = a.mk_int();
    sort* s_sort = m.mk_uninterpreted_sort(symbol("S"));
    expr_ref x(m.mk_const("x", int_sort), m);
    expr_ref y(m.mk_const("y", int_sort), m);
    expr_ref p(m.mk_const("p", m.mk_bool_sort()), m);
    expr_ref s(m.mk_const("s", s_sort), m);
    expr_ref t(m.mk_const("t", s_sort), m);
    func_decl_ref len(m.mk_func_decl(symbol("len"), s_sort, int_sort), m);
    expr_ref len_s(m.mk_app(len, s.get()), m);
    expr_ref len_t(m.mk_app(len, t.get()), m);

    smt::context ctx(m, params);
    ctx.assert_expr(a.mk_le(x, a.mk_int(3)));
    // a false arithmetic literal (decided inside a disjunction)
    ctx.assert_expr(m.mk_or(m.mk_not(a.mk_ge(y, a.mk_int(5))), m.mk_not(p)));
    ctx.assert_expr(p);
    // len(s) = len(t) follows only by congruence from s = t (an equality of a non-arithmetic sort), which is derived
    // during the search (as a unit, it would be eliminated by the preprocessing)
    ctx.assert_expr(m.mk_or(m.mk_eq(s, t), a.mk_gt(x, a.mk_int(100))));
    ctx.assert_expr(a.mk_ge(len_s, a.mk_int(2)));
    ctx.assert_expr(a.mk_ge(len_t, a.mk_int(-7)));
    REQUIRE(ctx.check() == l_true);

    expr_ref_vector projection(m);
    collect_arith_projection(ctx, projection);

    // the projection contains only arithmetic facts
    for (expr* e : projection) {
        expr* atom = e;
        m.is_not(e, atom);
        expr *lhs, *rhs;
        bool is_arith_eq = m.is_eq(atom, lhs, rhs) && a.is_int_real(lhs);
        CHECK((is_arith_eq || (is_app(atom) && to_app(atom)->get_family_id() == a.get_family_id())));
    }

    // check whether the projection implies @p fact
    auto implies = [&](expr* fact) {
        smt::kernel k(m, params);
        for (expr* e : projection) {
            k.assert_expr(e);
        }
        k.assert_expr(m.mk_not(fact));
        return k.check() == l_false;
    };
    CHECK(implies(a.mk_le(x, a.mk_int(3))));
    CHECK(implies(a.mk_le(y, a.mk_int(4))));
    CHECK(implies(a.mk_ge(len_t, a.mk_int(2))));
    CHECK_FALSE(implies(a.mk_le(x, a.mk_int(2))));
}
