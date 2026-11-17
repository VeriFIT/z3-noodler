#include <catch2/catch_test_macros.hpp>

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "smt/theory_str_noodler/axiom_replay.h"

using namespace smt::noodler;

TEST_CASE("AxiomReplay", "[noodler]") {
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref a(m.mk_const("a", m.mk_bool_sort()), m);
    expr_ref b(m.mk_const("b", m.mk_bool_sort()), m);
    expr_ref c(m.mk_const("c", m.mk_bool_sort()), m);
    auto clause = [&](expr* e) {
        expr_ref_vector res(m);
        res.push_back(e);
        return res;
    };

    AxiomReplay replay;

    SECTION("axioms are recorded only while recording") {
        replay.record(1, clause(a));
        CHECK_FALSE(replay.is_recording());
        {
            AxiomReplay::Recorder recorder(replay);
            CHECK(replay.is_recording());
            {
                AxiomReplay::Recorder nested(replay);
                CHECK(replay.is_recording());
            }
            CHECK(replay.is_recording());
            replay.record(1, clause(b));
        }
        CHECK_FALSE(replay.is_recording());
        replay.pop(0);
        auto pending = replay.take_pending();
        REQUIRE(pending.size() == 1);
        CHECK(pending[0].get(0) == b.get());
        CHECK_FALSE(replay.has_pending());
    }

    SECTION("only axioms above the new level become pending") {
        AxiomReplay::Recorder recorder(replay);
        replay.record(0, clause(a));
        replay.record(2, clause(b));
        replay.record(3, clause(c));

        replay.pop(3);
        CHECK_FALSE(replay.has_pending());

        replay.pop(1);
        REQUIRE(replay.has_pending());
        auto pending = replay.take_pending();
        REQUIRE(pending.size() == 2);
        CHECK(pending[0].get(0) == c.get());
        CHECK(pending[1].get(0) == b.get());

        // the axiom of level 0 stays recorded (and becomes pending only when backtracking below 0)
        replay.pop(0);
        CHECK_FALSE(replay.has_pending());
        replay.pop(-1);
        REQUIRE(replay.has_pending());
        CHECK(replay.take_pending()[0].get(0) == a.get());
    }

    SECTION("replayed axioms are recorded again at the current level") {
        AxiomReplay::Recorder recorder(replay);
        replay.record(5, clause(a));
        replay.pop(2);
        for (const expr_ref_vector& pending : replay.take_pending()) {
            replay.record(2, pending); // the theory adds it again at level 2
        }
        replay.pop(2);
        CHECK_FALSE(replay.has_pending());
        replay.pop(1);
        CHECK(replay.has_pending());
    }
}
