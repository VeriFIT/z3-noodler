#include <sstream>
#include <string>

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "ast/ast_pp.h"
#include "ast/seq_decl_plugin.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"

using Catch::Matchers::ContainsSubstring;

namespace {

// SMT-LIB script parsed command by command into one context, so that the parsed terms can be compared.
struct Smt2Script {
    cmd_context ctx;
    std::ostringstream errors;

    Smt2Script() : ctx(false) { ctx.set_regular_stream(errors); }

    // Parses commands that are expected to be correct.
    void parse(const std::string& commands) {
        std::istringstream in(commands);
        bool parsed = parse_smt2_commands(ctx, in);
        INFO(errors.str());
        REQUIRE(parsed);
    }

    // Parses commands that are expected to be rejected, returns the errors reported by the parser.
    std::string parse_error(const std::string& commands) {
        std::istringstream in(commands);
        REQUIRE_FALSE(parse_smt2_commands(ctx, in));
        return errors.str();
    }

    expr* assertion(unsigned i) const { return ctx.assertions()[i]; }
};

} // namespace

TEST_CASE("re.from_regex", "[noodler][from_regex]") {
    Smt2Script script;
    seq_util u(script.ctx.m());

    SECTION("re.from_ecma2020 is a synonym of the ecma2020 flavor") {
        script.parse(R"smt(
            (declare-const x String)
            (assert (str.in_re x ((_ re.from_regex ecma2020) "(a)\1")))
            (assert (str.in_re x (re.from_ecma2020 "(a)\1")))
        )smt");
        // terms are hash-consed, so the synonyms give the very same term
        CHECK(script.assertion(0) == script.assertion(1));
        expr* x = nullptr;
        symbol flavor;
        zstring pattern;
        REQUIRE(u.str.is_in_re_from_regex(script.assertion(0), x, flavor, pattern));
        CHECK(flavor == "ecma2020");
        CHECK(pattern == zstring("(a)\\1"));
    }

    SECTION("mk_from_regex gives the parsed term") {
        script.parse(R"smt(
            (declare-const x String)
            (assert (str.in_re x ((_ re.from_regex ecma2020) "a+")))
        )smt");
        CHECK(to_app(script.assertion(0))->get_arg(1) == u.re.mk_from_regex(symbol("ecma2020"), zstring("a+")));
    }

    SECTION("flavor is printed as the index of re.from_regex") {
        script.parse(R"smt(
            (declare-const x String)
            (assert (str.in_re x (re.from_ecma2020 "a+")))
        )smt");
        std::ostringstream printed;
        printed << mk_pp(script.assertion(0), script.ctx.m());
        CHECK(printed.str() == "(str.in_re x ((_ re.from_regex ecma2020) \"a+\"))");
        // the printed term is parsed back to the same term
        script.parse("(assert " + printed.str() + ")");
        CHECK(script.assertion(1) == script.assertion(0));
    }

    SECTION("flavor can be a quoted symbol") {
        script.parse(R"smt(
            (declare-const x String)
            (assert (str.in_re x ((_ re.from_regex |ecma2020|) "a")))
            (assert (str.in_re x (re.from_ecma2020 "a")))
        )smt");
        CHECK(script.assertion(0) == script.assertion(1));
    }

    SECTION("flavor can coincide with the name of a declared constant") {
        script.parse(R"smt(
            (declare-const ecma2020 String)
            (assert (str.in_re ecma2020 ((_ re.from_regex ecma2020) "a")))
            (assert (str.in_re ecma2020 (re.from_ecma2020 "a")))
        )smt");
        CHECK(script.assertion(0) == script.assertion(1));
    }

    SECTION("unknown flavor is rejected") {
        CHECK_THAT(script.parse_error(R"smt(
            (declare-const x String)
            (assert (str.in_re x ((_ re.from_regex perl) "a")))
        )smt"), ContainsSubstring("unknown regex flavor 'perl'"));
    }

    SECTION("missing flavor is rejected") {
        CHECK_THAT(script.parse_error(R"smt(
            (declare-const x String)
            (assert (str.in_re x (re.from_regex "a")))
        )smt"), ContainsSubstring("re.from_regex expects a regex flavor as its index"));
    }

    SECTION("more flavors are rejected") {
        CHECK_THAT(script.parse_error(R"smt(
            (declare-const x String)
            (assert (str.in_re x ((_ re.from_regex ecma2020 ecma2020) "a")))
        )smt"), ContainsSubstring("re.from_regex expects a regex flavor as its index"));
    }

    SECTION("numeral flavor is rejected") {
        CHECK_THAT(script.parse_error(R"smt(
            (declare-const x String)
            (assert (str.in_re x ((_ re.from_regex 2020) "a")))
        )smt"), ContainsSubstring("re.from_regex expects a regex flavor as its index"));
    }
}
