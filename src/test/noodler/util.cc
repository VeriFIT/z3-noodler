#include <iostream>
#include <algorithm>
#include <utility>

#include <catch2/catch_test_macros.hpp>
#include <mata/re2parser.hh>
#include <smt/theory_str_noodler/decision_procedure.h>
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "ast/reg_decl_plugins.h"
#include "test_utils.h"

using namespace smt::noodler;

TEST_CASE("theory_str_noodler::util::conv_to_regex_hex()", "[noodler]") {
    smt_params params;
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    smt::context ctx{ast_m, params };
    theory_str_params str_params{};
    TheoryStrNoodlerCUT noodler{ctx, ast_m, str_params };
    std::set<uint32_t> alphabet{ '\x78', '\x79', '\x7A' };
    auto& m_util_s{ noodler.m_util_s };
    auto& m{ noodler.m };
    auto& m_util_a{ noodler.m_util_a };
    auto default_sort{ ast_m.mk_sort(symbol{ "RegEx" }, sort_info{ noodler.get_family_id(), 1, sort_size(0), 0, nullptr }) };

    SECTION("util::conv_to_regex_hex()") {
        auto expr_x{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("x")) };
        auto regex{ util::conv_to_regex_hex(expr_x, m_util_s, m, alphabet) };
        CHECK(regex == "\\x{78}");

        auto expr_y{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("y")) };
        regex = util::conv_to_regex_hex(expr_y, m_util_s, m, alphabet);
        CHECK(regex == "\\x{79}");

        auto expr_hex{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("\x45")) };
        regex = util::conv_to_regex_hex(expr_hex, m_util_s, m, alphabet);
        CHECK(regex == "\\x{45}");

        auto expr_hex_char{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("x\x45")) };
        regex = util::conv_to_regex_hex(expr_hex_char, m_util_s, m, alphabet);
        CHECK(regex == "\\x{78}\\x{45}");

        auto expr_hex_char2{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("x\x45x")) };
        regex = util::conv_to_regex_hex(expr_hex_char2, m_util_s, m, alphabet);
        CHECK(regex == "\\x{78}\\x{45}\\x{78}");

        auto expr_star{ m_util_s.re.mk_star(expr_x) };
        regex = util::conv_to_regex_hex(expr_star, m_util_s, m, alphabet);
        CHECK(regex == "(\\x{78})*");

        auto expr_plus{ m_util_s.re.mk_plus(expr_y) };
        regex = util::conv_to_regex_hex(expr_plus, m_util_s, m, alphabet);
        CHECK(regex == "(\\x{79})+");

        auto expr_concat{ m_util_s.re.mk_concat(expr_star, expr_plus) };
        regex = util::conv_to_regex_hex(expr_concat, m_util_s, m, alphabet);
        CHECK(regex == "(\\x{78})*(\\x{79})+");

        //auto expr_all_char{ m_util_s.re.mk_full_char(default_sort) };
        //regex = util::conv_to_regex_hex(expr_all_char, m_util_s, m, alphabet);
        //CHECK(regex == ".");

        auto expr_all_char{ m_util_s.re.mk_full_seq(default_sort) };
        regex = util::conv_to_regex_hex(expr_all_char, m_util_s, m, alphabet);
        CHECK(regex == "[\\x{78}\\x{79}\\x{7a}]*");

        // FIXME.
        //auto expr_all_char_star{ m_util_s.re.mk_star(expr_all_char) };
        //regex = util::conv_to_regex_hex(expr_all_char_star, m_util_s, m, alphabet);
        //CHECK(regex == "(((.))*)");
    }
}

TEST_CASE("theory_str_noodler::util") {
    smt_params params;
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    smt::context ctx{ast_m, params };
    theory_str_params str_params{};
    TheoryStrNoodlerCUT noodler{ctx, ast_m, str_params };
    std::set<uint32_t> alphabet{ '\x78', '\x79', '\x7A' };
    auto& m_util_s{ noodler.m_util_s };
    auto& m_util_a{ noodler.m_util_a };
    auto& m{ noodler.m };
    auto default_sort{ ast_m.mk_sort(symbol{ "RegEx" }, sort_info{ noodler.get_family_id(), 1, sort_size(0), 0, nullptr }) };

    SECTION("util::get_dummy_symbols()") {
        vector<util::expr_pair> disequations{};
        auto expr_hex_char{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("x\x45")) };
        auto expr_hex_char2{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("y\x02")) };
        auto expr_hex_char3{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("z\x03")) };

        disequations.insert(std::make_pair(
                obj_ref<expr, ast_manager>{ expr_hex_char->get_arg(0), ast_m },
                obj_ref<expr, ast_manager>{ expr_hex_char->get_arg(0), ast_m }
        ));
        disequations.insert(std::make_pair(
                obj_ref<expr, ast_manager>{ expr_hex_char2->get_arg(0), ast_m },
                obj_ref<expr, ast_manager>{ expr_hex_char3->get_arg(0), ast_m }
        ));

        alphabet.insert({ '\x45', '\x02', '\x03', '\x00' });
        std::set<uint32_t> dummy_symbols{ util::get_dummy_symbols(disequations, alphabet) };
        CHECK(dummy_symbols == std::set<uint32_t>{ '\x01', '\x04' });
        CHECK(alphabet == std::set<uint32_t>{ '\x00', '\x01', '\x02', '\x03', '\x04', '\x45', '\x78', '\x79', '\x7a' });
    }

    SECTION("util::get_symbols()") {
        vector<util::expr_pair> disequations{};
        auto expr_hex_char{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("x\x45")) };
        auto expr_hex_char2{ m_util_s.re.mk_to_re(m_util_s.str.mk_string("wy\x02")) };
        auto expr_concat{ m_util_s.re.mk_concat(expr_hex_char, m_util_s.re.mk_star(expr_hex_char2)) };

        util::extract_symbols(expr_concat, m_util_s, m, alphabet);
        CHECK(alphabet == std::set<uint32_t>{ '\x02', '\x45', '\x77', '\x78', '\x79', '\x7a' });
    }

    SECTION("util::is_str_variable()") {
        expr_ref str_variable{ noodler.mk_str_var(symbol("var1")), m };
        CHECK(util::is_str_variable(str_variable, m_util_s));
        expr_ref str_literal{m_util_s.str.mk_string("var1"), m };
        CHECK(!util::is_str_variable(str_literal, m_util_s));
        expr_ref regex{ m_util_s.re.mk_to_re(m_util_s.str.mk_string(".*regex.*")), m };
        CHECK(!util::is_str_variable(regex, m_util_s));
        expr_ref int_literal{ m_util_a.mk_int(1), m };
        CHECK(!util::is_str_variable(int_literal, m_util_s));
    }
}
