#include <iostream>

#include <catch2/catch_test_macros.hpp>
#include <mata/nfa.hh>

#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "smt/theory_str_noodler/util.h"
#include "ast/reg_decl_plugins.h"

using namespace smt::noodler;

class TheoryStrNoodlerCUT : public theory_str_noodler {
public:
    TheoryStrNoodlerCUT(smt::context &ctx, ast_manager &m, const theory_str_params &params)
        : theory_str_noodler(ctx, m, params) {}

    using theory_str_noodler::m_util_s, theory_str_noodler::m;
};

TEST_CASE("theory_str_noodler", "[noodler]") {
    memory::initialize(0);
    smt_params params;
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    smt::context ctx{ast_m, params };
    theory_str_params str_params{};
    TheoryStrNoodlerCUT noodler{ctx, ast_m, str_params };
    std::set<uint32_t> alphabet{ '\x78', '\x79', '\x7A' };
    auto& m_util_s{ noodler.m_util_s };
    auto& m{ noodler.m };
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
        CHECK(regex == "[\\x{78}\\x{79}\\x{7a}]");

        // FIXME.
        //auto expr_all_char_star{ m_util_s.re.mk_star(expr_all_char) };
        //regex = util::conv_to_regex_hex(expr_all_char_star, m_util_s, m, alphabet);
        //CHECK(regex == "(((.))*)");
    }
    
    memory::finalize();
}
