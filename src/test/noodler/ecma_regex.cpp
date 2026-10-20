#include "smt/theory_str_noodler/extended_regex/ecma_regex.h"
#include "smt/theory_str_noodler/extended_regex/extended_regex.h"

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "params/theory_str_noodler_params.h"

#include <algorithm>
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>
#include <queue>
#include <sstream>

// =====================================================================
// LEXER TESTS
// =====================================================================

TEST_CASE("ECMA Regex Lexer", "[noodler][ecma]") {
    using namespace smt::noodler::extended_regex::ecma;

    SECTION("Get literal token from regex") {
        zstring regex = "a";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();

        REQUIRE(t.type == TokenType::LITERAL);
        uint32_t value = -1;
        REQUIRE_NOTHROW(value = std::get<uint32_t>(t.payload));
        REQUIRE(value == static_cast<uint32_t>('a'));

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::END_OF_INPUT);
    }

    SECTION("Escape sequence as literal") {
        zstring regex = "\\*";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();

        REQUIRE(t.type == TokenType::LITERAL);
        uint32_t value = -1;
        REQUIRE_NOTHROW(value = std::get<uint32_t>(t.payload));
        REQUIRE(value == static_cast<uint32_t>('*'));
        REQUIRE(t.lexeme.length() == 2);
    }

    SECTION("Hex escape sequence") {
        zstring regex = "\\x41\\x42";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);

        Token t1 = lexer.get_next_token();
        REQUIRE(t1.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t1.payload) == 65);
        REQUIRE(t1.lexeme.length() == 4);

        Token t2 = lexer.get_next_token();
        REQUIRE(t2.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t2.payload) == 66);
        REQUIRE(t2.lexeme.length() == 4);
    }

    SECTION("Quantifier {n}") {
        zstring regex = "{1}";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::QUANTIFIER);
        QuantifierRange range;
        REQUIRE_NOTHROW(range = std::get<QuantifierRange>(t.payload));
        REQUIRE(range.min == 1);
        REQUIRE(range.max == 1);
        REQUIRE(t.lexeme == "{1}");
    }

    SECTION("Quantifier {n,}") {
        zstring regex = "{1,}";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::QUANTIFIER);
        QuantifierRange range;
        REQUIRE_NOTHROW(range = std::get<QuantifierRange>(t.payload));
        REQUIRE(range.min == 1);
        REQUIRE(range.max == std::numeric_limits<std::size_t>::max());
        REQUIRE(t.lexeme == "{1,}");
    }

    SECTION("Quantifier {n,m}") {
        zstring regex = "{1,2}";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::QUANTIFIER);
        QuantifierRange range;
        REQUIRE_NOTHROW(range = std::get<QuantifierRange>(t.payload));
        REQUIRE(range.min == 1);
        REQUIRE(range.max == 2);
        REQUIRE(t.lexeme == "{1,2}");
    }

    SECTION("Quantifier {n,m} out of order") {
        zstring regex = "{3,2}";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Quantifier with too large bounds") {
        for (const char *r : {"{1,18446744073709551616}", "{18446744073709551616}", "{18446744073709551617}",
                              "{18446744073709551615}", "{18446744073709551615,}", "{1000001}", "{1,1000001}"}) {
            zstring regex = r;
            std::unordered_map<zstring_view, uint32_t> map;
            ECMALexer lexer(regex, map);
            REQUIRE_THROWS(lexer.get_next_token());
        }
    }

    SECTION("Quantifier with bound at the limit") {
        zstring regex = "{1000000,}";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::QUANTIFIER);
        REQUIRE(std::get<QuantifierRange>(t.payload).min == 1'000'000);
    }

    SECTION("Unfinished quantifier with overflowing bound is a literal") {
        zstring regex = "{18446744073709551616";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '{');
    }

    SECTION("Dot") {
        zstring regex = ".";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::DOT);
        REQUIRE(t.lexeme == ".");
    }

    SECTION("Alternation") {
        zstring regex = "|";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::ALTERNATION);
        REQUIRE(t.lexeme == "|");
    }

    SECTION("Assertion ^") {
        zstring regex = "^";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::ASSERTION);
        REQUIRE(std::get<uint32_t>(t.payload) == '^');
        REQUIRE(t.lexeme == "^");
    }

    SECTION("Assertion $") {
        zstring regex = "$";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::ASSERTION);
        REQUIRE(std::get<uint32_t>(t.payload) == '$');
        REQUIRE(t.lexeme == "$");
    }

    SECTION("Group start") {
        zstring regex = "(";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::GROUP_START);
        REQUIRE(t.lexeme == "(");
    }

    SECTION("Group end with open") {
        zstring regex = "()";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE(lexer.get_next_token().type == TokenType::GROUP_START);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::GROUP_END);
        REQUIRE(t.lexeme == ")");
    }

    SECTION("Char class start") {
        zstring regex = "[";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::CHAR_CLASS_START);
        REQUIRE(t.lexeme == "[");
    }

    SECTION("Non-capturing group") {
        zstring regex = "(?:";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::GROUP_NONCAPTURE_START);
        REQUIRE(t.lexeme == "(?:");
    }

    SECTION("Positive lookahead") {
        zstring regex = "(?=";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LOOKAHEAD_POS_START);
        REQUIRE(t.lexeme == "(?=");
    }

    SECTION("Negative lookahead") {
        zstring regex = "(?!";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LOOKAHEAD_NEG_START);
        REQUIRE(t.lexeme == "(?!");
    }

    SECTION("Positive lookbehind") {
        zstring regex = "(?<=";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LOOKBEHIND_POS_START);
        REQUIRE(t.lexeme == "(?<=");
    }

    SECTION("Negative lookbehind") {
        zstring regex = "(?<!";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LOOKBEHIND_NEG_START);
        REQUIRE(t.lexeme == "(?<!");
    }

    SECTION("Named capture group") {
        zstring regex = "(?<name>";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::GROUP_NAMED_START);
        REQUIRE(std::get<zstring_view>(t.payload) == "name");
        REQUIRE(t.lexeme == "(?<name>");
    }

    SECTION("Char class escape \\d") {
        zstring regex = "\\d";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::CHAR_CLASS_ESCAPE);
        REQUIRE(std::get<uint32_t>(t.payload) == 'd');
        REQUIRE(t.lexeme == "\\d");
    }

    SECTION("Assertion \\b") {
        zstring regex = "\\b";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::ASSERTION);
        REQUIRE(std::get<uint32_t>(t.payload) == 'b');
        REQUIRE(t.lexeme == "\\b");
    }

    SECTION("Assertion \\B") {
        zstring regex = "\\B";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::ASSERTION);
        REQUIRE(std::get<uint32_t>(t.payload) == 'B');
        REQUIRE(t.lexeme == "\\B");
    }

    SECTION("Control escape sequence") {
        zstring regex = "\\cA";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 1);  // Ctrl+A
        REQUIRE(t.lexeme == "\\cA");
    }

    SECTION("Named backreference") {
        zstring regex = "\\k<name>(?<name>)";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::BACKREFERENCE);
        REQUIRE(std::get<uint32_t>(t.payload) == 1);
        REQUIRE(t.lexeme == "\\k<name>");
    }

    // Caveats
    SECTION("Hex fallback to literal") {
        zstring regex = "\\x4Z";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);

        Token t1 = lexer.get_next_token();
        REQUIRE(t1.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t1.payload) == static_cast<uint32_t>('x'));
        REQUIRE(t1.lexeme.length() == 2);

        Token t2 = lexer.get_next_token();
        REQUIRE(t2.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t2.payload) == static_cast<uint32_t>('4'));

        Token t3 = lexer.get_next_token();
        REQUIRE(t3.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t3.payload) == static_cast<uint32_t>('Z'));
    }

    SECTION("Control escape fallback") {
        zstring regex = "\\c1";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Group end unmatched") {
        zstring regex = ")";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Braced quantifier fallback {") {
        zstring regex = "{";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '{');
        REQUIRE(t.lexeme == "{");
    }

    SECTION("Braced quantifier fallback {,}") {
        zstring regex = "{,}";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '{');
        REQUIRE(t.lexeme == "{");
    }

    SECTION("Braced quantifier fallback {n") {
        zstring regex = "{1";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '{');
        REQUIRE(t.lexeme == "{");
    }

    SECTION("Braced quantifier fallback {n,") {
        zstring regex = "{1,";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '{');
        REQUIRE(t.lexeme == "{");
    }

    SECTION("Braced quantifier fallback {n,m") {
        zstring regex = "{1,2";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '{');
        REQUIRE(t.lexeme == "{");
    }

    SECTION("Braced quantifier fallback {n,mX") {
        zstring regex = "{1,2X";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '{');
        REQUIRE(t.lexeme == "{");
    }

    SECTION("Braced quantifier fallback {nX") {
        zstring regex = "{1X";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '{');
        REQUIRE(t.lexeme == "{");
    }

    SECTION("Unfinished special group (?") {
        zstring regex = "(?";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Invalid special group (?X") {
        zstring regex = "(?X";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Unfinished lookbehind (?<") {
        zstring regex = "(?<";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Unfinished named capture group (?<name") {
        zstring regex = "(?<name";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Invalid char in named capture group") {
        zstring regex = "(?<na-me>";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Empty named capture group") {
        zstring regex = "(?<>)";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Unfinished escape sequence \\") {
        zstring regex = "\\";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Hex escape sequence fallback \\xH") {
        zstring regex = "\\x4";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 'x');
        REQUIRE(t.lexeme == "\\x");

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '4');
        REQUIRE(t.lexeme == "4");
    }

    SECTION("Unicode escape sequence fallback \\uHH") {
        zstring regex = "\\u12";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 'u');
        REQUIRE(t.lexeme == "\\u");

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '1');
        REQUIRE(t.lexeme == "1");

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '2');
        REQUIRE(t.lexeme == "2");
    }

    SECTION("Unicode escape sequence fallback \\uG") {
        zstring regex = "\\uG";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 'u');
        REQUIRE(t.lexeme == "\\u");

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 'G');
        REQUIRE(t.lexeme == "G");
    }

    SECTION("Control escape fallback \\c") {
        zstring regex = "\\c";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Invalid control escape sequence") {
        zstring regex = "\\c1";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Unfinished named backreference \\k<") {
        zstring regex = "\\k<";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Invalid named backreference \\kname") {
        zstring regex = "\\kname";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Unclosed named backreference") {
        zstring regex = "\\k<name";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Empty named backreference") {
        zstring regex = "\\k<>";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Invalid char in named backreference") {
        zstring regex = "\\k<na-me>";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Octal escape \\8 is invalid") {
        zstring regex = "\\8";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Octal escape \\0 followed by non-octal") {
        zstring regex = "\\0A";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 0);
        REQUIRE(t.lexeme == "\\0");
        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 'A');
    }

    SECTION("In-class escape \\b") {
        zstring regex = "[\\b]";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);

        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::CHAR_CLASS_START);
        REQUIRE(t.lexeme == "[");

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 8);
        REQUIRE(t.lexeme == "\\b");

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::CHAR_CLASS_END);
        REQUIRE(t.lexeme == "]");
    }

    SECTION("In-class octal escape \\8 is literal 8") {
        zstring regex = "[\\8]";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        lexer.get_next_token();
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == '8');
        REQUIRE(t.lexeme == "\\8");
    }

    SECTION("Unclosed group") {
        zstring regex = "(";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE(lexer.get_next_token().type == TokenType::GROUP_START);
        REQUIRE(lexer.get_next_token().type == TokenType::END_OF_INPUT);
    }

    SECTION("Unclosed char class") {
        zstring regex = "[a-";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);
        REQUIRE(lexer.get_next_token().type == TokenType::CHAR_CLASS_START);
        REQUIRE(lexer.get_next_token().type == TokenType::LITERAL);
        REQUIRE(lexer.get_next_token().type == TokenType::CHAR_CLASS_RANGE);
        REQUIRE(lexer.get_next_token().type == TokenType::END_OF_INPUT);
    }

    // Complex regexes
    SECTION("Octal vs Backreference handling") {
        zstring regex1 = "\\1";
        std::unordered_map<zstring_view, uint32_t> map1;
        ECMALexer lexer1(regex1, map1);
        Token t1 = lexer1.get_next_token();
        REQUIRE(t1.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t1.payload) == 1);

        zstring regex2 = "(a)\\1";
        std::unordered_map<zstring_view, uint32_t> map2;
        ECMALexer lexer2(regex2, map2);

        REQUIRE(lexer2.get_next_token().type == TokenType::GROUP_START);
        Token t = lexer2.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(static_cast<unsigned char>(std::get<uint32_t>(t.payload)) == 'a');
        REQUIRE(lexer2.get_next_token().type == TokenType::GROUP_END);

        Token t_backref = lexer2.get_next_token();
        REQUIRE(t_backref.type == TokenType::BACKREFERENCE);
        REQUIRE(std::get<uint32_t>(t_backref.payload) == 1);

        // 4294967297 = 2^32 + 1 must not wrap to backreference \1 -- it is octal \42 followed by literals
        zstring regex3 = "(a)\\4294967297";
        std::unordered_map<zstring_view, uint32_t> map3;
        ECMALexer lexer3(regex3, map3);

        REQUIRE(lexer3.get_next_token().type == TokenType::GROUP_START);
        REQUIRE(lexer3.get_next_token().type == TokenType::LITERAL);
        REQUIRE(lexer3.get_next_token().type == TokenType::GROUP_END);
        Token t_octal = lexer3.get_next_token();
        REQUIRE(t_octal.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t_octal.payload) == '"');
        Token t_next = lexer3.get_next_token();
        REQUIRE(t_next.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t_next.payload) == '9');

        // \01 is never a backreference, even when group 1 exists -- it is octal U+0001; \08 is NUL followed by '8'
        zstring regex4 = "(a)\\01\\08";
        std::unordered_map<zstring_view, uint32_t> map4;
        ECMALexer lexer4(regex4, map4);

        REQUIRE(lexer4.get_next_token().type == TokenType::GROUP_START);
        REQUIRE(lexer4.get_next_token().type == TokenType::LITERAL);
        REQUIRE(lexer4.get_next_token().type == TokenType::GROUP_END);
        Token t_01 = lexer4.get_next_token();
        REQUIRE(t_01.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t_01.payload) == 1);
        Token t_08 = lexer4.get_next_token();
        REQUIRE(t_08.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t_08.payload) == 0);
        Token t_8 = lexer4.get_next_token();
        REQUIRE(t_8.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t_8.payload) == '8');
    }

    SECTION("Character classes") {
        zstring regex = "[^a-z]";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);

        REQUIRE(lexer.get_next_token().type == TokenType::CHAR_CLASS_START);

        Token t_neg = lexer.get_next_token();
        REQUIRE(t_neg.type == TokenType::CHAR_CLASS_NEGATION);

        Token t_a = lexer.get_next_token();
        REQUIRE(t_a.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t_a.payload) == static_cast<uint32_t>('a'));

        REQUIRE(lexer.get_next_token().type == TokenType::CHAR_CLASS_RANGE);

        Token t_z = lexer.get_next_token();
        REQUIRE(t_z.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t_z.payload) == static_cast<uint32_t>('z'));

        REQUIRE(lexer.get_next_token().type == TokenType::CHAR_CLASS_END);
        REQUIRE(lexer.get_next_token().type == TokenType::END_OF_INPUT);
    }

    SECTION("Complex multi-token match") {
        zstring regex = "^(?:a|b){1,2}$";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);

        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::ASSERTION);
        REQUIRE(std::get<uint32_t>(t.payload) == static_cast<uint32_t>('^'));

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::GROUP_NONCAPTURE_START);

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == static_cast<uint32_t>('a'));

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::ALTERNATION);

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == static_cast<uint32_t>('b'));

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::GROUP_END);

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::QUANTIFIER);
        REQUIRE(t.lexeme.length() == 5);

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::ASSERTION);
        REQUIRE(std::get<uint32_t>(t.payload) == static_cast<uint32_t>('$'));

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::END_OF_INPUT);
    }

    SECTION("Lookarounds and groups") {
        zstring regex = "(?<=a)(b)(?=c)";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);

        REQUIRE(lexer.get_next_token().type == TokenType::LOOKBEHIND_POS_START);
        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 'a');
        REQUIRE(lexer.get_next_token().type == TokenType::GROUP_END);

        REQUIRE(lexer.get_next_token().type == TokenType::GROUP_START);
        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 'b');
        REQUIRE(lexer.get_next_token().type == TokenType::GROUP_END);

        REQUIRE(lexer.get_next_token().type == TokenType::LOOKAHEAD_POS_START);
        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 'c');
        REQUIRE(lexer.get_next_token().type == TokenType::GROUP_END);

        REQUIRE(lexer.get_next_token().type == TokenType::END_OF_INPUT);
    }

    SECTION("Character class with escapes") {
        zstring regex = "[\\d\\sA-Z]";
        std::unordered_map<zstring_view, uint32_t> map;
        ECMALexer lexer(regex, map);

        REQUIRE(lexer.get_next_token().type == TokenType::CHAR_CLASS_START);

        Token t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::CHAR_CLASS_ESCAPE);
        REQUIRE(std::get<uint32_t>(t.payload) == 'd');

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::CHAR_CLASS_ESCAPE);
        REQUIRE(std::get<uint32_t>(t.payload) == 's');

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 'A');

        REQUIRE(lexer.get_next_token().type == TokenType::CHAR_CLASS_RANGE);

        t = lexer.get_next_token();
        REQUIRE(t.type == TokenType::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == 'Z');

        REQUIRE(lexer.get_next_token().type == TokenType::CHAR_CLASS_END);
        REQUIRE(lexer.get_next_token().type == TokenType::END_OF_INPUT);
    }
}

// =====================================================================
// PARSER TESTS
// =====================================================================

namespace smt::noodler::extended_regex::ecma::test {
    std::string parse_and_serialize(const zstring& regex) {
        return serialize(*ECMAParser(regex).parse());
    }

    // The ECMA word characters \w
    const std::string WORD = "(SET '0'-'9' 'A'-'Z' '_' 'a'-'z')";
    // \b = (?<=\w)(?!\w)|(?<!\w)(?=\w)
    const std::string WORD_BOUNDARY = "(DISJ (SEQ (ASSERT ?<= " + WORD + ") (ASSERT ?! " + WORD +
                                      "))"
                                      " (SEQ (ASSERT ?<! " +
                                      WORD + ") (ASSERT ?= " + WORD + ")))";
    // \B = (?<=\w)(?=\w)|(?<!\w)(?!\w)
    const std::string NOT_WORD_BOUNDARY = "(DISJ (SEQ (ASSERT ?<= " + WORD + ") (ASSERT ?= " + WORD +
                                          "))"
                                          " (SEQ (ASSERT ?<! " +
                                          WORD + ") (ASSERT ?! " + WORD + ")))";
    // The ECMA white space and line terminators \s
    const std::string WHITE_SPACE = R"((SET '\u{9}'-'\u{d}' ' ' '\u{a0}' '\u{1680}' '\u{2000}'-'\u{200a}')"
                                    R"( '\u{2028}'-'\u{2029}' '\u{202f}' '\u{205f}' '\u{3000}' '\u{feff}'))";
    // Any character except a line terminator
    const std::string DOT = R"((SET ^ '\u{a}' '\u{d}' '\u{2028}'-'\u{2029}'))";
}  // namespace smt::noodler::extended_regex::ecma::test

TEST_CASE("ECMA Regex Parser", "[noodler][ecma]") {
    using namespace smt::noodler::extended_regex::ecma;
    using namespace smt::noodler::extended_regex::ecma::test;

    SECTION("Literals and Concatenation") {
        REQUIRE(parse_and_serialize("a") == "(SEQ (LIT 'a'))");
        REQUIRE(parse_and_serialize("ab") == "(SEQ (LIT 'a') (LIT 'b'))");
        REQUIRE(parse_and_serialize("abc") == "(SEQ (LIT 'a') (LIT 'b') (LIT 'c'))");
    }

    SECTION("Dot and Escapes") {
        REQUIRE(parse_and_serialize(".") == "(SEQ " + DOT + ")");
        REQUIRE(parse_and_serialize("\\d") == "(SEQ (SET '0'-'9'))");
        REQUIRE(parse_and_serialize("\\D") == "(SEQ (SET ^ '0'-'9'))");
        REQUIRE(parse_and_serialize("\\s") == "(SEQ " + WHITE_SPACE + ")");
        REQUIRE(parse_and_serialize("\\w") == "(SEQ " + WORD + ")");
    }

    SECTION("Alternation (Disjunction)") {
        REQUIRE(parse_and_serialize("a|b") == "(DISJ (SEQ (LIT 'a')) (SEQ (LIT 'b')))");
        REQUIRE(parse_and_serialize("a|b|c") == "(DISJ (SEQ (LIT 'a')) (SEQ (LIT 'b')) (SEQ (LIT 'c')))");
        REQUIRE(parse_and_serialize("a|") == "(DISJ (SEQ (LIT 'a')) (SEQ))");
    }

    SECTION("Quantifiers") {
        REQUIRE(parse_and_serialize("a*") == "(SEQ (QUANT {0,inf} (LIT 'a')))");
        REQUIRE(parse_and_serialize("a+") == "(SEQ (QUANT {1,inf} (LIT 'a')))");
        REQUIRE(parse_and_serialize("a?") == "(SEQ (QUANT {0,1} (LIT 'a')))");
        REQUIRE(parse_and_serialize("a{3}") == "(SEQ (QUANT {3,3} (LIT 'a')))");
        REQUIRE(parse_and_serialize("a{3,}") == "(SEQ (QUANT {3,inf} (LIT 'a')))");
        REQUIRE(parse_and_serialize("a{3,5}") == "(SEQ (QUANT {3,5} (LIT 'a')))");
    }

    SECTION("Operator Precedence") {
        REQUIRE(parse_and_serialize("ab*") == "(SEQ (LIT 'a') (QUANT {0,inf} (LIT 'b')))");
        REQUIRE(parse_and_serialize("a|bc") == "(DISJ (SEQ (LIT 'a')) (SEQ (LIT 'b') (LIT 'c')))");
        REQUIRE(parse_and_serialize("a|b*") == "(DISJ (SEQ (LIT 'a')) (SEQ (QUANT {0,inf} (LIT 'b'))))");
    }

    SECTION("Groups (Normal, Non-capturing, Named)") {
        REQUIRE(parse_and_serialize("()") == "(SEQ (GROUP #1 (SEQ)))");
        REQUIRE(parse_and_serialize("(a)") == "(SEQ (GROUP #1 (SEQ (LIT 'a'))))");
        REQUIRE(parse_and_serialize("(ab)+") == "(SEQ (QUANT {1,inf} (GROUP #1 (SEQ (LIT 'a') (LIT 'b')))))");
        // Non-capturing groups are replaced by their subpatterns
        REQUIRE(parse_and_serialize("(?:a)") == "(SEQ (SEQ (LIT 'a')))");
        REQUIRE(parse_and_serialize("(?<foo>a)") == "(SEQ (GROUP #1 (SEQ (LIT 'a'))))");
    }

    SECTION("Assertions and Lookarounds") {
        REQUIRE(parse_and_serialize("^a$") == "(SEQ (ASSERT '^') (LIT 'a') (ASSERT '$'))");
        // Word boundaries are translated into lookarounds
        REQUIRE(parse_and_serialize("\\b") == "(SEQ " + WORD_BOUNDARY + ")");
        REQUIRE(parse_and_serialize("\\B") == "(SEQ " + NOT_WORD_BOUNDARY + ")");
        REQUIRE(parse_and_serialize("(?=a)") == "(SEQ (ASSERT ?= (SEQ (LIT 'a'))))");
        REQUIRE(parse_and_serialize("(?!a)") == "(SEQ (ASSERT ?! (SEQ (LIT 'a'))))");
        REQUIRE(parse_and_serialize("(?<=a)") == "(SEQ (ASSERT ?<= (SEQ (LIT 'a'))))");
        REQUIRE(parse_and_serialize("(?<!a)") == "(SEQ (ASSERT ?<! (SEQ (LIT 'a'))))");
    }

    SECTION("Character Classes") {
        REQUIRE(parse_and_serialize("[a]") == "(SEQ (LIT 'a'))");
        REQUIRE(parse_and_serialize("[^a]") == "(SEQ (SET ^ 'a'))");
        REQUIRE(parse_and_serialize("[a-z]") == "(SEQ (SET 'a'-'z'))");
        REQUIRE(parse_and_serialize("[a-zA-Z]") == "(SEQ (SET 'A'-'Z' 'a'-'z'))");
        REQUIRE(parse_and_serialize("[\\d\\s]") ==
                R"((SEQ (SET '\u{9}'-'\u{d}' ' ' '0'-'9' '\u{a0}' '\u{1680}' '\u{2000}'-'\u{200a}')"
                R"( '\u{2028}'-'\u{2029}' '\u{202f}' '\u{205f}' '\u{3000}' '\u{feff}')))");
        REQUIRE(parse_and_serialize("[^a-z\\d_]") == "(SEQ (SET ^ '0'-'9' '_' 'a'-'z'))");
        // Empty class matches nothing, negated empty class matches any character
        REQUIRE(parse_and_serialize("[]") == "(SEQ (SET))");
        REQUIRE(parse_and_serialize("[^]") == "(SEQ (SET ^))");
    }

    SECTION("Backreferences") {
        REQUIRE(parse_and_serialize("(a)\\1") == "(SEQ (GROUP #1 (SEQ (LIT 'a'))) (BACKREF 1))");
        REQUIRE(parse_and_serialize("(?<name>a)\\k<name>") == "(SEQ (GROUP #1 (SEQ (LIT 'a'))) (BACKREF 1))");
    }

    SECTION("Nested capturing groups") {
        REQUIRE(parse_and_serialize("((a))") == "(SEQ (GROUP #1 (SEQ (GROUP #2 (SEQ (LIT 'a'))))))");
    }

    SECTION("Nested non-capturing groups") {
        REQUIRE(parse_and_serialize("(?:(?:a))") == "(SEQ (SEQ (SEQ (LIT 'a'))))");
    }

    SECTION("Mixed nested groups with quantifiers") {
        REQUIRE(parse_and_serialize("(a(b+)c)*") == "(SEQ (QUANT {0,inf} (GROUP #1 (SEQ"
                                                    " (LIT 'a')"
                                                    " (GROUP #2 (SEQ (QUANT {1,inf} (LIT 'b'))))"
                                                    " (LIT 'c')"
                                                    "))))");
    }

    SECTION("Named group inside non-capturing group") {
        REQUIRE(parse_and_serialize("(?:(?<foo>a))") == "(SEQ (SEQ (GROUP #1 (SEQ (LIT 'a')))))");
    }

    SECTION("Quantifier on group with alternation inside") {
        REQUIRE(parse_and_serialize("(a|b)+") == "(SEQ (QUANT {1,inf} (GROUP #1 (DISJ"
                                                 " (SEQ (LIT 'a'))"
                                                 " (SEQ (LIT 'b'))"
                                                 "))))");
    }

    SECTION("Quantifier {n,m} on group") {
        REQUIRE(parse_and_serialize("(ab){2,4}") == "(SEQ (QUANT {2,4} (GROUP #1 (SEQ (LIT 'a') (LIT 'b')))))");
    }

    SECTION("Quantifier on character class") {
        REQUIRE(parse_and_serialize("[a-z]+") == "(SEQ (QUANT {1,inf} (SET 'a'-'z')))");
    }

    SECTION("Quantifier on dot") {
        REQUIRE(parse_and_serialize(".*") == "(SEQ (QUANT {0,inf} " + DOT + "))");
    }

    SECTION("Alternation with empty right branch") {
        REQUIRE(parse_and_serialize("a|") == "(DISJ (SEQ (LIT 'a')) (SEQ))");
    }

    SECTION("Alternation with empty left branch") {
        REQUIRE(parse_and_serialize("|a") == "(DISJ (SEQ) (SEQ (LIT 'a')))");
    }

    SECTION("Alternation inside a group") {
        REQUIRE(parse_and_serialize("(a|b|c)") == "(SEQ"
                                                  " (GROUP #1 (DISJ"
                                                  " (SEQ (LIT 'a'))"
                                                  " (SEQ (LIT 'b'))"
                                                  " (SEQ (LIT 'c'))"
                                                  "))"
                                                  ")");
    }

    SECTION("Nested alternation") {
        REQUIRE(parse_and_serialize("(a|b)|(c|d)") == "(DISJ"
                                                      " (SEQ (GROUP #1 (DISJ"
                                                      " (SEQ (LIT 'a'))"
                                                      " (SEQ (LIT 'b'))"
                                                      ")))"
                                                      " (SEQ (GROUP #2 (DISJ"
                                                      " (SEQ (LIT 'c'))"
                                                      " (SEQ (LIT 'd'))"
                                                      ")))"
                                                      ")");
    }

    SECTION("Word boundary in the middle of pattern") {
        REQUIRE(parse_and_serialize("a\\bb") == "(SEQ (LIT 'a') " + WORD_BOUNDARY + " (LIT 'b'))");
    }

    SECTION("Lookahead with quantified subpattern") {
        REQUIRE(parse_and_serialize("(?=a+)") == "(SEQ"
                                                 " (ASSERT ?= (SEQ"
                                                 " (QUANT {1,inf} (LIT 'a'))"
                                                 "))"
                                                 ")");
    }

    SECTION("Negative lookbehind with char class") {
        REQUIRE(parse_and_serialize("(?<![0-9])a") == "(SEQ"
                                                      " (ASSERT ?<! (SEQ"
                                                      " (SET '0'-'9')"
                                                      "))"
                                                      " (LIT 'a')"
                                                      ")");
    }

    SECTION("Lookahead followed by group") {
        REQUIRE(parse_and_serialize("(?=a)(b)") == "(SEQ"
                                                   " (ASSERT ?= (SEQ (LIT 'a')))"
                                                   " (GROUP #1 (SEQ (LIT 'b')))"
                                                   ")");
    }

    SECTION("Multiple assertions in sequence") {
        REQUIRE(parse_and_serialize("^\\ba$") == "(SEQ (ASSERT '^') " + WORD_BOUNDARY + " (LIT 'a') (ASSERT '$'))");
    }

    SECTION("Character class with multiple ranges") {
        REQUIRE(parse_and_serialize("[a-zA-Z0-9]") == "(SEQ (SET '0'-'9' 'A'-'Z' 'a'-'z'))");
    }

    SECTION("Negated class with escape and range") {
        REQUIRE(parse_and_serialize("[^\\w0-9]") == "(SEQ (SET ^ '0'-'9' 'A'-'Z' '_' 'a'-'z'))");
    }

    SECTION("Character class with single char and range") {
        REQUIRE(parse_and_serialize("[_a-z]") == "(SEQ (SET '_' 'a'-'z'))");
    }

    SECTION("Multiple numeric backreferences") {
        REQUIRE(parse_and_serialize("(a)(b)\\1\\2") == "(SEQ"
                                                       " (GROUP #1 (SEQ (LIT 'a')))"
                                                       " (GROUP #2 (SEQ (LIT 'b')))"
                                                       " (BACKREF 1)"
                                                       " (BACKREF 2)"
                                                       ")");
    }

    SECTION("Named backreference after named group") {
        REQUIRE(parse_and_serialize("(?<word>[a-z]+)\\k<word>") == "(SEQ"
                                                                   " (GROUP #1 (SEQ (QUANT {1,inf} (SET 'a'-'z'))))"
                                                                   " (BACKREF 1)"
                                                                   ")");
    }

    SECTION("Simple email-like pattern") {
        REQUIRE(parse_and_serialize("[a-z]+@[a-z]+\\.[a-z]+") == "(SEQ"
                                                                 " (QUANT {1,inf} (SET 'a'-'z'))"
                                                                 " (LIT '@')"
                                                                 " (QUANT {1,inf} (SET 'a'-'z'))"
                                                                 " (LIT '.')"
                                                                 " (QUANT {1,inf} (SET 'a'-'z'))"
                                                                 ")");
    }

    SECTION("IP address octet pattern") {
        REQUIRE(parse_and_serialize("(25[0-5]|2[0-4][0-9]|[01]?[0-9]{1,2})") ==
                "(SEQ"
                " (GROUP #1 (DISJ"
                " (SEQ (LIT '2') (LIT '5') (SET '0'-'5'))"
                " (SEQ (LIT '2') (SET '0'-'4') (SET '0'-'9'))"
                " (SEQ"
                " (QUANT {0,1} (SET '0'-'1'))"
                " (QUANT {1,2} (SET '0'-'9'))"
                ")"
                "))"
                ")");
    }

    SECTION("Hex color pattern") {
        REQUIRE(parse_and_serialize("#([0-9a-fA-F]{3}|[0-9a-fA-F]{6})") ==
                "(SEQ"
                " (LIT '#')"
                " (GROUP #1 (DISJ"
                " (SEQ (QUANT {3,3} (SET '0'-'9' 'A'-'F' 'a'-'f')))"
                " (SEQ (QUANT {6,6} (SET '0'-'9' 'A'-'F' 'a'-'f')))"
                "))"
                ")");
    }

    SECTION("Date pattern with named groups") {
        REQUIRE(parse_and_serialize("(?<year>\\d{4})-(?<month>\\d{2})-(?<day>\\d{2})") ==
                "(SEQ"
                " (GROUP #1 (SEQ (QUANT {4,4} (SET '0'-'9'))))"
                " (LIT '-')"
                " (GROUP #2 (SEQ (QUANT {2,2} (SET '0'-'9'))))"
                " (LIT '-')"
                " (GROUP #3 (SEQ (QUANT {2,2} (SET '0'-'9'))))"
                ")");
    }

    SECTION("URL path segment with lookahead") {
        REQUIRE(parse_and_serialize("(?<=/)([a-z0-9\\-]+)(?=/)") ==
                "(SEQ"
                " (ASSERT ?<= (SEQ (LIT '/')))"
                " (GROUP #1 (SEQ (QUANT {1,inf} (SET '-' '0'-'9' 'a'-'z'))))"
                " (ASSERT ?= (SEQ (LIT '/')))"
                ")");
    }

    SECTION("Quantifier without preceding atom throws") {
        REQUIRE_THROWS(parse_and_serialize("*"));
        REQUIRE_THROWS(parse_and_serialize("+"));
        REQUIRE_THROWS(parse_and_serialize("?"));
    }

    SECTION("Unclosed group throws") {
        REQUIRE_THROWS(parse_and_serialize("(a"));
        REQUIRE_THROWS(parse_and_serialize("(?:a"));
    }

    SECTION("Unmatched closing paren throws") {
        REQUIRE_THROWS(parse_and_serialize(")"));
        REQUIRE_THROWS(parse_and_serialize("a)"));
    }

    SECTION("Character range out of order throws") {
        REQUIRE_THROWS(parse_and_serialize("[z-a]"));
        REQUIRE_THROWS(parse_and_serialize("[9-0]"));
    }

    SECTION("Character class as range bound throws") {
        REQUIRE_THROWS(parse_and_serialize("[\\w-z]"));
        REQUIRE_THROWS(parse_and_serialize("[a-\\d]"));
        REQUIRE_THROWS(parse_and_serialize("[\\d--]"));
    }

    SECTION("Crazy character class") {
        // The class consists of ']', '-'-'/', 'a'-'z', '^', '\b'-'-', '\0'-'\37' and '\cZ'
        REQUIRE(parse_and_serialize(R"([^\]\--/a-z^\b--\0-\37\cZ])") ==
                R"((SEQ (SET ^ '\u{0}'-'/' ']'-'^' 'a'-'z')))");
    }
}

// =====================================================================
// RCG SERIALIZATION HELPERS
// =====================================================================

namespace smt::noodler::extended_regex::ecma::test {
    // Converts a Z3 app_ref to a normalized string (collapses whitespace, removes newlines).
    std::string app_to_string(const app_ref& app, ast_manager& m) {
        return to_single_line_string(app.get(), m);
    }

    std::string build_and_serialize_rcg(const zstring& regex, ast_manager& m) {
        theory_str_noodler_params params;
        params.m_ecma_engine_semantics = true;
        RegexConstraintBuilder builder(m, symbol("ecma2020"), regex, params);
        return serialize_rcg(builder.build_rcg(), m);
    }
}  // namespace smt::noodler::extended_regex::ecma::test

// =====================================================================
// SERIALIZED RCG TESTS  (end-to-end: regex string -> RCG -> serialized string)
// =====================================================================

TEST_CASE("ECMA Regex serialized RCG tests", "[noodler][ecma]") {
    using Catch::Matchers::ContainsSubstring;
    using namespace smt::noodler::extended_regex;
    using namespace smt::noodler::extended_regex::ecma;
    using namespace smt::noodler::extended_regex::ecma::test;

    ast_manager m;
    reg_decl_plugins(m);

    // ---- Basic cases ----

    SECTION("Single literal") {
        REQUIRE(build_and_serialize_rcg("a", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re \"a\")]) (EDGE *->* [MATCH re.all]))");
    }

    SECTION("Capture group with markers") {
        REQUIRE(build_and_serialize_rcg("(a)", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re \"a\")]) (EDGE *->* [MATCH re.all]))");
    }

    SECTION("Non-capturing group") {
        // Non-capturing groups are transparent — no STARTS/ENDS markers.
        REQUIRE(build_and_serialize_rcg("(?:a)", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re \"a\")]) (EDGE *->* [MATCH re.all]))");
    }

    SECTION("Numeric backreference") {
        REQUIRE(build_and_serialize_rcg("(a)\\1", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1}) (EDGE *->* "
                "[BACKREF 1]) (EDGE *->* [MATCH re.all]))");
    }

    SECTION("Named capture group and named backreference") {
        // Named groups are translated to numeric groups internally.
        REQUIRE(build_and_serialize_rcg("(?<foo>a)\\k<foo>", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1}) (EDGE *->* "
                "[BACKREF 1]) (EDGE *->* [MATCH re.all]))");
    }

    // ---- Anchors ----

    SECTION("Anchors ^a$") {
        REQUIRE(build_and_serialize_rcg("^a$", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [ANCHOR '^']) (EDGE *->* [MATCH (str.to_re \"a\")]) (EDGE "
                "*->* [ANCHOR '$']) (EDGE *->* [MATCH re.all]))");
    }

    // ---- Alternation ----

    SECTION("Alternation without groups") {
        REQUIRE(build_and_serialize_rcg("a|b", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (re.union (str.to_re \"a\") (str.to_re \"b\"))]) "
                "(EDGE *->* [MATCH re.all]))");
    }

    SECTION("Alternation with capture groups") {
        REQUIRE(build_and_serialize_rcg("(a)|(b)", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (re.union (str.to_re \"a\") (str.to_re \"b\"))]) "
                "(EDGE *->* [MATCH re.all]))");
    }

    // ---- Sequential and nested groups ----

    SECTION("Sequential capture groups") {
        REQUIRE(build_and_serialize_rcg("(a)(b)(c)", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (re.++ (re.++ (str.to_re \"a\") (str.to_re \"b\")) "
                "(str.to_re \"c\"))]) (EDGE *->* [MATCH re.all]))");
    }

    SECTION("Complex nested groups and multiple backreferences") {
        REQUIRE(build_and_serialize_rcg(R"(((a)(b))\1\2\3)", m) ==
                "(RCG"
                " (EDGE *->* [MATCH re.all])"
                " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {2,1} ENDS {2})"
                " (EDGE *->* [MATCH (str.to_re \"b\")] STARTS {3} ENDS {3,1})"
                " (EDGE *->* [BACKREF 1])"
                " (EDGE *->* [BACKREF 2])"
                " (EDGE *->* [BACKREF 3])"
                " (EDGE *->* [MATCH re.all])"
                ")");
    }

    // ---- Regular lookarounds ----

    SECTION("Positive lookahead (regular)") {
        REQUIRE(build_and_serialize_rcg("(?=a)", m) == "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [LOOKAROUND ?= "
                                                       "(str.to_re \"a\")]) (EDGE *->* [MATCH re.all]))");
    }

    SECTION("Negative lookahead (regular)") {
        REQUIRE(build_and_serialize_rcg("(?!a)", m) == "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [LOOKAROUND ?! "
                                                       "(str.to_re \"a\")]) (EDGE *->* [MATCH re.all]))");
    }

    SECTION("Positive lookbehind (regular)") {
        REQUIRE(build_and_serialize_rcg("(?<=a)", m) == "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [LOOKAROUND ?<= "
                                                        "(str.to_re \"a\")]) (EDGE *->* [MATCH re.all]))");
    }

    SECTION("Negative lookbehind (regular)") {
        REQUIRE(build_and_serialize_rcg("(?<!a)", m) == "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [LOOKAROUND ?<! "
                                                        "(str.to_re \"a\")]) (EDGE *->* [MATCH re.all]))");
    }

    // ---- Non-regular lookarounds ----

    SECTION("Positive lookahead containing capture group (non-regular)") {
        // (?=(a)) — the lookahead contains a capture group, making its subregex non-regular.
        REQUIRE(build_and_serialize_rcg("(?=(a))", m) == "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [LOOKAROUND ?= "
                                                         "(str.to_re \"a\")]) (EDGE *->* [MATCH re.all]))");
    }

    SECTION("Positive lookahead with capture group and backreference inside") {
        // (?=(a)\1) — the lookahead captures group 1 and \1 inside the same lookahead references it.
        REQUIRE(build_and_serialize_rcg("(?=(a)\\1)", m) == "(RCG"
                                                            " (EDGE *->* [MATCH re.all])"
                                                            " (EDGE *->* [LOOKAROUND ?= (FRAGMENT"
                                                            " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1})"
                                                            " (EDGE *->* [BACKREF 1])"
                                                            " (EDGE *->* [MATCH re.all]))])"
                                                            " (EDGE *->* [MATCH re.all])"
                                                            ")");
    }

    SECTION("Positive lookbehind containing capture group (non-regular)") {
        // (?<=(a)) — lookbehind with capture group.
        REQUIRE(build_and_serialize_rcg("(?<=(a))", m) == "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [LOOKAROUND ?<= "
                                                          "(str.to_re \"a\")]) (EDGE *->* [MATCH re.all]))");
    }

    // ---- Word boundaries ----

    SECTION("Word boundary assertion (\\b)") {
        const std::string rcg_dump = build_and_serialize_rcg("\\b", m);
        // \b expands to two branches: (?<=\w)(?!\w)  |  (?<!\w)(?=\w).
        REQUIRE_THAT(rcg_dump, ContainsSubstring("[LOOKAROUND ?<= "));
        REQUIRE_THAT(rcg_dump, ContainsSubstring("[LOOKAROUND ?! "));
        REQUIRE_THAT(rcg_dump, ContainsSubstring("[LOOKAROUND ?<! "));
        REQUIRE_THAT(rcg_dump, ContainsSubstring("[LOOKAROUND ?= "));
    }

    SECTION("Negated word boundary assertion (\\B)") {
        const std::string rcg_dump = build_and_serialize_rcg("\\B", m);
        // \B is the negation of \b -- same lookaround types, opposite polarity.
        REQUIRE_THAT(rcg_dump, ContainsSubstring("[LOOKAROUND ?<= "));
        REQUIRE_THAT(rcg_dump, ContainsSubstring("[LOOKAROUND ?= "));
        REQUIRE_THAT(rcg_dump, ContainsSubstring("[LOOKAROUND ?<! "));
        REQUIRE_THAT(rcg_dump, ContainsSubstring("[LOOKAROUND ?! "));
    }

    // ---- Greedy merge / interleaving ----

    SECTION("Mix of regular sequence and backreference") {
        // (x)ab\1cd — 'ab' and 'cd' are each merged into a single MATCH edge.
        REQUIRE(build_and_serialize_rcg("(x)ab\\1cd", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re \"x\")] STARTS {1} ENDS {1}) (EDGE *->* "
                "[MATCH (str.to_re \"ab\")]) (EDGE *->* [BACKREF 1]) (EDGE *->* [MATCH (str.to_re \"cd\")]) (EDGE *->* "
                "[MATCH re.all]))");
    }

    SECTION("Alternation of regular and non-regular components") {
        // (x)|a|\1 — two MATCH edges and one BACKREF edge in parallel.
        REQUIRE(build_and_serialize_rcg("(x)|a|\\1", m) == "(RCG"
                                                           " (EDGE *->* [MATCH re.all])"
                                                           " (EDGE *->* [MATCH (str.to_re \"x\")] STARTS {1} ENDS {1})"
                                                           " (EDGE *->* [BACKREF 1])"
                                                           " (EDGE *->* [MATCH (str.to_re \"a\")])"
                                                           " (EDGE *->* [MATCH re.all])"
                                                           ")");
    }

    // ---- Complex patterns ----

    SECTION("Complex: Nested groups inside alternation with backreference") {
        REQUIRE(build_and_serialize_rcg("^((a)|(b))\\1$", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [ANCHOR '^']) (EDGE *->* [MATCH (re.union (str.to_re "
                "\"a\") (str.to_re \"b\"))] STARTS {1} ENDS {1}) (EDGE *->* [BACKREF 1]) (EDGE *->* [ANCHOR '$']) "
                "(EDGE *->* [MATCH re.all]))");
    }

    SECTION("Complex: HTML-like tag matching with interrupted greedy merge") {
        REQUIRE(build_and_serialize_rcg("<(?<tag>x)>y\\k<tag>", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re \"<\")]) (EDGE *->* [MATCH (str.to_re "
                "\"x\")] STARTS {1} ENDS {1}) (EDGE *->* [MATCH (str.to_re \">y\")]) (EDGE *->* [BACKREF 1]) (EDGE "
                "*->* [MATCH re.all]))");
    }

    SECTION("Final Boss 1: Perfect BFS interleaving of parallel complex branches") {
        REQUIRE(build_and_serialize_rcg("^(?<v1>a)x(?=y)\\1$|^(?<v2>b)z(?<!w)\\2$", m) ==
                "(RCG"
                " (EDGE *->* [MATCH re.all])"
                " (EDGE *->* [ANCHOR '^'])"
                " (EDGE *->* [ANCHOR '^'])"
                " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1})"
                " (EDGE *->* [MATCH (str.to_re \"b\")] STARTS {2} ENDS {2})"
                " (EDGE *->* [MATCH (str.to_re \"x\")])"
                " (EDGE *->* [MATCH (str.to_re \"z\")])"
                " (EDGE *->* [LOOKAROUND ?= (str.to_re \"y\")])"
                " (EDGE *->* [LOOKAROUND ?<! (str.to_re \"w\")])"
                " (EDGE *->* [BACKREF 1])"
                " (EDGE *->* [BACKREF 2])"
                " (EDGE *->* [ANCHOR '$'])"
                " (EDGE *->* [ANCHOR '$'])"
                " (EDGE *->* [MATCH re.all])"
                ")");
    }

    SECTION("Final Boss 2: Greedy merge boundaries with non-capturing groups and named refs") {
        REQUIRE(build_and_serialize_rcg("^a(?:b|c)(?<named>d)\\k<named>(?=e)\\1f$", m) ==
                "(RCG"
                " (EDGE *->* [MATCH re.all])"
                " (EDGE *->* [ANCHOR '^'])"
                // Non-capturing group content merges greedily with the leading 'a'
                " (EDGE *->* [MATCH (re.++ (str.to_re \"a\") (re.union (str.to_re \"b\") (str.to_re \"c\")))])"
                // Named capture group gets its own edge
                " (EDGE *->* [MATCH (str.to_re \"d\")] STARTS {1} ENDS {1})"
                " (EDGE *->* [BACKREF 1])"
                " (EDGE *->* [LOOKAROUND ?= (str.to_re \"e\")])"
                " (EDGE *->* [BACKREF 1])"
                " (EDGE *->* [MATCH (str.to_re \"f\")])"
                " (EDGE *->* [ANCHOR '$'])"
                " (EDGE *->* [MATCH re.all])"
                ")");
    }

    // ---- Bounded quantifiers over non-regular subpatterns ----

    SECTION("Unrolled iterations with capture group reset the captures") {
        REQUIRE(build_and_serialize_rcg("(?:(a)|b){2}\\1", m) ==
                "(RCG"
                " (EDGE *->* [MATCH re.all])"
                " (EDGE *->* [EPSILON] RESETS {1})"
                " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1})"
                " (EDGE *->* [MATCH (str.to_re \"b\")])"
                " (EDGE *->* [EPSILON] RESETS {1})"
                " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1})"
                " (EDGE *->* [MATCH (str.to_re \"b\")])"
                " (EDGE *->* [BACKREF 1])"
                " (EDGE *->* [MATCH re.all])"
                ")");
    }

    SECTION("Optional iteration with capture group must be nonempty") {
        REQUIRE(build_and_serialize_rcg("(?:(a)|b)?\\1", m) ==
                "(RCG"
                " (EDGE *->* [MATCH re.all])"
                " (EDGE *->* [EPSILON] RESETS {1})"
                // Zero iterations
                " (EDGE *->* [MATCH (str.to_re \"\")])"
                " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1})"
                " (EDGE *->* [MATCH (str.to_re \"b\")])"
                " (EDGE *->* [BACKREF 1])"
                " (EDGE *->* [EPSILON] NONEMPTY)"
                " (EDGE *->* [MATCH re.all])"
                ")");
    }

    SECTION("Unrolled iterations without capture group have no iteration edges") {
        REQUIRE(build_and_serialize_rcg("(a)(?:b\\1){2}", m) ==
                "(RCG"
                " (EDGE *->* [MATCH re.all])"
                " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1})"
                " (EDGE *->* [MATCH (str.to_re \"b\")])"
                " (EDGE *->* [BACKREF 1])"
                " (EDGE *->* [MATCH (str.to_re \"b\")])"
                " (EDGE *->* [BACKREF 1])"
                " (EDGE *->* [MATCH re.all])"
                ")");
    }

    SECTION("Zero iterations of non-regular subpattern stay regular") {
        REQUIRE(build_and_serialize_rcg("(?:(a)\\1){0}", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re \"\")]) (EDGE *->* [MATCH re.all]))");
    }

    // ---- Captures inside lookarounds ----

    SECTION("Backreference outside the lookaround of its capture group is unsupported") {
        REQUIRE_THROWS(build_and_serialize_rcg("^(?=(a))\\1b$", m));
        REQUIRE_THROWS(build_and_serialize_rcg("^a(?<=(a))\\1$", m));
        REQUIRE_THROWS(build_and_serialize_rcg("(?=(a))(?=\\1)", m));
        REQUIRE_THROWS(build_and_serialize_rcg("(?=(?=(a))\\1)", m));
    }

    SECTION("Backreference inside the lookaround of its capture group is supported") {
        REQUIRE_NOTHROW(build_and_serialize_rcg("(?=(a)\\1)", m));
        REQUIRE_NOTHROW(build_and_serialize_rcg("(?=(?=(a)\\1))", m));
        REQUIRE_NOTHROW(build_and_serialize_rcg("(a)(?=\\1)", m));
        REQUIRE_NOTHROW(build_and_serialize_rcg("^(a)b(?<=\\1b)$", m));
        REQUIRE_NOTHROW(build_and_serialize_rcg("(?<=(?=(a)\\1))", m));
    }

    SECTION("Backreference to a capture group inside a lookbehind is unsupported") {
        // Lookbehinds are matched from right to left
        REQUIRE_THROWS(build_and_serialize_rcg("^ba(?<=\\1(a))$", m));
        REQUIRE_THROWS(build_and_serialize_rcg("^a(?<=(a)\\1)$", m));
        REQUIRE_THROWS(build_and_serialize_rcg("(?<=(a)(?=\\1))", m));
    }
}

// =====================================================================
// CONSTRAINT GENERATION – UNIT TESTS
// =====================================================================

TEST_CASE("ECMA Regex constraint generation", "[noodler][ecma]") {
    using namespace smt::noodler::extended_regex;
    using namespace smt::noodler::extended_regex::ecma;
    using namespace smt::noodler::extended_regex::ecma::test;

    ast_manager m;
    reg_decl_plugins(m);
    seq_util util_s(m);
    const app_ref x(m.mk_const("x", util_s.mk_string_sort()), m);
    theory_str_noodler_params params;

    // Regular patterns must not introduce fresh variables, otherwise the negative axiom becomes quantified (#495)
    SECTION("Regular pattern generates a plain membership") {
        RegexConstraintBuilder builder(m, symbol("ecma2020"), zstring("a|b"), params);
        builder.build_rcg();
        const expr_ref formula = builder.generate_constraints(x);
        REQUIRE(builder.get_fresh_vars().empty());
        REQUIRE(app_to_string(app_ref(to_app(formula), m), m) ==
                "(str.in_re x (re.union (str.to_re \"a\") (str.to_re \"b\")))");
    }

    SECTION("Regular pattern with engine semantics generates a membership in Sigma* R Sigma*") {
        params.m_ecma_engine_semantics = true;
        RegexConstraintBuilder builder(m, symbol("ecma2020"), zstring("a"), params);
        builder.build_rcg();
        const expr_ref formula = builder.generate_constraints(x);
        REQUIRE(builder.get_fresh_vars().empty());
        REQUIRE(app_to_string(app_ref(to_app(formula), m), m) ==
                "(str.in_re x (re.++ re.all (re.++ (str.to_re \"a\") re.all)))");
    }

    SECTION("Regular pattern with an unreferenced capture group generates a plain membership") {
        RegexConstraintBuilder builder(m, symbol("ecma2020"), zstring("(a)b"), params);
        builder.build_rcg();
        const expr_ref formula = builder.generate_constraints(x);
        REQUIRE(builder.get_fresh_vars().empty());
        REQUIRE(util_s.str.is_in_re(formula));
    }

    SECTION("Pattern with a backreference introduces fresh variables") {
        RegexConstraintBuilder builder(m, symbol("ecma2020"), zstring("(a)\\1"), params);
        builder.build_rcg();
        const expr_ref formula = builder.generate_constraints(x);
        REQUIRE(!builder.get_fresh_vars().empty());
        REQUIRE(!util_s.str.is_in_re(formula));
    }
}

// Zero-width assertions consume no text, so no fresh variable is created for them (#507)
TEST_CASE("ECMA Regex constraint generation for zero-width assertions", "[noodler][ecma]") {
    using namespace smt::noodler::extended_regex;
    using namespace smt::noodler::extended_regex::ecma;
    using namespace smt::noodler::extended_regex::ecma::test;

    ast_manager m;
    reg_decl_plugins(m);
    seq_util util_s(m);
    const app_ref x(m.mk_const("x", util_s.mk_string_sort()), m);
    theory_str_noodler_params params;

    SECTION("Anchors do not introduce fresh variables") {
        RegexConstraintBuilder builder(m, symbol("ecma2020"), zstring("^(a)\\1$"), params);
        builder.build_rcg();
        const expr_ref formula = builder.generate_constraints(x);
        REQUIRE(builder.get_fresh_vars().size() == 2);
        REQUIRE(app_to_string(app_ref(to_app(formula), m), m) ==
                "(and (= \"\" \"\")"
                " (str.in_re regex!0 (str.to_re \"a\"))"
                " (= regex!1 regex!0)"
                " (= (str.++ regex!0 regex!1) x)"
                " (= x (str.++ regex!0 regex!1)))");
    }

    SECTION("Lookahead constrains the suffix after its position") {
        RegexConstraintBuilder builder(m, symbol("ecma2020"), zstring("a(?=b)c"), params);
        builder.build_rcg();
        const expr_ref formula = builder.generate_constraints(x);
        REQUIRE(builder.get_fresh_vars().size() == 3);
        REQUIRE(app_to_string(app_ref(to_app(formula), m), m) ==
                "(and (str.in_re regex!0 (str.to_re \"a\"))"
                " (str.in_re regex!1 (str.to_re \"c\"))"
                " (= regex!2 regex!1)"
                " (str.in_re regex!2 (re.++ (str.to_re \"b\") re.all))"
                " (= x (str.++ regex!0 regex!1)))");
    }
}

// Language (dis)equations compare regular patterns as classical regexes, other patterns cannot be compared (#521)
TEST_CASE("ECMA Regex translation to classical regexes", "[noodler][ecma]") {
    using namespace smt::noodler::extended_regex;
    using namespace smt::noodler::extended_regex::ecma;
    using namespace smt::noodler::extended_regex::ecma::test;

    ast_manager m;
    reg_decl_plugins(m);
    seq_util util_s(m);
    theory_str_noodler_params params;

    SECTION("Regular pattern is replaced by its regex") {
        const expr_ref regex =
            to_classical_regex(util_s.re.mk_from_regex(symbol("ecma2020"), zstring("a|b")), m, params);
        REQUIRE(regex);
        REQUIRE(app_to_string(app_ref(to_app(regex), m), m) == "(re.union (str.to_re \"a\") (str.to_re \"b\"))");
    }

    SECTION("Regular pattern with engine semantics is replaced by Sigma* R Sigma*") {
        params.m_ecma_engine_semantics = true;
        const expr_ref regex =
            to_classical_regex(util_s.re.mk_from_regex(symbol("ecma2020"), zstring("a")), m, params);
        REQUIRE(regex);
        REQUIRE(app_to_string(app_ref(to_app(regex), m), m) == "(re.++ re.all (re.++ (str.to_re \"a\") re.all))");
    }

    SECTION("Pattern with a backreference is not translated") {
        REQUIRE(!to_classical_regex(util_s.re.mk_from_regex(symbol("ecma2020"), zstring("(a)\\1")), m, params));
    }

    SECTION("Pattern with anchors is not translated") {
        REQUIRE(!to_classical_regex(util_s.re.mk_from_regex(symbol("ecma2020"), zstring("^a$")), m, params));
    }

    SECTION("Pattern nested in another regex operation is replaced") {
        const app_ref nested(util_s.re.mk_union(util_s.re.mk_from_regex(symbol("ecma2020"), zstring("a")),
                                                util_s.re.mk_to_re(util_s.str.mk_string(zstring("b")))),
                             m);
        const expr_ref regex = to_classical_regex(nested, m, params);
        REQUIRE(regex);
        REQUIRE(app_to_string(app_ref(to_app(regex), m), m) == "(re.union (str.to_re \"a\") (str.to_re \"b\"))");
    }

    SECTION("Regex without patterns is not changed") {
        const app_ref classical(util_s.re.mk_star(util_s.re.mk_to_re(util_s.str.mk_string(zstring("a")))), m);
        REQUIRE(to_classical_regex(classical, m, params).get() == classical.get());
    }
}
