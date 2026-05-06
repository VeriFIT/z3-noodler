#include "smt/theory_str_noodler/ecma_regex.h"

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"

#include <algorithm>
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>
#include <queue>
#include <sstream>

// =====================================================================
// LEXER TESTS
// =====================================================================

TEST_CASE("ECMA Regex Lexer", "[noodler][ecma]") {
    using namespace smt::noodler::ecma;

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
        REQUIRE(range.max == std::numeric_limits<uint32_t>::max());
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

namespace smt::noodler::ecma::test {
    zstring parse_and_serialize(const zstring& regex) {
        using namespace smt::noodler::ecma;
        ECMAParser parser(regex);
        const ASTNodeRef root = parser.parse();
        return root->serialize();
    }
}  // namespace smt::noodler::ecma::test

TEST_CASE("ECMA Regex Parser", "[noodler][ecma]") {
    using namespace smt::noodler::ecma;
    using namespace smt::noodler::ecma::test;

    SECTION("Literals and Concatenation") {
        REQUIRE(parse_and_serialize("a") == zstring("(SEQ (LIT 'a'))"));
        REQUIRE(parse_and_serialize("ab") == zstring("(SEQ (LIT 'a') (LIT 'b'))"));
        REQUIRE(parse_and_serialize("abc") == zstring("(SEQ (LIT 'a') (LIT 'b') (LIT 'c'))"));
    }

    SECTION("Dot and Escapes") {
        REQUIRE(parse_and_serialize(".") == zstring("(SEQ (DOT))"));
        REQUIRE(parse_and_serialize("\\d") == zstring("(SEQ (CLASS (CHAR_CLASS 'd')))"));
        REQUIRE(parse_and_serialize("\\s") == zstring("(SEQ (CLASS (CHAR_CLASS 's')))"));
        REQUIRE(parse_and_serialize("\\w") == zstring("(SEQ (CLASS (CHAR_CLASS 'w')))"));
    }

    SECTION("Alternation (Disjunction)") {
        REQUIRE(parse_and_serialize("a|b") == zstring("(DISJ (SEQ (LIT 'a')) (SEQ (LIT 'b')))"));
        REQUIRE(parse_and_serialize("a|b|c") == zstring("(DISJ (SEQ (LIT 'a')) (SEQ (LIT 'b')) (SEQ (LIT 'c')))"));
        REQUIRE(parse_and_serialize("a|") == zstring("(DISJ (SEQ (LIT 'a')) (SEQ))"));
    }

    SECTION("Quantifiers") {
        REQUIRE(parse_and_serialize("a*") == zstring("(SEQ (QUANT {0,inf} (LIT 'a')))"));
        REQUIRE(parse_and_serialize("a+") == zstring("(SEQ (QUANT {1,inf} (LIT 'a')))"));
        REQUIRE(parse_and_serialize("a?") == zstring("(SEQ (QUANT {0,1} (LIT 'a')))"));
        REQUIRE(parse_and_serialize("a{3}") == zstring("(SEQ (QUANT {3,3} (LIT 'a')))"));
        REQUIRE(parse_and_serialize("a{3,}") == zstring("(SEQ (QUANT {3,inf} (LIT 'a')))"));
        REQUIRE(parse_and_serialize("a{3,5}") == zstring("(SEQ (QUANT {3,5} (LIT 'a')))"));
    }

    SECTION("Operator Precedence") {
        REQUIRE(parse_and_serialize("ab*") == zstring("(SEQ (LIT 'a') (QUANT {0,inf} (LIT 'b')))"));
        REQUIRE(parse_and_serialize("a|bc") == zstring("(DISJ (SEQ (LIT 'a')) (SEQ (LIT 'b') (LIT 'c')))"));
        REQUIRE(parse_and_serialize("a|b*") == zstring("(DISJ (SEQ (LIT 'a')) (SEQ (QUANT {0,inf} (LIT 'b'))))"));
    }

    SECTION("Groups (Normal, Non-capturing, Named)") {
        REQUIRE(parse_and_serialize("()") == zstring("(SEQ (GROUP #1 (SEQ)))"));
        REQUIRE(parse_and_serialize("(a)") == zstring("(SEQ (GROUP #1 (SEQ (LIT 'a'))))"));
        REQUIRE(parse_and_serialize("(ab)+") == zstring("(SEQ (QUANT {1,inf} (GROUP #1 (SEQ (LIT 'a') (LIT 'b')))))"));
        REQUIRE(parse_and_serialize("(?:a)") == zstring("(SEQ (GROUP-NONCAP (SEQ (LIT 'a'))))"));
        REQUIRE(parse_and_serialize("(?<foo>a)") == zstring("(SEQ (GROUP #1 (SEQ (LIT 'a'))))"));
    }

    SECTION("Assertions and Lookarounds") {
        REQUIRE(parse_and_serialize("^a$") == zstring("(SEQ (ASSERT '^') (LIT 'a') (ASSERT '$'))"));
        REQUIRE(parse_and_serialize("\\b") == zstring("(SEQ (ASSERT 'b'))"));
        REQUIRE(parse_and_serialize("\\B") == zstring("(SEQ (ASSERT 'B'))"));
        REQUIRE(parse_and_serialize("(?=a)") == zstring("(SEQ (ASSERT ?= (SEQ (LIT 'a'))))"));
        REQUIRE(parse_and_serialize("(?!a)") == zstring("(SEQ (ASSERT ?! (SEQ (LIT 'a'))))"));
        REQUIRE(parse_and_serialize("(?<=a)") == zstring("(SEQ (ASSERT ?<= (SEQ (LIT 'a'))))"));
        REQUIRE(parse_and_serialize("(?<!a)") == zstring("(SEQ (ASSERT ?<! (SEQ (LIT 'a'))))"));
    }

    SECTION("Character Classes") {
        REQUIRE(parse_and_serialize("[a]") == zstring("(SEQ (CLASS (LIT 'a')))"));
        REQUIRE(parse_and_serialize("[^a]") == zstring("(SEQ (CLASS ^ (LIT 'a')))"));
        REQUIRE(parse_and_serialize("[a-z]") == zstring("(SEQ (CLASS (RANGE 'a' 'z')))"));
        REQUIRE(parse_and_serialize("[a-zA-Z]") == zstring("(SEQ (CLASS (RANGE 'a' 'z') (RANGE 'A' 'Z')))"));
        REQUIRE(parse_and_serialize("[\\d\\s]") == zstring("(SEQ (CLASS (CHAR_CLASS 'd') (CHAR_CLASS 's')))"));
        REQUIRE(parse_and_serialize("[^a-z\\d_]") ==
                zstring("(SEQ (CLASS ^ (RANGE 'a' 'z') (CHAR_CLASS 'd') (LIT '_')))"));
    }

    SECTION("Backreferences") {
        REQUIRE(parse_and_serialize("(a)\\1") == zstring("(SEQ (GROUP #1 (SEQ (LIT 'a'))) (BACKREF 1))"));
        REQUIRE(parse_and_serialize("(?<name>a)\\k<name>") == zstring("(SEQ (GROUP #1 (SEQ (LIT 'a'))) (BACKREF 1))"));
    }

    SECTION("Nested capturing groups") {
        REQUIRE(parse_and_serialize("((a))") == zstring("(SEQ (GROUP #1 (SEQ (GROUP #2 (SEQ (LIT 'a'))))))"));
    }

    SECTION("Nested non-capturing groups") {
        REQUIRE(parse_and_serialize("(?:(?:a))") ==
                zstring("(SEQ (GROUP-NONCAP (SEQ (GROUP-NONCAP (SEQ (LIT 'a'))))))"));
    }

    SECTION("Mixed nested groups with quantifiers") {
        REQUIRE(parse_and_serialize("(a(b+)c)*") == zstring("(SEQ (QUANT {0,inf} (GROUP #1 (SEQ"
                                                            " (LIT 'a')"
                                                            " (GROUP #2 (SEQ (QUANT {1,inf} (LIT 'b'))))"
                                                            " (LIT 'c')"
                                                            "))))"));
    }

    SECTION("Named group inside non-capturing group") {
        REQUIRE(parse_and_serialize("(?:(?<foo>a))") ==
                zstring("(SEQ (GROUP-NONCAP (SEQ (GROUP #1 (SEQ (LIT 'a'))))))"));
    }

    SECTION("Quantifier on group with alternation inside") {
        REQUIRE(parse_and_serialize("(a|b)+") == zstring("(SEQ (QUANT {1,inf} (GROUP #1 (DISJ"
                                                         " (SEQ (LIT 'a'))"
                                                         " (SEQ (LIT 'b'))"
                                                         "))))"));
    }

    SECTION("Quantifier {n,m} on group") {
        REQUIRE(parse_and_serialize("(ab){2,4}") ==
                zstring("(SEQ (QUANT {2,4} (GROUP #1 (SEQ (LIT 'a') (LIT 'b')))))"));
    }

    SECTION("Quantifier on character class") {
        REQUIRE(parse_and_serialize("[a-z]+") == zstring("(SEQ (QUANT {1,inf} (CLASS (RANGE 'a' 'z'))))"));
    }

    SECTION("Quantifier on dot") {
        REQUIRE(parse_and_serialize(".*") == zstring("(SEQ (QUANT {0,inf} (DOT)))"));
    }

    SECTION("Alternation with empty right branch") {
        REQUIRE(parse_and_serialize("a|") == zstring("(DISJ (SEQ (LIT 'a')) (SEQ))"));
    }

    SECTION("Alternation with empty left branch") {
        REQUIRE(parse_and_serialize("|a") == zstring("(DISJ (SEQ) (SEQ (LIT 'a')))"));
    }

    SECTION("Alternation inside a group") {
        REQUIRE(parse_and_serialize("(a|b|c)") == zstring("(SEQ"
                                                          " (GROUP #1 (DISJ"
                                                          " (SEQ (LIT 'a'))"
                                                          " (SEQ (LIT 'b'))"
                                                          " (SEQ (LIT 'c'))"
                                                          "))"
                                                          ")"));
    }

    SECTION("Nested alternation") {
        REQUIRE(parse_and_serialize("(a|b)|(c|d)") == zstring("(DISJ"
                                                              " (SEQ (GROUP #1 (DISJ"
                                                              " (SEQ (LIT 'a'))"
                                                              " (SEQ (LIT 'b'))"
                                                              ")))"
                                                              " (SEQ (GROUP #2 (DISJ"
                                                              " (SEQ (LIT 'c'))"
                                                              " (SEQ (LIT 'd'))"
                                                              ")))"
                                                              ")"));
    }

    SECTION("Word boundary in the middle of pattern") {
        REQUIRE(parse_and_serialize("a\\bb") == zstring("(SEQ"
                                                        " (LIT 'a')"
                                                        " (ASSERT 'b')"
                                                        " (LIT 'b')"
                                                        ")"));
    }

    SECTION("Lookahead with quantified subpattern") {
        REQUIRE(parse_and_serialize("(?=a+)") == zstring("(SEQ"
                                                         " (ASSERT ?= (SEQ"
                                                         " (QUANT {1,inf} (LIT 'a'))"
                                                         "))"
                                                         ")"));
    }

    SECTION("Negative lookbehind with char class") {
        REQUIRE(parse_and_serialize("(?<![0-9])a") == zstring("(SEQ"
                                                              " (ASSERT ?<! (SEQ"
                                                              " (CLASS (RANGE '0' '9'))"
                                                              "))"
                                                              " (LIT 'a')"
                                                              ")"));
    }

    SECTION("Lookahead followed by group") {
        REQUIRE(parse_and_serialize("(?=a)(b)") == zstring("(SEQ"
                                                           " (ASSERT ?= (SEQ (LIT 'a')))"
                                                           " (GROUP #1 (SEQ (LIT 'b')))"
                                                           ")"));
    }

    SECTION("Multiple assertions in sequence") {
        REQUIRE(parse_and_serialize("^\\ba$") == zstring("(SEQ"
                                                         " (ASSERT '^')"
                                                         " (ASSERT 'b')"
                                                         " (LIT 'a')"
                                                         " (ASSERT '$')"
                                                         ")"));
    }

    SECTION("Character class with multiple ranges") {
        REQUIRE(parse_and_serialize("[a-zA-Z0-9]") == zstring("(SEQ"
                                                              " (CLASS"
                                                              " (RANGE 'a' 'z')"
                                                              " (RANGE 'A' 'Z')"
                                                              " (RANGE '0' '9')"
                                                              ")"
                                                              ")"));
    }

    SECTION("Negated class with escape and range") {
        REQUIRE(parse_and_serialize("[^\\w0-9]") == zstring("(SEQ"
                                                            " (CLASS ^"
                                                            " (CHAR_CLASS 'w')"
                                                            " (RANGE '0' '9')"
                                                            ")"
                                                            ")"));
    }

    SECTION("Character class with single char and range") {
        REQUIRE(parse_and_serialize("[_a-z]") == zstring("(SEQ"
                                                         " (CLASS"
                                                         " (LIT '_')"
                                                         " (RANGE 'a' 'z')"
                                                         ")"
                                                         ")"));
    }

    SECTION("Multiple numeric backreferences") {
        REQUIRE(parse_and_serialize("(a)(b)\\1\\2") == zstring("(SEQ"
                                                               " (GROUP #1 (SEQ (LIT 'a')))"
                                                               " (GROUP #2 (SEQ (LIT 'b')))"
                                                               " (BACKREF 1)"
                                                               " (BACKREF 2)"
                                                               ")"));
    }

    SECTION("Named backreference after named group") {
        REQUIRE(parse_and_serialize("(?<word>[a-z]+)\\k<word>") ==
                zstring("(SEQ"
                        " (GROUP #1 (SEQ (QUANT {1,inf} (CLASS (RANGE 'a' 'z')))))"
                        " (BACKREF 1)"
                        ")"));
    }

    SECTION("Simple email-like pattern") {
        REQUIRE(parse_and_serialize("[a-z]+@[a-z]+\\.[a-z]+") == zstring("(SEQ"
                                                                         " (QUANT {1,inf} (CLASS (RANGE 'a' 'z')))"
                                                                         " (LIT '@')"
                                                                         " (QUANT {1,inf} (CLASS (RANGE 'a' 'z')))"
                                                                         " (LIT '.')"
                                                                         " (QUANT {1,inf} (CLASS (RANGE 'a' 'z')))"
                                                                         ")"));
    }

    SECTION("IP address octet pattern") {
        REQUIRE(parse_and_serialize("(25[0-5]|2[0-4][0-9]|[01]?[0-9]{1,2})") ==
                zstring("(SEQ"
                        " (GROUP #1 (DISJ"
                        " (SEQ (LIT '2') (LIT '5') (CLASS (RANGE '0' '5')))"
                        " (SEQ (LIT '2') (CLASS (RANGE '0' '4')) (CLASS (RANGE '0' '9')))"
                        " (SEQ"
                        " (QUANT {0,1} (CLASS (LIT '0') (LIT '1')))"
                        " (QUANT {1,2} (CLASS (RANGE '0' '9')))"
                        ")"
                        "))"
                        ")"));
    }

    SECTION("Hex color pattern") {
        REQUIRE(parse_and_serialize("#([0-9a-fA-F]{3}|[0-9a-fA-F]{6})") ==
                zstring("(SEQ"
                        " (LIT '#')"
                        " (GROUP #1 (DISJ"
                        " (SEQ (QUANT {3,3} (CLASS (RANGE '0' '9') (RANGE 'a' 'f') (RANGE 'A' 'F'))))"
                        " (SEQ (QUANT {6,6} (CLASS (RANGE '0' '9') (RANGE 'a' 'f') (RANGE 'A' 'F'))))"
                        "))"
                        ")"));
    }

    SECTION("Date pattern with named groups") {
        REQUIRE(parse_and_serialize("(?<year>\\d{4})-(?<month>\\d{2})-(?<day>\\d{2})") ==
                zstring("(SEQ"
                        " (GROUP #1 (SEQ (QUANT {4,4} (CLASS (CHAR_CLASS 'd')))))"
                        " (LIT '-')"
                        " (GROUP #2 (SEQ (QUANT {2,2} (CLASS (CHAR_CLASS 'd')))))"
                        " (LIT '-')"
                        " (GROUP #3 (SEQ (QUANT {2,2} (CLASS (CHAR_CLASS 'd')))))"
                        ")"));
    }

    SECTION("URL path segment with lookahead") {
        REQUIRE(parse_and_serialize("(?<=/)([a-z0-9\\-]+)(?=/)") == zstring("(SEQ"
                                                                            " (ASSERT ?<= (SEQ (LIT '/')))"
                                                                            " (GROUP #1 (SEQ (QUANT {1,inf} (CLASS"
                                                                            " (RANGE 'a' 'z')"
                                                                            " (RANGE '0' '9')"
                                                                            " (LIT '-')"
                                                                            "))))"
                                                                            " (ASSERT ?= (SEQ (LIT '/')))"
                                                                            ")"));
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
    }

    SECTION("Crazy character class") {
        std::string regex_input = R"([^\]\--/a-z^\b--\0-\37\cZ])";

        zstring expected = zstring("(SEQ (CLASS ^"
                                   " (LIT ']')"
                                   " (RANGE '-' '/')"
                                   " (RANGE 'a' 'z')"
                                   " (LIT '^')"
                                   " (RANGE '\x08' '-')"
                                   " (RANGE '") +
                           zstring(static_cast<uint32_t>('\0')) +
                           zstring("' '\x1f')"
                                   " (LIT '\x1a')"
                                   "))");

        REQUIRE(parse_and_serialize(regex_input) == expected);
    }
}

// =====================================================================
// RCG SERIALIZATION HELPERS
// =====================================================================

namespace smt::noodler::ecma::test {

    // Converts a Z3 app_ref to a normalized string (collapses whitespace, removes newlines).
    std::string app_to_string(const app_ref& app, ast_manager& m) {
        std::stringstream ss;
        ss << mk_pp(app.get(), m);
        std::string res = ss.str();
        std::erase(res, '\n');
        res.erase(std::ranges::unique(res,
                                      [](const char a, const char b) {
                                          return a == ' ' && b == ' ';
                                      })
                      .begin(),
                  res.end());
        return res;
    }

    // Normalizes a raw pretty-printer string (same as above but takes std::string).
    static std::string normalize_pp(std::string s) {
        std::erase(s, '\n');
        s.erase(std::ranges::unique(s,
                                    [](char a, char b) {
                                        return a == ' ' && b == ' ';
                                    })
                    .begin(),
                s.end());
        return s;
    }

    // Builds the group-start / group-end marker string for a single edge, e.g. " STARTS {1,2} ENDS {1}".
    static std::string serialize_edge_markers(const RegexConstraintGraph& graph, EdgeID eid) {
        std::string res;
        if (graph.group_starts.contains(eid) && !graph.group_starts.at(eid).empty()) {
            res += " STARTS {";
            for (const uint32_t gid : graph.group_starts.at(eid)) {
                res += std::to_string(gid) + ",";
            }
            res.pop_back();
            res += "}";
        }
        if (graph.group_ends.contains(eid) && !graph.group_ends.at(eid).empty()) {
            res += " ENDS {";
            for (const uint32_t gid : graph.group_ends.at(eid)) {
                res += std::to_string(gid) + ",";
            }
            res.pop_back();
            res += "}";
        }
        return res;
    }

    // Forward declaration – serialize_payload and serialize_fragment are mutually recursive
    // (a lookaround can contain a non-regular GraphFragment that itself has edges).
    std::string serialize_fragment(const RegexConstraintGraph& graph, const GraphFragment& frag, ast_manager& m);

    // Serializes a single RCG edge payload.
    // Takes the full graph so it can recursively serialize non-regular lookaround fragments.
    std::string serialize_payload(const RegexConstraintGraph& graph, const RCGEdgePayload& payload, ast_manager& m) {
        if (std::holds_alternative<std::monostate>(payload)) {
            return "EPSILON";
        }

        if (std::holds_alternative<MatchEdge>(payload)) {
            const MatchEdge& match = std::get<MatchEdge>(payload);
            std::stringstream ss;
            ss << mk_pp(match.regex.get(), m);
            return "MATCH " + normalize_pp(ss.str());
        }

        if (std::holds_alternative<AssertionEdge>(payload)) {
            const AssertionEdge& assertion = std::get<AssertionEdge>(payload);

            if (std::holds_alternative<Anchor>(assertion.payload)) {
                const uint32_t anchor_char = std::get<Anchor>(assertion.payload);
                return std::string("ANCHOR '") + static_cast<char>(anchor_char) + "'";
            }

            const Lookaround& la = std::get<Lookaround>(assertion.payload);

            std::string type_str;
            if (la.direction == LookaroundDirection::FORWARD) {
                type_str = la.is_positive ? "?=" : "?!";
            } else {
                type_str = la.is_positive ? "?<=" : "?<!";
            }

            std::string inner_str;
            if (std::holds_alternative<app_ref>(la.subregex)) {
                // Regular lookaround: serialize the Z3 regex expression directly.
                std::stringstream ss;
                ss << mk_pp(std::get<app_ref>(la.subregex).get(), m);
                inner_str = normalize_pp(ss.str());
            } else {
                // Non-regular lookaround: recursively serialize the embedded graph fragment.
                inner_str = serialize_fragment(graph, std::get<GraphFragment>(la.subregex), m);
            }

            return "LOOKAROUND " + type_str + " " + inner_str;
        }

        if (std::holds_alternative<BackrefEdge>(payload)) {
            return "BACKREF " + std::to_string(std::get<BackrefEdge>(payload).backref_id);
        }

        return "UNKNOWN";
    }

    // BFS over the graph starting from start_vertex; appends edge IDs (in BFS order) to ordered_edges.
    void rcg_bfs(const RegexConstraintGraph& graph, VertexID start_vertex, std::vector<bool>& visited_edges,
                 std::vector<EdgeID>& ordered_edges) {
        if (start_vertex == UNKNOWN_VERTEX || start_vertex >= graph.vertices.size()) {
            return;
        }

        std::queue<VertexID> q;
        std::vector<bool> visited_vertices(graph.vertices.size(), false);
        q.push(start_vertex);
        visited_vertices[start_vertex] = true;

        while (!q.empty()) {
            const VertexID curr = q.front();
            q.pop();

            for (EdgeID eid : graph.vertices[curr].outgoing_edges) {
                if (!visited_edges[eid]) {
                    visited_edges[eid] = true;
                    ordered_edges.push_back(eid);
                }
                const VertexID target = graph.edges[eid].target;
                if (!visited_vertices[target]) {
                    visited_vertices[target] = true;
                    q.push(target);
                }
            }
        }
    }

    // Serializes the graph fragment reachable from frag.v_in up to (but not beyond) frag.v_out.
    // Used to serialize non-regular lookaround subgraphs stored inline in edge payloads.
    //
    // The BFS stops exploring outgoing edges of frag.v_out, which correctly bounds the traversal
    // to the inner sub-graph (frag.v_out has no outgoing edges in the outer graph because it was
    // created as an isolated end-vertex of the inner pattern before being moved into the payload).
    std::string serialize_fragment(const RegexConstraintGraph& graph, const GraphFragment& frag, ast_manager& m) {
        std::queue<VertexID> q;
        std::vector<bool> visited_vertices(graph.vertices.size(), false);
        std::vector<bool> visited_edges(graph.edges.size(), false);
        std::vector<EdgeID> ordered_edges;

        q.push(frag.v_in);
        visited_vertices[frag.v_in] = true;

        while (!q.empty()) {
            const VertexID curr = q.front();
            q.pop();

            // Do not follow edges out of the fragment's output vertex.
            if (curr == frag.v_out) {
                continue;
            }

            for (EdgeID eid : graph.vertices[curr].outgoing_edges) {
                if (!visited_edges[eid]) {
                    visited_edges[eid] = true;
                    ordered_edges.push_back(eid);
                }
                const VertexID target = graph.edges[eid].target;
                if (!visited_vertices[target]) {
                    visited_vertices[target] = true;
                    q.push(target);
                }
            }
        }

        std::string res = "(FRAGMENT";
        for (EdgeID eid : ordered_edges) {
            const RCGEdge& edge = graph.edges[eid];
            res += " (EDGE *->* [";
            res += serialize_payload(graph, edge.payload, m) + "]";
            res += serialize_edge_markers(graph, eid);
            res += ")";
        }
        res += ")";
        return res;
    }

    // Full RCG serialization: BFS from start_vertex, emit one token per edge.
    std::string serialize_rcg(const RegexConstraintGraph& graph, ast_manager& m) {
        std::string res = "(RCG";

        if (graph.start_vertex == UNKNOWN_VERTEX) {
            return "(RCG INVALID_START_VERTEX)";
        }

        std::vector<bool> visited_edges(graph.edges.size(), false);
        std::vector<EdgeID> ordered_edges;
        rcg_bfs(graph, graph.start_vertex, visited_edges, ordered_edges);

        for (EdgeID eid : ordered_edges) {
            const RCGEdge& edge = graph.edges[eid];
            res += " (EDGE *->* [";
            res += serialize_payload(graph, edge.payload, m) + "]";
            res += serialize_edge_markers(graph, eid);
            res += ")";
        }
        res += ")";
        return res;
    }

    std::string build_and_serialize_rcg(const zstring& regex, ast_manager& m) {
        RegexConstraintBuilder builder(m, regex);
        const RegexConstraintGraph& rcg = builder.build_rcg();
        return serialize_rcg(rcg, m);
    }

}  // namespace smt::noodler::ecma::test

// =====================================================================
// RCG GENERATION FROM AST – UNIT TESTS
// =====================================================================

TEST_CASE("ECMA Regex RCG generation from AST", "[noodler][ecma]") {
    using Catch::Matchers::ContainsSubstring;
    using namespace smt::noodler::ecma;
    using namespace smt::noodler::ecma::test;

    ast_manager m;
    reg_decl_plugins(m);
    seq_util util_s(m);
    RegexConstraintGraph graph;

    SECTION("ASTNodeLiteral returns regular app_ref") {
        ASTNodeLiteral literal_node;
        literal_node.set_char('x');

        RegexComponent comp = literal_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        app_ref z3_regex = std::get<app_ref>(comp);
        REQUIRE(app_to_string(z3_regex, m) == "(str.to_re \"x\")");
    }

    SECTION("ASTNodeQuantifier wraps the child node in a quantifier") {
        auto literal_node = std::make_unique<ASTNodeLiteral>();
        literal_node->set_char('x');

        ASTNodeQuantifier quant_node;
        Token dummy_token = {TokenType::QUANTIFIER, static_cast<uint32_t>('*'), zstring("*")};
        quant_node.set(dummy_token, std::move(literal_node));

        RegexComponent comp = quant_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        app_ref z3_regex = std::get<app_ref>(comp);
        REQUIRE(app_to_string(z3_regex, m) == "(re.* (str.to_re \"x\"))");
    }

    SECTION("ASTNodeBackref mutates graph and returns GraphFragment") {
        ASTNodeBackref backref_node;
        backref_node.set_ref(1);

        RegexComponent comp = backref_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        REQUIRE(graph.vertices.size() == 2);
        REQUIRE(graph.edges.size() == 1);
        REQUIRE(frag.v_in == 0);
        REQUIRE(frag.v_out == 1);
        REQUIRE(frag.edges_pointing_to_vout.size() == 1);

        const RCGEdge& edge = graph.edges[frag.edges_pointing_to_vout[0]];
        REQUIRE(std::holds_alternative<BackrefEdge>(edge.payload));
        REQUIRE(std::get<BackrefEdge>(edge.payload).backref_id == 1);
    }

    SECTION("ASTNodeGroup tags edges correctly") {
        auto literal_node = std::make_unique<ASTNodeLiteral>();
        literal_node->set_char('a');

        ASTNodeGroup group_node;
        group_node.set_type(GroupType::CAPTURE);
        group_node.set_id(42);
        group_node.set_expr(std::move(literal_node));

        RegexComponent comp = group_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        EdgeID the_edge_id = frag.edges_pointing_to_vout[0];

        REQUIRE(graph.group_starts.count(the_edge_id) > 0);
        REQUIRE(graph.group_starts.at(the_edge_id).size() == 1);
        REQUIRE(graph.group_starts.at(the_edge_id)[0] == 42);

        REQUIRE(graph.group_ends.count(the_edge_id) > 0);
        REQUIRE(graph.group_ends.at(the_edge_id).size() == 1);
        REQUIRE(graph.group_ends.at(the_edge_id)[0] == 42);
    }

    SECTION("ASTNodeDot creates regular app_ref with re.allchar") {
        ASTNodeDot dot_node;
        RegexComponent comp = dot_node.get_subgraph(graph, util_s, m);

        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        app_ref z3_regex = std::get<app_ref>(comp);
        REQUIRE(app_to_string(z3_regex, m) == "re.allchar");
    }

    SECTION("ASTNodeAssertion anchor ^ creates assertion edge") {
        ASTNodeAssertion assert_node;
        assert_node.set_type(TokenType::ASSERTION);
        assert_node.set_payload('^');

        RegexComponent comp = assert_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        REQUIRE(graph.vertices.size() == 2);
        REQUIRE(graph.edges.size() == 1);

        const RCGEdge& edge = graph.edges[frag.edges_pointing_to_vout[0]];
        REQUIRE(std::holds_alternative<AssertionEdge>(edge.payload));
        const AssertionEdge& ae = std::get<AssertionEdge>(edge.payload);
        REQUIRE(std::holds_alternative<Anchor>(ae.payload));
        REQUIRE(std::get<Anchor>(ae.payload) == '^');
    }

    SECTION("ASTNodeQuantifier throws on unbounded non-regular subregex") {
        // Kleene star/plus over backreferences would create a dynamic number of string variables.
        auto backref_node = std::make_unique<ASTNodeBackref>();
        backref_node->set_ref(1);

        ASTNodeQuantifier quant_node;
        Token dummy_token = {TokenType::QUANTIFIER, static_cast<uint32_t>('*'), zstring("*")};
        quant_node.set(dummy_token, std::move(backref_node));

        REQUIRE_THROWS(quant_node.get_subgraph(graph, util_s, m));
    }

    SECTION("ASTNodeQuantifier with finite bounds on non-regular subregex creates fragment") {
        // {n,m} quantifier over a backreference expands into m copies of the sub-graph.
        auto backref_node = std::make_unique<ASTNodeBackref>();
        backref_node->set_ref(1);

        ASTNodeQuantifier quant_node;
        Token dummy_token = {TokenType::QUANTIFIER, QuantifierRange {1, 2}, zstring("{1,2}")};
        quant_node.set(dummy_token, std::move(backref_node));

        RegexComponent comp = quant_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));
        // Two copies of the backref fragment plus epsilon alternations are created.
        REQUIRE(!graph.vertices.empty());
        REQUIRE(!graph.edges.empty());
    }

    SECTION("ASTNodeAlternative merges two regular literals into one app_ref") {
        auto lit_a = std::make_unique<ASTNodeLiteral>();
        lit_a->set_char('a');
        auto lit_b = std::make_unique<ASTNodeLiteral>();
        lit_b->set_char('b');

        ASTNodeAlternative concat_node;
        concat_node.add_term(std::move(lit_a));
        concat_node.add_term(std::move(lit_b));

        RegexComponent comp = concat_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        app_ref z3_regex = std::get<app_ref>(comp);
        REQUIRE(app_to_string(z3_regex, m) == "(re.++ (str.to_re \"a\") (str.to_re \"b\"))");
    }

    SECTION("ASTNodeAlternative creates graph fragment when mixing literal and backref") {
        auto lit = std::make_unique<ASTNodeLiteral>();
        lit->set_char('a');
        auto backref = std::make_unique<ASTNodeBackref>();
        backref->set_ref(1);

        ASTNodeAlternative concat_node;
        concat_node.add_term(std::move(lit));
        concat_node.add_term(std::move(backref));

        RegexComponent comp = concat_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        // Backref creates {v0,v1,e_br}, literal is lifted to {v2,v3,e_match}.
        // chain_fragments orphans v3 (retargets e_match to v0) → 4 vertices, 2 edges.
        REQUIRE(graph.vertices.size() == 4);
        REQUIRE(graph.edges.size() == 2);
    }

    SECTION("ASTNodeAlternative chains adjacent regular subregexes into one") {
        // "ab\1cd" – 'ab' and 'cd' are each merged into a single MATCH edge.
        auto lit_a = std::make_unique<ASTNodeLiteral>();
        lit_a->set_char('a');
        auto lit_b = std::make_unique<ASTNodeLiteral>();
        lit_b->set_char('b');
        auto backref = std::make_unique<ASTNodeBackref>();
        backref->set_ref(1);
        auto lit_c = std::make_unique<ASTNodeLiteral>();
        lit_c->set_char('c');
        auto lit_d = std::make_unique<ASTNodeLiteral>();
        lit_d->set_char('d');

        ASTNodeAlternative concat_node;
        concat_node.add_term(std::move(lit_a));
        concat_node.add_term(std::move(lit_b));
        concat_node.add_term(std::move(backref));
        concat_node.add_term(std::move(lit_c));
        concat_node.add_term(std::move(lit_d));

        RegexComponent comp = concat_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        // Expected: MATCH('ab'), BACKREF(1), MATCH('cd') — 3 edges total.
        REQUIRE(graph.edges.size() == 3);

        bool has_match_ab = false, has_match_cd = false, has_backref = false;
        for (const RCGEdge& edge : graph.edges) {
            if (std::holds_alternative<MatchEdge>(edge.payload)) {
                std::string s = app_to_string(std::get<MatchEdge>(edge.payload).regex, m);
                if (s.find("str.to_re \"a\"") != std::string::npos && s.find("str.to_re \"b\"") != std::string::npos) {
                    has_match_ab = true;
                }
                if (s.find("str.to_re \"c\"") != std::string::npos && s.find("str.to_re \"d\"") != std::string::npos) {
                    has_match_cd = true;
                }
            } else if (std::holds_alternative<BackrefEdge>(edge.payload)) {
                has_backref = true;
            }
        }
        REQUIRE((has_match_ab && has_match_cd && has_backref));
    }

    // ---- Lookaround tests ----

    SECTION("ASTNodeAssertion: regular lookahead creates assertion edge with app_ref subregex") {
        ASTNodeAssertion assert_node;
        assert_node.set_type(TokenType::LOOKAHEAD_POS_START);

        auto lit = std::make_unique<ASTNodeLiteral>();
        lit->set_char('a');
        assert_node.set_expr(std::move(lit));

        RegexComponent comp = assert_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        const RCGEdge& edge = graph.edges[frag.edges_pointing_to_vout[0]];
        REQUIRE(std::holds_alternative<AssertionEdge>(edge.payload));
        const Lookaround& la = std::get<Lookaround>(std::get<AssertionEdge>(edge.payload).payload);
        REQUIRE(std::holds_alternative<app_ref>(la.subregex));
        REQUIRE(la.is_positive == true);
        REQUIRE(la.direction == LookaroundDirection::FORWARD);
    }

    SECTION("ASTNodeAssertion: positive lookaround with non-regular subregex creates fragment") {
        // A positive lookahead whose inner pattern is non-regular (backreference) is now supported.
        // The subregex in the Lookaround is stored as a GraphFragment instead of an app_ref.
        auto backref = std::make_unique<ASTNodeBackref>();
        backref->set_ref(1);

        ASTNodeAssertion assert_node;
        assert_node.set_type(TokenType::LOOKAHEAD_POS_START);
        assert_node.set_expr(std::move(backref));

        RegexComponent comp = assert_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        REQUIRE(graph.edges.size() >= 1);

        const RCGEdge& outer_edge = graph.edges[frag.edges_pointing_to_vout[0]];
        REQUIRE(std::holds_alternative<AssertionEdge>(outer_edge.payload));
        const Lookaround& la = std::get<Lookaround>(std::get<AssertionEdge>(outer_edge.payload).payload);

        // The subregex must be a GraphFragment (non-regular).
        REQUIRE(std::holds_alternative<GraphFragment>(la.subregex));
        REQUIRE(la.is_positive == true);
        REQUIRE(la.direction == LookaroundDirection::FORWARD);

        // The inner fragment must contain exactly one BackrefEdge.
        const GraphFragment& inner = std::get<GraphFragment>(la.subregex);
        REQUIRE(graph.vertices[inner.v_in].outgoing_edges.size() == 1);
        EdgeID inner_eid = graph.vertices[inner.v_in].outgoing_edges[0];
        REQUIRE(std::holds_alternative<BackrefEdge>(graph.edges[inner_eid].payload));
        REQUIRE(std::get<BackrefEdge>(graph.edges[inner_eid].payload).backref_id == 1);
    }

    SECTION("ASTNodeAssertion: negative lookaround with non-regular subregex throws") {
        // A negative non-regular lookaround would require universal quantifiers — not supported.
        auto backref = std::make_unique<ASTNodeBackref>();
        backref->set_ref(1);

        ASTNodeAssertion assert_node;
        assert_node.set_type(TokenType::LOOKAHEAD_NEG_START);
        assert_node.set_expr(std::move(backref));

        REQUIRE_THROWS(assert_node.get_subgraph(graph, util_s, m));
    }

    SECTION("ASTNodeCharClass negates correctly") {
        ASTNodeCharClass char_class;
        char_class.set_negation(true);
        char_class.add_element({ElementType::SINGLE, 'a', 0});

        RegexComponent comp = char_class.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<app_ref>(comp));

        app_ref z3_regex = std::get<app_ref>(comp);
        std::string s = app_to_string(z3_regex, m);
        // Z3 may represent the negation as re.diff or re.inter + re.complement,
        // but either way the universe regex and the complement must be present.
        REQUIRE((s.find("re.diff") != std::string::npos || s.find("re.comp") != std::string::npos));
        REQUIRE((s.find("re.all") != std::string::npos));  // covers both re.all and re.allchar
    }
}

// =====================================================================
// SERIALIZED RCG TESTS  (end-to-end: regex string -> RCG -> serialized string)
// =====================================================================

TEST_CASE("ECMA Regex serialized RCG tests", "[noodler][ecma]") {
    using Catch::Matchers::ContainsSubstring;
    using namespace smt::noodler::ecma;
    using namespace smt::noodler::ecma::test;

    ast_manager m;
    reg_decl_plugins(m);

    // ---- Basic cases ----

    SECTION("Single literal") {
        REQUIRE(build_and_serialize_rcg("a", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re \"a\")]) (EDGE *->* [MATCH re.all]))");
    }

    SECTION("Capture group with markers") {
        REQUIRE(build_and_serialize_rcg("(a)", m) == "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re "
                                                     "\"a\")] STARTS {1} ENDS {1}) (EDGE *->* [MATCH re.all]))");
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
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1}) (EDGE *->* "
                "[MATCH (str.to_re \"b\")] STARTS {2} ENDS {2}) (EDGE *->* [MATCH re.all]))");
    }

    // ---- Sequential and nested groups ----

    SECTION("Sequential capture groups") {
        REQUIRE(build_and_serialize_rcg("(a)(b)(c)", m) ==
                "(RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1}) (EDGE *->* "
                "[MATCH (str.to_re \"b\")] STARTS {2} ENDS {2}) (EDGE *->* [MATCH (str.to_re \"c\")] STARTS {3} ENDS "
                "{3}) (EDGE *->* [MATCH re.all]))");
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
        REQUIRE(build_and_serialize_rcg("(?=(a))", m) == "(RCG"
                                                         " (EDGE *->* [MATCH re.all])"
                                                         " (EDGE *->* [LOOKAROUND ?= (FRAGMENT"
                                                         " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1})"
                                                         " (EDGE *->* [MATCH re.all]))])"
                                                         " (EDGE *->* [MATCH re.all])"
                                                         ")");
    }

    SECTION("Positive lookahead with capture group followed by backreference") {
        // (?=(a))\1 — lookahead captures group 1, then \1 references it.
        REQUIRE(build_and_serialize_rcg("(?=(a))\\1", m) == "(RCG"
                                                            " (EDGE *->* [MATCH re.all])"
                                                            " (EDGE *->* [LOOKAROUND ?= (FRAGMENT"
                                                            " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1})"
                                                            " (EDGE *->* [MATCH re.all]))])"  // <-- nová Sigma* hrana
                                                            " (EDGE *->* [BACKREF 1])"
                                                            " (EDGE *->* [MATCH re.all])"
                                                            ")");
    }

    SECTION("Positive lookbehind containing capture group (non-regular)") {
        // (?<=(a)) — lookbehind with capture group.
        REQUIRE(build_and_serialize_rcg("(?<=(a))", m) ==
                "(RCG"
                " (EDGE *->* [MATCH re.all])"
                " (EDGE *->* [LOOKAROUND ?<= (FRAGMENT"
                " (EDGE *->* [MATCH re.all])"
                " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1}))])"
                " (EDGE *->* [MATCH re.all])"
                ")");
    }

    SECTION("Negative lookaround containing non-regular content throws") {
        // Negative non-regular lookarounds require universal quantifiers -- not supported.
        REQUIRE_THROWS(build_and_serialize_rcg("(?!(a))", m));
        REQUIRE_THROWS(build_and_serialize_rcg("(?<!(a))", m));
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
                "(RCG"
                " (EDGE *->* [MATCH re.all])"
                " (EDGE *->* [MATCH (str.to_re \"x\")] STARTS {1} ENDS {1})"
                " (EDGE *->* [MATCH (re.++ (str.to_re \"a\") (str.to_re \"b\"))])"
                " (EDGE *->* [BACKREF 1])"
                " (EDGE *->* [MATCH (re.++ (str.to_re \"c\") (str.to_re \"d\"))])"
                " (EDGE *->* [MATCH re.all])"
                ")");
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
                "(RCG"
                " (EDGE *->* [MATCH re.all])"
                " (EDGE *->* [ANCHOR '^'])"
                " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {2,1} ENDS {2,1})"
                " (EDGE *->* [MATCH (str.to_re \"b\")] STARTS {3,1} ENDS {3,1})"
                " (EDGE *->* [BACKREF 1])"
                " (EDGE *->* [ANCHOR '$'])"
                " (EDGE *->* [MATCH re.all])"
                ")");
    }

    SECTION("Complex: HTML-like tag matching with interrupted greedy merge") {
        REQUIRE(build_and_serialize_rcg("<(?<tag>x)>y\\k<tag>", m) ==
                "(RCG"
                " (EDGE *->* [MATCH re.all])"
                " (EDGE *->* [MATCH (str.to_re \"<\")])"
                " (EDGE *->* [MATCH (str.to_re \"x\")] STARTS {1} ENDS {1})"
                " (EDGE *->* [MATCH (re.++ (str.to_re \">\") (str.to_re \"y\"))])"
                " (EDGE *->* [BACKREF 1])"
                " (EDGE *->* [MATCH re.all])"
                ")");
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
}
