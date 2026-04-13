#include "smt/theory_str_noodler/ecma_regex.h"

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"

#include <algorithm>
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>
#include <queue>
#include <regex>
#include <sstream>

TEST_CASE("ECMA Regex Lexer", "[noodler]") {
    using namespace smt::noodler::ecma;

    // Basic token tests
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
        // GROUP_NAMED_START payload is still the string view
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
        // Payload is now the uint32_t group ID!
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

// just to make sure it is not a global function so it does not make a mess
namespace smt::noodler::ecma::test {
    zstring parse_and_serialize(const zstring& regex) {
        using namespace smt::noodler::ecma;
        ECMAParser parser(regex);
        const ASTNodeRef root = parser.parse();
        return root->serialize();
    }
};  // namespace smt::noodler::ecma::test

TEST_CASE("ECMA Regex Parser", "[noodler]") {
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
}

namespace smt::noodler::ecma::test {
    std::string app_to_string(const app_ref& app, ast_manager& m) {
        std::stringstream ss;
        ss << mk_pp(app.get(), m);
        std::string res = ss.str();
        // mk_pp inserts redundant whitespaces and newlines --> remove all of them and keep one space only
        std::erase(res, '\n');
        res.erase(std::ranges::unique(res,
                                      [](const char a, const char b) {
                                          return a == ' ' && b == ' ';
                                      })
                      .begin(),
                  res.end());
        return res;
    }

    std::string serialize_payload(const RCGEdgePayload& payload, ast_manager& m) {
        if (std::holds_alternative<std::monostate>(payload)) {
            return "EPSILON";
        }
        if (std::holds_alternative<MatchEdge>(payload)) {
            const MatchEdge& match = std::get<MatchEdge>(payload);
            std::stringstream ss;
            ss << mk_pp(match.regex.get(), m);
            std::string res = ss.str();
            std::erase(res, '\n');
            res.erase(std::ranges::unique(res,
                                          [](char a, char b) {
                                              return a == ' ' && b == ' ';
                                          })
                          .begin(),
                      res.end());
            return "MATCH " + res;
        }
        if (std::holds_alternative<AssertionEdge>(payload)) {
            const AssertionEdge& assertion = std::get<AssertionEdge>(payload);
            if (std::holds_alternative<Anchor>(assertion.assertion)) {
                return std::string("ANCHOR '") + static_cast<char>(std::get<Anchor>(assertion.assertion)) + "'";
            }
            const Lookaround& la = std::get<Lookaround>(assertion.assertion);
            // The type of lookaround in the serialized rcg
            std::string type_str;
            if (la.direction == AssertionDirection::FORWARD) {
                type_str = la.is_positive ? "?=" : "?!";
            } else {
                type_str = la.is_positive ? "?<=" : "?<!";
            }

            // Inner regex
            std::stringstream ss;
            ss << mk_pp(la.regex.get(), m);
            std::string res = ss.str();
            std::erase(res, '\n');
            res.erase(std::ranges::unique(res,
                                          [](char a, char b) {
                                              return a == ' ' && b == ' ';
                                          })
                          .begin(),
                      res.end());

            return "LOOKAROUND " + type_str + " " + res;
        }
        if (std::holds_alternative<BackrefEdge>(payload)) {
            const auto& br = std::get<BackrefEdge>(payload).backreference;
            return "BACKREF " + std::to_string(std::get<uint32_t>(br));  // RCG už zná jen čísla!
        }
        return "UNKNOWN";
    }

    void rcg_bfs_visit(const RegexConstraintGraph& graph, VertexId start_vertex, std::vector<bool>& visited_edges,
                       std::vector<EdgeId>& ordered_edges) {
        if (start_vertex == UNKNOWN_VERTEX || start_vertex >= graph.vertices.size()) {
            return;
        }

        std::queue<VertexId> q;
        std::vector<bool> visited_vertices(graph.vertices.size(), false);

        // Inicializace fronty startovním uzlem
        q.push(start_vertex);
        visited_vertices[start_vertex] = true;

        while (!q.empty()) {
            VertexId curr = q.front();
            q.pop();

            // Projdeme všechny odchozí hrany aktuálního uzlu
            for (EdgeId eid : graph.vertices[curr].outgoing_edges) {
                // Přidáme hranu do výpisu, pokud jsme ji ještě neviděli
                if (!visited_edges[eid]) {
                    visited_edges[eid] = true;
                    ordered_edges.push_back(eid);
                }

                // Přidáme cílový uzel do fronty, pokud jsme ho ještě nenavštívili
                VertexId target = graph.edges[eid].target;
                if (!visited_vertices[target]) {
                    visited_vertices[target] = true;
                    q.push(target);
                }
            }
        }
    }

    std::string serialize_rcg(const RegexConstraintGraph& graph, ast_manager& m) {
        std::string res = "(RCG";

        if (graph.start_vertex == UNKNOWN_VERTEX) {
            return "(RCG INVALID_START_VERTEX)";
        }

        std::vector<bool> visited_edges(graph.edges.size(), false);
        std::vector<EdgeId> ordered_edges;

        // 1. Spustíme BFS přes iterativní funkci a posbíráme hrany po vrstvách
        rcg_bfs_visit(graph, graph.start_vertex, visited_edges, ordered_edges);

        // 2. Vypíšeme posbírané hrany (zbytek funkce zůstává naprosto stejný)
        for (EdgeId eid : ordered_edges) {
            const RCGEdge& edge = graph.edges[eid];

            res += " (EDGE *->* [";
            res += serialize_payload(edge.payload, m) + "]";

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
            res += ")";
        }
        res += ")";
        return res;
    }

    std::string build_and_serialize_rcg(const zstring& regex, ast_manager& m) {
        RCGBuilder builder(m, regex);
        const RegexConstraintGraph rcg = builder.build_rcg();
        return serialize_rcg(rcg, m);
    }
}  // namespace smt::noodler::ecma::test

using Catch::Matchers::ContainsSubstring;

TEST_CASE("ECMA Regex RCG generation from AST", "[noodler]") {
    using namespace smt::noodler::ecma;
    using namespace smt::noodler::ecma::test;
    ast_manager m;
    reg_decl_plugins(m);
    seq_util util_s(m);
    RegexConstraintGraph graph;

    SECTION("ASTNodeLiteral returns regular app_ref") {
        ASTNodeLiteral literal_node;
        literal_node.set_char('x');  // 'x' = 120

        RegexComponent comp = literal_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        app_ref z3_regex = std::get<app_ref>(comp);
        REQUIRE(app_to_string(z3_regex, m) == "(str.to_re (seq.unit (_ Char 120)))");
    }

    SECTION("ASTNodeQuantifier merges regular child into app_ref") {
        auto literal_node = std::make_unique<ASTNodeLiteral>();
        literal_node->set_char('x');

        ASTNodeQuantifier quant_node;
        Token dummy_token = {TokenType::QUANTIFIER, static_cast<uint32_t>('*'), zstring("*")};
        quant_node.set(dummy_token, std::move(literal_node));

        RegexComponent comp = quant_node.get_subgraph(graph, util_s, m);
        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        app_ref z3_regex = std::get<app_ref>(comp);
        REQUIRE(app_to_string(z3_regex, m) == "(re.* (str.to_re (seq.unit (_ Char 120))))");
    }

    SECTION("ASTNodeBackref returns GraphFragment and mutates graph") {
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
        REQUIRE(std::get<uint32_t>(std::get<BackrefEdge>(edge.payload).backreference) == 1);
    }

    SECTION("ASTNodeGroup tags edges correctly") {
        auto literal_node = std::make_unique<ASTNodeLiteral>();
        literal_node->set_char('a');

        ASTNodeGroup group_node;
        group_node.set_type(GroupType::NORMAL);
        group_node.set_id(42);
        group_node.set_expr(std::move(literal_node));

        RegexComponent comp = group_node.get_subgraph(graph, util_s, m);

        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        EdgeId the_edge_id = frag.edges_pointing_to_vout[0];

        REQUIRE(graph.group_starts.count(the_edge_id) > 0);
        REQUIRE(graph.group_starts[the_edge_id].size() == 1);
        REQUIRE(graph.group_starts[the_edge_id][0] == 42);  // Starts: 42

        REQUIRE(graph.group_ends.count(the_edge_id) > 0);
        REQUIRE(graph.group_ends[the_edge_id].size() == 1);
        REQUIRE(graph.group_ends[the_edge_id][0] == 42);  // Ends: 42
    }

    SECTION("ASTNodeDot returns regular app_ref with re.allchar") {
        ASTNodeDot dot_node;
        RegexComponent comp = dot_node.get_subgraph(graph, util_s, m);

        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        app_ref z3_regex = std::get<app_ref>(comp);
        REQUIRE(app_to_string(z3_regex, m) == "re.allchar");
    }

    SECTION("ASTNodeAssertion anchor ^ returns GraphFragment") {
        ASTNodeAssertion assert_node;
        assert_node.set_type(TokenType::ASSERTION);
        assert_node.set_payload('^');

        RegexComponent comp = assert_node.get_subgraph(graph, util_s, m);

        // Kotvy tvoří hrany, neslévají se do regexu!
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        REQUIRE(graph.vertices.size() == 2);
        REQUIRE(graph.edges.size() == 1);

        const RCGEdge& edge = graph.edges[frag.edges_pointing_to_vout[0]];
        REQUIRE(std::holds_alternative<AssertionEdge>(edge.payload));
        const AssertionEdge& ae = std::get<AssertionEdge>(edge.payload);
        REQUIRE(std::holds_alternative<Anchor>(ae.assertion));
        REQUIRE(std::get<Anchor>(ae.assertion) == '^');
    }

    SECTION("ASTNodeQuantifier throws on non-regular child (GraphFragment)") {
        // Vytvoříme potomka, který je Backreference (tzn. vrací GraphFragment)
        auto backref_node = std::make_unique<ASTNodeBackref>();
        backref_node->set_ref(1);

        ASTNodeQuantifier quant_node;
        Token dummy_token = {TokenType::QUANTIFIER, static_cast<uint32_t>('*'), zstring("*")};
        quant_node.set(dummy_token, std::move(backref_node));

        // Kvantifikátor nesmí umět zabalit GraphFragment (zatím nepodporováno)
        REQUIRE_THROWS(quant_node.get_subgraph(graph, util_s, m));
    }

    SECTION("ASTNodeAlternative merges two regular literals") {
        auto lit_a = std::make_unique<ASTNodeLiteral>();
        lit_a->set_char('a');
        auto lit_b = std::make_unique<ASTNodeLiteral>();
        lit_b->set_char('b');

        ASTNodeAlternative concat_node;
        concat_node.add_term(std::move(lit_a));
        concat_node.add_term(std::move(lit_b));

        RegexComponent comp = concat_node.get_subgraph(graph, util_s, m);

        // Mělo by to vrátit jeden slitý app_ref a graf by měl zůstat prázdný
        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        app_ref z3_regex = std::get<app_ref>(comp);
        // re.++ je v Z3 API zřetězení
        REQUIRE(app_to_string(z3_regex, m) ==
                "(re.++ (str.to_re (seq.unit (_ Char 97))) (str.to_re (seq.unit (_ Char 98))))");
    }

    SECTION("ASTNodeAlternative creates fragment when mixing literal and backref") {
        auto lit = std::make_unique<ASTNodeLiteral>();
        lit->set_char('a');
        auto backref = std::make_unique<ASTNodeBackref>();
        backref->set_ref(1);

        ASTNodeAlternative concat_node;
        concat_node.add_term(std::move(lit));
        concat_node.add_term(std::move(backref));

        RegexComponent comp = concat_node.get_subgraph(graph, util_s, m);

        // Protože jeden uzel vrátil Fragment, výsledek musí být také Fragment
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);

        // There are four vertices, because first, v1 -> MatchEdge -> v2 is created for 'a', then v3 -> BackrefEdge -> v4 is created for '\1'
        // and because of the optimalization, the MatchEdge is redirected to point to v3 instead of v2
        REQUIRE(graph.vertices.size() == 4);
        REQUIRE(graph.edges.size() == 2);
    }

    SECTION("ASTNodeAlternative merges multiple regular segments intelligently") {
        // Sestavíme "a" + "b" + "\1" + "c" + "d"
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
        GraphFragment frag = std::get<GraphFragment>(comp);

        // Očekáváme 3 hrany v grafu: MATCH("ab"), BACKREF(1), MATCH("cd")
        REQUIRE(graph.edges.size() == 3);

        // Zkontrolujeme hrubou strukturu payloadů (přesné ověření dělá RCG dump výše)
        bool has_match_ab = false, has_match_cd = false, has_backref = false;
        for (const auto& edge : graph.edges) {
            if (std::holds_alternative<MatchEdge>(edge.payload)) {
                std::string s = app_to_string(std::get<MatchEdge>(edge.payload).regex, m);
                if (s.find("Char 97") != std::string::npos && s.find("Char 98") != std::string::npos) {
                    has_match_ab = true;
                }
                if (s.find("Char 99") != std::string::npos && s.find("Char 100") != std::string::npos) {
                    has_match_cd = true;
                }
            } else if (std::holds_alternative<BackrefEdge>(edge.payload)) {
                has_backref = true;
            }
        }
        REQUIRE((has_match_ab && has_match_cd && has_backref));
    }

    SECTION("ASTNodeAssertion throws on non-regular subpattern") {
        auto backref = std::make_unique<ASTNodeBackref>();
        backref->set_ref(1);

        ASTNodeAssertion assert_node;
        assert_node.set_type(TokenType::LOOKAHEAD_POS_START);
        assert_node.set_expr(std::move(backref));

        // Lookaround nesmí obsahovat zpětnou referenci
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
        // Očekáváme rozdíl (diff) mezi všemi znaky (re.allchar) a znakem 'a'
        REQUIRE(s.find("re.diff") != std::string::npos);
        REQUIRE(s.find("re.allchar") != std::string::npos);
    }
}

TEST_CASE("ECMA Regex serialized RCG tests", "[noodler]") {
    using namespace smt::noodler::ecma::test;

    ast_manager m;
    reg_decl_plugins(m);

    SECTION("Simple match string") {
        REQUIRE(build_and_serialize_rcg("a", m) == "(RCG (EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))]))");
    }

    SECTION("Capture group with markers") {
        REQUIRE(build_and_serialize_rcg("(a)", m) ==
                "(RCG (EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))] STARTS {1} ENDS {1}))");
    }

    SECTION("Numeric backreference") {
        REQUIRE(build_and_serialize_rcg("(a)\\1", m) ==
                "(RCG (EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))] STARTS {1} ENDS {1}) (EDGE *->* "
                "[BACKREF 1]))");
    }

    SECTION("Anchors") {
        REQUIRE(build_and_serialize_rcg("^a", m) ==
                "(RCG (EDGE *->* [ANCHOR '^']) (EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))]))");
    }

    SECTION("Complex nested groups and multiple backreferences") {
        REQUIRE(build_and_serialize_rcg(R"(((a)(b))\1\2\3)", m) ==
                "(RCG "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))] STARTS {2,1} ENDS {2}) "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 98)))] STARTS {3} ENDS {3,1}) "
                "(EDGE *->* [BACKREF 1]) "
                "(EDGE *->* [BACKREF 2]) "
                "(EDGE *->* [BACKREF 3])"
                ")");
    }
    SECTION("Non-capturing group ignores markers") {
        REQUIRE(build_and_serialize_rcg("(?:a)", m) == "(RCG (EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))]))");
    }

    SECTION("Sequential capture groups") {
        REQUIRE(build_and_serialize_rcg("(a)(b)(c)", m) ==
                "(RCG "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))] STARTS {1} ENDS {1}) "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 98)))] STARTS {2} ENDS {2}) "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 99)))] STARTS {3} ENDS {3})"
                ")");
    }

    SECTION("Alternation without groups (greedy merge)") {
        REQUIRE(build_and_serialize_rcg("a|b", m) ==
                "(RCG (EDGE *->* [MATCH (re.union (str.to_re (seq.unit (_ Char 97))) (str.to_re (seq.unit "
                "(_ Char 98))))]))");
    }

    SECTION("Alternation with capture groups") {
        REQUIRE(build_and_serialize_rcg("(a)|(b)", m) ==
                "(RCG "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))] STARTS {1} ENDS {1}) "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 98)))] STARTS {2} ENDS {2})"
                ")");
    }

    SECTION("Named capture group and named backreference") {
        REQUIRE(
            build_and_serialize_rcg("(?<foo>a)\\k<foo>", m) ==
            "(RCG (EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))] STARTS {1} ENDS {1}) (EDGE *->* [BACKREF 1]))");
    }

    SECTION("Positive Lookahead") {
        REQUIRE(build_and_serialize_rcg("(?=a)", m) ==
                "(RCG (EDGE *->* [LOOKAROUND ?= (str.to_re (seq.unit (_ Char 97)))]))");
    }

    SECTION("Word boundary assertion (\\b)") {
        const std::string rcg_dump = build_and_serialize_rcg("\\b", m);

        // \b: (?<=\w)RE(?!\w)  |  (?<!\w)RE(?=\w)
        REQUIRE_THAT(rcg_dump, Catch::Matchers::ContainsSubstring("[LOOKAROUND ?<= "));
        REQUIRE_THAT(rcg_dump, Catch::Matchers::ContainsSubstring("[LOOKAROUND ?! "));
        REQUIRE_THAT(rcg_dump, Catch::Matchers::ContainsSubstring("[LOOKAROUND ?<! "));
        REQUIRE_THAT(rcg_dump, Catch::Matchers::ContainsSubstring("[LOOKAROUND ?= "));
    }

    SECTION("Negated word boundary assertion (\\B)") {
        const std::string rcg_dump = build_and_serialize_rcg("\\B", m);

        // \B is the same as \b but the lookaheads are swapped
        REQUIRE_THAT(rcg_dump, Catch::Matchers::ContainsSubstring("[LOOKAROUND ?<= "));
        REQUIRE_THAT(rcg_dump, Catch::Matchers::ContainsSubstring("[LOOKAROUND ?= "));
        REQUIRE_THAT(rcg_dump, Catch::Matchers::ContainsSubstring("[LOOKAROUND ?<! "));
        REQUIRE_THAT(rcg_dump, Catch::Matchers::ContainsSubstring("[LOOKAROUND ?! "));
    }

    SECTION("Lookaround containing capture group throws") {
        // Capture groups inside lookarounds are unsupported now (what the hell is even the semantics of capture group inside lookaround)
        REQUIRE_THROWS(build_and_serialize_rcg("(?=(a))", m));
    }

    SECTION("Mix of regular sequence and backreference") {
        // "(x)ab\1cd"
        // (x) creates a match edge with capture group markers
        // "ab" should merge into one match edge
        // "\1" is a backref edge
        // "cd" should merge into one match edge
        REQUIRE(build_and_serialize_rcg("(x)ab\\1cd", m) ==
                "(RCG "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 120)))] STARTS {1} ENDS {1}) "
                "(EDGE *->* [MATCH (re.++ (str.to_re (seq.unit (_ Char 97))) (str.to_re (seq.unit (_ Char 98))))]) "
                "(EDGE *->* [BACKREF 1]) "
                "(EDGE *->* [MATCH (re.++ (str.to_re (seq.unit (_ Char 99))) (str.to_re (seq.unit (_ Char 100))))])"
                ")");
    }

    SECTION("Alternation of regular and non-regular components") {
        // "(x)|a|\\1"
        // Two match edges and one backref edge in parallel
        REQUIRE(build_and_serialize_rcg("(x)|a|\\1", m) ==
                "(RCG "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 120)))] STARTS {1} ENDS {1}) "
                "(EDGE *->* [BACKREF 1]) "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))])"
                ")");
    }

    SECTION("Complex: Nested groups inside alternation with backreference") {
        // Regex: ^((a)|(b))\1$

        // Očekáváme 5 hran (Anchor, 2x Match proětve alternace, Backref, Anchor)
        REQUIRE(build_and_serialize_rcg("^((a)|(b))\\1$", m) ==
                "(RCG "
                "(EDGE *->* [ANCHOR '^']) "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))] STARTS {2,1} ENDS {2,1}) "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 98)))] STARTS {3,1} ENDS {3,1}) "
                "(EDGE *->* [BACKREF 1]) "
                "(EDGE *->* [ANCHOR '$'])"
                ")");
    }

    SECTION("Complex: HTML-like tag matching with interrupted greedy merge") {
        // '<' = 60, 'x' = 120, '>' = 62, 'y' = 121
        REQUIRE(build_and_serialize_rcg("<(?<tag>x)>y\\k<tag>", m) ==
                "(RCG "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 60)))]) "
                "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 120)))] STARTS {1} ENDS {1}) "
                "(EDGE *->* [MATCH (re.++ (str.to_re (seq.unit (_ Char 62))) (str.to_re (seq.unit (_ Char 121))))]) "
                "(EDGE *->* [BACKREF 1])"
                ")");
    }
    SECTION("Final Boss 1: Perfect BFS interleaving of parallel complex branches") {
        // Regex: ^(?<v1>a)x(?=y)\1$|^(?<v2>b)z(?<!w)\2$
        // ASCII: a=97, b=98, x=120, y=121, z=122, w=119
        const std::string dump = build_and_serialize_rcg("^(?<v1>a)x(?=y)\\1$|^(?<v2>b)z(?<!w)\\2$", m);

        REQUIRE(dump == "(RCG "
                        // Vrstva 1: Kotvy
                        "(EDGE *->* [ANCHOR '^']) "
                        "(EDGE *->* [ANCHOR '^']) "
                        // Vrstva 2: Capture grupy
                        "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 97)))] STARTS {1} ENDS {1}) "
                        "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 98)))] STARTS {2} ENDS {2}) "
                        // Vrstva 3: Obyčejný text (neslil se, protože před ním i za ním jsou uzly)
                        "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 120)))]) "
                        "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 122)))]) "
                        // Vrstva 4: Lookaroundy (jeden dopředu, jeden dozadu s negací)
                        "(EDGE *->* [LOOKAROUND ?= (str.to_re (seq.unit (_ Char 121)))]) "
                        "(EDGE *->* [LOOKAROUND ?<! (str.to_re (seq.unit (_ Char 119)))]) "
                        // Vrstva 5: Backreference (na různé grupy)
                        "(EDGE *->* [BACKREF 1]) "
                        "(EDGE *->* [BACKREF 2]) "
                        // Vrstva 6: Koncové kotvy
                        "(EDGE *->* [ANCHOR '$']) "
                        "(EDGE *->* [ANCHOR '$'])"
                        ")");
    }
    SECTION("Final Boss 2: Greedy merge boundaries with non-capturing groups and named refs") {
        // Regex: ^a(?:b|c)(?<named>d)\k<named>(?=e)\1f$
        // ASCII: a=97, b=98, c=99, d=100, e=101, f=102
        const std::string dump = build_and_serialize_rcg("^a(?:b|c)(?<named>d)\\k<named>(?=e)\\1f$", m);

        REQUIRE(dump == "(RCG "
                        "(EDGE *->* [ANCHOR '^']) "
                        // Tady se ukáže síla Greedy Merge! Obyčejný znak se slil s non-capturing alternací.
                        "(EDGE *->* [MATCH (re.++ (str.to_re (seq.unit (_ Char 97))) (re.union (str.to_re (seq.unit (_ "
                        "Char 98))) (str.to_re (seq.unit (_ Char 99)))))]) "
                        // Capture grupa sloučení zastavila a vytvořila vlastní hranu.
                        "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 100)))] STARTS {1} ENDS {1}) "
                        // Pojmenovaná zpětná reference
                        "(EDGE *->* [BACKREF 1]) "
                        "(EDGE *->* [LOOKAROUND ?= (str.to_re (seq.unit (_ Char 101)))]) "
                        // Číselná zpětná reference odkazující na totéž
                        "(EDGE *->* [BACKREF 1]) "
                        // Přeživší osamocený text před kotvou
                        "(EDGE *->* [MATCH (str.to_re (seq.unit (_ Char 102)))]) "
                        "(EDGE *->* [ANCHOR '$'])"
                        ")");
    }
}