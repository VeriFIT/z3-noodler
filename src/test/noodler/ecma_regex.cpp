#include "smt/theory_str_noodler/ecma_regex.h"

#include <catch2/catch_test_macros.hpp>

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