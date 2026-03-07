#include "smt/theory_str_noodler/ecma_regex.h"

#include <catch2/catch_test_macros.hpp>

TEST_CASE("ecma regex lexer", "[noodler]") {
    using namespace smt::noodler::ecma;

    SECTION("Get literal token from regex") {
        zstring regex = "a";
        ecma_lexer lexer(regex);
        token t = lexer.get_next_token();

        REQUIRE(t.type == token_type::LITERAL);
        uint32_t value = -1;
        REQUIRE_NOTHROW(value = std::get<uint32_t>(t.payload));
        REQUIRE(value == static_cast<uint32_t>('a'));

        t = lexer.get_next_token();
        REQUIRE(t.type == token_type::END_OF_INPUT);
    }

    SECTION("Escape sequence as literal") {
        // Escaped asterisk should be parsed as a literal '*'
        zstring regex = "\\*";
        ecma_lexer lexer(regex);
        token t = lexer.get_next_token();

        REQUIRE(t.type == token_type::LITERAL);
        uint32_t value = -1;
        REQUIRE_NOTHROW(value = std::get<uint32_t>(t.payload));
        REQUIRE(value == static_cast<uint32_t>('*'));
        REQUIRE(t.lexeme.length() == 2);  // Should consume both '\' and '*'
    }

    SECTION("Hex escape sequence") {
        zstring regex = "\\x41\\x42";  // 'A' and 'B'
        ecma_lexer lexer(regex);

        token t1 = lexer.get_next_token();
        REQUIRE(t1.type == token_type::LITERAL);
        REQUIRE(std::get<uint32_t>(t1.payload) == 65);  // 0x41
        REQUIRE(t1.lexeme.length() == 4);

        token t2 = lexer.get_next_token();
        REQUIRE(t2.type == token_type::LITERAL);
        REQUIRE(std::get<uint32_t>(t2.payload) == 66);  // 0x42
        REQUIRE(t2.lexeme.length() == 4);
    }

    SECTION("Hex fallback to literal") {
        // \x4Z is invalid, should fallback to literal 'x', leaving '4' and 'Z'
        zstring regex = "\\x4Z";
        ecma_lexer lexer(regex);

        token t1 = lexer.get_next_token();
        REQUIRE(t1.type == token_type::LITERAL);
        REQUIRE(std::get<uint32_t>(t1.payload) == static_cast<uint32_t>('x'));
        REQUIRE(t1.lexeme.length() == 2);  // Consumes '\x'

        token t2 = lexer.get_next_token();
        REQUIRE(t2.type == token_type::LITERAL);
        REQUIRE(std::get<uint32_t>(t2.payload) == static_cast<uint32_t>('4'));

        token t3 = lexer.get_next_token();
        REQUIRE(t3.type == token_type::LITERAL);
        REQUIRE(std::get<uint32_t>(t3.payload) == static_cast<uint32_t>('Z'));
    }

    SECTION("Control escape fallback") {
        // \c1 is invalid, should throw an error
        zstring regex = "\\c1";
        ecma_lexer lexer(regex);

        REQUIRE_THROWS(lexer.get_next_token());
    }

    SECTION("Octal vs Backreference handling") {
        // No capture groups, \1 should be evaluated as an octal sequence (fallback to literal)
        zstring regex1 = "\\1";
        ecma_lexer lexer1(regex1);
        token t1 = lexer1.get_next_token();
        REQUIRE(t1.type == token_type::LITERAL);
        REQUIRE(std::get<uint32_t>(t1.payload) == 1);

        // One capture group, \1 should be evaluated as a backreference
        zstring regex2 = "(a)\\1";
        ecma_lexer lexer2(regex2);

        REQUIRE(lexer2.get_next_token().type == token_type::GROUP_START);
        token t = lexer2.get_next_token();
        REQUIRE(t.type == token_type::LITERAL);
        REQUIRE(static_cast<unsigned char>(std::get<uint32_t>(t.payload)) == 'a');
        REQUIRE(lexer2.get_next_token().type == token_type::GROUP_END);

        token t_backref = lexer2.get_next_token();
        REQUIRE(t_backref.type == token_type::BACKREFERENCE);
        REQUIRE(std::get<uint32_t>(t_backref.payload) == 1);
    }

    SECTION("Character classes") {
        // [^a-z]
        zstring regex = "[^a-z]";
        ecma_lexer lexer(regex);

        REQUIRE(lexer.get_next_token().type == token_type::CHAR_CLASS_START);

        token t_neg = lexer.get_next_token();
        REQUIRE(t_neg.type == token_type::CHAR_CLASS_NEGATION);

        token t_a = lexer.get_next_token();
        REQUIRE(t_a.type == token_type::LITERAL);
        REQUIRE(std::get<uint32_t>(t_a.payload) == static_cast<uint32_t>('a'));

        REQUIRE(lexer.get_next_token().type == token_type::CHAR_CLASS_RANGE);

        token t_z = lexer.get_next_token();
        REQUIRE(t_z.type == token_type::LITERAL);
        REQUIRE(std::get<uint32_t>(t_z.payload) == static_cast<uint32_t>('z'));

        REQUIRE(lexer.get_next_token().type == token_type::CHAR_CLASS_END);
        REQUIRE(lexer.get_next_token().type == token_type::END_OF_INPUT);
    }

    SECTION("Complex multi-token match") {
        // Match regex: ^(?:a|b){1,2}$
        zstring regex = "^(?:a|b){1,2}$";
        ecma_lexer lexer(regex);

        token t = lexer.get_next_token();
        REQUIRE(t.type == token_type::ASSERTION);
        REQUIRE(std::get<uint32_t>(t.payload) == static_cast<uint32_t>('^'));

        t = lexer.get_next_token();
        REQUIRE(t.type == token_type::GROUP_NONCAPTURE_START);

        t = lexer.get_next_token();
        REQUIRE(t.type == token_type::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == static_cast<uint32_t>('a'));

        t = lexer.get_next_token();
        REQUIRE(t.type == token_type::ALTERNATION);

        t = lexer.get_next_token();
        REQUIRE(t.type == token_type::LITERAL);
        REQUIRE(std::get<uint32_t>(t.payload) == static_cast<uint32_t>('b'));

        t = lexer.get_next_token();
        REQUIRE(t.type == token_type::GROUP_END);

        t = lexer.get_next_token();
        REQUIRE(t.type == token_type::QUANTIFIER);
        REQUIRE(t.lexeme.length() == 5);  // "{1,2}" length

        t = lexer.get_next_token();
        REQUIRE(t.type == token_type::ASSERTION);
        REQUIRE(std::get<uint32_t>(t.payload) == static_cast<uint32_t>('$'));

        t = lexer.get_next_token();
        REQUIRE(t.type == token_type::END_OF_INPUT);
    }
}