#include "smt/theory_str_noodler/extended_regex/extended_regex.h"
#include "smt/theory_str_noodler/extended_regex/pcre2.h"

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "params/theory_str_noodler_params.h"

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>
#include <string>
#include <utility>
#include <vector>

using namespace smt::noodler::extended_regex;
using namespace smt::noodler::extended_regex::pcre2;
using Catch::Matchers::ContainsSubstring;

namespace {
    // All the tokens of @p regex before the end of input, @p num_capture_groups is the number of capture groups that
    // the parser would report to the lexer
    std::vector<Token> tokenize(const zstring& regex, const GroupID num_capture_groups = 0) {
        PCRE2Lexer lexer(regex);
        lexer.set_num_capture_groups(num_capture_groups);
        std::vector<Token> tokens;
        for (Token t = lexer.get_next_token(); t.type != TokenType::END_OF_INPUT; t = lexer.get_next_token()) {
            tokens.push_back(t);
        }
        return tokens;
    }

    std::vector<TokenType> token_types(const zstring& regex) {
        std::vector<TokenType> types;
        for (const Token& t : tokenize(regex)) {
            types.push_back(t.type);
        }
        return types;
    }

    // The characters of the literal tokens of @p regex
    std::vector<Z3Char> literals(const zstring& regex) {
        std::vector<Z3Char> chars;
        for (const Token& t : tokenize(regex)) {
            if (t.type == TokenType::LITERAL) {
                chars.push_back(std::get<Z3Char>(t.payload));
            }
        }
        return chars;
    }

    std::string parse_and_serialize(const zstring& regex) {
        return serialize(*PCRE2Parser(regex).parse());
    }

    std::string build_and_serialize_rcg(const zstring& regex, ast_manager& m) {
        const theory_str_noodler_params params;
        RegexConstraintBuilder builder(m, symbol("pcre2"), regex, params);
        return serialize_rcg(builder.build_rcg(), m);
    }

    // \w
    const std::string WORD = "(SET '0'-'9' 'A'-'Z' '_' 'a'-'z')";
    // Any character except \n
    const std::string DOT = R"((SET ^ '\u{a}'))";
    // $ and \Z: no character other than \n follows, and no \n with one more character
    const std::string DOLLAR = R"((ASSERT ?! (DISJ (SET ^ '\u{a}') (SEQ (LIT '\u{a}') (SET ^)))))";
}  // namespace

// =====================================================================
// LEXER TESTS
// =====================================================================

TEST_CASE("PCRE2 Regex Lexer", "[noodler][pcre2]") {
    SECTION("Literals and escape sequences") {
        // a, escaped punctuation, \_, hexadecimal, octal, control and C escapes
        REQUIRE(literals(R"(a\*\_\x41\x{42}\x{ 43 }\x4\101\0\012\o{104}\cA\ca\c;\e\n\t\a\f\r)") ==
                std::vector<Z3Char> {'a', '*', '_', 'A', 'B',  'C',  4,    'A',  '\0', '\n',
                                     'D', 1,   1,   '{', 0x1B, '\n', '\t', '\a', '\f', '\r'});
        // \N{U+h...} is a character
        REQUIRE(literals(R"(\N{U+41}\N{ U+2028 })") == std::vector<Z3Char> {'A', 0x2028});
        // An octal escape has at most three digits and can be greater than 255
        REQUIRE(literals(R"(\1234\777)") == std::vector<Z3Char> {0123, '4', 0777});
        // Characters that are not ASCII letters or digits are themselves after '\'
        REQUIRE(literals(R"(\\u{e9})") == std::vector<Z3Char> {0xE9});
    }

    SECTION("Octal escapes and backreferences") {
        // \NN is an octal escape if there are fewer than NN capture groups before it
        REQUIRE(literals(R"(\11)") == std::vector<Z3Char> {'\t'});
        std::vector<Token> tokens = tokenize(R"(\11)", 11);
        REQUIRE(tokens.size() == 1);
        REQUIRE(tokens[0].type == TokenType::BACKREFERENCE);
        REQUIRE(std::get<BackrefTarget>(tokens[0].payload).kind == BackrefTarget::Kind::NUMBER);
        REQUIRE(std::get<BackrefTarget>(tokens[0].payload).number == 11);
        // \1 to \9 and the numbers starting with 8 or 9 are always backreferences
        for (const auto& [regex, number] :
             std::vector<std::pair<const char*, int64_t>> {{R"(\1)", 1}, {R"(\9)", 9}, {R"(\81)", 81}}) {
            tokens = tokenize(regex);
            REQUIRE(tokens.size() == 1);
            REQUIRE(tokens[0].type == TokenType::BACKREFERENCE);
            REQUIRE(std::get<BackrefTarget>(tokens[0].payload).number == number);
        }
    }

    SECTION("Quoted text") {
        REQUIRE(token_types(R"(\Qa.*\E+)") == std::vector<TokenType> {TokenType::LITERAL, TokenType::LITERAL,
                                                                      TokenType::LITERAL, TokenType::QUANTIFIER});
        REQUIRE(literals(R"(\Qa.*\E+)") == std::vector<Z3Char> {'a', '.', '*'});
        // Without \E, the text is quoted up to the end of the regex
        REQUIRE(literals(R"(\Q(\b)") == std::vector<Z3Char> {'(', '\\', 'b'});
        // \E that does not end quoted text and empty quoted text are ignored
        REQUIRE(token_types(R"(a\E\Q\E*)") == std::vector<TokenType> {TokenType::LITERAL, TokenType::QUANTIFIER});
    }

    SECTION("Quantifiers") {
        const std::vector<Token> tokens = tokenize("a*b+?c?+d{2}e{2,}?f{2,5}+g{,3}h{ 1 , 2 }i{02}");
        std::vector<std::pair<uint64_t, uint64_t>> ranges;
        std::vector<QuantifierMode> modes;
        for (const Token& t : tokens) {
            if (t.type == TokenType::QUANTIFIER) {
                const Quantifier quantifier = std::get<Quantifier>(t.payload);
                ranges.emplace_back(quantifier.range.min, quantifier.range.max);
                modes.push_back(quantifier.mode);
            }
        }
        REQUIRE(ranges ==
                std::vector<std::pair<uint64_t, uint64_t>> {
                    {0, UNBOUNDED}, {1, UNBOUNDED}, {0, 1}, {2, 2}, {2, UNBOUNDED}, {2, 5}, {0, 3}, {1, 2}, {2, 2}});
        REQUIRE(modes ==
                std::vector<QuantifierMode> {QuantifierMode::GREEDY, QuantifierMode::LAZY, QuantifierMode::POSSESSIVE,
                                             QuantifierMode::GREEDY, QuantifierMode::LAZY, QuantifierMode::POSSESSIVE,
                                             QuantifierMode::GREEDY, QuantifierMode::GREEDY, QuantifierMode::GREEDY});
    }

    SECTION("Brace that does not start a quantifier is a literal") {
        REQUIRE(literals("a{,}") == std::vector<Z3Char> {'a', '{', ',', '}'});
        REQUIRE(literals("a{}") == std::vector<Z3Char> {'a', '{', '}'});
        REQUIRE(literals("a{2") == std::vector<Z3Char> {'a', '{', '2'});
        REQUIRE(literals("a{x}") == std::vector<Z3Char> {'a', '{', 'x', '}'});
        REQUIRE(literals(R"(a{\Q2\E})") == std::vector<Z3Char> {'a', '{', '2', '}'});
    }

    SECTION("Assertions") {
        std::vector<Z3Char> assertions;
        for (const Token& t : tokenize(R"(^\A\b\B\Z\z\G$)")) {
            REQUIRE(t.type == TokenType::ASSERTION);
            assertions.push_back(std::get<Z3Char>(t.payload));
        }
        REQUIRE(assertions == std::vector<Z3Char> {'^', 'A', 'b', 'B', 'Z', 'z', 'G', '$'});
    }

    SECTION("Character types and newline sequences") {
        REQUIRE(token_types(R"(\d\H\v\N\R.)") ==
                std::vector<TokenType> {TokenType::CHAR_CLASS_ESCAPE, TokenType::CHAR_CLASS_ESCAPE,
                                        TokenType::CHAR_CLASS_ESCAPE, TokenType::CHAR_CLASS_ESCAPE,
                                        TokenType::NEWLINE_SEQUENCE, TokenType::DOT});
        // \N{n} is \N with a quantifier
        REQUIRE(token_types(R"(\N{2})") ==
                std::vector<TokenType> {TokenType::CHAR_CLASS_ESCAPE, TokenType::QUANTIFIER});
    }

    SECTION("Groups and flags") {
        // The names of groups are views into the regex, which has to outlive the tokens
        const zstring regex("(a)(?:b)(?P<x>c)(?<y>d)(?'z'e)(?m)(?s-m:f)(?^n:g)");
        const std::vector<Token> tokens = tokenize(regex);
        std::vector<TokenType> types;
        for (const Token& t : tokens) {
            if (t.type != TokenType::LITERAL) {
                types.push_back(t.type);
            }
        }
        REQUIRE(types == std::vector<TokenType> {
                             TokenType::GROUP_START, TokenType::GROUP_END, TokenType::GROUP_NONCAPTURE_START,
                             TokenType::GROUP_END, TokenType::GROUP_NAMED_START, TokenType::GROUP_END,
                             TokenType::GROUP_NAMED_START, TokenType::GROUP_END, TokenType::GROUP_NAMED_START,
                             TokenType::GROUP_END, TokenType::FLAGS, TokenType::GROUP_NONCAPTURE_START,
                             TokenType::GROUP_END, TokenType::GROUP_NONCAPTURE_START, TokenType::GROUP_END});
        REQUIRE(std::get<zstring_view>(tokens[6].payload) == zstring("x"));
        REQUIRE(std::get<zstring_view>(tokens[9].payload) == zstring("y"));
        REQUIRE(std::get<zstring_view>(tokens[12].payload) == zstring("z"));
        const FlagChanges multi_line = std::get<FlagChanges>(tokens[15].payload);
        REQUIRE(multi_line.set == MULTI_LINE);
        REQUIRE(multi_line.cleared == 0);
        const FlagChanges dot_all = std::get<FlagChanges>(tokens[16].payload);
        REQUIRE(dot_all.set == DOT_ALL);
        REQUIRE(dot_all.cleared == MULTI_LINE);
        // (?^n:...) clears i, m, n, r, s, x and xx and then sets n
        const FlagChanges reset = std::get<FlagChanges>(tokens[19].payload);
        REQUIRE(reset.set == NO_AUTO_CAPTURE);
        REQUIRE(reset.cleared ==
                (CASE_INSENSITIVE | MULTI_LINE | CASELESS_RESTRICT | DOT_ALL | EXTENDED | EXTENDED_MORE));
    }

    SECTION("Lookarounds and atomic groups") {
        const std::vector<Token> tokens = tokenize("(?=a)(?!b)(?<=c)(?<!d)(?>e)");
        // Whether the lookaround is a lookahead and whether it is positive
        std::vector<std::pair<bool, bool>> kinds;
        for (const Token& t : tokens) {
            if (t.type == TokenType::LOOKAROUND_START) {
                const LookaroundKind kind = std::get<LookaroundKind>(t.payload);
                kinds.emplace_back(kind.direction == LookaroundDirection::FORWARD, kind.is_positive);
            }
        }
        REQUIRE(kinds ==
                std::vector<std::pair<bool, bool>> {{true, true}, {true, false}, {false, true}, {false, false}});
        REQUIRE(tokens[12].type == TokenType::ATOMIC_GROUP_START);
    }

    SECTION("Comments and start-of-pattern options produce no tokens") {
        REQUIRE(token_types("(*UTF)(*NO_JIT)(*LIMIT_MATCH=10)a(?#comment)*") ==
                std::vector<TokenType> {TokenType::LITERAL, TokenType::QUANTIFIER});
        // The comment ends at the first ')'
        REQUIRE(literals(R"((?#\)a)") == std::vector<Z3Char> {'a'});
        // "(*" that is not followed by a letter is the start of a group and a quantifier
        REQUIRE(token_types("(*)") ==
                std::vector<TokenType> {TokenType::GROUP_START, TokenType::QUANTIFIER, TokenType::GROUP_END});
    }

    SECTION("Character class") {
        // ']' is a literal at the start of the class, '-' starts a range after a single character
        REQUIRE(token_types("[^]a-c-]") ==
                std::vector<TokenType> {TokenType::CHAR_CLASS_START, TokenType::CHAR_CLASS_NEGATION, TokenType::LITERAL,
                                        TokenType::LITERAL, TokenType::CHAR_CLASS_RANGE, TokenType::LITERAL,
                                        TokenType::LITERAL, TokenType::CHAR_CLASS_END});
        REQUIRE(token_types("[--a]") == std::vector<TokenType> {TokenType::CHAR_CLASS_START, TokenType::LITERAL,
                                                                TokenType::CHAR_CLASS_RANGE, TokenType::LITERAL,
                                                                TokenType::CHAR_CLASS_END});
        // '-' after a class escape is a literal before ']'
        REQUIRE(token_types(R"([\d-])") == std::vector<TokenType> {TokenType::CHAR_CLASS_START,
                                                                   TokenType::CHAR_CLASS_ESCAPE, TokenType::LITERAL,
                                                                   TokenType::CHAR_CLASS_END});
        // Quoted characters are literals, also '-', ']' and '^'
        REQUIRE(token_types(R"([\Q^a-]\E])") == std::vector<TokenType> {TokenType::CHAR_CLASS_START, TokenType::LITERAL,
                                                                        TokenType::LITERAL, TokenType::LITERAL,
                                                                        TokenType::LITERAL, TokenType::CHAR_CLASS_END});
        // \E and empty quoted text do not change the position in the class
        REQUIRE(token_types(R"([\E\Q\E^\E]a])") ==
                std::vector<TokenType> {TokenType::CHAR_CLASS_START, TokenType::CHAR_CLASS_NEGATION, TokenType::LITERAL,
                                        TokenType::LITERAL, TokenType::CHAR_CLASS_END});
        // \b is a backspace, \8, \9, \g and \k are the characters themselves, \1 to \7 start octal escapes
        REQUIRE(literals(R"([\b\8\9\g\k\18])") == std::vector<Z3Char> {'\b', '8', '9', 'g', 'k', 1, '8'});
    }

    SECTION("POSIX classes") {
        const zstring regex("[[:alpha:][:^digit:]x]");
        const std::vector<Token> tokens = tokenize(regex);
        REQUIRE(tokens.size() == 5);
        REQUIRE(tokens[1].type == TokenType::POSIX_CLASS);
        REQUIRE(std::get<zstring_view>(tokens[1].payload) == zstring("alpha"));
        REQUIRE(tokens[2].type == TokenType::POSIX_CLASS);
        REQUIRE(std::get<zstring_view>(tokens[2].payload) == zstring("^digit"));
        // '[' is a literal if no ":]" follows before the next ']'
        REQUIRE(literals("[[:alpha]") == std::vector<Z3Char> {'[', ':', 'a', 'l', 'p', 'h', 'a'});
    }

    SECTION("Invalid escape sequences") {
        // \u{5c}u0041 is the pattern \u0041 (zstring decodes \u{5c} to the backslash)
        for (const char* regex : {R"(\q)", R"(\x)", R"(\xg1)", R"(\x{})", R"(\x{110000})", R"(\x{d800})", R"(\x{41)",
                                  R"(\o)", R"(\o{8})", R"(\c)", R"(\u{5c}u0041)", R"(\L)", R"(\N{LATIN})",
                                  R"(\N{U+ 41})", "a\\", R"([\B])", R"([\R])", R"([\N])", R"([\z])"}) {
            CHECK_THROWS_WITH(tokenize(regex), ContainsSubstring("PCRE2 regex syntax error"));
        }
    }

    SECTION("Invalid groups and flags") {
        for (const char* regex :
             {"(?", "(?#a", "(?P'n'a)", "(?<>a)", "(?<1a>b)", "(?<a-b>c)", "(?<a", "(?'a>b)", "(?z)", "(?i-m-s)",
              "(?^-i)", "(?i^)", "(?aX)", "(?im", "a(*UTF)", "(*FOO)", "(*foo:a)", "(*LIMIT_MATCH=)a"}) {
            CHECK_THROWS_WITH(tokenize(regex), ContainsSubstring("PCRE2 regex syntax error"));
        }
    }

    SECTION("Invalid character classes") {
        // '-' after a class escape or a POSIX class must be the last character of the class
        for (const char* regex : {R"([\d-z])", "[[:alpha:]-z]", "[[.a.]]", "[[=a=]]", "[:alpha:]", "[.a.]"}) {
            CHECK_THROWS_WITH(tokenize(regex), ContainsSubstring("PCRE2 regex syntax error"));
        }
    }

    SECTION("Unsupported features") {
        for (const char* regex :
             {R"(\pL)",   R"(\p{Greek})", R"([\PN])",        R"(\X)",        R"(\C)",          R"(\K)",
              R"(\g1)",   R"(\k<n>)",     "(?P=n)",          "(?P>n)",       "(?R)",           "(?1)",
              "(?-1)",    "(?+1)",        "(?&n)",           "(?(1)a)",      "(?C1)",          "(?|a)",
              "(?*a)",    "(?<*a)",       "(?[a])",          "[[:<:]]",      "[[:>:]]",        "(*UCP)a",
              "(*CRLF)a", "(*ANYCRLF)a",  "(*BSR_ANYCRLF)a", "(*NOTEMPTY)a", "(*ACCEPT)",      "(*FAIL)",
              "(*:name)", "(*pla:a)",     "(*atomic:a)",     "(*sr:a)",      R"((?<\u{e9}>a))"}) {
            CHECK_THROWS_WITH(tokenize(regex), ContainsSubstring("Unsupported"));
        }
    }
}

// =====================================================================
// PARSER TESTS
// =====================================================================

TEST_CASE("PCRE2 Regex Parser", "[noodler][pcre2]") {
    SECTION("Literals, concatenation and alternation") {
        REQUIRE(parse_and_serialize("") == "(SEQ)");
        REQUIRE(parse_and_serialize("ab") == "(SEQ (LIT 'a') (LIT 'b'))");
        REQUIRE(parse_and_serialize("a|") == "(DISJ (SEQ (LIT 'a')) (SEQ))");
        REQUIRE(parse_and_serialize(R"(\Qa.b\E)") == "(SEQ (LIT 'a') (LIT '.') (LIT 'b'))");
    }

    SECTION("Dot and character types") {
        REQUIRE(parse_and_serialize(".") == "(SEQ " + DOT + ")");
        REQUIRE(parse_and_serialize("(?s).") == "(SEQ (SET ^))");
        // \N does not match \n even with the flag s
        REQUIRE(parse_and_serialize(R"((?s)\N)") == "(SEQ " + DOT + ")");
        REQUIRE(parse_and_serialize(R"(\d)") == "(SEQ (SET '0'-'9'))");
        REQUIRE(parse_and_serialize(R"(\D)") == "(SEQ (SET ^ '0'-'9'))");
        // \s includes the vertical tab
        REQUIRE(parse_and_serialize(R"(\s)") == R"((SEQ (SET '\u{9}'-'\u{d}' ' ')))");
        REQUIRE(parse_and_serialize(R"(\w)") == "(SEQ " + WORD + ")");
        // \h and \v match also non-ASCII characters
        REQUIRE(parse_and_serialize(R"(\h)") ==
                R"((SEQ (SET '\u{9}' ' ' '\u{a0}' '\u{1680}' '\u{180e}' '\u{2000}'-'\u{200a}' '\u{202f}' '\u{205f}')"
                R"( '\u{3000}')))");
        REQUIRE(parse_and_serialize(R"(\v)") == R"((SEQ (SET '\u{a}'-'\u{d}' '\u{85}' '\u{2028}'-'\u{2029}')))");
    }

    SECTION("Newline sequence") {
        // \R is atomic, so \r alone matches only if no \n follows
        REQUIRE(parse_and_serialize(R"(\R)") ==
                R"((SEQ (DISJ (SEQ (LIT '\u{d}') (LIT '\u{a}')) (SEQ (LIT '\u{d}') (ASSERT ?! (LIT '\u{a}'))))"
                R"( (SET '\u{a}'-'\u{c}' '\u{85}' '\u{2028}'-'\u{2029}'))))");
    }

    SECTION("Character classes") {
        // Negated classes match \n
        REQUIRE(parse_and_serialize("[^a]") == "(SEQ (SET ^ 'a'))");
        REQUIRE(parse_and_serialize("[]a]") == "(SEQ (SET ']' 'a'))");
        REQUIRE(parse_and_serialize("[a-c-]") == "(SEQ (SET '-' 'a'-'c'))");
        REQUIRE(parse_and_serialize("[a-]") == "(SEQ (SET '-' 'a'))");
        REQUIRE(parse_and_serialize("[--a]") == "(SEQ (SET '-'-'a'))");
        REQUIRE(parse_and_serialize("[a-b-c]") == "(SEQ (SET '-' 'a'-'c'))");
        REQUIRE(parse_and_serialize(R"([\d-])") == "(SEQ (SET '-' '0'-'9'))");
        REQUIRE(parse_and_serialize(R"([\x41-\x{43}])") == "(SEQ (SET 'A'-'C'))");
        // Quoted characters can be the bounds of a range, a quoted '-' is a literal
        REQUIRE(parse_and_serialize(R"([\Qa\E-\Qc\E])") == "(SEQ (SET 'a'-'c'))");
        REQUIRE(parse_and_serialize(R"([\Qa-c\E])") == "(SEQ (SET '-' 'a' 'c'))");
        REQUIRE(parse_and_serialize("[[:alpha:]_]") == "(SEQ (SET 'A'-'Z' '_' 'a'-'z'))");
        REQUIRE(parse_and_serialize("[[:^alpha:]]") == "(SEQ (SET ^ 'A'-'Z' 'a'-'z'))");
        REQUIRE(parse_and_serialize("[[:space:]]") == R"((SEQ (SET '\u{9}'-'\u{d}' ' ')))");
    }

    SECTION("Anchors and word boundaries") {
        // $ matches also before \n at the end of the text (like \Z), \z only at the end of the text
        REQUIRE(parse_and_serialize("^a$") == "(SEQ (ASSERT '^') (LIT 'a') " + DOLLAR + ")");
        REQUIRE(parse_and_serialize(R"(\Aa\Z)") == "(SEQ (ASSERT '^') (LIT 'a') " + DOLLAR + ")");
        REQUIRE(parse_and_serialize(R"(\Aa\z)") == "(SEQ (ASSERT '^') (LIT 'a') (ASSERT '$'))");
        REQUIRE(parse_and_serialize(R"(\b)") == "(SEQ (DISJ (SEQ (ASSERT ?<= " + WORD + ") (ASSERT ?! " + WORD +
                                                    "))"
                                                    " (SEQ (ASSERT ?<! " +
                                                    WORD + ") (ASSERT ?= " + WORD + "))))");
    }

    SECTION("Multi-line anchors are lookarounds") {
        // ^ matches at the start of the text and after \n that does not end the text, $ before any \n
        REQUIRE(parse_and_serialize("(?m)^a$") ==
                R"((SEQ (DISJ (ASSERT '^') (SEQ (ASSERT ?<= (LIT '\u{a}')) (ASSERT ?= (SET ^)))) (LIT 'a'))"
                " (ASSERT ?! " +
                    DOT + "))");
        // \A, \Z and \z do not depend on the flag m
        REQUIRE(parse_and_serialize(R"((?m)\Aa\Z)") == "(SEQ (ASSERT '^') (LIT 'a') " + DOLLAR + ")");
    }

    SECTION("Flags hold until the end of the enclosing group") {
        // The flag s set in the first alternative holds also in the second one, but not after the group
        REQUIRE(parse_and_serialize("(a(?s).|.).") ==
                "(SEQ (GROUP #1 (DISJ (SEQ (LIT 'a') (SET ^)) (SEQ (SET ^)))) " + DOT + ")");
        REQUIRE(parse_and_serialize("(?s:a.)b.") == "(SEQ (SEQ (LIT 'a') (SET ^)) (LIT 'b') " + DOT + ")");
        REQUIRE(parse_and_serialize("(?s)a(?-s).") == "(SEQ (LIT 'a') " + DOT + ")");
        REQUIRE(parse_and_serialize("(?s)a(?^).") == "(SEQ (LIT 'a') " + DOT + ")");
        // A flag both set and cleared is cleared
        REQUIRE(parse_and_serialize("(?s-s).") == "(SEQ " + DOT + ")");
    }

    SECTION("Flags without an effect on the matched strings") {
        REQUIRE(parse_and_serialize("(?U)a+") == "(SEQ (QUANT {1,inf} (LIT 'a')))");
        REQUIRE(parse_and_serialize(R"((?r)(?a)(?aD)(?J)\d)") == "(SEQ (SET '0'-'9'))");
    }

    SECTION("Repetitions") {
        REQUIRE(parse_and_serialize("a*?b+c??") ==
                "(SEQ (QUANT {0,inf} (LIT 'a')) (QUANT {1,inf} (LIT 'b')) (QUANT {0,1} (LIT 'c')))");
        REQUIRE(parse_and_serialize("a{2}b{2,}c{2,5}?d{,3}") ==
                "(SEQ (QUANT {2,2} (LIT 'a')) (QUANT {2,inf} (LIT 'b')) (QUANT {2,5} (LIT 'c'))"
                " (QUANT {0,3} (LIT 'd')))");
        REQUIRE(parse_and_serialize("a{65535}") == "(SEQ (QUANT {65535,65535} (LIT 'a')))");
        // A comment between an item and its quantifier is ignored
        REQUIRE(parse_and_serialize("a(?#x)*") == "(SEQ (QUANT {0,inf} (LIT 'a')))");
        // \R can be repeated
        REQUIRE_THAT(parse_and_serialize(R"(\R{2})"), ContainsSubstring("(QUANT {2,2} (DISJ"));
    }

    SECTION("Groups") {
        REQUIRE(parse_and_serialize("(a)(?P<x>b)(?<y>c)(?'z'd)(?:e)") ==
                "(SEQ (GROUP #1 (SEQ (LIT 'a'))) (GROUP #2 (SEQ (LIT 'b'))) (GROUP #3 (SEQ (LIT 'c')))"
                " (GROUP #4 (SEQ (LIT 'd'))) (SEQ (LIT 'e')))");
        // With the flag n, only named groups capture
        REQUIRE(parse_and_serialize("(?n)(a)(?<x>b)") == "(SEQ (SEQ (LIT 'a')) (GROUP #1 (SEQ (LIT 'b'))))");
        REQUIRE(parse_and_serialize("(?n:(a))(b)") == "(SEQ (SEQ (SEQ (LIT 'a'))) (GROUP #1 (SEQ (LIT 'b'))))");
    }

    SECTION("Octal escapes depend on the number of capture groups before them") {
        // One capture group is opened before \11, so it is the octal escape of the tab
        REQUIRE(parse_and_serialize(R"((a)\11)") == R"((SEQ (GROUP #1 (SEQ (LIT 'a'))) (LIT '\u{9}')))");
        // With the flag n, plain parentheses are not counted
        REQUIRE(parse_and_serialize(R"((?n)(a)(b)(c)(d)(e)(f)(g)(h)(i)(j)\12)") ==
                "(SEQ (SEQ (LIT 'a')) (SEQ (LIT 'b')) (SEQ (LIT 'c')) (SEQ (LIT 'd')) (SEQ (LIT 'e')) (SEQ (LIT 'f'))"
                R"( (SEQ (LIT 'g')) (SEQ (LIT 'h')) (SEQ (LIT 'i')) (SEQ (LIT 'j')) (LIT '\u{a}')))");
    }

    SECTION("Invalid repetitions") {
        for (const char* regex : {"a**", "a{2}{3}", "*a", "a|{2}", "^*", "$+", R"(\b?)", R"(\Z{2})", "(?s)*"}) {
            CHECK_THROWS_WITH(parse_and_serialize(regex),
                              ContainsSubstring("quantifier does not follow a repeatable item"));
        }
        CHECK_THROWS_WITH(parse_and_serialize("a{65536}"), ContainsSubstring("number too big in {} quantifier"));
        CHECK_THROWS_WITH(parse_and_serialize("a{2,1}"), ContainsSubstring("numbers out of order in {} quantifier"));
    }

    SECTION("Invalid brackets and parentheses") {
        CHECK_THROWS_WITH(parse_and_serialize("[a"), ContainsSubstring("missing terminating ]"));
        CHECK_THROWS_WITH(parse_and_serialize("[]"), ContainsSubstring("missing terminating ]"));
        CHECK_THROWS_WITH(parse_and_serialize(R"([\Qa])"), ContainsSubstring("missing terminating ]"));
        CHECK_THROWS_WITH(parse_and_serialize("(a"), ContainsSubstring("missing closing parenthesis"));
        CHECK_THROWS_WITH(parse_and_serialize("a)"), ContainsSubstring("unmatched closing parenthesis"));
    }

    SECTION("Invalid character classes") {
        CHECK_THROWS_WITH(parse_and_serialize("[z-a]"), ContainsSubstring("range out of order in character class"));
        CHECK_THROWS_WITH(parse_and_serialize(R"([a-\d])"), ContainsSubstring("invalid range in character class"));
        CHECK_THROWS_WITH(parse_and_serialize("[a-[:alpha:]]"), ContainsSubstring("invalid range in character class"));
        CHECK_THROWS_WITH(parse_and_serialize("[[:foo:]]"), ContainsSubstring("unknown POSIX class name"));
    }

    SECTION("Invalid names of capture groups") {
        CHECK_THROWS_WITH(parse_and_serialize("(?<n>a)(?<n>b)"),
                          ContainsSubstring("two named subpatterns have the same name"));
        CHECK_THROWS_WITH(parse_and_serialize("(?J)(?<n>a)(?<n>b)"), ContainsSubstring("Unsupported"));
    }

    SECTION("Unsupported flags") {
        CHECK_THROWS_WITH(parse_and_serialize("(?i)a"), ContainsSubstring("Unsupported"));
        CHECK_THROWS_WITH(parse_and_serialize("(?i:a)"), ContainsSubstring("Unsupported"));
        CHECK_THROWS_WITH(parse_and_serialize("(?x)a"), ContainsSubstring("Unsupported"));
        CHECK_THROWS_WITH(parse_and_serialize("(?xx)a"), ContainsSubstring("Unsupported"));
        // Clearing the flags is fine
        REQUIRE(parse_and_serialize("(?i-i)(?-x)(?^)a") == "(SEQ (LIT 'a'))");
    }

    SECTION("Features that are not implemented yet") {
        for (const char* regex : {R"((a)\1)", "(?=a)", "(?<!a)", "(?>a)", "a++", "a{2}+", R"(\G)"}) {
            CHECK_THROWS_WITH(parse_and_serialize(regex), ContainsSubstring("Unsupported"));
        }
    }
}

// =====================================================================
// SERIALIZED RCG TESTS
// =====================================================================

TEST_CASE("PCRE2 Regex serialized RCG tests", "[noodler][pcre2]") {
    ast_manager m;
    reg_decl_plugins(m);

    SECTION("Regular pattern is a single match edge") {
        // Capture groups are removed, since they are not referenced
        REQUIRE(build_and_serialize_rcg("(a)[0-9]+", m) ==
                "(RCG (EDGE *->* [MATCH (re.++ (str.to_re \"a\") (re.+ (re.range \"0\" \"9\")))]))");
    }

    SECTION("Anchors of the text") {
        REQUIRE(build_and_serialize_rcg(R"(\Aa\z)", m) ==
                "(RCG (EDGE *->* [ANCHOR '^']) (EDGE *->* [MATCH (str.to_re \"a\")]) (EDGE *->* [ANCHOR '$']))");
    }

    SECTION("Dollar is a negative lookahead") {
        REQUIRE(build_and_serialize_rcg("a$", m) ==
                "(RCG"
                " (EDGE *->* [MATCH (str.to_re \"a\")])"
                " (EDGE *->* [LOOKAROUND ?! (re.union (re.inter re.allchar (re.comp (str.to_re \"\\u{a}\")))"
                " (re.++ (str.to_re \"\\u{a}\") re.allchar))])"
                ")");
    }
}

// =====================================================================
// CONSTRAINT GENERATION
// =====================================================================

TEST_CASE("PCRE2 Regex constraint generation", "[noodler][pcre2]") {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util util_s(m);
    const app_ref x(m.mk_const("x", util_s.mk_string_sort()), m);
    const theory_str_noodler_params params;

    SECTION("Regular pattern generates a plain membership") {
        RegexConstraintBuilder builder(m, symbol("pcre2"), zstring("[[:alpha:]_]\\w*\\h{,2}"), params);
        builder.build_rcg();
        const expr_ref formula = builder.generate_constraints(x);
        REQUIRE(builder.get_fresh_vars().empty());
        REQUIRE(util_s.str.is_in_re(formula));
    }

    SECTION("Pattern with a dollar introduces fresh variables") {
        RegexConstraintBuilder builder(m, symbol("pcre2"), zstring("a$"), params);
        builder.build_rcg();
        const expr_ref formula = builder.generate_constraints(x);
        REQUIRE(!builder.get_fresh_vars().empty());
        REQUIRE(!util_s.str.is_in_re(formula));
    }
}
