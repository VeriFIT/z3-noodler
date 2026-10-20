#include "smt/theory_str_noodler/extended_regex/extended_regex.h"
#include "smt/theory_str_noodler/extended_regex/re2_regex.h"

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "params/theory_str_noodler_params.h"

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>
#include <string>
#include <vector>

using namespace smt::noodler::extended_regex;
using namespace smt::noodler::extended_regex::re2;
using Catch::Matchers::ContainsSubstring;

namespace {
    // All the tokens of @p regex before the end of input
    std::vector<Token> tokenize(const zstring& regex) {
        RE2Lexer lexer(regex);
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
        return serialize(*RE2Parser(regex).parse());
    }

    std::string build_and_serialize_rcg(const zstring& regex, ast_manager& m) {
        const theory_str_noodler_params params;
        RegexConstraintBuilder builder(m, symbol("re2"), regex, params);
        return serialize_rcg(builder.build_rcg(), m);
    }

    // \w
    const std::string WORD = "(SET '0'-'9' 'A'-'Z' '_' 'a'-'z')";
    // Any character except \n
    const std::string DOT = R"((SET ^ '\u{a}'))";
}  // namespace

// =====================================================================
// LEXER TESTS
// =====================================================================

TEST_CASE("RE2 Regex Lexer", "[noodler][re2]") {
    SECTION("Literals and escape sequences") {
        // a, escaped punctuation, \_, hexadecimal, octal and C escapes
        REQUIRE(literals(R"(a\*\_\x41\x{42}\x{000043}\101\0\012\n\t\a\f\v\r)") ==
                std::vector<Z3Char> {'a', '*', '_', 'A', 'B', 'C', 'A', '\0', '\n', '\n', '\t', '\a', '\f', '\v',
                                     '\r'});
        // An octal escape has at most three digits
        REQUIRE(literals(R"(\1234)") == std::vector<Z3Char> {0123, '4'});
    }

    SECTION("Quoted text") {
        REQUIRE(token_types(R"(\Qa.*\E+)") == std::vector<TokenType> {TokenType::LITERAL, TokenType::LITERAL,
                                                                      TokenType::LITERAL, TokenType::QUANTIFIER});
        REQUIRE(literals(R"(\Qa.*\E+)") == std::vector<Z3Char> {'a', '.', '*'});
        // Without \E, the text is quoted up to the end of the regex
        REQUIRE(literals(R"(\Q(\b)") == std::vector<Z3Char> {'(', '\\', 'b'});
    }

    SECTION("Quantifiers") {
        const std::vector<Token> tokens = tokenize("a*b+?c??d{2}e{2,}?f{2,5}");
        std::vector<std::pair<uint64_t, uint64_t>> ranges;
        for (const Token& t : tokens) {
            if (t.type == TokenType::QUANTIFIER) {
                ranges.emplace_back(std::get<QuantifierRange>(t.payload).min, std::get<QuantifierRange>(t.payload).max);
            }
        }
        REQUIRE(ranges == std::vector<std::pair<uint64_t, uint64_t>> {
                              {0, UNBOUNDED}, {1, UNBOUNDED}, {0, 1}, {2, 2}, {2, UNBOUNDED}, {2, 5}});
    }

    SECTION("Brace that does not start a counted repetition is a literal") {
        REQUIRE(literals("a{,2}") == std::vector<Z3Char> {'a', '{', ',', '2', '}'});
        REQUIRE(literals("a{01}") == std::vector<Z3Char> {'a', '{', '0', '1', '}'});
        REQUIRE(literals("a{2") == std::vector<Z3Char> {'a', '{', '2'});
    }

    SECTION("Assertions") {
        std::vector<Z3Char> assertions;
        for (const Token& t : tokenize(R"(^\A\b\B\z$)")) {
            REQUIRE(t.type == TokenType::ASSERTION);
            assertions.push_back(std::get<Z3Char>(t.payload));
        }
        REQUIRE(assertions == std::vector<Z3Char> {'^', 'A', 'b', 'B', 'z', '$'});
    }

    SECTION("Groups and flags") {
        // The names of groups are views into the regex, which has to outlive the tokens
        const zstring regex("(a)(?:b)(?P<x>c)(?<y>d)(?m)(?s-m:e)");
        const std::vector<Token> tokens = tokenize(regex);
        std::vector<TokenType> types;
        for (const Token& t : tokens) {
            if (t.type != TokenType::LITERAL) {
                types.push_back(t.type);
            }
        }
        REQUIRE(types == std::vector<TokenType> {TokenType::GROUP_START, TokenType::GROUP_END,
                                                 TokenType::GROUP_NONCAPTURE_START, TokenType::GROUP_END,
                                                 TokenType::GROUP_NAMED_START, TokenType::GROUP_END,
                                                 TokenType::GROUP_NAMED_START, TokenType::GROUP_END, TokenType::FLAGS,
                                                 TokenType::GROUP_NONCAPTURE_START, TokenType::GROUP_END});
        REQUIRE(std::get<zstring_view>(tokens[6].payload) == zstring("x"));
        REQUIRE(std::get<zstring_view>(tokens[9].payload) == zstring("y"));
        const FlagChanges multi_line = std::get<FlagChanges>(tokens[12].payload);
        REQUIRE(multi_line.set == MULTI_LINE);
        REQUIRE(multi_line.cleared == 0);
        const FlagChanges dot_nl = std::get<FlagChanges>(tokens[13].payload);
        REQUIRE(dot_nl.set == DOT_NL);
        REQUIRE(dot_nl.cleared == MULTI_LINE);
    }

    SECTION("Character class") {
        // ']' is a literal at the start of the class, '-' makes a range unless it is followed by ']' or starts an
        // element
        REQUIRE(token_types("[^]a-c-]") ==
                std::vector<TokenType> {TokenType::CHAR_CLASS_START, TokenType::CHAR_CLASS_NEGATION, TokenType::LITERAL,
                                        TokenType::LITERAL, TokenType::CHAR_CLASS_RANGE, TokenType::LITERAL,
                                        TokenType::LITERAL, TokenType::CHAR_CLASS_END});
        REQUIRE(token_types("[--a]") == std::vector<TokenType> {TokenType::CHAR_CLASS_START, TokenType::LITERAL,
                                                                TokenType::CHAR_CLASS_RANGE, TokenType::LITERAL,
                                                                TokenType::CHAR_CLASS_END});
        REQUIRE(token_types(R"([\d-a])") == std::vector<TokenType> {TokenType::CHAR_CLASS_START,
                                                                    TokenType::CHAR_CLASS_ESCAPE, TokenType::LITERAL,
                                                                    TokenType::LITERAL, TokenType::CHAR_CLASS_END});
    }

    SECTION("POSIX classes") {
        const zstring regex("[[:alpha:][:^digit:]x]");
        const std::vector<Token> tokens = tokenize(regex);
        REQUIRE(tokens.size() == 5);
        REQUIRE(tokens[1].type == TokenType::POSIX_CLASS);
        REQUIRE(std::get<zstring_view>(tokens[1].payload) == zstring("alpha"));
        REQUIRE(tokens[2].type == TokenType::POSIX_CLASS);
        REQUIRE(std::get<zstring_view>(tokens[2].payload) == zstring("^digit"));
        // "[:" as the upper bound of a range is no POSIX class
        REQUIRE(literals("[!-[:alpha:]]") == std::vector<Z3Char> {'!', '[', ':', 'a', 'l', 'p', 'h', 'a', ':', ']'});
    }

    SECTION("Invalid escape sequences") {
        // Backreferences, escaped letters and digits that are no escape sequences, invalid hexadecimal escapes
        for (const char* regex : {R"(\1)", R"(\8)", R"(\q)", R"(\x)", R"(\x4)", R"(\xg1)", R"(\x{})", R"(\x{110000})",
                                  R"(\E)", "a\\", R"([\b])"}) {
            CHECK_THROWS_WITH(tokenize(regex), ContainsSubstring("RE2 regex syntax error"));
        }
    }

    SECTION("Invalid groups") {
        // Lookarounds, invalid flags and names of groups
        for (const char* regex : {"(?=a)", "(?!a)", "(?<=a)", "(?<!a)", "(?#a)", "(?>a)", "(?P=n)", "(?x)", "(?--i)",
                                  "(?-)", "(?i-)", "(?", "(?P<>a)", "(?P<a-b>c)", "(?P<x"}) {
            CHECK_THROWS_WITH(tokenize(regex), ContainsSubstring("RE2 regex syntax error"));
        }
    }

    SECTION("Unsupported features") {
        for (const char* regex : {R"(\pL)", R"(\p{Greek})", R"(\PN)", R"([\p{Greek}])", R"(\C)"}) {
            CHECK_THROWS_WITH(tokenize(regex), ContainsSubstring("Unsupported"));
        }
    }
}

// =====================================================================
// PARSER TESTS
// =====================================================================

TEST_CASE("RE2 Regex Parser", "[noodler][re2]") {
    SECTION("Literals, concatenation and alternation") {
        REQUIRE(parse_and_serialize("") == "(SEQ)");
        REQUIRE(parse_and_serialize("ab") == "(SEQ (LIT 'a') (LIT 'b'))");
        REQUIRE(parse_and_serialize("a|") == "(DISJ (SEQ (LIT 'a')) (SEQ))");
        REQUIRE(parse_and_serialize(R"(\Qa.b\E)") == "(SEQ (LIT 'a') (LIT '.') (LIT 'b'))");
    }

    SECTION("Dot and Perl classes") {
        REQUIRE(parse_and_serialize(".") == "(SEQ " + DOT + ")");
        REQUIRE(parse_and_serialize(R"(\d)") == "(SEQ (SET '0'-'9'))");
        REQUIRE(parse_and_serialize(R"(\D)") == "(SEQ (SET ^ '0'-'9'))");
        REQUIRE(parse_and_serialize(R"(\s)") == R"((SEQ (SET '\u{9}'-'\u{a}' '\u{c}'-'\u{d}' ' ')))");
        REQUIRE(parse_and_serialize(R"(\w)") == "(SEQ " + WORD + ")");
    }

    SECTION("Character classes") {
        // Negated classes match \n
        REQUIRE(parse_and_serialize("[^a]") == "(SEQ (SET ^ 'a'))");
        REQUIRE(parse_and_serialize("[]a]") == "(SEQ (SET ']' 'a'))");
        REQUIRE(parse_and_serialize("[a-c-]") == "(SEQ (SET '-' 'a'-'c'))");
        REQUIRE(parse_and_serialize("[--a]") == "(SEQ (SET '-'-'a'))");
        REQUIRE(parse_and_serialize(R"([\d-a])") == "(SEQ (SET '-' '0'-'9' 'a'))");
        REQUIRE(parse_and_serialize("[[:alpha:]_]") == "(SEQ (SET 'A'-'Z' '_' 'a'-'z'))");
        REQUIRE(parse_and_serialize("[[:^alpha:]]") == "(SEQ (SET ^ 'A'-'Z' 'a'-'z'))");
        REQUIRE(parse_and_serialize("[[:space:]]") == R"((SEQ (SET '\u{9}'-'\u{d}' ' ')))");
    }

    SECTION("Anchors and word boundaries") {
        // $ matches only at the end of the text (like \z, not \Z)
        REQUIRE(parse_and_serialize("^a$") == "(SEQ (ASSERT '^') (LIT 'a') (ASSERT '$'))");
        REQUIRE(parse_and_serialize(R"(\Aa\z)") == "(SEQ (ASSERT '^') (LIT 'a') (ASSERT '$'))");
        REQUIRE(parse_and_serialize(R"(\b)") == "(SEQ (DISJ (SEQ (ASSERT ?<= " + WORD + ") (ASSERT ?! " + WORD +
                                                    "))"
                                                    " (SEQ (ASSERT ?<! " +
                                                    WORD + ") (ASSERT ?= " + WORD + "))))");
    }

    SECTION("Multi-line anchors are lookarounds") {
        REQUIRE(parse_and_serialize("(?m)^a$") == "(SEQ (ASSERT ?<! " + DOT + ") (LIT 'a') (ASSERT ?! " + DOT + "))");
        REQUIRE(parse_and_serialize("(?m:^)^") == "(SEQ (SEQ (ASSERT ?<! " + DOT + ")) (ASSERT '^'))");
    }

    SECTION("Flags hold until the end of the enclosing group") {
        // The flag s set in the first alternative holds also in the second one, but not after the group
        REQUIRE(parse_and_serialize("(a(?s).|.).") ==
                "(SEQ (GROUP #1 (DISJ (SEQ (LIT 'a') (SET ^)) (SEQ (SET ^)))) " + DOT + ")");
        REQUIRE(parse_and_serialize("(?s:a.)b.") == "(SEQ (SEQ (LIT 'a') (SET ^)) (LIT 'b') " + DOT + ")");
        REQUIRE(parse_and_serialize("(?s)a(?-s).") == "(SEQ (LIT 'a') " + DOT + ")");
    }

    SECTION("Repetitions") {
        REQUIRE(parse_and_serialize("a*?b+c??") ==
                "(SEQ (QUANT {0,inf} (LIT 'a')) (QUANT {1,inf} (LIT 'b')) (QUANT {0,1} (LIT 'c')))");
        REQUIRE(parse_and_serialize("a{2}b{2,}c{2,5}?") ==
                "(SEQ (QUANT {2,2} (LIT 'a')) (QUANT {2,inf} (LIT 'b')) (QUANT {2,5} (LIT 'c')))");
        // Repetitions of assertions are allowed
        REQUIRE(parse_and_serialize("^?a") == "(SEQ (QUANT {0,1} (ASSERT '^')) (LIT 'a'))");
        REQUIRE(parse_and_serialize("a{1000}") == "(SEQ (QUANT {1000,1000} (LIT 'a')))");
        REQUIRE(parse_and_serialize("(?:a{10}){100}") == "(SEQ (QUANT {100,100} (SEQ (QUANT {10,10} (LIT 'a')))))");
    }

    SECTION("Groups") {
        REQUIRE(parse_and_serialize("(a)(?P<x>b)(?<y>c)(?:d)") ==
                "(SEQ (GROUP #1 (SEQ (LIT 'a'))) (GROUP #2 (SEQ (LIT 'b'))) (GROUP #3 (SEQ (LIT 'c')))"
                " (SEQ (LIT 'd')))");
    }

    SECTION("Invalid repetitions") {
        CHECK_THROWS_WITH(parse_and_serialize("a**"), ContainsSubstring("bad repetition operator"));
        CHECK_THROWS_WITH(parse_and_serialize("a{2}{3}"), ContainsSubstring("bad repetition operator"));
        CHECK_THROWS_WITH(parse_and_serialize("*a"), ContainsSubstring("no argument for repetition operator"));
        CHECK_THROWS_WITH(parse_and_serialize("a|{2}"), ContainsSubstring("no argument for repetition operator"));
        CHECK_THROWS_WITH(parse_and_serialize("a{1001}"), ContainsSubstring("invalid repetition size"));
        CHECK_THROWS_WITH(parse_and_serialize("a{2,1}"), ContainsSubstring("invalid repetition size"));
        // Nested counted repetitions repeat more than 1000 times
        CHECK_THROWS_WITH(parse_and_serialize("(a{10}){101}"), ContainsSubstring("invalid repetition size"));
    }

    SECTION("Invalid brackets and parentheses") {
        CHECK_THROWS_WITH(parse_and_serialize("[a"), ContainsSubstring("missing ]"));
        CHECK_THROWS_WITH(parse_and_serialize("[]"), ContainsSubstring("missing ]"));
        CHECK_THROWS_WITH(parse_and_serialize("(a"), ContainsSubstring("missing )"));
        CHECK_THROWS_WITH(parse_and_serialize("a)"), ContainsSubstring("unexpected )"));
    }

    SECTION("Invalid character classes") {
        CHECK_THROWS_WITH(parse_and_serialize("[z-a]"), ContainsSubstring("invalid character class range"));
        CHECK_THROWS_WITH(parse_and_serialize(R"([a-\d])"), ContainsSubstring("invalid character class range"));
        CHECK_THROWS_WITH(parse_and_serialize("[[:foo:]]"), ContainsSubstring("invalid character class range"));
    }

    SECTION("Case-insensitive matching is unsupported") {
        CHECK_THROWS_WITH(parse_and_serialize("(?i)a"), ContainsSubstring("Unsupported"));
        CHECK_THROWS_WITH(parse_and_serialize("(?i:a)"), ContainsSubstring("Unsupported"));
        // Clearing the flag is fine
        REQUIRE(parse_and_serialize("(?i-i)a") == "(SEQ (LIT 'a'))");
    }
}

// =====================================================================
// SERIALIZED RCG TESTS
// =====================================================================

TEST_CASE("RE2 Regex serialized RCG tests", "[noodler][re2]") {
    ast_manager m;
    reg_decl_plugins(m);

    SECTION("Regular pattern is a single match edge") {
        // Capture groups are removed, since RE2 has no backreferences
        REQUIRE(build_and_serialize_rcg("(a)[0-9]+", m) ==
                "(RCG (EDGE *->* [MATCH (re.++ (str.to_re \"a\") (re.+ (re.range \"0\" \"9\")))]))");
    }

    SECTION("Anchors") {
        REQUIRE(build_and_serialize_rcg("^a$", m) ==
                "(RCG (EDGE *->* [ANCHOR '^']) (EDGE *->* [MATCH (str.to_re \"a\")]) (EDGE *->* [ANCHOR '$']))");
    }

    SECTION("Multi-line anchors") {
        REQUIRE(build_and_serialize_rcg("(?m)^a$", m) ==
                "(RCG"
                " (EDGE *->* [LOOKAROUND ?<! (re.inter re.allchar (re.comp (str.to_re \"\\u{a}\")))])"
                " (EDGE *->* [MATCH (str.to_re \"a\")])"
                " (EDGE *->* [LOOKAROUND ?! (re.inter re.allchar (re.comp (str.to_re \"\\u{a}\")))])"
                ")");
    }
}

// =====================================================================
// CONSTRAINT GENERATION
// =====================================================================

TEST_CASE("RE2 Regex constraint generation", "[noodler][re2]") {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util util_s(m);
    const app_ref x(m.mk_const("x", util_s.mk_string_sort()), m);
    const theory_str_noodler_params params;

    SECTION("Regular pattern generates a plain membership") {
        RegexConstraintBuilder builder(m, symbol("re2"), zstring("[[:alpha:]_]\\w*"), params);
        builder.build_rcg();
        const expr_ref formula = builder.generate_constraints(x);
        REQUIRE(builder.get_fresh_vars().empty());
        REQUIRE(util_s.str.is_in_re(formula));
    }

    SECTION("Pattern with a word boundary introduces fresh variables") {
        RegexConstraintBuilder builder(m, symbol("re2"), zstring("a\\b"), params);
        builder.build_rcg();
        const expr_ref formula = builder.generate_constraints(x);
        REQUIRE(!builder.get_fresh_vars().empty());
        REQUIRE(!util_s.str.is_in_re(formula));
    }
}
