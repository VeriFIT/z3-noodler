#pragma once

#include "regex_ast.h"

#include "util/zstring_view.h"

#include <cstdint>
#include <optional>
#include <string>
#include <variant>

// Frontend of the RE2 regex flavor (https://github.com/google/re2/wiki/Syntax): the lexer and the parser into the
// common AST
namespace smt::noodler::extended_regex::re2 {
    // ======================= TOKENS =======================
    enum class TokenType {
        ALTERNATION,             // |
        ASSERTION,               // ^, $, \A, \z, \b, \B
        CHAR_CLASS_START,        // [
        CHAR_CLASS_END,          // ]
        CHAR_CLASS_NEGATION,     // '^' after '['
        CHAR_CLASS_RANGE,        // '-' between the bounds of a range inside '[]'
        CHAR_CLASS_ESCAPE,       // \d, \D, \s, \S, \w, \W
        POSIX_CLASS,             // [:alpha:], [:^alpha:] inside '[]'
        DOT,                     // .
        END_OF_INPUT,            // EOF
        GROUP_START,             // (
        GROUP_NAMED_START,       // (?P<name>, (?<name>
        GROUP_NONCAPTURE_START,  // (?:, (?flags:
        FLAGS,                   // (?flags)
        GROUP_END,               // )
        LITERAL,                 // a, \*, \x41, \101, characters of \Q...\E, ...
        QUANTIFIER,              // *, +, ?, {n}, {n,}, {n,m}, each possibly followed by ? (lazy)
    };

    // Flags of RE2 regexes, changed by (?flags) and (?flags:re)
    enum Flag : uint8_t {
        CASE_INSENSITIVE = 1,  // i
        MULTI_LINE = 2,        // m: ^ and $ match also at the start and at the end of lines
        DOT_NL = 4,            // s: '.' matches also \n
        UNGREEDY = 8,          // U: swaps the meaning of x* and x*?, x+ and x+?, ...
    };

    // Flags set and cleared by (?flags) or (?flags:re), e.g., (?i-s) sets i and clears s
    struct FlagChanges {
        uint8_t set = 0;
        uint8_t cleared = 0;
    };

    struct QuantifierRange {
        uint64_t min;
        uint64_t max;
    };

    // no payload, literal/escape/assertion, quantifier range, flag changes, capture group/POSIX class names
    using TokenPayload = std::variant<std::monostate, Z3Char, QuantifierRange, FlagChanges, zstring_view>;

    struct Token {
        TokenType type;
        TokenPayload payload;
        zstring_view lexeme;
    };

    // ================== RE2 REGEX LEXER ==================

    /**
     * Tokenizes an RE2 regex string on demand.
     *
     * The lexer switches between standard tokenization, character-class tokenization and quoted text (\Q...\E), since
     * characters have different meanings in them. Inside a character class, the lexer tracks the position in the
     * current element of the class, which determines whether ']' closes the class, whether '-' makes a range and
     * whether "[:" starts a POSIX class.
     *
     * The lexer reports invalid escape sequences, groups and flags; whether the tokens follow each other correctly is
     * checked by RE2Parser.
     */
    class RE2Lexer {
    public:
        explicit RE2Lexer(const zstring_view regex)
            : m_regex(regex) { }

        Token get_next_token();

    private:
        enum class ClassPosition {
            START,        // right after '[', where '^' negates the class
            FIRST,        // at the first element, where ']' is a literal
            ELEMENT,      // at the start of an element
            AFTER_LOWER,  // after a single character, which can be the lower bound of a range
            UPPER,        // after '-' of a range, at its upper bound
        };

        zstring_view m_regex;
        std::size_t m_position = 0;
        std::size_t m_lexeme_start_pos = 0;
        bool m_in_char_class = false;
        ClassPosition m_class_position = ClassPosition::START;
        bool m_in_quote = false;

        Token make_token(TokenType type, const TokenPayload& payload = {}) const;
        void throw_syntax_error(const std::string& message) const;

        Token get_token_standard();
        Token get_token_char_class();
        Token get_quoted_token();
        Token get_escape_sequence_token();
        Token get_char_class_escape_sequence_token();
        Z3Char parse_escaped_char(Z3Char escaped);
        Z3Char parse_hex_escape();
        Token get_group_token();
        Token get_named_group_token(std::size_t name_start);
        Token get_flags_token();
        Token get_quantifier_token(Z3Char op);
        Token get_braced_quantifier_token();
        bool parse_integer(std::size_t& pos, uint64_t& value) const;

        static bool is_digit(Z3Char ch);
        static bool is_octal_digit(Z3Char ch);
        static bool is_alnum(Z3Char ch);
        // The value of the hexadecimal digit @p ch, or -1 if @p ch is no hexadecimal digit
        static int hex_value(Z3Char ch);
    };

    // =============== RE2 REGEX PARSER ===============

    /**
     * Recursive descent parser for RE2 regex syntax. Consumes tokens from RE2Lexer and builds the common AST.
     * The grammar is:
     *   disjunction  -> alternative ('|' alternative)*
     *   alternative  -> (term | flags)*
     *   term         -> (assertion | atom) quantifier?
     *   atom         -> literal | dot | class_escape | group | char_class
     *
     * The RE2 constructs are translated into the primitives of the common AST while parsing, i.e., literals, the
     * dot, character classes and class escapes into character sets, word boundaries and the anchors of lines into
     * lookarounds, and non-capturing groups into their subpatterns. The flags hold until the end of the enclosing
     * group (also in the following alternatives), the flags of (?flags:re) only in re.
     *
     * RE2 has no backreferences, so the capture groups do not influence the matched strings and the semantics of
     * captures in repetitions does not matter.
     *
     * Unsupported: case-insensitive matching (flag i), Unicode classes (\p, \P) and \C.
     */
    class RE2Parser {
    public:
        explicit RE2Parser(const zstring_view regex)
            : m_lexer(regex),
              m_current_token(m_lexer.get_next_token()) { }

        NodeRef parse();

    private:
        RE2Lexer m_lexer;
        Token m_current_token;
        GroupID m_current_group_id = 0;
        uint8_t m_flags = 0;

        void next();
        bool match(TokenType type);
        void throw_syntax_error(const std::string& message) const;
        void apply_flags(FlagChanges changes);

        NodeRef parse_disjunction();
        NodeRef parse_alternative();
        NodeRef parse_term();
        NodeRef parse_maybe_quantifier(NodeRef term);
        NodeRef parse_assertion();
        NodeRef parse_atom();
        NodeRef parse_group();
        NodeRef parse_character_class();

        // \w, i.e., [0-9A-Za-z_] (RE2 classes are ASCII only)
        static CharSet word_chars();
        // \s, i.e., [\t\n\f\r ]
        static CharSet space_chars();
        /**
         * @brief The characters of the Perl class escape \d, \D, \s, \S, \w or \W given by its letter @p escape.
         */
        static CharSet perl_class_chars(Z3Char escape);
        /**
         * @brief The characters of the ASCII class [:name:] with the given @p name, or nothing for an unknown name.
         */
        static std::optional<CharSet> ascii_class_chars(const std::string& name);
        /**
         * @brief Divide @p remaining by the counts of the repetitions on every path from @p node to a leaf, return the
         * smallest result (RE2 RepetitionWalker).
         *
         * The count of a repetition is its maximum, or its minimum if it is unbounded. The counts of *, + and ? are at
         * most 1, so only the counted repetitions matter, as in RE2.
         */
        static uint64_t remaining_repeat_count(const Node& node, uint64_t remaining);
    };
}  // namespace smt::noodler::extended_regex::re2
