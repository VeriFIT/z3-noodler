#pragma once

#include "regex_ast.h"

#include "util/zstring.h"
#include "util/zstring_view.h"

#include <cstdint>
#include <unordered_map>
#include <variant>

// Frontend of the ECMAScript 2020 regex flavor: the lexer and the parser into the common AST
namespace smt::noodler::extended_regex::ecma {
    // ======================= TOKENS =======================
    enum class TokenType {
        ALTERNATION,             // |
        ASSERTION,               // ^, $, \b, \B
        BACKREFERENCE,           // \1, \2, \k<name>
        CHAR_CLASS_START,        // [
        CHAR_CLASS_END,          // ]
        CHAR_CLASS_NEGATION,     // '^' after '['
        CHAR_CLASS_RANGE,        // '-' inside '[]'
        CHAR_CLASS_ESCAPE,       // \d, \D, \s, \S, \w, \W
        DOT,                     // .
        END_OF_INPUT,            // EOF
        GROUP_START,             // (
        GROUP_NONCAPTURE_START,  // (?:
        GROUP_NAMED_START,       // (?<name>
        LOOKAHEAD_POS_START,     // (?=
        LOOKAHEAD_NEG_START,     // (?!
        LOOKBEHIND_POS_START,    // (?<=
        LOOKBEHIND_NEG_START,    // (?<!
        GROUP_END,               // )
        LITERAL,                 // a, b, c, ...
        QUANTIFIER,              // *, +, ?, {n,m}
    };

    struct QuantifierRange {
        uint64_t min;
        uint64_t max;
    };

    // no payload, literal/escape, quantifier_range, capture group names/raw string data
    using TokenPayload = std::variant<std::monostate, Z3Char, QuantifierRange, zstring_view>;

    struct Token {
        TokenType type;
        TokenPayload payload;
        zstring_view lexeme;
    };

    // ================== ECMA REGEX LEXER ==================

    /**
     * Tokenizes an ECMA regex string on demand.
     *
     * The first call to get_next_token() triggers a one-time pre-scan of the entire regex string to count capture
     * groups and populate the named group map. This is needed so that backreferences can be resolved correctly during
     * lexing.
     *
     * After the pre-scan, tokens are produced one at a time as get_next_token() is called. The lexer maintains a flag
     * m_in_char_class to switch between standard tokenization and character-class tokenization, since some characters
     * have different semantics inside a character class.
     */
    class ECMALexer {
    public:
        explicit ECMALexer(const zstring_view regex, std::unordered_map<zstring_view, GroupID>& named_groups)
            : m_regex(regex),
              m_named_groups(named_groups) { }

        Token get_next_token();

    private:
        zstring_view m_regex;
        std::size_t m_position = 0;
        std::size_t m_lexeme_start_pos = 0;
        std::size_t m_num_capture_groups = 0;
        bool m_in_char_class = false;
        bool m_first_in_char_class = false;
        bool m_first_traverse = true;
        std::unordered_map<zstring_view, GroupID>& m_named_groups;

        static bool is_digit(Z3Char digit);
        static bool is_alpha(Z3Char digit);
        static bool is_alnum(Z3Char digit);
        static bool is_hex_digit(Z3Char digit);
        static bool is_octal_digit(Z3Char digit);
        static bool is_upper(Z3Char digit);
        static uint32_t alphabet_rank(Z3Char digit);
        static Z3Char hex2char(zstring_view number);
        static Z3Char oct2char(zstring_view number);

        Token make_token(TokenType type, const TokenPayload& payload = {}) const;
        Token get_hex_escape_seq_token();
        Token get_unicode_escape_seq_token();
        Token get_control_escape_seq_token();
        Token get_named_capture_group_token();
        uint32_t get_backref_name_len(uint32_t name_start_pos) const;
        Token get_named_backref_token();
        Token octal_or_backref(Z3Char first_digit);
        Token get_octal_escape_sequence_token(bool from_char_class, Z3Char first_digit);
        uint32_t validate_and_get_bound(uint64_t& bound_value);
        Token make_quantifier_token(uint64_t min, uint64_t max);
        Token get_braced_quant_token();
        Token get_lookbehind_or_named_group_token();
        Token get_special_group_or_lookaround_token();
        Token get_group_token();
        Token get_escape_sequence_token();
        Token get_token_standard();
        Token get_char_class_escape_sequence_token();
        Token get_token_char_class();
        std::pair<bool, zstring_view> is_capture_or_named_capture(uint32_t position) const;
        void perform_first_traverse();
    };

    // =============== ECMA REGEX PARSER ===============

    /**
     * Recursive descent parser for ECMA regex syntax. Consumes tokens from ECMALexer and builds the common AST.
     * The grammar is approximately (simplified from the ECMA 2020 standard, because lexer takes care of some details):
     *   disjunction  -> alternative ('|' alternative)*
     *   alternative  -> term*
     *   term         -> assertion | atom quantifier?
     *   atom         -> literal | dot | backref | char_class_escape | group | char_class
     *
     * The ECMA constructs are translated into the primitives of the common AST while parsing, i.e., literals, the
     * dot, character classes and class escapes into character sets, word boundaries into lookarounds, and
     * non-capturing groups into their subpatterns. Repetitions and backreferences get the ES2020 semantics.
     */
    struct CharClassAtom {
        bool is_escape;
        Z3Char val;
    };

    class ECMAParser {
    public:
        explicit ECMAParser(const zstring_view regex)
            : m_lexer(regex, m_named_groups),
              m_current_token(m_lexer.get_next_token()) { }

        NodeRef parse();

    private:
        std::unordered_map<zstring_view, GroupID> m_named_groups {};
        ECMALexer m_lexer;
        Token m_current_token;
        GroupID m_current_group_id = 0;

        void next();
        bool match(TokenType type);
        Token consume(TokenType type, const char* message);

        NodeRef parse_disjunction();
        NodeRef parse_alternative();
        NodeRef parse_term();
        NodeRef parse_maybe_quantifier(NodeRef term);
        NodeRef parse_assertion();
        NodeRef parse_atom();
        NodeRef parse_group();
        NodeRef parse_character_class();

        void parse_class_ranges(CharSet& chars);
        void parse_class_ranges_tail(CharSet& chars, CharClassAtom prev_atom);
        void parse_dash_tail(CharSet& chars, CharClassAtom atom_before_dash);
        CharClassAtom parse_class_atom();
        CharClassAtom parse_class_atom_no_dash();

        static void add_atom_to_class(CharSet& chars, CharClassAtom atom);
        static void add_range_to_class(CharSet& chars, Z3Char from, Z3Char to);

        // \w (https://tc39.es/ecma262/2020/#sec-characterclassescape)
        static CharSet word_chars();
        // \s is WhiteSpace or LineTerminator (https://tc39.es/ecma262/2020/#sec-characterclassescape)
        static CharSet white_space_chars();
        /**
         * @brief The characters of the class escape \d, \D, \s, \S, \w or \W given by its letter @p escape.
         */
        static CharSet class_escape_chars(Z3Char escape);
        // Without the dotAll flag (flags are not supported), '.' matches any character except a line terminator
        // (https://tc39.es/ecma262/2020/#sec-atom)
        static CharSet dot_chars();
    };
}  // namespace smt::noodler::extended_regex::ecma
