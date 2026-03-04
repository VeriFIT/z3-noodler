#pragma once

#include "ast/ast.h"
#include "util/zstring.h"
#include "util/zstring_view.h"

#include <variant>
#include <vector>

namespace smt::noodler::ecma {
    // ======================= UTILS =======================
    enum class token_type {
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
        QUANTIFIER,              // *, +, ?
    };

    typedef struct {
        uint32_t min;
        uint32_t max;
    } quantifier_range;

    // no payload, literal/escape, quantifier_range, capture group names/raw string data
    using token_payload = std::variant<std::monostate, uint32_t, quantifier_range, zstring_view>;

    struct token {
        token_type type;
        token_payload payload;
        zstring_view lexeme;
    };

    // =============== REGEX CONSTRAINT GRAPH ===============
    enum class rcg_edge_type {
        MATCH_EDGE,
        ASSERTION_EDGE,
        BACKREF_EDGE
    };

    typedef struct {
        app* regex;
    } match_edge;

    enum class assertion_direction {
        FORWARD,
        BACKWARD
    };

    typedef struct {
        app* regex;
        assertion_direction direction;
    } assertion_edge;

    typedef struct {
        std::variant<int, zstring_view> backreference;
    } backref_edge;

    using rcg_edge_payload = std::variant<match_edge, assertion_edge, backref_edge>;

    struct rcg_edge {
        rcg_edge_type type;
        rcg_edge_payload payload;
    };

    struct regex_constraint_graph {
        std::vector<std::vector<rcg_edge>> adj_list;
    };

    // ================== ECMA REGEX LEXER ==================
    class ecma_lexer {
    private:
        zstring_view m_regex;
        uint32_t m_position = 0;
        uint32_t m_token_len = 0;
        uint32_t m_num_capture_groups = 0;
        uint32_t m_lexeme_start_pos = 0;
        bool m_in_char_class = false;
        bool m_first_traverse = true;

        static bool is_digit(uint32_t digit);
        static bool is_alpha(uint32_t digit);
        static bool is_alnum(uint32_t digit);
        static bool is_hex_digit(uint32_t digit);
        static bool is_octal_digit(uint32_t digit);
        static bool is_upper(uint32_t digit);
        static uint32_t alphabet_rank(uint32_t digit);
        static uint32_t hex2dec(zstring_view number);
        static uint32_t oct2dec(zstring_view number);
        token get_hex_escape_seq_token() const;
        token get_unicode_escape_seq_token() const;
        token get_control_escape_seq_token() const;
        token get_named_capture_group_token(uint32_t group_name_start_pos) const;
        uint32_t get_backref_name_len(uint32_t name_start_pos);
        token get_named_backref_token();
        token octal_or_backref();
        token get_octal_escape_sequence_token();
        bool validate_and_get_bound(uint32_t& bound, uint32_t& current_pos) const;
        token get_braced_quant_token();
        token get_lookbehind_or_named_group_token();
        token get_special_group_or_lookaround_token();
        token get_group_token();
        token get_escape_sequence_token();
        token get_token_standard();
        token get_char_class_escape_sequence_token();
        token get_token_char_class();
        bool is_capture_or_named_capture(uint32_t position);
        static uint32_t octal_to_dec(zstring_view octal_text, uint32_t octal_len);


    public:
        explicit ecma_lexer(zstring_view regex)
            : m_regex(regex) { }

        token get_next_token();
        void perform_first_traverse();
    };

    // =============== ECMA REGEX PARSER ===============

    /**
     * @brief The ECMAScript2020 regular expression parser class.
     * The parser is based on grammar found at https://tc39.es/ecma262/2020/#sec-regular-expressions.
     *
     *
     */
    class ecma_parser {
    private:
        ecma_lexer m_lexer;
        token m_current_token;

        void next();
        bool match(token_type type);
        void consume(token_type type, const char* message);

        void parse_disjunction();
        void parse_alternative();
        void parse_term();
        void parse_assertion();
        void parse_atom();
        void parse_character_class();

    public:
        explicit ecma_parser(zstring_view regex)
            : m_lexer(regex),
              m_current_token(m_lexer.get_next_token()) { }

        regex_constraint_graph parse();
    };

    // =============== ECMA REGEX HANDLER ===============
    class ecma_regex_handler {
    private:
        zstring_view m_regex;

    public:
        explicit ecma_regex_handler(const zstring& regex_pattern)
            : m_regex(regex_pattern) { }

        void build_rcg() { }

        void generate_constraints() { }
    };
}  // namespace smt::noodler::ecma
