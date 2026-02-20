#pragma once

#include "util/zstring.h"
#include "util/zstring_view.h"

#include <vector>

namespace smt::noodler::ecma {
    // ======================= UTILS =======================
    typedef enum token_type {
        ALTERNATION,
        ANCHOR_END,
        ANCHOR_NONWORD_BOUNDARY,
        ANCHOR_START,
        ANCHOR_WORD_BOUNDARY,
        BACKREFERENCE,
        CHAR_CLASS_END,
        CHAR_CLASS_NEGATION,
        CHAR_CLASS_RANGE,
        CHAR_CLASS_START,
        COMMA,
        DIGIT_CLASS,
        DOT,
        END_OF_INPUT,
        GROUP_END,
        GROUP_NAMED_START,
        GROUP_NONCAPTURE_START,
        GROUP_START,
        LITERAL,
        LOOKAHEAD_NEGATIVE_START,
        LOOKAHEAD_POSITIVE_START,
        LOOKBEHIND_NEGATIVE_START,
        LOOKBEHIND_POSITIVE_START,
        NAMED_BACKREFERENCE,
        NON_DIGIT_CLASS,
        NON_WHITESPACE_CLASS,
        NON_WORD_CHAR_CLASS,
        QUANT_BRACE_END,
        QUANT_BRACE_START,
        QUANT_PLUS,
        QUANT_QUESTION_MARK,
        QUANT_STAR,
        WHITESPACE_CLASS,
        WORD_CHAR_CLASS
    } token_type;

    struct token {
        token_type type;
        zstring_view text;
    };

    class sequence_validator {
        inline bool is_octal(uint32_t digit) const;
        zstring_view m_regex;
        uint32_t m_position;

    public:
        sequence_validator(zstring_view regex, uint32_t position);

        void validate_hex_escape_sequence(uint32_t& token_length) const;
        void validate_unicode_escape_sequence(uint32_t& token_length) const;
        void validate_control_escape_sequence(uint32_t& token_length) const;
        void validate_named_back_reference(uint32_t& token_length) const;
        void validate_back_reference(uint32_t& token_length) const;
        void validate_octal_escape_sequence(uint32_t& token_length) const;
    };

    // =============== REGEX CONSTRAINT GRAPH ===============
    struct regex_constraint_graph { };

    // ================== ECMA REGEX LEXER ==================
    class ecma_lexer {
    private:
        zstring_view m_regex;
        uint32_t m_position = 0;
        bool m_in_char_class = false;

        uint32_t get_backref_name_length(uint32_t group_name_start_pos) const;
        token_type parse_fourth_char_in_capture_group(uint32_t& token_length) const;
        token_type parse_third_char_in_capture_group(uint32_t& token_length) const;
        token_type get_group_token(uint32_t& token_length) const;
        token_type get_escape_sequence_token(uint32_t& token_length) const;
        token_type get_standard_token_type(uint32_t& token_length, uint32_t current_char);
        token_type get_char_class_escape_sequence_token(uint32_t& token_length) const;
        token_type get_token_type_from_char_class(uint32_t& token_length, uint32_t current_char);

    public:
        explicit ecma_lexer(zstring_view regex)
            : m_regex(regex) { }

        token get_next_token();
    };

    // =============== ECMA REGEX PARSER ===============
    class ecma_parser {
    private:
        ecma_lexer m_lexer;
        token m_current_token;

        void next_token();
        bool match(token_type type);
        void consume(token_type type, const char* message);

        void parse_disjunction();
        void parse_alternative();
        void parse_term();
        void parse_assertion();
        void parse_atom();
        void parse_quantifier();
        void parse_braced_quantifier();
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
