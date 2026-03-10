#pragma once

#include "ast/ast.h"
#include "util/zstring.h"
#include "util/zstring_view.h"

#include <memory>
#include <ostream>
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
        QUANTIFIER,              // *, +, ?, {n,m}
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
    public:
        explicit ecma_lexer(zstring_view regex)
            : m_regex(regex) { }

        token get_next_token();

    private:
        zstring_view m_regex;
        uint32_t m_position = 0;
        uint32_t m_lexeme_start_pos = 0;
        uint32_t m_num_capture_groups = 0;
        bool m_in_char_class = false;
        bool m_first_in_char_class = false;
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

        token make_token(token_type type, token_payload payload = {});
        token get_hex_escape_seq_token();
        token get_unicode_escape_seq_token();
        token get_control_escape_seq_token();
        token get_named_capture_group_token();
        uint32_t get_backref_name_len(uint32_t name_start_pos);
        token get_named_backref_token();
        token octal_or_backref(uint32_t first_digit);
        token get_octal_escape_sequence_token(bool from_char_class, uint32_t first_digit);
        uint32_t validate_and_get_bound(uint32_t& bound);
        token get_braced_quant_token();
        token get_lookbehind_or_named_group_token();
        token get_special_group_or_lookaround_token();
        token get_group_token();
        token get_escape_sequence_token();
        token get_token_standard();
        token get_char_class_escape_sequence_token();
        token get_token_char_class();
        bool is_capture_or_named_capture(uint32_t position) const;
        void perform_first_traverse();
    };

    // ================== ECMA REGEX AST ==================
    enum class ast_node_type {
        DISJUNCTION,
        ALTERNATIVE,
        ASSERTION,
        QUANTIFIER,
        LITERAL,
        DOT,
        BACKREFERENCE,
        CHAR_CLASS_ESCAPE,
        GROUP,
        GROUP_NAMED,
        GROUP_NONCAPTURE,
        CHARACTER_CLASS,
        CLASS_RANGES,
        CLASS_ATOM
    };

    struct ast_node;
    using ast_node_ref = std::shared_ptr<ast_node>;

    struct ast_node {
        ast_node_type type;
        token_payload payload;
        bool is_negated;  // used for character classes
        std::vector<ast_node_ref> children;

        ast_node(ast_node_type t, token_payload p = {}, bool n = false)
            : type(t),
              payload(p),
              is_negated(n) { }

        void print_dot(std::ostream& out, int& node_count) const;
    };

    // =============== ECMA REGEX PARSER ===============

    /**
     * @brief The ECMAScript2020 regular expression parser class.
     * The parser is based on grammar found at https://tc39.es/ecma262/2020/#sec-regular-expressions.
     *
     *
     */
    class ecma_parser {
    public:
        explicit ecma_parser(zstring_view regex)
            : m_lexer(regex),
              m_current_token(m_lexer.get_next_token()) { }

        ast_node_ref parse();

    private:
        ecma_lexer m_lexer;
        token m_current_token;

        void next();
        bool match(token_type type);
        token consume(token_type type, const char* message);

        ast_node_ref parse_disjunction();
        ast_node_ref parse_alternative();
        ast_node_ref parse_term();
        ast_node_ref parse_maybe_quantifier(ast_node_ref term);
        ast_node_ref parse_assertion();
        ast_node_ref parse_atom();
        ast_node_ref parse_group();
        ast_node_ref parse_character_class();
        bool parse_maybe_negation();
        void parse_class_ranges(const ast_node_ref& parent);
        void parse_class_ranges_tail(const ast_node_ref& parent);
        void parse_dash_tail(const ast_node_ref& parent);
        ast_node_ref parse_class_atom();
        ast_node_ref parse_class_atom_no_dash();
    };

    // =============== ECMA REGEX HANDLER ===============
    class ecma_regex_handler {
    public:
        explicit ecma_regex_handler(const zstring& regex_pattern)
            : m_regex(regex_pattern),
              m_parser(regex_pattern) { }

        regex_constraint_graph build_rcg() {
            ast_node_ref ast = m_parser.parse();
            return {};
        }

        void generate_constraints() { }

    private:
        zstring_view m_regex;
        ecma_parser m_parser;
    };
}  // namespace smt::noodler::ecma
