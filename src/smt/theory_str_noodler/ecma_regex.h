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

    zstring view_to_zstring(zstring_view view);

    // ================== ECMA REGEX LEXER ==================
    class ecma_lexer {
    public:
        explicit ecma_lexer(const zstring_view regex)
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

        token make_token(token_type type, const token_payload& payload = {});
        token get_hex_escape_seq_token();
        token get_unicode_escape_seq_token();
        token get_control_escape_seq_token();
        token get_named_capture_group_token();
        uint32_t get_backref_name_len(uint32_t name_start_pos) const;
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

    class ast_node {
    public:
        virtual ~ast_node() = default;
        virtual uint32_t print_dot(std::ostream& out, uint32_t& node_count) const = 0;
        virtual zstring serialize() const = 0;
    };

    using ast_node_ref = std::unique_ptr<ast_node>;

    class ast_node_disjunction : public ast_node {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void add_alternative(ast_node_ref alt);

    private:
        std::vector<ast_node_ref> m_alternatives;
    };

    class ast_node_alternative : public ast_node {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void add_term(ast_node_ref term);

    private:
        std::vector<ast_node_ref> m_terms;
    };

    class ast_node_assertion : public ast_node {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void set_type(token_type type);
        void set_payload(uint32_t payload);
        void set_expr(ast_node_ref expr);

    private:
        token_type m_assert_type {};
        uint32_t m_payload {};  // Pro ^, $, \b, \B,
        ast_node_ref m_child;   // Pro lookaroundy (mohou být null pro ^, $, \b)
    };

    class ast_node_quantifier : public ast_node {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void set(const token& t, ast_node_ref term);

    private:
        quantifier_range m_range {};
        ast_node_ref m_child;
    };

    class ast_node_literal : public ast_node {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void set_char(uint32_t ch);

    private:
        uint32_t m_char = std::numeric_limits<uint32_t>::max();
    };

    class ast_node_dot : public ast_node {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
    };

    class ast_node_backreference : public ast_node {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void set_ref(zstring_view backref_name);
        void set_ref(uint32_t backref_number);

    private:
        std::variant<uint32_t, zstring_view> m_backref;
    };

    enum class group_type {
        NORMAL,
        NONCAPTURE,
        NAMED
    };

    class ast_node_group : public ast_node {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void set_type(group_type type);
        void set_name(zstring_view name);
        void set_expr(ast_node_ref expr);

    private:
        group_type m_type = group_type::NORMAL;

        zstring_view m_name;
        ast_node_ref m_child;
    };

    enum class element_type {
        SINGLE,
        RANGE,
        ESCAPE
    };

    struct char_class_element {
        element_type kind = element_type::SINGLE;
        uint32_t lower = 0;  // for SINGLE and ESCAPE, this serves as the value
        uint32_t upper = std::numeric_limits<uint32_t>::max();
    };

    class ast_node_character_class : public ast_node {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void add_element(char_class_element elem);
        void set_negation(bool neg);

    private:
        bool m_is_negated = false;
        std::vector<char_class_element> m_elements;
    };

    struct class_atom {
        bool is_escape;
        uint32_t val;
    };

    // =============== ECMA REGEX PARSER ===============

    class ecma_parser {
    public:
        explicit ecma_parser(const zstring_view regex)
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

        void parse_class_ranges(const std::unique_ptr<ast_node_character_class>& char_class_parent);
        void parse_class_ranges_tail(const std::unique_ptr<ast_node_character_class>& char_class_parent,
                                     class_atom prev_atom);
        void parse_dash_tail(const std::unique_ptr<ast_node_character_class>& char_class_parent,
                             class_atom prev_atom) const;
        class_atom parse_class_atom();
        class_atom parse_class_atom_no_dash();

        void add_atom_to_class(const std::unique_ptr<ast_node_character_class>& char_class_parent,
                               class_atom atom) const;
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
