#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "util/zstring.h"
#include "util/zstring_view.h"

#include <memory>
#include <ostream>
#include <variant>
#include <vector>

namespace smt::noodler::ecma {
    // ======================= UTILS =======================
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
        uint32_t min;
        uint32_t max;
    };

    // no payload, literal/escape, quantifier_range, capture group names/raw string data
    using token_payload = std::variant<std::monostate, uint32_t, QuantifierRange, zstring_view>;

    struct Token {
        TokenType type;
        token_payload payload;
        zstring_view lexeme;
    };

    // =============== REGEX CONSTRAINT GRAPH ===============

    struct MatchEdge {
        app_ref regex;
    };

    enum class AssertionDirection {
        FORWARD,
        BACKWARD
    };

    struct AssertionEdge {
        app_ref regex;
        AssertionDirection direction;
    };

    struct BackrefEdge {
        std::variant<int, zstring_view> backreference;
    };

    using RCGEdgePayload = std::variant<MatchEdge, AssertionEdge, BackrefEdge>;
    using VertexId = uint32_t;
    using EdgeId = uint32_t;

    struct RCGEdge {
        EdgeId id;
        VertexId target;
        RCGEdgePayload payload;
    };

    struct RCGVertex {
        VertexId id;
        std::vector<RCGEdge> outgoing_edges;

        RCGVertex(const VertexId id, std::vector<RCGEdge> edges)
            : id(id),
              outgoing_edges(std::move(edges)) { }
    };

    struct RegexConstraintGraph {
        std::vector<RCGVertex> vertices;
        std::vector<RCGEdge> edges;

        void add_vertex(RCGVertex vtx);
        VertexId create_vertex();
        void add_edge(RCGEdge child);
        EdgeId create_edge();
    };

    struct GraphFragment {
        VertexId v_in;
        VertexId v_out;
        std::vector<EdgeId> edges_pointing_to_out;
    };

    zstring view_to_zstring(zstring_view view);

    // ================== ECMA REGEX LEXER ==================
    class ECMALexer {
    public:
        explicit ECMALexer(const zstring_view regex)
            : m_regex(regex) { }

        Token get_next_token();

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

        Token make_token(TokenType type, const token_payload& payload = {}) const;
        Token get_hex_escape_seq_token();
        Token get_unicode_escape_seq_token();
        Token get_control_escape_seq_token();
        Token get_named_capture_group_token();
        uint32_t get_backref_name_len(uint32_t name_start_pos) const;
        Token get_named_backref_token();
        Token octal_or_backref(uint32_t first_digit);
        Token get_octal_escape_sequence_token(bool from_char_class, uint32_t first_digit);
        uint32_t validate_and_get_bound(uint32_t& bound);
        Token get_braced_quant_token();
        Token get_lookbehind_or_named_group_token();
        Token get_special_group_or_lookaround_token();
        Token get_group_token();
        Token get_escape_sequence_token();
        Token get_token_standard();
        Token get_char_class_escape_sequence_token();
        Token get_token_char_class();
        bool is_capture_or_named_capture(uint32_t position) const;
        void perform_first_traverse();
    };

    // ================== ECMA REGEX AST ==================

    // When building RCG from AST, the methods return either a reference to the built sub-rcg, represented by GraphFragment,
    // or app* when the AST subtree contains regular parts of ECMA regex that can be compiled into an SMT-LIB regex.
    // (optimalization -- merging the regular parts of ECMA regex instead of creating edges for all of them)
    using RegexComponent = std::variant<GraphFragment, app_ref>;

    class ASTNode {
    public:
        virtual ~ASTNode() = default;
        virtual uint32_t print_dot(std::ostream& out, uint32_t& node_count) const = 0;
        virtual zstring serialize() const = 0;
        virtual RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const = 0;
    };

    using ASTNodeRef = std::unique_ptr<ASTNode>;

    class ASTNodeDisjunction : public ASTNode {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void add_alternative(ASTNodeRef alt);
        RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const override;

    private:
        std::vector<ASTNodeRef> m_alternatives;
    };

    class ASTNodeAlternative : public ASTNode {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void add_term(ASTNodeRef term);
        RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const override;

    private:
        std::vector<ASTNodeRef> m_terms;
    };

    class ASTNodeAssertion : public ASTNode {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void set_type(TokenType type);
        void set_payload(uint32_t payload);
        void set_expr(ASTNodeRef expr);
        RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const override;

    private:
        TokenType m_assert_type {};
        uint32_t m_payload {};              // for ^, $, \b, \B assertions
        ASTNodeRef m_subpattern = nullptr;  // for lookarounds (may be null for ^, $, \b, \B)
    };

    class ASTNodeQuantifier : public ASTNode {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void set(const Token& t, ASTNodeRef term);
        RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const override;

    private:
        QuantifierRange m_range {};
        ASTNodeRef m_child;
    };

    class ASTNodeLiteral : public ASTNode {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void set_char(uint32_t ch);
        RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const override;

    private:
        uint32_t m_char = std::numeric_limits<uint32_t>::max();
    };

    class ASTNodeDot : public ASTNode {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const override;
    };

    class ASTNodeBackref : public ASTNode {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void set_ref(zstring_view backref_name);
        void set_ref(uint32_t backref_number);
        RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const override;

    private:
        std::variant<uint32_t, zstring_view> m_backref;
    };

    enum class GroupType {
        NORMAL,
        NONCAPTURE,
        NAMED
    };

    class ASTNodeGroup : public ASTNode {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void set_type(GroupType type);
        void set_name(zstring_view name);
        void set_expr(ASTNodeRef expr);
        RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const override;

    private:
        GroupType m_type = GroupType::NORMAL;

        zstring_view m_name;
        ASTNodeRef m_child;
    };

    enum class ElementType {
        SINGLE,
        RANGE,
        ESCAPE
    };

    struct CharClassElement {
        ElementType kind = ElementType::SINGLE;
        uint32_t lower = 0;  // for SINGLE and ESCAPE, this serves as the value
        uint32_t upper = std::numeric_limits<uint32_t>::max();
    };

    class ASTNodeCharClass : public ASTNode {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void add_element(CharClassElement elem);
        void set_negation(bool neg);
        RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const override;

    private:
        bool m_is_negated = false;
        std::vector<CharClassElement> m_elements;
    };

    // =============== ECMA REGEX PARSER ===============
    struct CharClassAtom {
        bool is_escape;
        uint32_t val;
    };

    using ASTNodeCharClassRef = std::unique_ptr<ASTNodeCharClass>;

    class ECMAParser {
    public:
        explicit ECMAParser(const zstring_view regex)
            : m_lexer(regex),
              m_current_token(m_lexer.get_next_token()) { }

        ASTNodeRef parse();

    private:
        ECMALexer m_lexer;
        Token m_current_token;

        void next();
        bool match(TokenType type);
        Token consume(TokenType type, const char* message);

        ASTNodeRef parse_disjunction();
        ASTNodeRef parse_alternative();
        ASTNodeRef parse_term();
        ASTNodeRef parse_maybe_quantifier(ASTNodeRef term);
        ASTNodeRef parse_assertion();
        ASTNodeRef parse_atom();
        ASTNodeRef parse_group();
        ASTNodeRef parse_character_class();

        void parse_class_ranges(const ASTNodeCharClassRef& char_class_parent);
        void parse_class_ranges_tail(const ASTNodeCharClassRef& char_class_parent, CharClassAtom prev_atom);
        void parse_dash_tail(const ASTNodeCharClassRef& char_class, CharClassAtom atom_before_dash);
        CharClassAtom parse_class_atom();
        CharClassAtom parse_class_atom_no_dash();

        void add_atom_to_class(const ASTNodeCharClassRef& char_class_parent, CharClassAtom atom) const;
    };

    // =============== ECMA REGEX HANDLER ===============
    class RCGBuilder {
    public:
        explicit RCGBuilder(ast_manager& m, const zstring& regex_pattern)
            : m_regex(regex_pattern),
              m_parser(regex_pattern),
              m_util_s(m) { }

        RegexConstraintGraph build_rcg();

    private:
        zstring_view m_regex;
        ECMAParser m_parser;
        seq_util m_util_s;
    };
}  // namespace smt::noodler::ecma
