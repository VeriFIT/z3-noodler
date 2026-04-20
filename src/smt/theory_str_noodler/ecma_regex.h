#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "util/zstring.h"
#include "util/zstring_view.h"

#include <limits>
#include <memory>
#include <ostream>
#include <unordered_map>
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

    enum class LookaroundDirection {
        FORWARD,
        BACKWARD
    };
    using VertexId = uint32_t;
    using EdgeId = uint32_t;

    struct GraphFragment {
        VertexId v_in = std::numeric_limits<VertexId>::max();
        VertexId v_out = std::numeric_limits<VertexId>::max();
        std::vector<EdgeId> edges_pointing_to_vout;
        bool is_initialized() const;
    };

    struct Lookaround {
        std::variant<app_ref, GraphFragment> subregex;
        LookaroundDirection direction;
        bool is_positive;
    };

    using Anchor = uint32_t;

    struct AssertionEdge {
        std::variant<Anchor, Lookaround> payload;
    };

    struct BackrefEdge {
        uint32_t backref_id;
    };

    using RCGEdgePayload = std::variant<std::monostate, MatchEdge, AssertionEdge, BackrefEdge>;

    struct RCGEdge {
        EdgeId id;
        VertexId target;
        RCGEdgePayload payload;

        RCGEdge(const EdgeId eid, const VertexId target_id, RCGEdgePayload edge_payload)
            : id(eid),
              target(target_id),
              payload(std::move(edge_payload)) { }
    };

    struct RCGVertex {
        VertexId id;
        std::vector<EdgeId> outgoing_edges;

        RCGVertex(const VertexId vid, std::vector<EdgeId> edges)
            : id(vid),
              outgoing_edges(std::move(edges)) { }
    };

    constexpr uint32_t UNKNOWN_VERTEX = std::numeric_limits<uint32_t>::max();

    struct RegexConstraintGraph {
        std::vector<RCGVertex> vertices;
        std::vector<RCGEdge> edges;

        std::unordered_map<EdgeId, std::vector<uint32_t>> group_starts;
        std::unordered_map<EdgeId, std::vector<uint32_t>> group_ends;

        VertexId start_vertex = UNKNOWN_VERTEX;
        VertexId end_vertex = UNKNOWN_VERTEX;

        void add_vertex(RCGVertex vtx);
        VertexId create_vertex();
        VertexId create_vertex(std::vector<EdgeId> edge_list);
        void add_edge(RCGEdge child);
        EdgeId create_edge();
        EdgeId create_edge(VertexId target, RCGEdgePayload payload);
    };

    zstring view_to_zstring(zstring_view view);

    GraphFragment chain_fragments(RegexConstraintGraph& graph, const GraphFragment& first, const GraphFragment& second);

    GraphFragment alternate_fragments(RegexConstraintGraph& graph, const GraphFragment& first,
                                      const GraphFragment& second);

    GraphFragment make_epsilon_fragment(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m);

    // ================== ECMA REGEX LEXER ==================
    class ECMALexer {
    public:
        explicit ECMALexer(const zstring_view regex, std::unordered_map<zstring_view, uint32_t>& named_groups)
            : m_regex(regex),
              m_named_groups(named_groups) { }

        Token get_next_token();

    private:
        zstring_view m_regex;
        uint32_t m_position = 0;
        uint32_t m_lexeme_start_pos = 0;
        uint32_t m_num_capture_groups = 0;
        bool m_in_char_class = false;
        bool m_first_in_char_class = false;
        bool m_first_traverse = true;
        std::unordered_map<zstring_view, uint32_t>& m_named_groups;

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
        std::pair<bool, zstring_view> is_capture_or_named_capture(uint32_t position) const;
        void perform_first_traverse();
    };

    // ================== ECMA REGEX AST ==================

    // When building RCG from AST, the methods return either a reference to the built sub-rcg, represented by
    // GraphFragment, or app* when the AST subtree contains regular parts of ECMA regex that can be compiled into an
    // SMT-LIB regex. (optimalization -- merging the regular parts of ECMA regex instead of creating edges for all of
    // them)
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

        static GraphFragment make_assertion_fragment(RegexConstraintGraph& graph, ast_manager& m, app_ref assert_regex,
                                                     LookaroundDirection dir, bool is_positive);

        static GraphFragment make_word_boundary_fragment(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m,
                                                         bool is_word_boundary);
        static app_ref make_word_char_re(seq_util& util_s, ast_manager& m);
    };

    class ASTNodeQuantifier : public ASTNode {
    public:
        uint32_t print_dot(std::ostream& out, uint32_t& node_count) const override;
        zstring serialize() const override;
        void set(const Token& t, ASTNodeRef term);


        /**
         * @brief Create 'm' chained copies of subgraph for {n, m} quantifier.
         *  Nonregular fragments under {n,m} quantifiers:
         *  - copy the fragment `m` times,
         *  - chain the first `n` fragments, which are mandatory,
         *  - the remaining (`m` - `n`) fragments are optional --> alternate it with an epsilon-edge, so it can be
         * skipped,
         *  - connect the `m`th copied fragment back to the original flow in the graph.
         * @param graph The graph in which the copies are created.
         * @param util_s z3's seq_util
         * @param manager z3's ast_manager
         * @return
         */
        RegexComponent build_fixed_quantifier_subgraph(RegexConstraintGraph& graph, seq_util& util_s,
                                                       ast_manager& manager) const;
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
        void set_ref(uint32_t backref_number);
        RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const override;

    private:
        uint32_t m_backref_id;
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
        void set_expr(ASTNodeRef expr);
        void set_id(uint32_t gid);
        RegexComponent get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const override;

    private:
        GroupType m_type = GroupType::NORMAL;

        ASTNodeRef m_child;
        uint32_t m_gid;
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
            : m_lexer(regex, m_named_groups),
              m_current_token(m_lexer.get_next_token()) { }

        ASTNodeRef parse();

    private:
        std::unordered_map<zstring_view, uint32_t> m_named_groups {};
        ECMALexer m_lexer;
        Token m_current_token;
        uint32_t m_current_group_id = 0;

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

        static void add_atom_to_class(const ASTNodeCharClassRef& char_class_parent, CharClassAtom atom);
    };

    // =============== ECMA REGEX HANDLER ===============
    class RegexConstraintBuilder {
    public:
        explicit RegexConstraintBuilder(ast_manager& m, const zstring& regex_pattern)
            : m_regex(regex_pattern),
              m_parser(regex_pattern),
              m_manager(m),
              m_util_s(m),
              m_str_sort(m_util_s.mk_string_sort()),
              m_unique_paths(m),
              m_current_path_vars(m),
              m_current_path_constraints(m) { }

        RegexConstraintGraph build_rcg();
        expr_ref generate_constraints(app* target_string);

    private:
        zstring_view m_regex;
        ECMAParser m_parser;
        ast_manager& m_manager;
        seq_util m_util_s;
        RegexConstraintGraph m_graph;
        sort* m_str_sort = nullptr;

        // Global result of DFS traversal (all the unique paths in graph)
        expr_ref_vector m_unique_paths;

        // DFS 'backpack' -- all the necessary structures for DFS traversal
        // 1. All the active string variables and their constraints of the current path
        expr_ref_vector m_current_path_vars;
        expr_ref_vector m_current_path_constraints;

        // 2. Active capture group information
        std::vector<uint32_t> m_active_groups;
        std::unordered_map<uint32_t, expr_ref_vector> m_group_vars;

        // 3. Active lookahead information
        struct ActiveLookahead {
            std::variant<app_ref, GraphFragment> subregex;
            bool is_positive;
            size_t start_index;
            bool is_end_anchor;
        };

        std::vector<ActiveLookahead> m_active_lookaheads;

        app* mk_fresh_string_var() const;
        expr_ref concat_vars(const expr_ref_vector& vars, std::size_t start_idx = 0);
        expr_ref run_inner_rcg_dfs(const GraphFragment& fragment, app* target_string);
        void cleanup_after_edge_visit(const std::vector<uint32_t>& newly_started_groups,
                                      const std::vector<uint32_t>& newly_ended_groups, bool la_pushed,
                                      const size_t& num_edge_constraints);
        void push_constraint(const app_ref& constraint, size_t& num_edge_constraints);
        void handle_lookaround_constraints(bool& la_pushed, const AssertionEdge& assertion,
                                           size_t& num_edge_constraints);
        void generate_lookahead_constraints(expr_ref_vector final_constraints);
        void generate_edge_constraints(const RCGEdge& edge, const app_ref& edge_var, size_t& num_edge_constraints,
                                       bool& la_pushed);
        void rcg_dfs_visit(VertexId current_vertex, app* target_string);
    };
}  // namespace smt::noodler::ecma
