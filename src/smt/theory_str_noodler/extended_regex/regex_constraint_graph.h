#pragma once

#include "regex_ast.h"

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"

#include <cstdint>
#include <limits>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

namespace smt::noodler::extended_regex {
    // =============== REGEX CONSTRAINT GRAPH ===============

    /**
     * Payload for a regular match edge. During DFS, the variable assigned to this edge
     * must satisfy str.in_re(edge_var, regex).
     */
    struct MatchEdge {
        app_ref regex;
    };

    using VertexID = uint32_t;
    using EdgeID = uint32_t;

    /**
     * A connected subgraph of the RCG produced from a single AST node by build_component().
     *
     * `v_in` and `v_out` are the entry and exit vertices of the fragment.
     *
     * `edges_pointing_to_vout` holds all edges whose target is `v_out`.
     * This list is needed when chaining fragments -- all edges going to `v_out` are redirected to the next fragment's
     * `v_in`. When alternating fragments, all edges in both fragments' `edges_pointing_to_vout` lists are redirected to
     * a new shared `v_out`.
     */
    struct GraphFragment {
        VertexID v_in = std::numeric_limits<VertexID>::max();
        VertexID v_out = std::numeric_limits<VertexID>::max();
        std::vector<EdgeID> edges_pointing_to_vout;
    };

    /**
     * The result type of build_component(). Each AST node converts into one of two forms:
     *
     *   app_ref       -- the subtree is fully regular and collapses to a single Z3 regex expression.
     *
     *   GraphFragment -- the subtree contains non-regular constructs (backreferences, anchors, or lookarounds) and is
     *                    represented as a sub-portion of the RCG. The DFS will traverse this subgraph and generate
     *                    explicit string constraints for each path through it.
     *
     * The more subtrees are kept as app_refs, the smaller the RCG and the fewer constraints are generated.
     */
    using RegexComponent = std::variant<GraphFragment, app_ref>;

    /**
     * Represents a lookaround assertion (lookahead or lookbehind, positive or negative).
     *
     * `subregex` holds the inner pattern of the assertion.
     * If the inner pattern is fully regular it is stored as z3 regular expression via app_ref; the DFS evaluates it
     * with `str.to_re` constraint. If the inner pattern contains non-regular constructs it is stored as a GraphFragment
     * and evaluated by running a nested DFS on the fragment.
     *
     * `contains_lookahead` is set for a non-regular lookbehind whose fragment contains a lookahead (also the one of
     * a word boundary). Such a lookahead must be evaluated against the rest of the whole string, not only against the
     * rest of the lookbehind target.
     */
    struct LookaroundAssertion {
        RegexComponent subregex;
        LookaroundDirection direction;
        bool is_positive;
        bool contains_lookahead = false;
    };

    /**
     * Payload for an assertion edge, which is either an anchor (start or end of the text) or a lookaround.
     * The edge variable generated for assertions is always empty string "".
     */
    struct AssertionEdge {
        std::variant<Anchor, LookaroundAssertion> payload;
    };

    /**
     * Payload for a backreference edge. During constraint generation, the edge variable must equal the string captured
     * by that group on the current path. If the group has no capture on the current path (it has not been entered
     * yet, it is still open, or its capture was reset), the edge variable is constrained to be empty if
     * `unset_matches_empty` is set, otherwise the path is infeasible.
     */
    struct BackrefEdge {
        GroupID backref_id;
        bool unset_matches_empty = false;
    };

    struct RCGVertex {
        VertexID id;
        std::vector<EdgeID> outgoing_edges;

        RCGVertex(const VertexID vid, std::vector<EdgeID> edges)
            : id(vid),
              outgoing_edges(std::move(edges)) { }
    };

    using MarkerEdge = std::monostate;  // no payload, used for bookkeeping only
    using RCGEdgePayload = std::variant<MarkerEdge, MatchEdge, AssertionEdge, BackrefEdge>;

    struct RCGEdge {
        EdgeID id;
        VertexID target;
        RCGEdgePayload payload;

        RCGEdge(const EdgeID eid, const VertexID target_id, RCGEdgePayload edge_payload)
            : id(eid),
              target(target_id),
              payload(std::move(edge_payload)) { }
    };

    constexpr VertexID UNKNOWN_VERTEX = std::numeric_limits<VertexID>::max();

    /**
     * The Regex Constraint Graph (RCG) encodes the structure of an extended regex.
     * Vertices represent split points where the regex transitions between regular and non-regular components, or other
     * structural boundaries (such as alternations).
     *
     * Edges carry one of four payloads:
     *   - MatchEdge:      the edge variable belongs to a standard Z3 regex.
     *   - AssertionEdge:  zero-width assertion (anchors, lookarounds); consumes nothing and gets no edge variable.
     *   - BackrefEdge:    the edge variable must equal the string captured by a group.
     *   - MarkerEdge:     consumes nothing and gets no edge variable, it only carries bookkeeping
     *                     (see `group_resets` and `nonempty_iterations`).
     *
     * A valid match corresponds to a path from start_vertex to end_vertex, where
     * the concatenated edge variables equal the target string.
     *
     * The `group_starts` and `group_ends` maps track which edges open and close
     * specific capture groups, allowing the DFS to evaluate backreferences.
     *
     * The `group_resets` and `nonempty_iterations` maps mark the marker edges that start and end the iterations of
     * an unrolled bounded repetition (see Repetition).
     */
    struct RegexConstraintGraph {
        std::vector<RCGVertex> vertices;
        std::vector<RCGEdge> edges;

        std::unordered_map<EdgeID, std::vector<GroupID>> group_starts;
        std::unordered_map<EdgeID, std::vector<GroupID>> group_ends;

        // Edges starting an iteration of an unrolled repetition, mapped to the capture groups inside the repeated
        // subpattern whose captures are reset at the start of the iteration (none if the repetition does not reset
        // captures, the edge then only marks the start of the iteration).
        std::unordered_map<EdgeID, std::vector<GroupID>> group_resets;
        // Edges ending an iteration beyond the repetition minimum, mapped to the edge that started the iteration. Such
        // an iteration is rejected if it matched the empty string.
        std::unordered_map<EdgeID, EdgeID> nonempty_iterations;

        VertexID start_vertex = UNKNOWN_VERTEX;
        VertexID end_vertex = UNKNOWN_VERTEX;

        VertexID create_vertex();
        VertexID create_vertex(std::vector<EdgeID> edge_list);
        EdgeID create_edge(VertexID target, RCGEdgePayload payload);
    };

    /**
     * @brief Connect two fragments sequentially: first -> second.
     *
     * Optimization: redirects every edge in first.edges_pointing_to_vout to point to second.v_in instead
     * of first.v_out. The resulting fragment spans from first.v_in to second.v_out.
     *
     * @param graph  The RCG owning both fragments.
     * @param first  The fragment that runs first.
     * @param second The fragment that runs after first.
     * @return GraphFragment A fragment from first.v_in to second.v_out.
     */
    GraphFragment chain_fragments(RegexConstraintGraph& graph, const GraphFragment& first, const GraphFragment& second);

    /**
     * @brief Merge two fragments into one that accepts either branch.
     *
     * Optimization: creates new global v_in and v_out, steals edges pointing from both fragments' v_in and adds them to
     * the new v_in. Then, redirects all edges in both fragments' edges_pointing_to_vout to the new v_out. The resulting
     * fragment spans from the new v_in to the new v_out.
     *
     * @param graph  The RCG owning both fragments.
     * @param first  One branch of the alternation.
     * @param second The other branch of the alternation.
     * @return GraphFragment A fragment spanning from the new v_in to the new v_out with two alternating branches.
     */
    GraphFragment alternate_fragments(RegexConstraintGraph& graph, const GraphFragment& first,
                                      const GraphFragment& second);

    /**
     * @brief Create a fragment that matches the empty string (epsilon).
     *
     * @param graph  The RCG to add the fragment to.
     * @param util_s Z3 sequence/regex utilities.
     * @param m      The Z3 AST manager.
     * @return GraphFragment A two-vertex fragment with a single epsilon MatchEdge.
     */
    GraphFragment make_epsilon_fragment(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m);

    /**
     * @brief Create a fragment with a single MarkerEdge.
     *
     * Unlike an epsilon fragment, the marker edge gets no edge variable and no constraint during the DFS. It is used
     * only to attach bookkeeping to a position in the graph.
     *
     * @param graph The RCG to add the fragment to.
     * @return GraphFragment A two-vertex fragment with a single marker edge.
     */
    GraphFragment make_marker_fragment(RegexConstraintGraph& graph);

    // ================ AST TO RCG CONVERSION ================

    /**
     * @brief Convert the AST @p node into a RegexComponent.
     *
     * If the whole AST is regular, returns an app_ref containing the combined Z3 regex expression for it. Otherwise,
     * creates the necessary vertices and edges in @p graph and returns a GraphFragment describing the subgraph:
     *   - CharSet: always regular.
     *   - Concatenation: adjacent literals are merged into one string and adjacent regular terms are merged with
     *     mk_concat, the remaining fragments are connected with chain_fragments.
     *   - Alternation: all the regular alternatives are merged with mk_union into a single app_ref (alternation is
     *     commutative), which is then alternated with the non-regular fragments.
     *   - Repetition: a regular subpattern is repeated with regex operations. A non-regular subpattern is unrolled
     *     into an alternation of chains of its copies if the repetition is bounded, an unbounded one is unsupported
     *     (it leads to a dynamic number of string variables and constraints).
     *   - Capture: the fragment of the subpattern, its boundary edges are annotated with the group ID so that the
     *     constraint generation can track which edge variables fall inside the capture.
     *   - Backreference, Anchor, Lookaround: always a GraphFragment, the assertions are handled during the constraint
     *     generation with special constraints.
     *
     * @param node   The AST to convert.
     * @param graph  The RCG being built. New vertices and edges are appended here.
     * @param util_s Z3 sequence/regex utility object.
     * @param m      The Z3 AST manager.
     * @return RegexComponent Either an app_ref (regular AST) or a GraphFragment (non-regular AST).
     */
    RegexComponent build_component(const Node& node, RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m);

    /**
     * @brief Convert the alternation @p alternation into a RegexComponent, see build_component().
     */
    RegexComponent build_alternation(const Alternation& alternation, RegexConstraintGraph& graph, seq_util& util_s,
                                     ast_manager& m);

    /**
     * @brief Convert the concatenation @p concatenation into a RegexComponent, see build_component().
     */
    RegexComponent build_concatenation(const Concatenation& concatenation, RegexConstraintGraph& graph,
                                       seq_util& util_s, ast_manager& m);

    /**
     * @brief Convert the repetition @p repetition into a RegexComponent, see build_component().
     *
     * A bounded repetition of a non-regular subpattern is expanded by unroll(), an unbounded one throws "unsupported".
     */
    RegexComponent build_repetition(const Repetition& repetition, RegexConstraintGraph& graph, seq_util& util_s,
                                    ast_manager& m);

    /**
     * @brief Expand a bounded repetition {min,max} with a non-regular child into the graph.
     *
     * Produces a fragment equivalent to:
     *   (child^min | ... | child^max | epsilon)
     * where epsilon is included only when min == 0. Every iteration is a fresh copy of the child's subgraph, see
     * make_iteration().
     *
     * @return GraphFragment The fragment of the unrolled repetition.
     */
    GraphFragment unroll(const Repetition& repetition, RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m);

    /**
     * @brief Build one iteration of an unrolled repetition as a fresh copy of the subgraph of its subpattern.
     *
     * If the subpattern contains capture groups and the repetition resets captures or rejects empty iterations, the
     * copy is wrapped in marker edges: the first one is registered in `group_resets` (with the captures to reset, if
     * any), and for iterations beyond the minimum of a repetition rejecting empty iterations, the last one is
     * registered in `nonempty_iterations`.
     *
     * Without capture groups, iterations do not influence each other and an empty iteration can be left out without
     * changing the matched string, so the copy is returned as is.
     *
     * @param captures  The capture groups inside the subpattern.
     * @param iteration 1-based number of the iteration in its chain.
     * @return GraphFragment The fragment of a single iteration.
     */
    GraphFragment make_iteration(const Repetition& repetition, RegexConstraintGraph& graph, seq_util& util_s,
                                 ast_manager& m, const std::vector<GroupID>& captures, uint64_t iteration);

    /**
     * @brief Convert the capture group @p capture into the fragment of its subpattern whose boundary edges are
     * registered in `group_starts` and `group_ends`.
     */
    GraphFragment build_capture(const Capture& capture, RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m);

    /**
     * @brief Create a fragment with a single BackrefEdge for the backreference @p backref.
     */
    GraphFragment build_backreference(const Backreference& backref, RegexConstraintGraph& graph);

    /**
     * @brief Create a fragment with a single AssertionEdge for the anchor @p anchor.
     */
    GraphFragment build_anchor(Anchor anchor, RegexConstraintGraph& graph);

    /**
     * @brief Convert the lookaround @p lookaround into a fragment with a single AssertionEdge.
     *
     * A regular subpattern becomes the regex of the assertion. A non-regular subpattern is supported only in a
     * positive lookaround: its fragment is extended with Sigma* on the open side (after the subpattern of a lookahead,
     * before the subpattern of a lookbehind) and stored in the assertion. A negative lookaround with a non-regular
     * subpattern throws "unsupported", since it would require universal quantification.
     */
    GraphFragment build_lookaround(const Lookaround& lookaround, RegexConstraintGraph& graph, seq_util& util_s,
                                   ast_manager& m);

    /**
     * @brief Create a two-vertex fragment with a single AssertionEdge for a lookaround.
     *
     * @param graph        The RCG to add the fragment to.
     * @param assert_regex The inner regex of the lookaround.
     * @param dir          FORWARD for lookahead, BACKWARD for lookbehind.
     * @param is_positive  True for (?=...) or (?<=...), false for (?!...) or (?<!...).
     * @return GraphFragment The constructed assertion fragment.
     */
    GraphFragment make_assertion_fragment(RegexConstraintGraph& graph, app_ref assert_regex, LookaroundDirection dir,
                                          bool is_positive);

    /**
     * @brief Check whether the @p fragment contains a lookahead edge (nested lookarounds are not searched).
     *
     * @param graph    The RCG owning the fragment.
     * @param fragment The fragment to search.
     * @return bool True if some edge reachable from the fragment's v_in is a lookahead.
     */
    bool contains_lookahead(const RegexConstraintGraph& graph, const GraphFragment& fragment);

    /**
     * @brief Build the Regex Constraint Graph (RCG) of the AST @p root.
     *
     * If @p engine_semantics is set, the graph of the regex is wrapped in Sigma* to model the regex engine matching
     * semantics -- any substring can be matched:
     *
     *   start_vertex --(Sigma*)--> core_v_in
     *                              ...core subgraph...
     *                              core_v_out --(Sigma*)--> end_vertex
     *
     * @param root             The AST of the regex.
     * @param engine_semantics Whether the regex matches a substring of the target string.
     * @param util_s           Z3 sequence/regex utility object.
     * @param m                The Z3 AST manager.
     * @return RegexConstraintGraph The fully assembled RCG.
     */
    RegexConstraintGraph build_rcg(const Node& root, bool engine_semantics, seq_util& util_s, ast_manager& m);

    // ==================== RCG SERIALIZATION ====================

    /**
     * @brief Print the Z3 expression @p e on a single line, e.g., (re.union (str.to_re "a") (str.to_re "b")).
     */
    std::string to_single_line_string(expr* e, ast_manager& m);

    /**
     * @brief Serialize the RCG @p graph into one token per edge, with the edges in the BFS order from the start
     * vertex, e.g., (RCG (EDGE *->* [MATCH re.all]) (EDGE *->* [BACKREF 1] STARTS {1})).
     *
     * Non-regular lookarounds are serialized with the edges of their fragments.
     */
    std::string serialize_rcg(const RegexConstraintGraph& graph, ast_manager& m);

    /**
     * @brief Serialize the group IDs @p gids, e.g., {1,2}.
     */
    std::string serialize_group_ids(const std::vector<GroupID>& gids);

    /**
     * @brief Serialize the markers of the edge @p eid, e.g., " STARTS {1,2} ENDS {1}", " RESETS {1}" or " NONEMPTY".
     */
    std::string serialize_edge_markers(const RegexConstraintGraph& graph, EdgeID eid);

    /**
     * @brief Serialize the edge payload @p payload, e.g., MATCH (str.to_re "a") or BACKREF 1.
     *
     * Takes the whole graph to serialize the fragments of non-regular lookarounds, see serialize_fragment().
     */
    std::string serialize_payload(const RegexConstraintGraph& graph, const RCGEdgePayload& payload, ast_manager& m);

    /**
     * @brief Append the edges reachable from @p start_vertex that are not in @p visited_edges to @p ordered_edges, in
     * the BFS order.
     */
    void rcg_bfs(const RegexConstraintGraph& graph, VertexID start_vertex, std::vector<bool>& visited_edges,
                 std::vector<EdgeID>& ordered_edges);

    /**
     * @brief Serialize the edges of the fragment @p frag reachable from frag.v_in up to (but not beyond) frag.v_out,
     * e.g., (FRAGMENT (EDGE *->* [MATCH (str.to_re "a")])).
     *
     * Used for the fragments of non-regular lookarounds stored in edge payloads. The traversal stops at frag.v_out,
     * which has no outgoing edges in the outer graph, since it was created as the end of the subpattern before the
     * fragment was moved into the payload.
     */
    std::string serialize_fragment(const RegexConstraintGraph& graph, const GraphFragment& frag, ast_manager& m);
}  // namespace smt::noodler::extended_regex
