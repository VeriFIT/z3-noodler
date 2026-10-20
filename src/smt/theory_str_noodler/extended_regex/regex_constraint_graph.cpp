#include "regex_constraint_graph.h"

#include "smt/theory_str_noodler/util.h"

#include "ast/ast_pp.h"
#include "util/debug.h"
#include "util/zstring.h"

#include <algorithm>
#include <queue>
#include <sstream>

namespace smt::noodler::extended_regex {
    // =============== REGEX CONSTRAINT GRAPH ==============

    VertexID RegexConstraintGraph::create_vertex() {
        VertexID new_id = vertices.size();
        vertices.emplace_back(new_id, std::vector<EdgeID> {});
        return new_id;
    }

    VertexID RegexConstraintGraph::create_vertex(std::vector<EdgeID> edge_list) {
        VertexID new_id = vertices.size();
        vertices.emplace_back(new_id, std::move(edge_list));
        return new_id;
    }

    EdgeID RegexConstraintGraph::create_edge(VertexID target_vertex, RCGEdgePayload payload) {
        EdgeID new_id = edges.size();
        edges.emplace_back(new_id, target_vertex, std::move(payload));
        return new_id;
    }

    GraphFragment chain_fragments(RegexConstraintGraph& graph, const GraphFragment& first,
                                  const GraphFragment& second) {
        for (const EdgeID id : first.edges_pointing_to_vout) {
            graph.edges[id].target = second.v_in;
        }
        return GraphFragment {first.v_in, second.v_out, second.edges_pointing_to_vout};
    }

    GraphFragment alternate_fragments(RegexConstraintGraph& graph, const GraphFragment& first,
                                      const GraphFragment& second) {
        std::vector<EdgeID> new_vin_outgoing;
        for (const EdgeID id : graph.vertices[first.v_in].outgoing_edges) {
            new_vin_outgoing.push_back(id);
        }
        for (const EdgeID id : graph.vertices[second.v_in].outgoing_edges) {
            new_vin_outgoing.push_back(id);
        }

        graph.vertices[first.v_in].outgoing_edges.clear();
        graph.vertices[second.v_in].outgoing_edges.clear();

        const VertexID new_vin = graph.create_vertex(new_vin_outgoing);
        const VertexID new_vout = graph.create_vertex();

        std::vector<EdgeID> new_vout_incoming;
        for (const EdgeID id : first.edges_pointing_to_vout) {
            graph.edges[id].target = new_vout;
            new_vout_incoming.push_back(id);
        }
        for (const EdgeID id : second.edges_pointing_to_vout) {
            graph.edges[id].target = new_vout;
            new_vout_incoming.push_back(id);
        }

        return GraphFragment {new_vin, new_vout, new_vout_incoming};
    }

    GraphFragment make_epsilon_fragment(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) {
        const VertexID v_in = graph.create_vertex();
        const VertexID v_out = graph.create_vertex();
        app_ref eps(util_s.re.mk_epsilon(util_s.mk_string_sort()), m);
        const EdgeID eid = graph.create_edge(v_out, RCGEdgePayload {MatchEdge {eps}});
        graph.vertices[v_in].outgoing_edges.push_back(eid);
        return GraphFragment {v_in, v_out, {eid}};
    }

    GraphFragment make_marker_fragment(RegexConstraintGraph& graph) {
        const VertexID v_in = graph.create_vertex();
        const VertexID v_out = graph.create_vertex();
        const EdgeID eid = graph.create_edge(v_out, RCGEdgePayload {MarkerEdge {}});
        graph.vertices[v_in].outgoing_edges.push_back(eid);
        return GraphFragment {v_in, v_out, {eid}};
    }

    // ================ AST TO RCG CONVERSION ================

    RegexComponent build_alternation(const Alternation& alternation, RegexConstraintGraph& graph, seq_util& util_s,
                                     ast_manager& m) {
        std::vector<app_ref> regular_alternatives;
        std::vector<GraphFragment> nonregular_alternatives;

        // First pass -- sort regular and nonregular alternatives
        for (const NodeRef& alternative : alternation.alternatives) {
            RegexComponent current_term = build_component(*alternative, graph, util_s, m);
            if (std::holds_alternative<app_ref>(current_term)) {
                regular_alternatives.push_back(std::get<app_ref>(current_term));
                continue;
            }
            nonregular_alternatives.push_back(std::get<GraphFragment>(current_term));
        }

        // All alternatives regular -- create a single regular fragment
        if (!regular_alternatives.empty() && nonregular_alternatives.empty()) {
            app_ref final_regular_segment = regular_alternatives[0];
            for (std::size_t i = 1; i < regular_alternatives.size(); i++) {
                final_regular_segment = util_s.re.mk_union(final_regular_segment, regular_alternatives[i]);
            }
            return final_regular_segment;
        }

        // No alternatives at all (should not happen for valid input) -- matches nothing
        if (regular_alternatives.empty() && nonregular_alternatives.empty()) {
            return app_ref(util_s.re.mk_empty(util_s.re.mk_re(util_s.mk_string_sort())), m);
        }

        // Since alternation is commutative, unite all nonregular fragments first
        GraphFragment result_fragment = nonregular_alternatives[0];
        for (std::size_t i = 1; i < nonregular_alternatives.size(); i++) {
            result_fragment = alternate_fragments(graph, result_fragment, nonregular_alternatives[i]);
        }

        if (!regular_alternatives.empty()) {
            // Then, merge all regular alternatives into one regular fragment
            app_ref merged_regular = regular_alternatives[0];
            for (std::size_t i = 1; i < regular_alternatives.size(); i++) {
                merged_regular = {util_s.re.mk_union(merged_regular, regular_alternatives[i]), m};
            }

            // Lastly, unite the created regular fragment with all the non-regular ones
            VertexID reg_vout = graph.create_vertex();
            EdgeID reg_eid = graph.create_edge(reg_vout, RCGEdgePayload {MatchEdge {merged_regular}});
            VertexID reg_vin = graph.create_vertex(std::vector<EdgeID> {reg_eid});
            GraphFragment reg_fragment {reg_vin, reg_vout, {reg_eid}};

            result_fragment = alternate_fragments(graph, result_fragment, reg_fragment);
        }

        return result_fragment;
    }

    RegexComponent build_concatenation(const Concatenation& concatenation, RegexConstraintGraph& graph,
                                       seq_util& util_s, ast_manager& m) {
        if (concatenation.terms.empty()) {
            return app_ref(util_s.re.mk_epsilon(util_s.mk_string_sort()), m);
        }

        // First pass: merge adjacent literals (sets with a single character) into one string
        std::vector<RegexComponent> components;
        zstring literal_buf;
        auto flush_literals = [&]() {
            if (!literal_buf.empty()) {
                components.emplace_back(app_ref(util_s.re.mk_to_re(util_s.str.mk_string(literal_buf)), m));
                literal_buf = zstring();
            }
        };

        for (const NodeRef& term : concatenation.terms) {
            const auto* chars = std::get_if<CharSet>(&term->content);
            Z3Char ch;
            if (chars != nullptr && chars->is_single(ch)) {
                literal_buf += ch;
            }
            else {
                flush_literals();
                components.emplace_back(build_component(*term, graph, util_s, m));
            }
        }
        flush_literals();

        if (components.size() == 1) {
            return components[0];
        }

        // Second pass: merge adjacent regular components into one regex
        std::vector<RegexComponent> simplified;
        for (RegexComponent& comp : components) {
            if (!simplified.empty() && std::holds_alternative<app_ref>(simplified.back()) &&
                std::holds_alternative<app_ref>(comp)) {
                simplified.back() =
                    app_ref(util_s.re.mk_concat(std::get<app_ref>(simplified.back()), std::get<app_ref>(comp)), m);
            }
            else {
                simplified.emplace_back(std::move(comp));
            }
        }

        if (simplified.size() == 1) {
            return simplified[0];
        }

        // Helper lambda for fragment creation
        auto to_fragment = [&](RegexComponent& component) -> GraphFragment {
            if (std::holds_alternative<app_ref>(component)) {
                const VertexID v_in = graph.create_vertex();
                const VertexID v_out = graph.create_vertex();
                EdgeID eid = graph.create_edge(v_out, RCGEdgePayload {MatchEdge {std::get<app_ref>(component)}});
                graph.vertices[v_in].outgoing_edges.push_back(eid);
                return GraphFragment {v_in, v_out, {eid}};
            }
            return std::get<GraphFragment>(component);
        };

        // Chain all the regular and non-regular fragments together in order
        GraphFragment result = to_fragment(simplified[0]);
        for (std::size_t i = 1; i < simplified.size(); i++) {
            result = chain_fragments(graph, result, to_fragment(simplified[i]));
        }
        return result;
    }

    GraphFragment make_iteration(const Repetition& repetition, RegexConstraintGraph& graph, seq_util& util_s,
                                 ast_manager& m, const std::vector<GroupID>& captures, const uint64_t iteration) {
        // The child is non-regular (checked in build_repetition()), therefore its subgraph is always a fragment
        const RegexComponent child_subgraph = build_component(*repetition.child, graph, util_s, m);
        SASSERT(std::holds_alternative<GraphFragment>(child_subgraph));
        const GraphFragment body = std::get<GraphFragment>(child_subgraph);
        if (captures.empty() || (!repetition.resets_captures && !repetition.rejects_empty_iterations)) {
            return body;
        }

        // Marker edge starting the iteration -- resets the captures inside the child
        const GraphFragment start = make_marker_fragment(graph);
        const EdgeID start_eid = start.edges_pointing_to_vout[0];
        graph.group_resets[start_eid] = repetition.resets_captures ? captures : std::vector<GroupID> {};
        GraphFragment result = chain_fragments(graph, start, body);

        // Marker edge ending an iteration beyond the minimum -- the iteration must not match the empty string
        if (repetition.rejects_empty_iterations && iteration > repetition.min) {
            const GraphFragment end = make_marker_fragment(graph);
            graph.nonempty_iterations[end.edges_pointing_to_vout[0]] = start_eid;
            result = chain_fragments(graph, result, end);
        }
        return result;
    }

    GraphFragment unroll(const Repetition& repetition, RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) {
        std::vector<GroupID> captures;
        collect_capture_groups(*repetition.child, captures);

        // Create chains with (min, min+1, ..., max) iterations and alternate them all.
        std::vector<GraphFragment> chains;
        const uint64_t start = std::max<uint64_t>(1, repetition.min);
        for (uint64_t k = start; k <= repetition.max; ++k) {
            GraphFragment chain = make_iteration(repetition, graph, util_s, m, captures, 1);
            for (uint64_t i = 2; i <= k; ++i) {
                chain = chain_fragments(graph, chain, make_iteration(repetition, graph, util_s, m, captures, i));
            }
            chains.push_back(chain);
        }

        // Zero iterations
        if (repetition.min == 0) {
            chains.push_back(make_epsilon_fragment(graph, util_s, m));
        }

        SASSERT(!chains.empty());
        GraphFragment result = chains[0];
        for (std::size_t i = 1; i < chains.size(); ++i) {
            result = alternate_fragments(graph, result, chains[i]);
        }
        return result;
    }

    RegexComponent build_repetition(const Repetition& repetition, RegexConstraintGraph& graph, seq_util& util_s,
                                    ast_manager& m) {
        const RegexComponent child_subgraph = build_component(*repetition.child, graph, util_s, m);

        if (std::holds_alternative<GraphFragment>(child_subgraph)) {
            // Nonregular fragments under unbounded repetitions -- unsupported.
            if (repetition.max == UNBOUNDED) {
                util::throw_error("Unsupported regex structure: Non-regular constructs under kleene star/kleene plus");
            }
            // Zero iterations only -- matches the empty string and leaves all captures untouched.
            if (repetition.max == 0) {
                return app_ref(util_s.re.mk_epsilon(util_s.mk_string_sort()), m);
            }
            // Nonregular fragments under bounded repetition -- statically unroll into the graph.
            return unroll(repetition, graph, util_s, m);
        }

        // Regular subregex --> directly create the corresponding regular expression
        SASSERT(std::holds_alternative<app_ref>(child_subgraph));
        const app_ref child_expr = std::get<app_ref>(child_subgraph);
        app* quant = nullptr;

        if (repetition.max == UNBOUNDED) {
            if (repetition.min == 0) {
                quant = util_s.re.mk_star(child_expr);
            }
            else if (repetition.min == 1) {
                quant = util_s.re.mk_plus(child_expr);
            }
            else {
                // Concatenation `min` times followed by kleene star
                quant = child_expr;
                for (uint64_t i = 1; i < repetition.min; i++) {
                    quant = util_s.re.mk_concat(quant, child_expr);
                }
                quant = util_s.re.mk_concat(quant, util_s.re.mk_star(child_expr));
            }
        }
        else {
            // For some reason, using mk_loop and mk_power directly leads to unsoudness of the solver, although the
            // semantics should be the same as concatenation.
            // if (repetition.min == repetition.max) {
            //     quant = util_s.re.mk_power(child_expr, repetition.min);
            // } else {
            //     quant = util_s.re.mk_loop(child_expr, repetition.min, repetition.max);
            // }
            if (repetition.min == repetition.max) {
                if (repetition.min == 0) {
                    quant = util_s.re.mk_epsilon(util_s.mk_string_sort());
                }
                else {
                    // A concrete number of concatenations
                    quant = child_expr;
                    for (uint64_t i = 1; i < repetition.min; i++) {
                        quant = util_s.re.mk_concat(quant, child_expr);
                    }
                }
            }
            else {
                // Range [min, max]:
                // Obligatory part -- at least `min` times
                app* at_least_min = util_s.re.mk_epsilon(util_s.mk_string_sort());
                if (repetition.min > 0) {
                    at_least_min = child_expr;
                    for (uint64_t i = 1; i < repetition.min; i++) {
                        at_least_min = util_s.re.mk_concat(at_least_min, child_expr);
                    }
                }

                // Optional pattern -- union with epsilon
                app* eps = util_s.re.mk_epsilon(util_s.mk_string_sort());
                app* re_optional = util_s.re.mk_union(eps, child_expr);

                // Chain the optional pattern `max` - `min` times
                app* up_to_max = re_optional;
                for (uint64_t i = 1; i < (repetition.max - repetition.min); i++) {
                    up_to_max = util_s.re.mk_concat(up_to_max, re_optional);
                }

                quant = util_s.re.mk_concat(at_least_min, up_to_max);
            }
        }

        SASSERT(quant != nullptr);
        return app_ref(quant, m);
    }

    GraphFragment build_capture(const Capture& capture, RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) {
        RegexComponent subregex = build_component(*capture.child, graph, util_s, m);

        GraphFragment fragment;
        if (std::holds_alternative<app_ref>(subregex)) {
            // Regular subregex in group -- create a MatchEdge and create a fragment
            const VertexID vin = graph.create_vertex();
            const VertexID vout = graph.create_vertex();
            const EdgeID eid = graph.create_edge(vout, RCGEdgePayload {MatchEdge {std::get<app_ref>(subregex)}});
            graph.vertices[vin].outgoing_edges.push_back(eid);
            fragment = GraphFragment {vin, vout, {eid}};
        }
        else {
            // Nonregular subregex in group -- take the fragment
            fragment = std::get<GraphFragment>(subregex);
        }

        // Mark all the outgoing edges from the v_in of the fragment as group starts
        for (const EdgeID eid : graph.vertices[fragment.v_in].outgoing_edges) {
            graph.group_starts[eid].push_back(capture.id);
        }

        // Mark all the incoming edges to the fragments' v_out as group ends
        for (const EdgeID eid : fragment.edges_pointing_to_vout) {
            graph.group_ends[eid].push_back(capture.id);
        }

        return fragment;
    }

    GraphFragment build_backreference(const Backreference& backref, RegexConstraintGraph& graph) {
        const VertexID vin = graph.create_vertex();
        const VertexID vout = graph.create_vertex();
        const EdgeID backref_eid = graph.create_edge(vout, {BackrefEdge {backref.id, backref.unset_matches_empty}});
        graph.vertices[vin].outgoing_edges.push_back(backref_eid);
        return GraphFragment {vin, vout, {backref_eid}};
    }

    GraphFragment build_anchor(const Anchor anchor, RegexConstraintGraph& graph) {
        VertexID v_in = graph.create_vertex();
        VertexID v_out = graph.create_vertex();
        EdgeID eid = graph.create_edge(v_out, RCGEdgePayload {AssertionEdge {anchor}});
        graph.vertices[v_in].outgoing_edges.push_back(eid);
        return GraphFragment {v_in, v_out, {eid}};
    }

    GraphFragment make_assertion_fragment(RegexConstraintGraph& graph, app_ref assert_regex,
                                          const LookaroundDirection dir, const bool is_positive) {
        const VertexID v_in = graph.create_vertex();
        const VertexID v_out = graph.create_vertex();
        EdgeID eid = graph.create_edge(v_out, RCGEdgePayload {AssertionEdge {
                                                  LookaroundAssertion {std::move(assert_regex), dir, is_positive}}});
        graph.vertices[v_in].outgoing_edges.push_back(eid);
        return GraphFragment {v_in, v_out, {eid}};
    }

    bool contains_lookahead(const RegexConstraintGraph& graph, const GraphFragment& fragment) {
        std::vector<bool> visited(graph.vertices.size(), false);
        std::vector<VertexID> to_visit {fragment.v_in};
        visited[fragment.v_in] = true;
        while (!to_visit.empty()) {
            const VertexID vertex = to_visit.back();
            to_visit.pop_back();
            for (const EdgeID eid : graph.vertices[vertex].outgoing_edges) {
                const RCGEdge& edge = graph.edges[eid];
                if (std::holds_alternative<AssertionEdge>(edge.payload)) {
                    const AssertionEdge& assertion = std::get<AssertionEdge>(edge.payload);
                    if (std::holds_alternative<LookaroundAssertion>(assertion.payload) &&
                        std::get<LookaroundAssertion>(assertion.payload).direction == LookaroundDirection::FORWARD) {
                        return true;
                    }
                }
                if (!visited[edge.target]) {
                    visited[edge.target] = true;
                    to_visit.push_back(edge.target);
                }
            }
        }
        return false;
    }

    GraphFragment build_lookaround(const Lookaround& lookaround, RegexConstraintGraph& graph, seq_util& util_s,
                                   ast_manager& m) {
        const RegexComponent inner_regex = build_component(*lookaround.child, graph, util_s, m);
        const LookaroundDirection dir = lookaround.direction;

        // Lookarounds with regular content --> create AssertionEdge with regex as payload
        if (std::holds_alternative<app_ref>(inner_regex)) {
            return make_assertion_fragment(graph, std::get<app_ref>(inner_regex), dir, lookaround.is_positive);
        }

        // Non-regular lookarounds with non-regular inner content are not supported, since they would require
        // universal quantification. Lookarounds with regular content can be expressed as a negation of regular
        // language --> supported.
        if (!lookaround.is_positive) {
            util::throw_error("Unsupported: negative lookaround with non-regular inner content "
                              "(would require universal quantifiers)");
        }

        GraphFragment inner_frag = std::get<GraphFragment>(inner_regex);

        // A non-regular lookaround needs to be wrapped on the open side with Sigma*,
        // otherwise it becomes a strict exact match up to the boundary.
        VertexID s_in = graph.create_vertex();
        VertexID s_out = graph.create_vertex();
        EdgeID s_eid =
            graph.create_edge(s_out, RCGEdgePayload {MatchEdge {app_ref(util_s.re.mk_full_seq(nullptr), m)}});
        graph.vertices[s_in].outgoing_edges.push_back(s_eid);
        GraphFragment sigma_frag {s_in, s_out, {s_eid}};

        // Chain Sigma* on the correct side of the inner fragment, depending on the lookaround direction
        // Lookaheads --> Pattern concat Sigma*
        // Lookbehinds --> Sigma* concat pattern
        if (dir == LookaroundDirection::FORWARD) {
            inner_frag = chain_fragments(graph, inner_frag, sigma_frag);
        }
        else {
            inner_frag = chain_fragments(graph, sigma_frag, inner_frag);
        }

        // A lookahead inside a lookbehind must see the rest of the whole string (see
        // ConstraintGenerator::handle_lookaround_constraints())
        const bool has_lookahead = dir == LookaroundDirection::BACKWARD && contains_lookahead(graph, inner_frag);

        // Wrap the resulting fragment into an AssertionEdge
        VertexID v_in = graph.create_vertex();
        VertexID v_out = graph.create_vertex();
        EdgeID eid = graph.create_edge(v_out, RCGEdgePayload {AssertionEdge {LookaroundAssertion {
                                                  std::move(inner_frag), dir, true, has_lookahead}}});
        graph.vertices[v_in].outgoing_edges.push_back(eid);
        return GraphFragment {v_in, v_out, {eid}};
    }

    RegexComponent build_component(const Node& node, RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) {
        return std::visit(overloaded {
                              [&](const CharSet& chars) -> RegexComponent {
                                  return chars.to_regex(util_s, m);
                              },
                              [&](const Concatenation& concatenation) -> RegexComponent {
                                  return build_concatenation(concatenation, graph, util_s, m);
                              },
                              [&](const Alternation& alternation) -> RegexComponent {
                                  return build_alternation(alternation, graph, util_s, m);
                              },
                              [&](const Repetition& repetition) -> RegexComponent {
                                  return build_repetition(repetition, graph, util_s, m);
                              },
                              [&](const Capture& capture) -> RegexComponent {
                                  return build_capture(capture, graph, util_s, m);
                              },
                              [&](const Backreference& backref) -> RegexComponent {
                                  return build_backreference(backref, graph);
                              },
                              [&](const Lookaround& lookaround) -> RegexComponent {
                                  return build_lookaround(lookaround, graph, util_s, m);
                              },
                              [&](const Anchor anchor) -> RegexComponent {
                                  return build_anchor(anchor, graph);
                              },
                          },
                          node.content);
    }

    RegexConstraintGraph build_rcg(const Node& root, const bool engine_semantics, seq_util& util_s, ast_manager& m) {
        RegexConstraintGraph graph;
        const RegexComponent comp = build_component(root, graph, util_s, m);

        VertexID inner_start = UNKNOWN_VERTEX;
        VertexID inner_end = UNKNOWN_VERTEX;

        if (std::holds_alternative<app_ref>(comp)) {
            // If the entire regex is regular, create a match edge and wrap it in two vertices
            inner_start = graph.create_vertex();
            inner_end = graph.create_vertex();
            const EdgeID eid = graph.create_edge(inner_end, RCGEdgePayload {MatchEdge {std::get<app_ref>(comp)}});
            graph.vertices[inner_start].outgoing_edges.push_back(eid);
        }
        else {
            const GraphFragment frag = std::get<GraphFragment>(comp);
            inner_start = frag.v_in;
            inner_end = frag.v_out;
        }

        if (engine_semantics) {
            // Wrap the entire regex in Sigma* to mimic the regex engine matching semantics --> the solution is any
            // substring
            const app_ref sigma_star(util_s.re.mk_full_seq(nullptr), m);

            graph.start_vertex = graph.create_vertex();
            const EdgeID prefix_eid = graph.create_edge(inner_start, RCGEdgePayload {MatchEdge {sigma_star}});
            graph.vertices[graph.start_vertex].outgoing_edges.push_back(prefix_eid);

            graph.end_vertex = graph.create_vertex();
            const EdgeID suffix_eid = graph.create_edge(graph.end_vertex, RCGEdgePayload {MatchEdge {sigma_star}});
            graph.vertices[inner_end].outgoing_edges.push_back(suffix_eid);
        }
        else {
            // No engine matching semantics --> the whole string must match the regex
            graph.start_vertex = inner_start;
            graph.end_vertex = inner_end;
        }

        return graph;
    }

    // ==================== RCG SERIALIZATION ====================

    std::string to_single_line_string(expr* e, ast_manager& m) {
        std::stringstream ss;
        ss << mk_pp(e, m);
        std::string res = ss.str();
        std::erase(res, '\n');
        res.erase(std::ranges::unique(res,
                                      [](const char a, const char b) {
                                          return a == ' ' && b == ' ';
                                      })
                      .begin(),
                  res.end());
        return res;
    }

    std::string serialize_group_ids(const std::vector<GroupID>& gids) {
        std::string res = "{";
        for (std::size_t i = 0; i < gids.size(); i++) {
            res += (i == 0 ? "" : ",") + std::to_string(gids[i]);
        }
        return res + "}";
    }

    std::string serialize_edge_markers(const RegexConstraintGraph& graph, const EdgeID eid) {
        std::string res;
        if (graph.group_resets.contains(eid)) {
            res += " RESETS " + serialize_group_ids(graph.group_resets.at(eid));
        }
        if (graph.nonempty_iterations.contains(eid)) {
            res += " NONEMPTY";
        }
        if (graph.group_starts.contains(eid) && !graph.group_starts.at(eid).empty()) {
            res += " STARTS " + serialize_group_ids(graph.group_starts.at(eid));
        }
        if (graph.group_ends.contains(eid) && !graph.group_ends.at(eid).empty()) {
            res += " ENDS " + serialize_group_ids(graph.group_ends.at(eid));
        }
        return res;
    }

    std::string serialize_payload(const RegexConstraintGraph& graph, const RCGEdgePayload& payload, ast_manager& m) {
        if (std::holds_alternative<MarkerEdge>(payload)) {
            return "EPSILON";
        }

        if (std::holds_alternative<MatchEdge>(payload)) {
            return "MATCH " + to_single_line_string(std::get<MatchEdge>(payload).regex.get(), m);
        }

        if (std::holds_alternative<AssertionEdge>(payload)) {
            const AssertionEdge& assertion = std::get<AssertionEdge>(payload);

            if (std::holds_alternative<Anchor>(assertion.payload)) {
                return (std::get<Anchor>(assertion.payload) == Anchor::START_OF_TEXT) ? "ANCHOR '^'" : "ANCHOR '$'";
            }

            const LookaroundAssertion& la = std::get<LookaroundAssertion>(assertion.payload);

            std::string type_str;
            if (la.direction == LookaroundDirection::FORWARD) {
                type_str = la.is_positive ? "?=" : "?!";
            }
            else {
                type_str = la.is_positive ? "?<=" : "?<!";
            }

            std::string inner_str;
            if (std::holds_alternative<app_ref>(la.subregex)) {
                // Regular lookaround: serialize the Z3 regex expression directly.
                inner_str = to_single_line_string(std::get<app_ref>(la.subregex).get(), m);
            }
            else {
                // Non-regular lookaround: recursively serialize the embedded graph fragment.
                inner_str = serialize_fragment(graph, std::get<GraphFragment>(la.subregex), m);
            }

            return "LOOKAROUND " + type_str + " " + inner_str;
        }

        if (std::holds_alternative<BackrefEdge>(payload)) {
            return "BACKREF " + std::to_string(std::get<BackrefEdge>(payload).backref_id);
        }

        return "UNKNOWN";
    }

    void rcg_bfs(const RegexConstraintGraph& graph, const VertexID start_vertex, std::vector<bool>& visited_edges,
                 std::vector<EdgeID>& ordered_edges) {
        if (start_vertex == UNKNOWN_VERTEX || start_vertex >= graph.vertices.size()) {
            return;
        }

        std::queue<VertexID> q;
        std::vector<bool> visited_vertices(graph.vertices.size(), false);
        q.push(start_vertex);
        visited_vertices[start_vertex] = true;

        while (!q.empty()) {
            const VertexID curr = q.front();
            q.pop();

            for (EdgeID eid : graph.vertices[curr].outgoing_edges) {
                if (!visited_edges[eid]) {
                    visited_edges[eid] = true;
                    ordered_edges.push_back(eid);
                }
                const VertexID target = graph.edges[eid].target;
                if (!visited_vertices[target]) {
                    visited_vertices[target] = true;
                    q.push(target);
                }
            }
        }
    }

    std::string serialize_fragment(const RegexConstraintGraph& graph, const GraphFragment& frag, ast_manager& m) {
        std::queue<VertexID> q;
        std::vector<bool> visited_vertices(graph.vertices.size(), false);
        std::vector<bool> visited_edges(graph.edges.size(), false);
        std::vector<EdgeID> ordered_edges;

        q.push(frag.v_in);
        visited_vertices[frag.v_in] = true;

        while (!q.empty()) {
            const VertexID curr = q.front();
            q.pop();

            // Do not follow edges out of the fragment's output vertex.
            if (curr == frag.v_out) {
                continue;
            }

            for (EdgeID eid : graph.vertices[curr].outgoing_edges) {
                if (!visited_edges[eid]) {
                    visited_edges[eid] = true;
                    ordered_edges.push_back(eid);
                }
                const VertexID target = graph.edges[eid].target;
                if (!visited_vertices[target]) {
                    visited_vertices[target] = true;
                    q.push(target);
                }
            }
        }

        std::string res = "(FRAGMENT";
        for (EdgeID eid : ordered_edges) {
            const RCGEdge& edge = graph.edges[eid];
            res += " (EDGE *->* [";
            res += serialize_payload(graph, edge.payload, m) + "]";
            res += serialize_edge_markers(graph, eid);
            res += ")";
        }
        res += ")";
        return res;
    }

    std::string serialize_rcg(const RegexConstraintGraph& graph, ast_manager& m) {
        std::string res = "(RCG";

        if (graph.start_vertex == UNKNOWN_VERTEX) {
            return "(RCG INVALID_START_VERTEX)";
        }

        std::vector<bool> visited_edges(graph.edges.size(), false);
        std::vector<EdgeID> ordered_edges;
        rcg_bfs(graph, graph.start_vertex, visited_edges, ordered_edges);

        for (EdgeID eid : ordered_edges) {
            const RCGEdge& edge = graph.edges[eid];
            res += " (EDGE *->* [";
            res += serialize_payload(graph, edge.payload, m) + "]";
            res += serialize_edge_markers(graph, eid);
            res += ")";
        }
        res += ")";
        return res;
    }
}  // namespace smt::noodler::extended_regex
