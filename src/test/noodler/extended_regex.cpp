#include "smt/theory_str_noodler/extended_regex/constraint_generator.h"
#include "smt/theory_str_noodler/extended_regex/regex_ast.h"
#include "smt/theory_str_noodler/extended_regex/regex_constraint_graph.h"

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"

#include <catch2/catch_test_macros.hpp>
#include <string>

using namespace smt::noodler::extended_regex;

namespace {
    // Converts a Z3 app_ref to a normalized string (collapses whitespace, removes newlines).
    std::string app_to_string(const app_ref& app, ast_manager& m) {
        return to_single_line_string(app.get(), m);
    }

    NodeRef make_char(const Z3Char ch) {
        return make_node(CharSet::single(ch));
    }

    NodeRef make_concatenation(std::vector<NodeRef> terms) {
        return make_node(Concatenation {std::move(terms)});
    }

    template<typename... Ts>
    std::vector<NodeRef> nodes(Ts... nodes) {
        std::vector<NodeRef> result;
        (result.push_back(std::move(nodes)), ...);
        return result;
    }
}  // namespace

// =====================================================================
// RCG GENERATION FROM AST – UNIT TESTS
// =====================================================================

TEST_CASE("Extended regex RCG generation from AST", "[noodler][extended_regex]") {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util util_s(m);
    RegexConstraintGraph graph;

    SECTION("Literal returns regular app_ref") {
        RegexComponent comp = build_component(*make_char('x'), graph, util_s, m);
        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        app_ref z3_regex = std::get<app_ref>(comp);
        REQUIRE(app_to_string(z3_regex, m) == "(str.to_re \"x\")");
    }

    SECTION("Repetition wraps the child node in a quantifier") {
        const NodeRef quant = make_node(Repetition {.child = make_char('x'), .min = 0, .max = UNBOUNDED});

        RegexComponent comp = build_component(*quant, graph, util_s, m);
        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        app_ref z3_regex = std::get<app_ref>(comp);
        REQUIRE(app_to_string(z3_regex, m) == "(re.* (str.to_re \"x\"))");
    }

    SECTION("Backreference mutates graph and returns GraphFragment") {
        RegexComponent comp = build_component(*make_node(Backreference {1}), graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        REQUIRE(graph.vertices.size() == 2);
        REQUIRE(graph.edges.size() == 1);
        REQUIRE(frag.v_in == 0);
        REQUIRE(frag.v_out == 1);
        REQUIRE(frag.edges_pointing_to_vout.size() == 1);

        const RCGEdge& edge = graph.edges[frag.edges_pointing_to_vout[0]];
        REQUIRE(std::holds_alternative<BackrefEdge>(edge.payload));
        REQUIRE(std::get<BackrefEdge>(edge.payload).backref_id == 1);
    }

    SECTION("Capture tags edges correctly") {
        const NodeRef group = make_node(Capture {42, make_char('a')});

        RegexComponent comp = build_component(*group, graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        EdgeID the_edge_id = frag.edges_pointing_to_vout[0];

        REQUIRE(graph.group_starts.count(the_edge_id) > 0);
        REQUIRE(graph.group_starts.at(the_edge_id).size() == 1);
        REQUIRE(graph.group_starts.at(the_edge_id)[0] == 42);

        REQUIRE(graph.group_ends.count(the_edge_id) > 0);
        REQUIRE(graph.group_ends.at(the_edge_id).size() == 1);
        REQUIRE(graph.group_ends.at(the_edge_id)[0] == 42);
    }

    SECTION("Set of all characters except a few creates regular app_ref with re.allchar without them") {
        const std::vector<Z3Char> line_terminators {0x0A, 0x0D, 0x2028, 0x2029};
        RegexComponent comp = build_component(*make_node(CharSet::of(line_terminators).complement()), graph, util_s, m);

        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        // re.inter(re.allchar, re.comp(line_terminators))
        app_ref z3_regex = std::get<app_ref>(comp);
        expr* all_chars = nullptr;
        expr* complement = nullptr;
        expr* excluded = nullptr;
        REQUIRE(util_s.re.is_intersection(z3_regex, all_chars, complement));
        REQUIRE(util_s.re.is_full_char(all_chars));
        REQUIRE(util_s.re.is_complement(complement, excluded));
        REQUIRE(app_to_string(app_ref(to_app(excluded), m), m) ==
                "(re.union (re.union (str.to_re \"\\u{a}\") (str.to_re \"\\u{d}\")) (re.range \"\\u{2028}\" "
                "\"\\u{2029}\"))");
    }

    SECTION("Anchor creates assertion edge") {
        RegexComponent comp = build_component(*make_node(Anchor::START_OF_TEXT), graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        REQUIRE(graph.vertices.size() == 2);
        REQUIRE(graph.edges.size() == 1);

        const RCGEdge& edge = graph.edges[frag.edges_pointing_to_vout[0]];
        REQUIRE(std::holds_alternative<AssertionEdge>(edge.payload));
        const AssertionEdge& ae = std::get<AssertionEdge>(edge.payload);
        REQUIRE(std::holds_alternative<Anchor>(ae.payload));
        REQUIRE(std::get<Anchor>(ae.payload) == Anchor::START_OF_TEXT);
    }

    SECTION("Repetition throws on unbounded non-regular subregex") {
        // Kleene star/plus over backreferences would create a dynamic number of string variables.
        const NodeRef quant = make_node(Repetition {.child = make_node(Backreference {1}), .min = 0, .max = UNBOUNDED});

        REQUIRE_THROWS(build_component(*quant, graph, util_s, m));
    }

    SECTION("Repetition with finite bounds on non-regular subregex creates fragment") {
        // {n,m} quantifier over a backreference expands into m copies of the sub-graph.
        const NodeRef quant = make_node(Repetition {.child = make_node(Backreference {1}), .min = 1, .max = 2});

        RegexComponent comp = build_component(*quant, graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));
        // Two copies of the backref fragment plus epsilon alternations are created.
        REQUIRE(!graph.vertices.empty());
        REQUIRE(!graph.edges.empty());
    }

    SECTION("Concatenation merges two regular literals into one app_ref") {
        const NodeRef concat = make_concatenation(nodes(make_char('a'), make_char('b')));

        RegexComponent comp = build_component(*concat, graph, util_s, m);
        REQUIRE(std::holds_alternative<app_ref>(comp));
        REQUIRE(graph.vertices.empty());

        app_ref z3_regex = std::get<app_ref>(comp);
        REQUIRE(app_to_string(z3_regex, m) == "(str.to_re \"ab\")");
    }

    SECTION("Concatenation creates graph fragment when mixing literal and backref") {
        const NodeRef concat = make_concatenation(nodes(make_char('a'), make_node(Backreference {1})));

        RegexComponent comp = build_component(*concat, graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        // Backref creates {v0,v1,e_br}, literal is lifted to {v2,v3,e_match}.
        // chain_fragments orphans v3 (retargets e_match to v0) → 4 vertices, 2 edges.
        REQUIRE(graph.vertices.size() == 4);
        REQUIRE(graph.edges.size() == 2);
    }

    SECTION("Concatenation chains adjacent regular subregexes into one") {
        // "ab\1cd" – 'ab' and 'cd' are each merged into a single MATCH edge.
        const NodeRef concat = make_concatenation(nodes(make_char('a'), make_char('b'), make_node(Backreference {1}),
                                                        make_char('c'), make_char('d')));

        RegexComponent comp = build_component(*concat, graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        // Expected: MATCH('ab'), BACKREF(1), MATCH('cd') — 3 edges total.
        REQUIRE(graph.edges.size() == 3);

        bool has_match_ab = false, has_match_cd = false, has_backref = false;
        for (const RCGEdge& edge : graph.edges) {
            if (std::holds_alternative<MatchEdge>(edge.payload)) {
                std::string s = app_to_string(std::get<MatchEdge>(edge.payload).regex, m);
                if (s.find("str.to_re \"ab\"") != std::string::npos) {
                    has_match_ab = true;
                }
                if (s.find("str.to_re \"cd\"") != std::string::npos) {
                    has_match_cd = true;
                }
            }
            else if (std::holds_alternative<BackrefEdge>(edge.payload)) {
                has_backref = true;
            }
        }
        REQUIRE((has_match_ab && has_match_cd && has_backref));
    }

    // ---- Lookaround tests ----

    SECTION("Regular lookahead creates assertion edge with app_ref subregex") {
        const NodeRef lookahead = make_node(Lookaround {make_char('a'), LookaroundDirection::FORWARD, true});

        RegexComponent comp = build_component(*lookahead, graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        const RCGEdge& edge = graph.edges[frag.edges_pointing_to_vout[0]];
        REQUIRE(std::holds_alternative<AssertionEdge>(edge.payload));
        const LookaroundAssertion& la = std::get<LookaroundAssertion>(std::get<AssertionEdge>(edge.payload).payload);
        REQUIRE(std::holds_alternative<app_ref>(la.subregex));
        REQUIRE(la.is_positive == true);
        REQUIRE(la.direction == LookaroundDirection::FORWARD);
    }

    SECTION("Positive lookaround with non-regular subregex creates fragment") {
        // A positive lookahead whose inner pattern is non-regular (backreference) is supported.
        // The subregex in the LookaroundAssertion is stored as a GraphFragment instead of an app_ref.
        const NodeRef lookahead =
            make_node(Lookaround {make_node(Backreference {1}), LookaroundDirection::FORWARD, true});

        RegexComponent comp = build_component(*lookahead, graph, util_s, m);
        REQUIRE(std::holds_alternative<GraphFragment>(comp));

        GraphFragment frag = std::get<GraphFragment>(comp);
        REQUIRE(graph.edges.size() >= 1);

        const RCGEdge& outer_edge = graph.edges[frag.edges_pointing_to_vout[0]];
        REQUIRE(std::holds_alternative<AssertionEdge>(outer_edge.payload));
        const LookaroundAssertion& la =
            std::get<LookaroundAssertion>(std::get<AssertionEdge>(outer_edge.payload).payload);

        // The subregex must be a GraphFragment (non-regular).
        REQUIRE(std::holds_alternative<GraphFragment>(la.subregex));
        REQUIRE(la.is_positive == true);
        REQUIRE(la.direction == LookaroundDirection::FORWARD);

        // The inner fragment must contain exactly one BackrefEdge.
        const GraphFragment& inner = std::get<GraphFragment>(la.subregex);
        REQUIRE(graph.vertices[inner.v_in].outgoing_edges.size() == 1);
        EdgeID inner_eid = graph.vertices[inner.v_in].outgoing_edges[0];
        REQUIRE(std::holds_alternative<BackrefEdge>(graph.edges[inner_eid].payload));
        REQUIRE(std::get<BackrefEdge>(graph.edges[inner_eid].payload).backref_id == 1);
    }

    SECTION("Negative lookaround with non-regular subregex throws") {
        // A negative non-regular lookaround would require universal quantifiers — not supported.
        const NodeRef lookahead =
            make_node(Lookaround {make_node(Backreference {1}), LookaroundDirection::FORWARD, false});

        REQUIRE_THROWS(build_component(*lookahead, graph, util_s, m));
    }

    SECTION("Complement of a set negates correctly") {
        RegexComponent comp = build_component(*make_node(CharSet::single('a').complement()), graph, util_s, m);
        REQUIRE(std::holds_alternative<app_ref>(comp));

        app_ref z3_regex = std::get<app_ref>(comp);
        std::string s = app_to_string(z3_regex, m);
        // Z3 may represent the negation as re.diff or re.inter + re.complement,
        // but either way the universe regex and the complement must be present.
        REQUIRE((s.find("re.diff") != std::string::npos || s.find("re.comp") != std::string::npos));
        REQUIRE((s.find("re.all") != std::string::npos));  // covers both re.all and re.allchar
    }
}

// Restoring a snapshot undoes all the changes of capture group variables made after it was taken (#506)
TEST_CASE("Extended regex DFS context backtracking", "[noodler][extended_regex]") {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util util_s(m);
    DFSContext ctx(m, util_s);

    // Group 1 captures v0 and stays active
    ctx.start_groups({1});
    const app_ref v0 = ctx.create_edge_var();
    ctx.push_edge_var_to_groups(v0);

    SECTION("Variables appended to an active group are removed") {
        const DFSStateSnapshot snapshot = ctx.save_snapshot();
        const app_ref v1 = ctx.create_edge_var();
        ctx.push_edge_var_to_groups(v1);
        REQUIRE(app_to_string(app_ref(to_app(ctx.concat_group_vars(1)), m), m) == "(str.++ regex!0 regex!1)");

        ctx.restore_snapshot(snapshot);
        REQUIRE(ctx.concat_group_vars(1).get() == v0.get());
    }

    SECTION("Restarted group gets its previous variables back") {
        ctx.end_groups({1});
        const DFSStateSnapshot snapshot = ctx.save_snapshot();
        ctx.start_groups({1});
        const app_ref v1 = ctx.create_edge_var();
        ctx.push_edge_var_to_groups(v1);
        REQUIRE(ctx.concat_group_vars(1).get() == v1.get());

        ctx.restore_snapshot(snapshot);
        REQUIRE(ctx.concat_group_vars(1).get() == v0.get());
    }

    SECTION("Group reset to undefined gets its previous variables back") {
        ctx.end_groups({1});
        const DFSStateSnapshot snapshot = ctx.save_snapshot();
        ctx.reset_groups({1});
        REQUIRE(!ctx.has_group(1));
        ctx.start_groups({1});
        const app_ref v1 = ctx.create_edge_var();
        ctx.push_edge_var_to_groups(v1);
        REQUIRE(ctx.concat_group_vars(1).get() == v1.get());

        ctx.restore_snapshot(snapshot);
        REQUIRE(ctx.has_group(1));
        REQUIRE(ctx.concat_group_vars(1).get() == v0.get());
    }

    SECTION("Group created after the snapshot is removed") {
        const DFSStateSnapshot snapshot = ctx.save_snapshot();
        ctx.start_groups({2});
        const app_ref v1 = ctx.create_edge_var();
        ctx.push_edge_var_to_groups(v1);
        REQUIRE(ctx.has_group(2));

        ctx.restore_snapshot(snapshot);
        REQUIRE(!ctx.has_group(2));
        REQUIRE(ctx.concat_group_vars(1).get() == v0.get());
    }

    SECTION("Nested snapshots are restored in reverse order") {
        ctx.end_groups({1});
        const DFSStateSnapshot outer_snapshot = ctx.save_snapshot();
        ctx.start_groups({1});
        const app_ref v1 = ctx.create_edge_var();
        ctx.push_edge_var_to_groups(v1);
        ctx.end_groups({1});

        const DFSStateSnapshot inner_snapshot = ctx.save_snapshot();
        ctx.start_groups({1});
        const app_ref v2 = ctx.create_edge_var();
        ctx.push_edge_var_to_groups(v2);
        REQUIRE(ctx.concat_group_vars(1).get() == v2.get());

        ctx.restore_snapshot(inner_snapshot);
        REQUIRE(ctx.concat_group_vars(1).get() == v1.get());
        ctx.restore_snapshot(outer_snapshot);
        REQUIRE(ctx.concat_group_vars(1).get() == v0.get());
    }
}
