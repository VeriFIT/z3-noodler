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

// =====================================================================
// CHARACTER SETS
// =====================================================================

TEST_CASE("Extended regex character sets", "[noodler][extended_regex]") {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util util_s(m);
    const Z3Char max_char = zstring::max_char();
    using Intervals = std::vector<CharSet::Interval>;

    SECTION("Overlapping and adjacent intervals are merged") {
        CharSet chars = CharSet::range('a', 'c');
        chars.add('e', 'g');
        REQUIRE(chars.get_intervals() == Intervals {{'a', 'c'}, {'e', 'g'}});
        chars.add('d');
        REQUIRE(chars.get_intervals() == Intervals {{'a', 'g'}});
        chars.add('0', 'b');
        REQUIRE(chars.get_intervals() == Intervals {{'0', 'g'}});
        REQUIRE(chars.size() == 'g' - '0' + 1);
    }

    SECTION("Intervals are sorted") {
        CharSet chars = CharSet::single('z');
        chars.add('a');
        chars.add(CharSet::range('m', 'n'));
        REQUIRE(chars.get_intervals() == Intervals {{'a', 'a'}, {'m', 'n'}, {'z', 'z'}});
    }

    SECTION("Complement") {
        REQUIRE(CharSet().complement() == CharSet::all());
        REQUIRE(CharSet::all().complement().is_empty());
        const CharSet chars = CharSet::range('b', 'c');
        REQUIRE(chars.complement().get_intervals() == Intervals {{0, 'a'}, {'d', max_char}});
        REQUIRE(chars.complement().complement() == chars);
    }

    SECTION("Characters beyond the maximal character are left out") {
        REQUIRE(CharSet::single(max_char + 1).is_empty());
        REQUIRE(CharSet::range('a', max_char + 100) == CharSet::range('a', max_char));
    }

    SECTION("Single character") {
        Z3Char ch = 0;
        REQUIRE(CharSet::single('a').is_single(ch));
        REQUIRE(ch == 'a');
        REQUIRE(!CharSet::range('a', 'b').is_single(ch));
        REQUIRE(!CharSet().is_single(ch));
    }

    SECTION("Serialization") {
        REQUIRE(CharSet().serialize().empty());
        REQUIRE(CharSet::range('a', 'z').serialize() == "'a'-'z'");
        const std::vector<Z3Char> chars {'_', '\n', 0x3000};
        REQUIRE(CharSet::of(chars).serialize() == R"('\u{a}' '_' '\u{3000}')");
        // A set whose complement is smaller is serialized by the complement
        REQUIRE(CharSet::single('a').complement().serialize() == "^ 'a'");
        REQUIRE(CharSet::all().serialize() == "^");
    }

    SECTION("Conversion to regex") {
        auto regex_of = [&](const CharSet& chars) {
            return to_single_line_string(chars.to_regex(util_s, m).get(), m);
        };
        REQUIRE(util_s.re.is_empty(CharSet().to_regex(util_s, m)));
        REQUIRE(util_s.re.is_full_char(CharSet::all().to_regex(util_s, m)));
        REQUIRE(regex_of(CharSet::single('a')) == "(str.to_re \"a\")");
        const std::vector<Z3Char> chars {'a', 'c', 'd'};
        REQUIRE(regex_of(CharSet::of(chars)) == "(re.union (str.to_re \"a\") (re.range \"c\" \"d\"))");
        // A set whose complement is smaller is given by the complement, so that its regex adds only few characters
        // to the alphabet of automata
        REQUIRE(regex_of(CharSet::range('b', 'c').complement()) ==
                "(re.inter re.allchar (re.comp (re.range \"b\" \"c\")))");
    }
}

// =====================================================================
// COMMON AST
// =====================================================================

TEST_CASE("Extended regex common AST", "[noodler][extended_regex]") {
    SECTION("Serialization") {
        const NodeRef root = make_concatenation(
            nodes(make_node(Anchor::START_OF_TEXT),
                  make_node(Capture {1, make_node(Repetition {.child = make_char('a'), .min = 2, .max = UNBOUNDED})}),
                  make_node(Lookaround {make_char('b'), LookaroundDirection::BACKWARD, false}),
                  make_node(Backreference {1}), make_node(CharSet::range('0', '9')), make_node(Anchor::END_OF_TEXT)));
        REQUIRE(serialize(*root) == "(SEQ (ASSERT '^') (GROUP #1 (QUANT {2,inf} (LIT 'a'))) (ASSERT ?<! (LIT 'b'))"
                                    " (BACKREF 1) (SET '0'-'9') (ASSERT '$'))");
    }

    SECTION("Word boundary is made of lookarounds") {
        REQUIRE(serialize(*make_word_boundary(CharSet::range('a', 'z'), false)) ==
                "(DISJ (SEQ (ASSERT ?<= (SET 'a'-'z')) (ASSERT ?! (SET 'a'-'z')))"
                " (SEQ (ASSERT ?<! (SET 'a'-'z')) (ASSERT ?= (SET 'a'-'z'))))");
        REQUIRE(serialize(*make_word_boundary(CharSet::range('a', 'z'), true)) ==
                "(DISJ (SEQ (ASSERT ?<= (SET 'a'-'z')) (ASSERT ?= (SET 'a'-'z')))"
                " (SEQ (ASSERT ?<! (SET 'a'-'z')) (ASSERT ?! (SET 'a'-'z'))))");
    }

    // ((a)\2)(b)\1
    auto make_groups = []() {
        return make_concatenation(nodes(make_node(Capture {
                                            1, make_concatenation(nodes(make_node(Capture {2, make_char('a')}),
                                                                        make_node(Backreference {2})))}),
                                        make_node(Capture {3, make_char('b')}), make_node(Backreference {1})));
    };

    SECTION("Collecting capture groups and backreferences") {
        const NodeRef root = make_groups();
        std::vector<GroupID> gids;
        collect_capture_groups(*root, gids);
        REQUIRE(gids == std::vector<GroupID> {1, 2, 3});
        std::unordered_set<GroupID> refs;
        collect_backrefs(*root, refs);
        REQUIRE(refs == std::unordered_set<GroupID> {1, 2});
    }

    SECTION("Unreferenced capture groups are removed") {
        NodeRef root = make_groups();
        strip_unreferenced_captures(root, {2});
        REQUIRE(serialize(*root) == "(SEQ (SEQ (GROUP #2 (LIT 'a')) (BACKREF 2)) (LIT 'b') (BACKREF 1))");
    }

    SECTION("Nested unreferenced capture groups are removed") {
        NodeRef root = make_node(Capture {1, make_node(Capture {2, make_char('a')})});
        strip_unreferenced_captures(root, {});
        REQUIRE(serialize(*root) == "(LIT 'a')");
    }

    SECTION("Backreference to a capture group inside a lookaround that does not contain it is unsupported") {
        // (?=(a))\1
        const NodeRef outside = make_concatenation(nodes(make_node(Lookaround {make_node(Capture {1, make_char('a')}),
                                                                               LookaroundDirection::FORWARD, true}),
                                                         make_node(Backreference {1})));
        REQUIRE_THROWS(check_lookaround_backrefs(*outside));
        // (?=(a)\1)
        const NodeRef inside = make_node(Lookaround {
            make_concatenation(nodes(make_node(Capture {1, make_char('a')}), make_node(Backreference {1}))),
            LookaroundDirection::FORWARD, true});
        REQUIRE_NOTHROW(check_lookaround_backrefs(*inside));
    }
}

// =====================================================================
// SEMANTICS PARAMETERS OF THE COMMON AST
// =====================================================================

TEST_CASE("Extended regex semantics parameters", "[noodler][extended_regex]") {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util util_s(m);
    const app_ref x(m.mk_const("x", util_s.mk_string_sort()), m);

    // (?:(a))?\1 with the given semantics of the repetition
    auto build_repeated_capture = [&](const bool resets_captures, const bool rejects_empty_iterations) {
        const NodeRef root =
            make_concatenation(nodes(make_node(Repetition {.child = make_node(Capture {1, make_char('a')}),
                                                           .min = 0,
                                                           .max = 1,
                                                           .resets_captures = resets_captures,
                                                           .rejects_empty_iterations = rejects_empty_iterations}),
                                     make_node(Backreference {1, true})));
        return serialize_rcg(build_rcg(*root, false, util_s, m), m);
    };

    SECTION("Iterations without capture resets and empty iteration checks are not marked") {
        REQUIRE(build_repeated_capture(false, false) == "(RCG"
                                                        " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1})"
                                                        " (EDGE *->* [MATCH (str.to_re \"\")])"
                                                        " (EDGE *->* [BACKREF 1])"
                                                        ")");
    }

    SECTION("Iterations resetting captures start with a reset") {
        REQUIRE(build_repeated_capture(true, false) == "(RCG"
                                                       " (EDGE *->* [EPSILON] RESETS {1})"
                                                       " (EDGE *->* [MATCH (str.to_re \"\")])"
                                                       " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1})"
                                                       " (EDGE *->* [BACKREF 1])"
                                                       ")");
    }

    SECTION("Iterations rejected if empty are checked without resetting captures") {
        REQUIRE(build_repeated_capture(false, true) == "(RCG"
                                                       " (EDGE *->* [EPSILON] RESETS {})"
                                                       " (EDGE *->* [MATCH (str.to_re \"\")])"
                                                       " (EDGE *->* [MATCH (str.to_re \"a\")] STARTS {1} ENDS {1})"
                                                       " (EDGE *->* [BACKREF 1])"
                                                       " (EDGE *->* [EPSILON] NONEMPTY)"
                                                       ")");
    }

    // \1(a) with the given semantics of the backreference to the unset group
    auto generate_forward_reference = [&](const bool unset_matches_empty) {
        const NodeRef root = make_concatenation(nodes(make_node(Backreference {1, unset_matches_empty}),
                                                      make_node(Capture {1, make_char('a')})));
        const RegexConstraintGraph graph = build_rcg(*root, false, util_s, m);
        ConstraintGenerator generator(m, graph);
        return to_single_line_string(generator.generate_constraints(x).get(), m);
    };

    SECTION("Backreference to an unset group matches the empty string") {
        REQUIRE(generate_forward_reference(true) == "(and (= regex!0 \"\")"
                                                    " (str.in_re regex!1 (str.to_re \"a\"))"
                                                    " (= x (str.++ regex!0 regex!1)))");
    }

    SECTION("Backreference to an unset group fails") {
        REQUIRE(generate_forward_reference(false) == "(and false"
                                                     " (str.in_re regex!1 (str.to_re \"a\"))"
                                                     " (= x (str.++ regex!0 regex!1)))");
    }
}
