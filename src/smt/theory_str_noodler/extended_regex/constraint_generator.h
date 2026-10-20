#pragma once

#include "regex_constraint_graph.h"

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"

#include <cstdint>
#include <limits>
#include <memory>
#include <unordered_map>
#include <vector>

namespace smt::noodler::extended_regex {
    // ================= DFS CONTEXT CLASSES ==================

    /**
     * A postponed lookahead assertion waiting to be evaluated at the end of the current path.
     *
     * Lookaheads cannot be evaluated at the point where they appear in the graph because they constrain the suffix of
     * the matched string, which is not yet known at that point. Instead, they are pushed onto a list and evaluated when
     * the graph traversal reaches the end vertex.
     *
     * `start_index` is the index into `m_current_path_vars` of the first variable after the position of the lookahead.
     * When the lookahead is evaluated at the end vertex, the suffix of the string is obtained by concatenating the
     * string variables from `start_index` to the end of `m_current_path_vars`.
     *
     * `group_vars` holds the captures of the groups closed at the moment the lookahead was encountered (only for
     * non-regular lookaheads, which can contain backreferences). Backreferences inside the lookahead refer to these
     * captures, not to the ones at the end of the path, which later iterations of a quantifier may reset or overwrite.
     */
    struct ActiveLookahead {
        RegexComponent subregex;
        bool is_positive;
        std::size_t start_index;
        std::unordered_map<GroupID, expr_ref_vector> group_vars;
    };

    /**
     * A single change of the capture group variables made during the DFS traversal, recorded so that
     * restore_snapshot() can undo it when backtracking.
     */
    struct GroupVarsChange {
        enum class Kind {
            APPEND,  // an edge variable was appended to the variables of the group
            CREATE,  // the group was started for the first time
            RESET,   // the group was started again, its previous variables were saved for restoring
            ERASE,   // the capture of the group was reset to undefined, its previous variables were saved for restoring
        };

        Kind kind;
        GroupID gid;
    };

    /**
     * A snapshot of the DFS context at a concrete point in the traversal.
     *
     * Saved before entering each outgoing edge of a vertex so that, after exploring one branch of an alternation, the
     * context can be fully restored before entering the next branch.
     *
     * The group variables are not copied into this snapshot, only the number of their changes recorded so far is
     * saved. restore_snapshot() then undoes all the changes recorded after the snapshot was taken.
     */
    struct DFSStateSnapshot {
    public:
        unsigned num_path_vars = 0;
        unsigned num_path_constraints = 0;
        unsigned num_active_lookaheads = 0;
        unsigned num_group_vars_changes = 0;
        std::vector<GroupID> active_groups;
    };

    /**
     * Holds the full outer DFS state while an inner DFS is running for a non-regular lookaround. The outer state is
     * moved into this struct by `suspend_for_inner_search()` and restored afterwards by `resume_from_inner_search()`.
     */
    struct OuterSearchState {
        std::unique_ptr<expr_ref_vector> unique_paths;
        std::unique_ptr<expr_ref_vector> current_path_vars;
        std::unique_ptr<expr_ref_vector> current_path_constraints;
        std::vector<GroupID> active_groups;
        std::vector<ActiveLookahead> active_lookaheads;
        VertexID end_vertex;
        app* target_string;
        std::vector<GroupID> existing_group_ids;
    };

    /**
     * Carries and manages all mutable state for a single DFS traversal of the RCG.
     *
     * The DFS explores every path from start_vertex to end_vertex. Along the way, it accumulates variables of edges
     * that consume text, i.e., all edges except zero-width assertions and marker edges (`m_current_path_vars`),
     * constraints on those variables (`m_current_path_constraints`), and lists of variables for each capture group
     * (`m_group_vars`). When a complete path is found, commit_current_path() merges all constraints into one
     * conjunction and adds it to `m_unique_paths`.
     *
     * Before each outgoing edge of a vertex, `save_snapshot()` / `restore_snapshot()` are used to backtrack between
     * branches. Changes of the group variables are recorded in an undo trail (`m_group_vars_changes`), so that
     * restoring a snapshot only undoes the changes made after it was taken.
     *
     * For non-regular lookarounds, the outer DFS state is moved into an `OuterSearchState` via
     * `suspend_for_inner_search()`, a nested DFS runs with fresh state, and then `resume_from_inner_search()` restores
     * it.
     *
     * `m_base_prefix` holds all the string variables accumulated by outer DFS calls.
     * `get_global_prefix()` concatenates `m_base_prefix` with the current inner DFS path's variables to give the full
     * prefix at the current position in the original target string.
     *
     * `m_base_suffix` is the rest of the original target string after the end of the current DFS target. It is
     * nonempty only inside a lookbehind, whose target ends at the lookbehind position. `get_global_suffix()` appends
     * it to the current path's variables, so that lookaheads see the rest of the whole string.
     */
    class DFSContext {
    public:
        DFSContext(ast_manager& manager, seq_util& util)
            : m_manager(manager),
              m_util_s(util),
              m_str_sort(util.mk_string_sort()),
              m_base_prefix(manager),
              m_base_suffix(manager),
              m_unique_paths(manager),
              m_current_path_vars(manager),
              m_current_path_constraints(manager),
              m_all_created_vars(manager) { }

        void set_target(app* target);
        app* get_target() const;
        void set_end_vertex(VertexID v);
        VertexID get_end_vertex() const;
        void set_base_prefix(const expr_ref& p);
        expr_ref get_base_prefix() const;
        void set_base_suffix(const expr_ref& s);
        expr_ref get_base_suffix() const;

        /**
         * @brief Save the current DFS state before exploring one outgoing edge.
         *
         * The snapshot captures the sizes of the path variable and constraint vectors, the active lookahead count, the
         * number of recorded changes of group variables, and the list of active groups. Used for backtracking between
         * branches in the DFS.
         *
         * @return DFSStateSnapshot The current state snapshot.
         */
        DFSStateSnapshot save_snapshot() const;

        /**
         * @brief Restore the DFS state to a previously saved @p snapshot after an edge visit.
         *
         * Fully undoes everything that was changed during the edge visit, including appends to path variable and
         * constraint vectors, modifications to active lookaheads and groups, and changes of group variables (in reverse
         * order of the recorded changes).
         * @param snapshot The snapshot to restore from.
         */
        void restore_snapshot(const DFSStateSnapshot& snapshot);

        /**
         * @brief Suspend the current outer DFS so a DFS for a subgraph can start a fresh search.
         *
         * Moves the whole state into an `OuterSearchState`, then resets the context to a clean empty state ready for
         * the inner search.
         *
         * @return OuterSearchState The suspended outer state.
         */
        OuterSearchState suspend_for_inner_search();

        /**
         * @brief Restore the outer DFS @p state after an inner search has completed.
         *
         * @param state The OuterSearchState returned by suspend_for_inner_search().
         */
        void resume_from_inner_search(OuterSearchState& state);

        /**
         * @brief Create a fresh string variable without adding it to the path.
         *
         * The variable is also tracked in the internal list of all created fresh variables so it can later
         * be existentially quantified over in the generated formula.
         *
         * @return app_ref The new string variable.
         */
        app_ref mk_fresh_string_var();

        /**
         * @brief Return all fresh string variables created during the entire DFS (including inner DFS runs).
         *
         * Used to existentially quantify over all auxiliary variables introduced during constraint generation.
         *
         * @return app_ref_vector The list of all created fresh variables.
         */
        const app_ref_vector& get_all_fresh_vars() const;

        /**
         * @brief Create a fresh string variable for the current edge and append it to the path variable list.
         *
         * The variable is also registered with all currently open capture groups via
         * push_edge_var_to_groups (called separately by the caller after this).
         *
         * @return app_ref The new edge variable.
         */
        app_ref create_edge_var();

        /**
         * @brief Add the @p edge_var to variable list of every currently open capture group.
         *
         * @param edge_var The edge variable to add to the active groups.
         */
        void push_edge_var_to_groups(const app_ref& edge_var);

        /**
         * @brief Add a @p constraint to the current path's constraint list.
         *
         * @param constraint The constraint to add.
         */
        void add_path_constraint(const app_ref& constraint);

        /**
         * @brief Marks all the capture groups, that start on the current edge, as active.
         *
         * Therefore, from this point, any string variable created during the traversal will be added a variable
         * list of each of these groups until they are closed.
         *
         * @param gids The group IDs to open.
         */
        void start_groups(const std::vector<GroupID>& gids);

        /**
         * @brief Marks all the capture groups, that end on the current edge, as inactive.
         *
         * After this, new edge variables will no longer be added to the variable list of these groups.
         *
         * @param gids The group IDs to close.
         */
        void end_groups(const std::vector<GroupID>& gids);

        bool has_group(GroupID gid) const;

        bool is_group_active(GroupID gid) const;

        /**
         * @brief Return the variable lists of the capture groups that are closed at the current position.
         *
         * The capture of a group that is still open is undefined at the current position, so a backreference to it
         * matches the empty string.
         */
        std::unordered_map<GroupID, expr_ref_vector> get_closed_group_vars() const;

        /**
         * @brief Reset the captures of the groups @p gids to undefined.
         *
         * A backreference to a reset group matches the empty string until the group is entered again.
         *
         * @param gids The group IDs to reset.
         */
        void reset_groups(const std::vector<GroupID>& gids);

        /**
         * @brief Remember the current position on the path as the start of the quantifier iteration that begins on
         * the edge @p start_eid.
         *
         * @param start_eid The edge starting the iteration.
         */
        void mark_iteration_start(EdgeID start_eid);

        /**
         * @brief Concatenate the edge variables of the current path from the start of the quantifier iteration that
         * began on the edge @p start_eid.
         *
         * @param start_eid The edge starting the iteration.
         * @return expr_ref The string matched by the iteration so far.
         */
        expr_ref concat_iteration_vars(EdgeID start_eid) const;

        /**
         * @brief Replace the variable lists of all capture groups by @p group_vars.
         *
         * @param group_vars The new variable lists of capture groups.
         * @return The previous variable lists of capture groups.
         */
        std::unordered_map<GroupID, expr_ref_vector>
        replace_group_vars(std::unordered_map<GroupID, expr_ref_vector> group_vars);

        /**
         * @brief Postpone a lookahead assertion for evaluation at the end of the current path.
         *
         * Saves the @p subregex, polarity, current position in the matched string and, for a non-regular lookahead,
         * the captures of the currently closed groups.
         *
         * @param subregex    The lookahead subregex.
         * @param is_positive The lookahead polarity.
         */
        void push_lookahead(const RegexComponent& subregex, bool is_positive);

        const std::vector<ActiveLookahead>& get_active_lookaheads() const;

        /**
         * @brief Take all the constraints accumulated during the current traversal and conjunct them.
         *
         * Takes `m_current_path_constraints` with @p additional_constraints (postponed lookaheads' constraints),
         * creates an equality `target_string` = concat(`edge_vars`), and stores the resulting conjunction in
         * `m_unique_paths`.
         *
         * @param additional_constraints Extra (lookahead) constraints to include.
         */
        void commit_current_path(const expr_ref_vector& additional_constraints);

        expr_ref_vector& get_unique_paths();

        /**
         * @brief Concatenate generated edge variables accumulated on the current path from @p start_idx to @p end_idx.
         *
         * @param start_idx Index of the first variable to include.
         * @param end_idx   One-past-last index (default: all variables).
         * @return expr_ref The concatenation of the selected edge variables.
         */
        expr_ref concat_vars(uint32_t start_idx = 0, uint32_t end_idx = std::numeric_limits<uint32_t>::max()) const;

        /**
         * @brief Return the prefix of the target string matched from the beginning, across all DFS levels.
         *
         * @return expr_ref The global prefix expression.
         */
        expr_ref get_global_prefix() const;

        /**
         * @brief Return the rest of the original target string from the edge variable at @p start_idx on the current
         * path, across all DFS levels.
         *
         * @param start_idx Index of the first edge variable of the suffix.
         * @return expr_ref The global suffix expression.
         */
        expr_ref get_global_suffix(uint32_t start_idx) const;

        /**
         * @brief Concatenate all edge variables captured by a group @p gid on the current path.
         *
         * @param gid The capture group whose variable list to concatenate.
         * @return expr_ref The string captured by the group on the current path.
         */
        expr_ref concat_group_vars(GroupID gid) const;

    private:
        ast_manager& m_manager;
        seq_util& m_util_s;
        sort* m_str_sort;

        app* m_target_string = nullptr;
        VertexID m_end_vertex = UNKNOWN_VERTEX;
        expr_ref m_base_prefix;
        expr_ref m_base_suffix;

        expr_ref_vector m_unique_paths;
        expr_ref_vector m_current_path_vars;
        expr_ref_vector m_current_path_constraints;

        std::vector<GroupID> m_active_groups;
        std::unordered_map<GroupID, expr_ref_vector> m_group_vars;
        std::vector<ActiveLookahead> m_active_lookaheads;

        // Index into `m_current_path_vars` where the quantifier iteration started by the given edge begins.
        // It does not need to be part of the snapshot: the RCG is acyclic and the edge ending an iteration is only
        // reachable through the edge starting it, so the stored index always comes from the current path.
        std::unordered_map<EdgeID, unsigned> m_iteration_starts;

        // Undo trail of all the changes of `m_group_vars` on the current path, undone by restore_snapshot()
        std::vector<GroupVarsChange> m_group_vars_changes;
        // Previous variables of the groups reset by start_groups() or reset_groups(), one for each RESET and ERASE
        // change in `m_group_vars_changes`
        std::vector<expr_ref_vector> m_reset_group_vars;

        // Accumulates every fresh variable created via mk_fresh_string_var() across the entire DFS (including inner
        // DFS runs for lookarounds). Used to existentially quantify over auxiliary variables in the final formula.
        app_ref_vector m_all_created_vars;

        expr_ref concat_expr_vector(const expr_ref_vector& vars, uint32_t start_idx, uint32_t end_idx) const;
    };

    // ============= CONSTRAINT GENERATOR =============

    /**
     * Translates a membership in the regex given by an RCG into Z3 string constraints by traversing all paths of the
     * RCG.
     *
     * Usage:
     *   1. Construct with the RCG of the regex.
     *   2. Call generate_constraints(target) to produce an SMT2 formula that is satisfiable iff target matches the
     *      regex.
     */
    class ConstraintGenerator {
    public:
        ConstraintGenerator(ast_manager& m, const RegexConstraintGraph& graph)
            : m_manager(m),
              m_util_s(m),
              m_graph(graph),
              m_str_sort(m_util_s.mk_string_sort()),
              m_fresh_vars(m) { }

        /**
         * @brief Generate constraints for the given target string based on the RCG.
         *
         * Returns a ground formula whose auxiliary (fresh) string variables are Skolem constants. The list of those
         * constants is available via get_fresh_vars() after this call returns. If the RCG is a single path of match
         * edges, the formula is a plain regex membership of @p target_string without any fresh variables.
         *
         * @param target_string The string for which the regex constraints are to be generated.
         * @return expr_ref A ground Z3 expression that is satisfiable iff target matches the regex pattern.
         */
        expr_ref generate_constraints(app* target_string);

        /**
         * @brief Return the fresh Skolem variables introduced during the last generate_constraints() call.
         *
         * Used by the caller to build the existentially-quantified form needed for the negative implication.
         *
         * @return const app_ref_vector& All fresh variables created during DFS (including inner DFS for lookarounds).
         */
        const app_ref_vector& get_fresh_vars() const;

        /**
         * @brief Get the regex of the whole RCG if the RCG is a single path consisting only of match edges.
         *
         * This is the case for regular patterns (possibly wrapped in Sigma* edges for the engine matching semantics).
         *
         * @return app_ref The concatenation of the regexes on the path, or null if the RCG is not a single path of
         *                 match edges.
         */
        app_ref get_regular_path_regex();

    private:
        ast_manager& m_manager;
        seq_util m_util_s;
        const RegexConstraintGraph& m_graph;
        sort* m_str_sort = nullptr;

        // used by anchor evaluation -- the anchors compare against the full original target string
        app* m_global_target_string = nullptr;

        // Populated by generate_constraints(); holds every fresh Skolem constant introduced during DFS.
        app_ref_vector m_fresh_vars;

        /**
         * @brief Run an inner DFS on a subgraph to evaluate a non-regular lookaround.
         *
         * @param fragment      The sub-fragment whose paths are to be enumerated.
         * @param target_string The string the inner search must match against.
         * @param ctx           The outer DFS context (will be suspended and restored).
         * @return expr_ref     OR of all satisfying path formulas for the inner search,
         *                      or false if no matching path exists.
         */
        expr_ref run_inner_rcg_dfs(const GraphFragment& fragment, app* target_string, DFSContext& ctx);

        /**
         * @brief Handle the lookaround assertions postponed during DFS traversal by generating constraints based on the
         * lookaround type and its subregex.
         *
         * @param ctx           The DFS context.
         * @param assertion     The lookaround assertion edge for which constraints are to be generated.
         */
        void handle_lookaround_constraints(DFSContext& ctx, const AssertionEdge& assertion);

        /**
         * @brief Generate lookahead constraints for the current path.
         *
         * @param ctx               The DFS context.
         * @param final_constraints The list of generated lookahead constraints.
         */
        void generate_lookahead_constraints(DFSContext& ctx, expr_ref_vector& final_constraints);

        /**
         * @brief Generate string constraints for a zero-width @p assertion (anchor or lookaround) at current position.
         *
         * @param ctx The DFS context containing the current path state and accumulated constraints.
         * @param assertion The assertion for which constraints are to be generated.
         */
        void generate_assertion_constraints(DFSContext& ctx, const AssertionEdge& assertion);

        /**
         * @brief Generate string constraints for a match or backreference @p edge in the RCG based on the @p edge type.
         *
         * @param ctx The DFS context containing the current path state and accumulated constraints.
         * @param edge The edge for which constraints are to be generated.
         * @param edge_var The string variable representing the @p edge.
         */
        void generate_edge_constraints(DFSContext& ctx, const RCGEdge& edge, const app_ref& edge_var);

        /**
         * @brief Require the repetition iteration that began on the edge @p start_eid to match a nonempty string.
         *
         * An iteration beyond the repetition minimum of a repetition rejecting empty iterations fails if it matched
         * the empty string (e.g., ES2020 RepeatMatcher, step 2.b).
         *
         * @param ctx       The DFS context.
         * @param start_eid The edge starting the iteration.
         */
        void generate_nonempty_iteration_constraint(DFSContext& ctx, EdgeID start_eid);

        /**
         * @brief One step of the DFS traversal of RCG.
         * Explores all outgoing edges of the @p current_vertex and generates constraints for each of them.
         *
         * @param current_vertex The vertex whose outgoing edges are currently being explored
         * @param ctx The context carrying DFS state accumulated on the curently explored path.
         */
        void rcg_dfs_visit(VertexID current_vertex, DFSContext& ctx);
    };
}  // namespace smt::noodler::extended_regex
