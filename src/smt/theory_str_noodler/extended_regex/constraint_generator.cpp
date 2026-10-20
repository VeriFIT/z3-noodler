#include "constraint_generator.h"

#include "smt/theory_str_noodler/util.h"

#include "util/debug.h"

#include <algorithm>

namespace smt::noodler::extended_regex {
    // ============= DFS CONTEXT =============

    void DFSContext::set_target(app* target) {
        m_target_string = target;
    }

    app* DFSContext::get_target() const {
        return m_target_string;
    }

    void DFSContext::set_end_vertex(VertexID v) {
        m_end_vertex = v;
    }

    VertexID DFSContext::get_end_vertex() const {
        return m_end_vertex;
    }

    void DFSContext::set_base_prefix(const expr_ref& p) {
        m_base_prefix = p;
    }

    expr_ref DFSContext::get_base_prefix() const {
        return m_base_prefix;
    }

    void DFSContext::set_base_suffix(const expr_ref& s) {
        m_base_suffix = s;
    }

    expr_ref DFSContext::get_base_suffix() const {
        return m_base_suffix;
    }

    bool DFSContext::has_group(GroupID gid) const {
        return m_group_vars.contains(gid);
    }

    bool DFSContext::is_group_active(GroupID gid) const {
        return std::ranges::find(m_active_groups, gid) != m_active_groups.end();
    }

    std::unordered_map<GroupID, expr_ref_vector> DFSContext::get_closed_group_vars() const {
        std::unordered_map<GroupID, expr_ref_vector> closed_group_vars;
        for (const auto& [gid, vars] : m_group_vars) {
            if (!is_group_active(gid)) {
                closed_group_vars.emplace(gid, vars);
            }
        }
        return closed_group_vars;
    }

    void DFSContext::reset_groups(const std::vector<GroupID>& gids) {
        for (GroupID gid : gids) {
            auto it = m_group_vars.find(gid);
            if (it != m_group_vars.end()) {
                // Keep the previous variables of the group, so that they can be restored when backtracking
                m_reset_group_vars.emplace_back(m_manager);
                m_reset_group_vars.back().swap(it->second);
                m_group_vars.erase(it);
                m_group_vars_changes.push_back({GroupVarsChange::Kind::ERASE, gid});
            }
        }
    }

    void DFSContext::mark_iteration_start(EdgeID start_eid) {
        m_iteration_starts[start_eid] = m_current_path_vars.size();
    }

    expr_ref DFSContext::concat_iteration_vars(EdgeID start_eid) const {
        return concat_vars(m_iteration_starts.at(start_eid));
    }

    const std::vector<ActiveLookahead>& DFSContext::get_active_lookaheads() const {
        return m_active_lookaheads;
    }

    expr_ref_vector& DFSContext::get_unique_paths() {
        return m_unique_paths;
    }

    app_ref DFSContext::mk_fresh_string_var() {
        app_ref var(m_manager.mk_fresh_const("regex", m_str_sort), m_manager);
        m_all_created_vars.push_back(var);
        return var;
    }

    const app_ref_vector& DFSContext::get_all_fresh_vars() const {
        return m_all_created_vars;
    }

    app_ref DFSContext::create_edge_var() {
        app_ref edge_var = mk_fresh_string_var();
        m_current_path_vars.push_back(edge_var);
        return edge_var;
    }

    void DFSContext::push_edge_var_to_groups(const app_ref& edge_var) {
        for (GroupID gid : m_active_groups) {
            m_group_vars.at(gid).push_back(edge_var);
            m_group_vars_changes.push_back({GroupVarsChange::Kind::APPEND, gid});
        }
    }

    void DFSContext::add_path_constraint(const app_ref& constraint) {
        m_current_path_constraints.push_back(constraint);
    }

    void DFSContext::start_groups(const std::vector<GroupID>& gids) {
        for (GroupID gid : gids) {
            m_active_groups.push_back(gid);
            auto it = m_group_vars.find(gid);
            if (it != m_group_vars.end()) {
                // Keep the previous variables of the group, so that they can be restored when backtracking
                m_reset_group_vars.emplace_back(m_manager);
                m_reset_group_vars.back().swap(it->second);
                m_group_vars_changes.push_back({GroupVarsChange::Kind::RESET, gid});
            }
            else {
                m_group_vars.insert({gid, expr_ref_vector(m_manager)});
                m_group_vars_changes.push_back({GroupVarsChange::Kind::CREATE, gid});
            }
        }
    }

    void DFSContext::end_groups(const std::vector<GroupID>& gids) {
        for (GroupID gid : gids) {
            auto it = std::ranges::find(m_active_groups, gid);
            if (it != m_active_groups.end()) {
                m_active_groups.erase(it);
            }
        }
    }

    void DFSContext::push_lookahead(const RegexComponent& subregex, bool is_positive) {
        // Only a non-regular lookahead can contain backreferences
        std::unordered_map<GroupID, expr_ref_vector> closed_group_vars;
        if (std::holds_alternative<GraphFragment>(subregex)) {
            closed_group_vars = get_closed_group_vars();
        }
        m_active_lookaheads.push_back({subregex, is_positive, m_current_path_vars.size(),
                                       std::move(closed_group_vars)});
    }

    std::unordered_map<GroupID, expr_ref_vector>
    DFSContext::replace_group_vars(std::unordered_map<GroupID, expr_ref_vector> group_vars) {
        std::swap(m_group_vars, group_vars);
        return group_vars;
    }

    void DFSContext::commit_current_path(const expr_ref_vector& additional_constraints) {
        expr_ref_vector final_constraints(m_manager);

        for (expr* c : m_current_path_constraints) {
            final_constraints.push_back(c);
        }
        for (expr* c : additional_constraints) {
            final_constraints.push_back(c);
        }

        expr_ref path_string = concat_vars();
        final_constraints.push_back(m_manager.mk_eq(m_target_string, path_string));
        expr_ref_vector conjunction(m_manager);
        for (expr* c : final_constraints) {
            conjunction.push_back(c);
        }
        m_unique_paths.push_back(m_manager.mk_and(conjunction));
    }

    expr_ref DFSContext::concat_expr_vector(const expr_ref_vector& vars, const uint32_t start_idx,
                                            const uint32_t end_idx) const {
        const uint32_t actual_end = std::min(end_idx, vars.size());
        if (start_idx >= actual_end) {
            return {m_util_s.str.mk_empty(m_str_sort), m_manager};
        }
        return {m_util_s.str.mk_concat(actual_end - start_idx, vars.data() + start_idx, m_str_sort), m_manager};
    }

    expr_ref DFSContext::concat_vars(const uint32_t start_idx, const uint32_t end_idx) const {
        return concat_expr_vector(m_current_path_vars, start_idx, end_idx);
    }

    expr_ref DFSContext::concat_group_vars(GroupID gid) const {
        const auto& vars = m_group_vars.at(gid);
        return concat_expr_vector(vars, 0, vars.size());
    }

    expr_ref DFSContext::get_global_prefix() const {
        expr_ref local_prefix = concat_vars();
        expr* empty_str = m_util_s.str.mk_empty(m_str_sort);

        if (m_base_prefix.get() == empty_str) {
            return local_prefix;
        }
        if (local_prefix.get() == empty_str) {
            return m_base_prefix;
        }

        return expr_ref(m_util_s.str.mk_concat(m_base_prefix, local_prefix), m_manager);
    }

    expr_ref DFSContext::get_global_suffix(const uint32_t start_idx) const {
        expr_ref local_suffix = concat_vars(start_idx);
        expr* empty_str = m_util_s.str.mk_empty(m_str_sort);

        if (m_base_suffix.get() == empty_str) {
            return local_suffix;
        }
        if (local_suffix.get() == empty_str) {
            return m_base_suffix;
        }

        return expr_ref(m_util_s.str.mk_concat(local_suffix, m_base_suffix), m_manager);
    }

    DFSStateSnapshot DFSContext::save_snapshot() const {
        DFSStateSnapshot s;
        s.num_path_vars = m_current_path_vars.size();
        s.num_path_constraints = m_current_path_constraints.size();
        s.num_active_lookaheads = m_active_lookaheads.size();
        s.num_group_vars_changes = m_group_vars_changes.size();
        s.active_groups = m_active_groups;
        return s;
    }

    void DFSContext::restore_snapshot(const DFSStateSnapshot& s) {
        m_current_path_vars.resize(s.num_path_vars);
        m_current_path_constraints.resize(s.num_path_constraints);

        // Safely truncating active lookaheads using pop_back avoids the need for a default constructor
        // which std::variant<app_ref, GraphFragment> natively prevents from existing.
        while (m_active_lookaheads.size() > s.num_active_lookaheads) {
            m_active_lookaheads.pop_back();
        }

        m_active_groups = s.active_groups;

        // Undo the changes of the group variables made in the discarded path branch, in reverse order
        while (m_group_vars_changes.size() > s.num_group_vars_changes) {
            const GroupVarsChange& change = m_group_vars_changes.back();
            switch (change.kind) {
            case GroupVarsChange::Kind::APPEND: m_group_vars.at(change.gid).pop_back(); break;
            case GroupVarsChange::Kind::CREATE: m_group_vars.erase(change.gid); break;
            case GroupVarsChange::Kind::RESET:
                m_group_vars.at(change.gid).swap(m_reset_group_vars.back());
                m_reset_group_vars.pop_back();
                break;
            case GroupVarsChange::Kind::ERASE:
                m_group_vars.insert({change.gid, std::move(m_reset_group_vars.back())});
                m_reset_group_vars.pop_back();
                break;
            }
            m_group_vars_changes.pop_back();
        }
    }

    OuterSearchState DFSContext::suspend_for_inner_search() {
        OuterSearchState state;
        state.unique_paths = std::make_unique<expr_ref_vector>(m_manager);
        state.current_path_vars = std::make_unique<expr_ref_vector>(m_manager);
        state.current_path_constraints = std::make_unique<expr_ref_vector>(m_manager);
        state.active_groups = std::move(m_active_groups);
        state.active_lookaheads = std::move(m_active_lookaheads);
        state.end_vertex = m_end_vertex;
        state.target_string = m_target_string;

        // Safe shallow copies via Z3 ref vectors
        for (unsigned i = 0; i < m_unique_paths.size(); ++i) {
            state.unique_paths->push_back(m_unique_paths.get(i));
        }
        for (unsigned i = 0; i < m_current_path_vars.size(); ++i) {
            state.current_path_vars->push_back(m_current_path_vars.get(i));
        }
        for (unsigned i = 0; i < m_current_path_constraints.size(); ++i) {
            state.current_path_constraints->push_back(m_current_path_constraints.get(i));
        }

        for (const auto& kv : m_group_vars) {
            state.existing_group_ids.push_back(kv.first);
        }

        m_unique_paths.reset();
        m_current_path_vars.reset();
        m_current_path_constraints.reset();
        m_active_groups.clear();
        m_active_lookaheads.clear();

        return state;
    }

    void DFSContext::resume_from_inner_search(OuterSearchState& state) {
        for (auto it = m_group_vars.begin(); it != m_group_vars.end();) {
            if (std::ranges::find(state.existing_group_ids, it->first) != state.existing_group_ids.end()) {
                ++it;
            }
            else {
                it = m_group_vars.erase(it);
            }
        }

        m_unique_paths.reset();
        for (unsigned i = 0; i < state.unique_paths->size(); ++i) {
            m_unique_paths.push_back(state.unique_paths->get(i));
        }
        m_current_path_vars.reset();
        for (unsigned i = 0; i < state.current_path_vars->size(); ++i) {
            m_current_path_vars.push_back(state.current_path_vars->get(i));
        }
        m_current_path_constraints.reset();
        for (unsigned i = 0; i < state.current_path_constraints->size(); ++i) {
            m_current_path_constraints.push_back(state.current_path_constraints->get(i));
        }

        m_active_groups = std::move(state.active_groups);
        m_active_lookaheads = std::move(state.active_lookaheads);
        m_end_vertex = state.end_vertex;
        m_target_string = state.target_string;
    }

    // ============= CONSTRAINT GENERATOR =============

    expr_ref ConstraintGenerator::generate_constraints(app* target_string) {
        // Just a little sanity check that the graph is (at least somehow) constructed
        SASSERT(m_graph.start_vertex != UNKNOWN_VERTEX);

        // A graph consisting of a single path of match edges is regular --> the target string just has to belong to the
        // regex of the whole path and no fresh variables are needed (the caller then adds a ground axiom instead of a
        // quantified one)
        const app_ref regular_regex = get_regular_path_regex();
        if (regular_regex) {
            m_fresh_vars.reset();
            return {m_util_s.re.mk_in_re(target_string, regular_regex), m_manager};
        }

        // Store the global target string in the context for access in nested DFS calls when evaluating anchors and
        // lookaheads
        m_global_target_string = target_string;

        // Initialize the base DFS context and start the traversal
        DFSContext ctx {m_manager, m_util_s};
        ctx.set_target(target_string);
        ctx.set_base_prefix(expr_ref(m_util_s.str.mk_empty(m_str_sort), m_manager));
        ctx.set_base_suffix(expr_ref(m_util_s.str.mk_empty(m_str_sort), m_manager));
        ctx.set_end_vertex(m_graph.end_vertex);
        rcg_dfs_visit(m_graph.start_vertex, ctx);

        // OR all the paths that were generated along the graph traversal
        expr_ref_vector& unique_paths = ctx.get_unique_paths();
        expr_ref result(m_manager);
        if (unique_paths.empty()) {
            result = {m_manager.mk_false(), m_manager};
        }
        else if (unique_paths.size() == 1) {
            SASSERT(is_expr(unique_paths.get(0)));
            result = {unique_paths.get(0), m_manager};
        }
        else {
            result = {m_manager.mk_or(unique_paths), m_manager};
        }

        // Snapshot the fresh Skolem variables for the caller (used to build the existentially quantified form
        // for the negative implication -- see handle_from_regex in theory_str_noodler.cpp).
        m_fresh_vars.reset();
        for (unsigned i = 0; i < ctx.get_all_fresh_vars().size(); i++) {
            m_fresh_vars.push_back(ctx.get_all_fresh_vars().get(i));
        }

        return result;
    }

    const app_ref_vector& ConstraintGenerator::get_fresh_vars() const {
        return m_fresh_vars;
    }

    app_ref ConstraintGenerator::get_regular_path_regex() {
        std::vector<app*> regexes;
        VertexID current_vertex = m_graph.start_vertex;
        while (current_vertex != m_graph.end_vertex) {
            const std::vector<EdgeID>& outgoing_edges = m_graph.vertices[current_vertex].outgoing_edges;
            if (outgoing_edges.size() != 1) {
                return app_ref(m_manager);
            }
            const RCGEdge& edge = m_graph.edges[outgoing_edges[0]];
            if (!std::holds_alternative<MatchEdge>(edge.payload)) {
                return app_ref(m_manager);
            }
            regexes.push_back(std::get<MatchEdge>(edge.payload).regex);
            current_vertex = edge.target;
        }

        if (regexes.empty()) {
            return {m_util_s.re.mk_epsilon(m_str_sort), m_manager};
        }
        app_ref result(regexes.back(), m_manager);
        for (size_t i = regexes.size() - 1; i > 0; i--) {
            result = m_util_s.re.mk_concat(regexes[i - 1], result);
        }
        return result;
    }

    expr_ref ConstraintGenerator::run_inner_rcg_dfs(const GraphFragment& fragment, app* target_string,
                                                    DFSContext& ctx) {
        // Suspend the outer DFS context and save the state before proceeding with the inner DFS run
        auto suspended_state = ctx.suspend_for_inner_search();

        ctx.set_end_vertex(fragment.v_out);
        ctx.set_target(target_string);

        // Run the DFS
        rcg_dfs_visit(fragment.v_in, ctx);

        // Disjunct all the paths from the subgraph and add it to the current path constraints
        expr_ref inner_result(m_manager);
        auto& unique_paths = ctx.get_unique_paths();
        if (unique_paths.empty()) {
            inner_result = {m_manager.mk_false(), m_manager};
        }
        else if (unique_paths.size() == 1) {
            inner_result = {unique_paths.get(0), m_manager};
        }
        else {
            inner_result = {m_manager.mk_or(unique_paths), m_manager};
        }

        ctx.resume_from_inner_search(suspended_state);
        return inner_result;
    }

    void ConstraintGenerator::handle_lookaround_constraints(DFSContext& ctx, const AssertionEdge& assertion) {
        const auto& lookaround = std::get<LookaroundAssertion>(assertion.payload);

        if (lookaround.direction == LookaroundDirection::FORWARD) {
            // Lookaheads are postponed and evaluated at the end of each path in the graph because they depend on the
            // suffix of the matched string starting from current position.
            ctx.push_lookahead(lookaround.subregex, lookaround.is_positive);
        }
        else {
            // Lookbehinds are evaluated immediately since they depend on the prefix of the matched string up until the
            // current position (i.e., all the string variables preceding the current position).
            const expr_ref global_prefix = ctx.get_global_prefix();

            // Lookbehinds with regular subregexes are handled via automata operations
            if (std::holds_alternative<app_ref>(lookaround.subregex)) {
                // Create x = global_prefix (p1p2p3...)
                const app_ref lb_var(ctx.mk_fresh_string_var(), m_manager);
                ctx.add_path_constraint({m_manager.mk_eq(lb_var, global_prefix), m_manager});

                // The global prefix should end with a string that matches the lookbehind subregex, therefore generate
                // global_prefix \in (Sigma* concat lb.subregex)
                const app_ref& lb_regex_base = std::get<app_ref>(lookaround.subregex);
                const app_ref sigma_star = {m_util_s.re.mk_full_seq(nullptr), m_manager};
                app_ref lb_regex = {m_util_s.re.mk_concat(sigma_star, lb_regex_base), m_manager};
                if (!lookaround.is_positive) {
                    // negative regular lookbehind --> just complement the final lokbehind subregex
                    lb_regex = m_util_s.re.mk_complement(lb_regex);
                }
                const app_ref condition = {m_util_s.re.mk_in_re(lb_var, lb_regex), m_manager};
                ctx.add_path_constraint(condition);
            }
            else {
                // Non-regular lookbehind --> need to run a nested DFS to evaluate the inner graph fragment and generate
                // the corresponding constraints.
                if (!lookaround.is_positive) {
                    // Negative lookbehind with non-regular subregex leads to universal quantification
                    util::throw_error("Unsupported: negative lookbehind with non-regular subregex");
                }

                // Introduce a fresh variable x_lb for the subregex in lookbehind
                const GraphFragment& subregex_fragment = std::get<GraphFragment>(lookaround.subregex);
                const app_ref subregex_lb_var(ctx.mk_fresh_string_var(), m_manager);
                ctx.add_path_constraint({m_manager.mk_eq(global_prefix, subregex_lb_var), m_manager});

                // The lookbehind evaluates the subregex against the entire prefix --> the procedure starts from the
                // beginning of matched string, therefore the prefix is "".
                expr_ref old_base = ctx.get_base_prefix();
                ctx.set_base_prefix(expr_ref(m_util_s.str.mk_empty(m_str_sort), m_manager));

                // The inner target ends at the lookbehind position, but a lookahead inside the lookbehind sees the rest
                // of the whole string --> introduce x_rest such that target = global_prefix ++ x_rest.
                expr_ref old_suffix = ctx.get_base_suffix();
                if (lookaround.contains_lookahead) {
                    const app_ref rest_var(ctx.mk_fresh_string_var(), m_manager);
                    const expr_ref prefix_and_rest(m_util_s.str.mk_concat(global_prefix, rest_var), m_manager);
                    ctx.add_path_constraint({m_manager.mk_eq(m_global_target_string, prefix_and_rest), m_manager});
                    ctx.set_base_suffix(expr_ref(rest_var, m_manager));
                }

                // The subregex lookbehind is evaluated in a separate run of DFS on the subgraph.
                // We hand over x_lb which is the new global target for the inner DFS
                // run. The constraints for x_lb are generated in the same way.
                // Backreferences inside the lookbehind refer to the groups closed at the lookbehind position.
                std::unordered_map<GroupID, expr_ref_vector> outer_group_vars =
                    ctx.replace_group_vars(ctx.get_closed_group_vars());
                const expr_ref inner_result = run_inner_rcg_dfs(subregex_fragment, subregex_lb_var, ctx);
                ctx.replace_group_vars(std::move(outer_group_vars));

                // Restore the original base prefix and suffix for the outer DFS run and add the generated constraints
                // for the lookbehind.
                ctx.set_base_prefix(old_base);
                ctx.set_base_suffix(old_suffix);
                ctx.add_path_constraint({to_app(inner_result.get()), m_manager});
            }
        }
    }

    void ConstraintGenerator::generate_lookahead_constraints(DFSContext& ctx, expr_ref_vector& final_constraints) {
        for (const ActiveLookahead& la : ctx.get_active_lookaheads()) {
            expr_ref suffix = ctx.get_global_suffix(la.start_index);

            if (std::holds_alternative<app_ref>(la.subregex)) {
                app_ref la_var(ctx.mk_fresh_string_var(), m_manager);
                final_constraints.push_back(m_manager.mk_eq(la_var, suffix));
                const app_ref& la_regex_base = std::get<app_ref>(la.subregex);
                const app_ref sigma_star = {m_util_s.re.mk_full_seq(nullptr), m_manager};
                app_ref la_regex = {m_util_s.re.mk_concat(la_regex_base, sigma_star), m_manager};
                if (!la.is_positive) {
                    la_regex = m_util_s.re.mk_complement(la_regex);
                }
                const app_ref condition = {m_util_s.re.mk_in_re(la_var, la_regex), m_manager};
                final_constraints.push_back(condition);
            }
            else {
                SASSERT(std::holds_alternative<GraphFragment>(la.subregex));
                if (!la.is_positive) {
                    util::throw_error("Unsupported: negative lookaround with non-regular inner content "
                                      "(would require universal quantifiers)");
                }

                const GraphFragment& inner_frag = std::get<GraphFragment>(la.subregex);
                app_ref subregex_la_var(ctx.mk_fresh_string_var(), m_manager);
                final_constraints.push_back(m_manager.mk_eq(suffix, subregex_la_var));

                // The nested graph must inherently know its specific global position relative to the target string
                expr_ref old_base = ctx.get_base_prefix();
                expr_ref local_prefix_to_la = ctx.concat_vars(0, la.start_index);
                ctx.set_base_prefix(expr_ref(m_util_s.str.mk_concat(old_base, local_prefix_to_la), m_manager));
                // The inner target already reaches the end of the whole string
                expr_ref old_suffix = ctx.get_base_suffix();
                ctx.set_base_suffix(expr_ref(m_util_s.str.mk_empty(m_str_sort), m_manager));

                // Backreferences inside the lookahead refer to the captures at the lookahead position
                std::unordered_map<GroupID, expr_ref_vector> path_end_group_vars =
                    ctx.replace_group_vars(la.group_vars);
                expr_ref inner_result = run_inner_rcg_dfs(inner_frag, subregex_la_var, ctx);
                ctx.replace_group_vars(std::move(path_end_group_vars));

                ctx.set_base_prefix(old_base);
                ctx.set_base_suffix(old_suffix);
                final_constraints.push_back(inner_result);
            }
        }
    }

    void ConstraintGenerator::generate_assertion_constraints(DFSContext& ctx, const AssertionEdge& assertion) {
        if (std::holds_alternative<Anchor>(assertion.payload)) {
            // Get all the string variables preceding the current position, since anchors are dependent on the absolute
            // position in the text.
            const expr_ref global_prefix = ctx.get_global_prefix();
            // The start of the text means 'nothing is matched before this position' --> global prefix must be empty
            if (std::get<Anchor>(assertion.payload) == Anchor::START_OF_TEXT) {
                ctx.add_path_constraint({m_manager.mk_eq(global_prefix, m_util_s.str.mk_empty(m_str_sort)), m_manager});
            }
            // The end of the text means 'nothing is matched after this position' --> global prefix must be equal to
            // the entire target string
            else {
                ctx.add_path_constraint({m_manager.mk_eq(global_prefix, app_ref(m_global_target_string, m_manager)),
                                         m_manager});
            }
        }
        else if (std::holds_alternative<LookaroundAssertion>(assertion.payload)) {
            handle_lookaround_constraints(ctx, assertion);
        }
        else {
            util::throw_error("Internal error: ConstraintGenerator::generate_assertion_constraints: Assertion is "
                              "neither Anchor nor Lookaround");
        }
    }

    void ConstraintGenerator::generate_edge_constraints(DFSContext& ctx, const RCGEdge& edge, const app_ref& edge_var) {
        // The edge contains regular payload --> generate str.in_re(edge_var, payload)
        if (std::holds_alternative<MatchEdge>(edge.payload)) {
            const app_ref regex = std::get<MatchEdge>(edge.payload).regex;
            ctx.add_path_constraint({m_util_s.re.mk_in_re(edge_var, regex), m_manager});
        }
        // Backreference --> edge_var must be equal to the concatenation of all variables in the referenced group on the
        // current path. If the referenced group has not been captured yet (forward reference), is still open
        // (backreference inside its own group) or its capture was reset, its capture is undefined -- the backreference
        // either matches empty string or fails.
        // https://tc39.es/ecma262/2020/#sec-backreferencematcher -- "e. If `s` is undefined, return c(x)."
        else if (std::holds_alternative<BackrefEdge>(edge.payload)) {
            const BackrefEdge& backref = std::get<BackrefEdge>(edge.payload);
            const GroupID ref_id = backref.backref_id;

            if (ctx.has_group(ref_id) && !ctx.is_group_active(ref_id)) {
                // Backreference -- concatenate all the variables accumulated in the capture group during the current
                // path.
                expr_ref captured_string = ctx.concat_group_vars(ref_id);
                ctx.add_path_constraint({m_manager.mk_eq(edge_var, captured_string), m_manager});
            }
            else if (backref.unset_matches_empty) {
                // Forward reference or backreference inside its own group
                ctx.add_path_constraint({m_manager.mk_eq(edge_var, m_util_s.str.mk_empty(m_str_sort)), m_manager});
            }
            else {
                // The backreference fails, the current path cannot match
                ctx.add_path_constraint({m_manager.mk_false(), m_manager});
            }
        }
        else {
            util::throw_error("Internal error: ConstraintGenerator::generate_edge_constraints: edge payload is "
                              "neither BackrefEdge nor MatchEdge");
        }
    }

    void ConstraintGenerator::generate_nonempty_iteration_constraint(DFSContext& ctx, const EdgeID start_eid) {
        const expr_ref iteration_string = ctx.concat_iteration_vars(start_eid);
        const app_ref is_empty(m_manager.mk_eq(iteration_string, m_util_s.str.mk_empty(m_str_sort)), m_manager);
        ctx.add_path_constraint({m_manager.mk_not(is_empty), m_manager});
    }

    void ConstraintGenerator::rcg_dfs_visit(const VertexID current_vertex, DFSContext& ctx) {
        // End of (sub)graph reached --> evaluate postponed lookaheads and commit current path
        if (current_vertex == ctx.get_end_vertex()) {
            expr_ref_vector final_constraints(m_manager);
            generate_lookahead_constraints(ctx, final_constraints);
            ctx.commit_current_path(final_constraints);
            return;
        }

        for (EdgeID eid : m_graph.vertices[current_vertex].outgoing_edges) {
            // Before continuing, save a snapshot of the previous edge in case of alternation
            const RCGEdge& edge = m_graph.edges[eid];
            DFSStateSnapshot snapshot = ctx.save_snapshot();

            // Start of a quantifier iteration -- reset the captures inside the quantified subpattern
            if (m_graph.group_resets.contains(eid)) {
                ctx.reset_groups(m_graph.group_resets.at(eid));
                ctx.mark_iteration_start(eid);
            }

            // Mark all groups that begin on this edge as active
            if (m_graph.group_starts.contains(eid)) {
                ctx.start_groups(m_graph.group_starts.at(eid));
            }

            // Zero-width assertions consume no text and marker edges only carry bookkeeping, therefore no variable is
            // created for them. Other edges get a fresh variable (which is added to all the active capture groups) and
            // constraints for the current edge.
            if (std::holds_alternative<AssertionEdge>(edge.payload)) {
                generate_assertion_constraints(ctx, std::get<AssertionEdge>(edge.payload));
            }
            else if (!std::holds_alternative<MarkerEdge>(edge.payload)) {
                app_ref edge_var = ctx.create_edge_var();
                ctx.push_edge_var_to_groups(edge_var);
                generate_edge_constraints(ctx, edge, edge_var);
            }

            // End of a quantifier iteration beyond the minimum -- it must not match the empty string
            if (m_graph.nonempty_iterations.contains(eid)) {
                generate_nonempty_iteration_constraint(ctx, m_graph.nonempty_iterations.at(eid));
            }

            // Mark all groups that end on this edge as inactive
            if (m_graph.group_ends.contains(eid)) {
                ctx.end_groups(m_graph.group_ends.at(eid));
            }

            // Continue DFS on the next edge, rollback to the snapshot after exploring the branch
            rcg_dfs_visit(edge.target, ctx);
            ctx.restore_snapshot(snapshot);
        }
    }

}  // namespace smt::noodler::extended_regex
