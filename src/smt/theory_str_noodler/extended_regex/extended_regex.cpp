#include "extended_regex.h"

#include "ecma_regex.h"
#include "re2_regex.h"

#include "smt/theory_str_noodler/util.h"

#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"

#include <unordered_set>

namespace smt::noodler::extended_regex {
    NodeRef parse(const symbol& flavor, const zstring& pattern) {
        if (flavor == "ecma2020") {
            return ecma::ECMAParser(pattern).parse();
        }
        if (flavor == "re2") {
            return re2::RE2Parser(pattern).parse();
        }
        util::throw_error("Unsupported regex flavor " + flavor.str());
        return nullptr;
    }

    const RegexConstraintGraph& RegexConstraintBuilder::build_rcg() {
        NodeRef root = parse(m_flavor, m_pattern);

        std::unordered_set<GroupID> referenced_groups;
        collect_backrefs(*root, referenced_groups);
        strip_unreferenced_captures(root, referenced_groups);
        check_lookaround_backrefs(*root);

        m_graph = extended_regex::build_rcg(*root, m_params.m_ecma_engine_semantics, m_util_s, m_manager);
        return m_graph;
    }

    expr_ref RegexConstraintBuilder::generate_constraints(app* target_string) {
        ConstraintGenerator generator(m_manager, m_graph);
        expr_ref result = generator.generate_constraints(target_string);
        m_fresh_vars.reset();
        m_fresh_vars.append(generator.get_fresh_vars());
        return result;
    }

    const app_ref_vector& RegexConstraintBuilder::get_fresh_vars() const {
        return m_fresh_vars;
    }

    app_ref RegexConstraintBuilder::get_regular_path_regex() {
        return ConstraintGenerator(m_manager, m_graph).get_regular_path_regex();
    }

    expr_ref to_classical_regex(expr* regex, ast_manager& m, const theory_str_noodler_params& params) {
        seq_util util_s(m);
        expr_safe_replace replacer(m);
        for (expr* subterm : subterms::all(expr_ref(regex, m))) {
            if (!util_s.re.is_from_regex(subterm)) {
                continue;
            }
            symbol flavor;
            zstring pattern;
            if (!util_s.re.is_from_regex(subterm, flavor, pattern)) {
                return expr_ref(m);
            }
            RegexConstraintBuilder builder(m, flavor, pattern, params);
            builder.build_rcg();
            const app_ref classical_regex = builder.get_regular_path_regex();
            if (!classical_regex) {
                return expr_ref(m);
            }
            replacer.insert(subterm, classical_regex);
        }
        expr_ref result(m);
        replacer(regex, result);
        return result;
    }
}  // namespace smt::noodler::extended_regex
