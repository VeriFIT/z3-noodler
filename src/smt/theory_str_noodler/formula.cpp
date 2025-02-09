#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"

#include "formula.h"
#include "util.h"


namespace smt::noodler {
    void collect_free_vars_rec(const LenNode& root, std::set<BasicTerm>& free_vars, std::set<BasicTerm>& quantified_vars) {
        switch (root.type) {
            case LenFormulaType::TRUE:
            case LenFormulaType::FALSE:
                return;
            case LenFormulaType::LEAF: {
                if (root.atom_val.is_variable()) {
                    const BasicTerm& var = root.atom_val;
                    if (!quantified_vars.contains(var)) {
                        free_vars.insert(var);
                    }
                }
                return;
            }
            case LenFormulaType::NOT:
                collect_free_vars_rec(root.succ.at(0), free_vars, quantified_vars);
                return;
            case LenFormulaType::LEQ:
            case LenFormulaType::LT:
            case LenFormulaType::EQ:
            case LenFormulaType::NEQ:
                collect_free_vars_rec(root.succ.at(0), free_vars, quantified_vars);
                collect_free_vars_rec(root.succ.at(1), free_vars, quantified_vars);
                return;
            case LenFormulaType::PLUS:
            case LenFormulaType::MINUS:
            case LenFormulaType::TIMES:
            case LenFormulaType::AND:
            case LenFormulaType::OR: {
                for (const auto& child : root.succ) {
                    collect_free_vars_rec(child, free_vars, quantified_vars);
                }
                return;
            }
            case LenFormulaType::FORALL:
            case LenFormulaType::EXISTS: {
                auto children_iterator = root.succ.begin();
                const LenNode& quantified_var_node = *children_iterator;
                const BasicTerm quantified_var = quantified_var_node.atom_val;
                children_iterator++;

                auto [target_bucket, did_emplace_happen] = quantified_vars.emplace(quantified_var);
                assert (did_emplace_happen);  // We want all quantified vars to be unique, at least for now

                for (; children_iterator != root.succ.end(); children_iterator++) {
                    collect_free_vars_rec(*children_iterator, free_vars, quantified_vars);
                }

                quantified_vars.erase(quantified_var);

                return;
            }
            default:
                UNREACHABLE();
        }
    }

    LenNodePrecision get_resulting_precision_for_conjunction(const LenNodePrecision& p0, const LenNodePrecision& p1) {
        if ((p0 == LenNodePrecision::UNDERAPPROX && p1 == LenNodePrecision::OVERAPPROX) || (p0 == LenNodePrecision::OVERAPPROX && p1 == LenNodePrecision::UNDERAPPROX)) {
            // We have that one is UNDERAPPROXIMATION and the other one is OVERAPPROXIMATION
            // For example, we have `not-contains(x, y) AND x != z` where we
            // p0=underapproximate not-contains to {b, c} whereas its real solutions are {a, b, c}
            // p1=overapproximate disequation to {a, b, c, d, e} whereas its real solutions are {a, c, d}
            // The resulting conjuction will have models {b, c}, but in reality it should have {a, c} ---- we cannot claim anything and we throw an error
            throw std::runtime_error("Attempting to compute precision of a conjunction of an underapproximation an an overapproximation - impossible.");
        }

        if (p0 == LenNodePrecision::PRECISE) {
            // if p1 == underapprox, result is also underapprox
            // if p1 == precise, result is also precise
            // if p1 == overapproximation, result is also an overapproximation
            // ---> just return p1
            return p1;
        }

        if (p0 == LenNodePrecision::OVERAPPROX) {
            // if p1 == precise    --> return overapprox
            // if p1 == overapprox --> return overapprox
            // p1 == underapprox is illegal - error should be thrown above
            return LenNodePrecision::OVERAPPROX;
        }

        // if (p0 == LenNodePrecision::UNDERAPPROX) {
            // if p1 == precise     --> return underapprox
            // if p1 == underapprox --> return underapprox
            // p1 == overapprox is illegal - error should be thrown above
        //}

        return LenNodePrecision::UNDERAPPROX; // See above
    }

    LenNode substitute_free_vars_for_int_values_rec(const LenNode& node, const std::map<BasicTerm, int>& substitution) {
        switch (node.type) {
            case LenFormulaType::TRUE:
            case LenFormulaType::FALSE:
                return node;
            case LenFormulaType::LEAF: {
                if (node.atom_val.is_variable()) {
                    BasicTerm needle_var(BasicTermType::Variable, node.atom_val.get_name());
                    auto value_to_substitute_it = substitution.find(needle_var);
                    if (value_to_substitute_it == substitution.end()) {
                        return node;
                    }

                    return LenNode(value_to_substitute_it->second);
                }
                return node;
            }
            case LenFormulaType::NOT:
                return substitute_free_vars_for_int_values_rec(node.succ.at(0), substitution);
            case LenFormulaType::LEQ:
            case LenFormulaType::LT:
            case LenFormulaType::EQ:
            case LenFormulaType::NEQ:
            case LenFormulaType::MINUS:
            case LenFormulaType::TIMES:
            case LenFormulaType::AND:
            case LenFormulaType::OR:
            case LenFormulaType::PLUS: {
                std::vector<LenNode> modified_children;
                modified_children.reserve(node.succ.size());

                for (auto& child : node.succ) {
                    LenNode new_child = substitute_free_vars_for_int_values_rec(child, substitution);
                    modified_children.push_back(new_child);
                }

                return LenNode(node.type, modified_children);
            }
            case LenFormulaType::FORALL:
            case LenFormulaType::EXISTS: {
                // node.succ[0] contains variables bound by this quantifier
                LenNode new_child = substitute_free_vars_for_int_values_rec(node.succ.at(1), substitution);
                return LenNode(node.type, {node.succ.at(0), new_child});
            }
            default:
                UNREACHABLE();
        }

        return LenNode(0);
    }

    LenNode substitute_free_vars_for_concrete_values(const LenNode& formula, const std::map<BasicTerm, int> substitution) {
        return substitute_free_vars_for_int_values_rec(formula, substitution);
    }

    std::set<BasicTerm> collect_free_vars(const LenNode& len_node) {
        std::set<BasicTerm> free_vars;
        std::set<BasicTerm> quantified_vars;

        collect_free_vars_rec(len_node, free_vars, quantified_vars);

        return free_vars;
    }

    void write_len_formula_as_smt2(const LenNode& formula, std::ostream& out_stream) {
        out_stream << "(set-logic LIA)" << std::endl;

        std::set<BasicTerm> free_vars = collect_free_vars(formula);

        for (const BasicTerm& free_var : free_vars) {
            out_stream << "(declare-fun " << free_var << "() Int)" << std::endl;
        }
        out_stream << "(assert " << std::endl;
        out_stream << formula;
        out_stream << ")" << std::endl;
        out_stream << "(check-sat)" << std::endl;
        out_stream << "(exit)" << std::endl;
    }

    std::set<BasicTerm> Predicate::get_vars() const {
        std::set<BasicTerm> vars;
        for (const auto& side: params) {
            for (const auto &term: side) {
                if (term.is_variable()) {
                    vars.insert(term);
                }
            }
        }
        return vars;
    }

    std::set<BasicTerm> Predicate::get_side_vars(const Predicate::EquationSideType side) const {
        assert(is_eq_or_ineq());
        std::set<BasicTerm> vars;
        std::vector<BasicTerm> side_terms;
        switch (side) {
            case EquationSideType::Left:
                side_terms = get_left_side();
                break;
            case EquationSideType::Right:
                side_terms = get_right_side();
                break;
            default:
                throw std::runtime_error("unhandled equation side_terms type");
                break;
        }

        for (const auto &term: side_terms) {
            if (term.is_variable()) {
                bool found{false};
                for (const auto &var: vars) {
                    if (var == term) {
                        found = true;
                        break;
                    }
                }
                if (!found) { vars.insert(term); }
            }
        }
        return vars;
    }

    bool Predicate::mult_occurr_var_side(const Predicate::EquationSideType side) const {
        assert(is_eq_or_ineq());
        const auto terms_begin{ get_side(side).cbegin() };
        const auto terms_end{ get_side(side).cend() };
        for (auto term_iter{ terms_begin }; term_iter < terms_end; ++term_iter) {
            if (term_iter->is_variable()) {
                for (auto term_iter_following{ term_iter + 1}; term_iter_following < terms_end;
                     ++term_iter_following) {
                    if (*term_iter == *term_iter_following) {
                        return true;
                        // TODO: How to handle calls of predicates?
                    }
                }
            }
        }
        return false;
    }

    Predicate Predicate::split_literals() const {
        const auto& split_concat = [&](const std::vector<BasicTerm>& con) {
            std::vector<BasicTerm> ret;
            for(const BasicTerm& bt : con) {
                if(bt.is_literal()) {
                    zstring name = bt.get_name();
                    for(size_t i = 0; i < name.length(); ++i) {
                        ret.emplace_back(BasicTerm(BasicTermType::Literal, zstring(name[i])));
                    }
                } else {
                    ret.push_back(bt);
                }
            }
            return ret;
        };

        std::vector<std::vector<BasicTerm>> new_pars;
        for(const auto& par : this->params) {
            new_pars.push_back(split_concat(par));
        }
        return Predicate(this->get_type(), new_pars);
    }

    std::string Predicate::to_string() const {

        // joining BasicTerm in the given vector with str
        auto join = [&](const std::vector<BasicTerm>& vec, const std::string& str) -> std::string {
            if(vec.empty()) return "";
            std::string ret = vec[0].to_string();
            for(size_t i = 1; i < vec.size(); i++) {
                ret += str + vec[i].to_string();
            }
            return ret;
        };

        switch (type) {
            case PredicateType::Equation: {
                std::string result{ "Equation:" };
                result += join(get_left_side(), " ") + " = " + join(get_right_side(), " ");
                return result;
            }

            case PredicateType::Inequation: {
                std::string result{ "Inequation:" };
                result += join(get_left_side(), " ") + " != " + join(get_right_side(), " ");
                return result;
            }

            case PredicateType::NotContains: {
                std::string result{ "Notcontains " };
                result += join(params[0], " ") + " , " + join(params[1], " ");
                return result;
            }

            case PredicateType::Transducer: {
                std::string result{ "Transducer " };
                result += join(params[0], " ") + " , " + join(params[1], " ");
                return result;
            }

            case PredicateType::ReplaceAll: {
                std::string result{ "ReplaceAll " };
                result += join(params[0], " ") + " = replace_all( " + join(params[1], " ") + ", " + join(params[2], " ") + ", " + join(params[3], " ") + ")";
                return result;
            }

            case PredicateType::ReplaceREAll: {
                std::string result{ "ReplaceREAll " };
                result += join(params[0], " ") + " = replace_re_all( " + join(params[1], " ") + ", " + join(params[2], " ") + ", " + join(params[3], " ") + ")";
                return result;
            }
        }

        throw std::runtime_error("Unhandled predicate type passed as 'this' to to_string().");
    }

    bool Predicate::equals(const Predicate &other) const {
        if (type == other.type) {
            if (is_two_sided()) {
                return params[0] == other.params[0] && params[1] == other.params[1];
            }
            return params == other.params;
        }
        return false;
    }

    const std::vector<BasicTerm> &Predicate::get_side(const Predicate::EquationSideType side) const {
        assert(is_eq_or_ineq());
        switch (side) {
            case EquationSideType::Left:
                return params[0];
                break;
            case EquationSideType::Right:
                return params[1];
                break;
            default:
                throw std::runtime_error("unhandled equation side type");
                break;
        }
    }

    std::vector<BasicTerm> &Predicate::get_side(const Predicate::EquationSideType side) {
        assert(is_eq_or_ineq());
        switch (side) {
            case EquationSideType::Left:
                return params[0];
                break;
            case EquationSideType::Right:
                return params[1];
                break;
            default:
                throw std::runtime_error("unhandled equation side type");
                break;
        }
    }

    std::map<BasicTerm, unsigned> Predicate::variable_count(const Predicate::EquationSideType side) const {
        std::map<BasicTerm, unsigned> occurr;
        BasicTerm litTerm(BasicTermType::Literal, "");
        unsigned lits = 0;
        for(const BasicTerm& b : this->get_side(side)) {
            if(b.is_variable()) {
                occurr[b]++;
            } else {
                lits += b.get_name().length();
            }
        }
        occurr[litTerm] = lits;
        return occurr;
    }

    std::string BasicTerm::to_string() const {
        switch (type) {
            case BasicTermType::Literal: {
                return ("\"" + name.encode() + "\"");
            }
            case BasicTermType::Variable:
                return name.encode();
            case BasicTermType::Length:
                return name.encode() + " (" + noodler::to_string(type) + ")";
                // TODO: Decide what will have names and when to use them.
        }

        throw std::runtime_error("Unhandled basic term type passed as 'this' to to_string().");
    }

    expr_ref construct_z3_expr_for_len_node_quantifier(LenFormulaContext& ctx, const LenNode& node, enum quantifier_kind quantif_kind) {
        // add existentially  quantified variable to the map (if not present)
        std::string quantif_var_name = node.succ[0].atom_val.get_name().encode();

        int this_quantifier_depth = ctx.current_quantif_depth;
        ctx.current_quantif_depth += 1;

        auto [dest_bucket_it, did_emplace_happen] = ctx.quantified_vars.emplace(quantif_var_name, this_quantifier_depth);

        // occurrences of the quantifier variable are created as z3 variable, not skolem constant
        expr_ref bodyref = convert_len_node_to_z3_formula(ctx, node.succ[1]);

        ctx.current_quantif_depth -= 1; // Reset it back

        // @Optimize(mhecko): Is this iterator invalidated at this point? Probably.
        auto this_quantif_bucket_it = ctx.quantified_vars.find(quantif_var_name);
        ctx.quantified_vars.erase(this_quantif_bucket_it);

        ptr_vector<sort> sorts;
        svector<symbol> names;
        sorts.push_back(ctx.arith_utilities.mk_int());
        names.push_back(symbol(dest_bucket_it->second));

        expr_ref z3_quantif(ctx.manager.mk_quantifier(quantif_kind, sorts.size(), sorts.data(), names.data(), bodyref, 1), ctx.manager);
        return z3_quantif;
    }

    expr_ref constr_z3_expr_for_leaf(LenFormulaContext& ctx, const LenNode& node) {
        if (node.atom_val.get_type() == BasicTermType::Length) {
            return expr_ref(ctx.arith_utilities.mk_int(rational(node.atom_val.get_name().encode().c_str())), ctx.manager);
        }

        if (node.atom_val.get_type() == BasicTermType::Literal) {
            // for literal, get its exact length
            return expr_ref(ctx.arith_utilities.mk_int(node.atom_val.get_name().length()), ctx.manager);
        }

        //
        // Leaf contains a variable
        //

        // Check whether we already have a z3 expr for this variable. Expressions for quantified variables
        // cannot be cached as they variable.id is dynamic.
        auto known_expr_it = ctx.known_z3_exprs.find(node.atom_val);
        if (known_expr_it != ctx.known_z3_exprs.end()) {  // We have a know/cached z3_expr
            expr_ref expr = known_expr_it->second;

            if (ctx.seq_utilities.is_string(expr.get()->get_sort())) {
                // for string variables we want its length
                return expr_ref(ctx.seq_utilities.str.mk_length(expr), ctx.manager);
            }

            // we assume here that all other variables are int, so they map into the predicate they represent
            return expr;
        }

        std::string var_name = node.atom_val.get_name().encode();
        auto it = ctx.quantified_vars.find(var_name);
        bool is_quantified = (it != ctx.quantified_vars.end());

        if (is_quantified) {
            int quantifier_node_height = it->second;
            int de_brujin_index = ctx.current_quantif_depth - (quantifier_node_height + 1);

            return expr_ref(ctx.manager.mk_var(de_brujin_index, ctx.arith_utilities.mk_int()), ctx.manager);
        }

        // Not quantified - needs to be skolem, because it seems they are not printed for models
        app* var = ctx.manager.mk_skolem_const(symbol(var_name.c_str()), ctx.arith_utilities.mk_int());
        return expr_ref(var, ctx.manager);
    }

    expr_ref convert_len_node_to_z3_formula(LenFormulaContext &ctx, const LenNode &node) {
        arith_util&  m_util_a = ctx.arith_utilities;
        seq_util&    m_util_s = ctx.seq_utilities;
        ast_manager& manager  = ctx.manager;

        switch(node.type) {
        case LenFormulaType::LEAF: {
            return constr_z3_expr_for_leaf(ctx, node);
        }

        case LenFormulaType::PLUS: {
            if (node.succ.size() == 0)
                return expr_ref(m_util_a.mk_int(0), manager);
            expr_ref plus = convert_len_node_to_z3_formula(ctx, node.succ[0]);
            for(size_t i = 1; i < node.succ.size(); i++) {
                plus = m_util_a.mk_add(plus, convert_len_node_to_z3_formula(ctx, node.succ[i]));
            }
            return plus;
        }

        case LenFormulaType::MINUS: {
            if (node.succ.size() == 0)
                return expr_ref(m_util_a.mk_int(0), manager);
            if (node.succ.size() == 1) {  // Unary minus (- x)
                expr_ref child_expr = convert_len_node_to_z3_formula(ctx, node.succ[0]);
                child_expr = m_util_a.mk_uminus(child_expr);
                return child_expr;
            }
            expr_ref minus = convert_len_node_to_z3_formula(ctx, node.succ[0]);
            for(size_t i = 1; i < node.succ.size(); i++) {
                minus = m_util_a.mk_sub(minus, convert_len_node_to_z3_formula(ctx, node.succ[i]));
            }
            return minus;
        }

        case LenFormulaType::TIMES: {
            if (node.succ.size() == 0)
                return expr_ref(m_util_a.mk_int(1), manager);
            expr_ref times = convert_len_node_to_z3_formula(ctx, node.succ[0]);
            for(size_t i = 1; i < node.succ.size(); i++) {
                times = m_util_a.mk_mul(times, convert_len_node_to_z3_formula(ctx, node.succ[i]));
            }
            return times;
        }

        case LenFormulaType::EQ: {
            assert(node.succ.size() == 2);
            expr_ref left = convert_len_node_to_z3_formula(ctx, node.succ[0]);
            expr_ref right = convert_len_node_to_z3_formula(ctx, node.succ[1]);

            expr_ref eq(m_util_a.mk_eq(left, right), manager);
            return eq;
        }

        case LenFormulaType::NEQ: {
            assert(node.succ.size() == 2);
            expr_ref left = convert_len_node_to_z3_formula(ctx, node.succ[0]);
            expr_ref right = convert_len_node_to_z3_formula(ctx, node.succ[1]);
            expr_ref neq(manager.mk_not(m_util_a.mk_eq(left, right)), manager);
            return neq;
        }

        case LenFormulaType::LEQ: {
            assert(node.succ.size() == 2);
            expr_ref left = convert_len_node_to_z3_formula(ctx, node.succ[0]);
            expr_ref right = convert_len_node_to_z3_formula(ctx, node.succ[1]);
            expr_ref leq(m_util_a.mk_le(left, right), manager);
            return leq;
        }

        case LenFormulaType::LT: {
            assert(node.succ.size() == 2);
            expr_ref left = convert_len_node_to_z3_formula(ctx, node.succ[0]);
            expr_ref right = convert_len_node_to_z3_formula(ctx, node.succ[1]);
            // LIA solver fails if we use "L < R" for some reason (it cannot be internalized in smt::theory_lra::imp::internalize_atom, as it expects only <= or >=); we use "!(R <= L)" instead
            expr_ref lt(manager.mk_not(m_util_a.mk_le(right, left)), manager);
            return lt;
        }

        case LenFormulaType::NOT: {
            assert(node.succ.size() == 1);
            expr_ref no(manager.mk_not(convert_len_node_to_z3_formula(ctx, node.succ[0])), manager);
            return no;
        }

        case LenFormulaType::AND: {
            if(node.succ.size() == 0)
                return expr_ref(manager.mk_true(), manager);
            expr_ref andref = convert_len_node_to_z3_formula(ctx, node.succ[0]);
            for(size_t i = 1; i < node.succ.size(); i++) {
                andref = manager.mk_and(andref, convert_len_node_to_z3_formula(ctx, node.succ[i]));
            }
            return andref;
        }

        case LenFormulaType::OR: {
            if(node.succ.size() == 0)
                return expr_ref(manager.mk_false(), manager);
            expr_ref orref = convert_len_node_to_z3_formula(ctx, node.succ[0]);
            for(size_t i = 1; i < node.succ.size(); i++) {
                orref = manager.mk_or(orref, convert_len_node_to_z3_formula(ctx, node.succ[i]));
            }
            return orref;
        }

        case LenFormulaType::FORALL: {
            expr_ref forall = construct_z3_expr_for_len_node_quantifier(ctx, node, quantifier_kind::forall_k);
            return forall;
        }

        case LenFormulaType::EXISTS: {
            expr_ref exists = construct_z3_expr_for_len_node_quantifier(ctx, node, quantifier_kind::exists_k);
            return exists;
        }

        case LenFormulaType::TRUE: {
            return expr_ref(manager.mk_true(), manager);
        }

        case LenFormulaType::FALSE: {
            return expr_ref(manager.mk_false(), manager);
        }

        default:
            util::throw_error("Unexpected length formula type");
            return {{}, manager};
        }
    }
} // Namespace smt::noodler.
