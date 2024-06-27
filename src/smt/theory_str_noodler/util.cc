#include <cassert>

#include "util/z3_exception.h"

#include "util.h"
#include "theory_str_noodler.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"

namespace {
    using mata::nfa::Nfa;
}

namespace smt::noodler::util {

    void throw_error(std::string errMsg) {
        // TODO maybe for benchnarking throw_error in release should also really throw error
#ifndef NDEBUG
        // for debugging, we use std::runtime_error, because that one is not caught by z3
        throw std::runtime_error(errMsg);
#else
        // for release, we use this, as it is caught by z3 and it transform it into 'unknown'
        throw default_exception(std::move(errMsg));
#endif
    }

    void get_str_variables(expr* const ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<expr>& res, obj_map<expr, expr*>* pred_map) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_str_variable(ex, m_util_s)) {
            res.insert(ex);
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app{ to_app(ex) };
        if(pred_map != nullptr) {
            expr* rpl;
            if(pred_map->find(ex_app, rpl)) {
                get_str_variables(rpl, m_util_s, m, res, pred_map);
            }
        }

        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_str_variables(arg, m_util_s, m, res, pred_map);
        }
    }

    void get_variable_names(expr* const ex, const seq_util& m_util_s, const ast_manager& m, std::unordered_set<std::string>& res) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_variable(ex)) {
            res.insert(std::to_string(to_app(ex)->get_name()));
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app{ to_app(ex) };

        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_variable_names(arg, m_util_s, m, res);
        }
    }

    bool is_variable(const expr* expression) {
        if (!is_app(expression)) {
            return false;
        }
        const app *n = to_app(expression);
        return n->get_num_args() == 0 && n->get_family_id() == null_family_id && n->get_decl_kind() == null_decl_kind;
    }

    bool is_str_variable(const expr* expression, const seq_util& m_util_s) {
        return m_util_s.is_string(expression->get_sort()) && is_variable(expression);
    }

    std::set<uint32_t> get_dummy_symbols(size_t new_symb_num, std::set<uint32_t>& symbols_to_append_to) {
        std::set<uint32_t> dummy_symbols{};
        uint32_t dummy_symbol{ 0 };
        const size_t disequations_number{ new_symb_num };
        for (size_t diseq_index{ 0 }; diseq_index < disequations_number; ++diseq_index) {
            while (symbols_to_append_to.find(dummy_symbol) != symbols_to_append_to.end()) { ++dummy_symbol; }
            dummy_symbols.insert(dummy_symbol);
            ++dummy_symbol;
        }
        [[maybe_unused]] const size_t dummy_symbols_number{ dummy_symbols.size() };
        assert(dummy_symbols_number == disequations_number);
        [[maybe_unused]] const size_t symbols_in_formula_number{ symbols_to_append_to.size() };
        symbols_to_append_to.insert(dummy_symbols.begin(), dummy_symbols.end());
        assert(dummy_symbols_number + symbols_in_formula_number == symbols_to_append_to.size());
        return dummy_symbols;
    }

    void collect_terms(app* const ex, ast_manager& m, const seq_util& m_util_s, obj_map<expr, expr*>& pred_replace,
                       std::map<BasicTerm, expr_ref>& var_name, std::vector<BasicTerm>& terms) {

        if(m_util_s.str.is_string(ex)) { // Handle string literals.
            terms.emplace_back(BasicTermType::Literal, ex->get_parameter(0).get_zstring());
            return;
        }

        if(is_variable(ex)) {
            std::string var = ex->get_decl()->get_name().str();
            BasicTerm bvar(BasicTermType::Variable, var);
            terms.emplace_back(bvar);
            var_name.insert({bvar, expr_ref(ex, m)});
            return;
        }

        if(!m_util_s.str.is_concat(ex)) {
            expr* rpl = pred_replace.find(ex); // dies if it is not found
            collect_terms(to_app(rpl), m, m_util_s, pred_replace, var_name, terms);
            return;
        }

        SASSERT(ex->get_num_args() == 2);
        app *a_x = to_app(ex->get_arg(0));
        app *a_y = to_app(ex->get_arg(1));
        collect_terms(a_x, m, m_util_s, pred_replace, var_name, terms);
        collect_terms(a_y, m, m_util_s, pred_replace, var_name, terms);
    }

    BasicTerm get_variable_basic_term(expr *const variable) {
        SASSERT(is_app(variable));
        const app* variable_app{ to_app(variable) };
        SASSERT(variable_app->get_num_args() == 0);
        return BasicTerm{ BasicTermType::Variable, variable_app->get_decl()->get_name().str() };
    }

    void get_len_exprs(app* const ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<app>& res) {
        if(m_util_s.str.is_length(ex)) {
            res.insert(ex);
            return;
        }

        for(unsigned i = 0; i < ex->get_num_args(); i++) {
            SASSERT(is_app(ex->get_arg(i)));
            app *arg = to_app(ex->get_arg(i));
            get_len_exprs(arg, m_util_s, m, res);
        }
    }

    bool is_len_sub(expr* val, expr* s, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& num_res) {
        expr* num = nullptr;
        expr* len = nullptr;
        expr* str = nullptr;
        if(!m_util_a.is_add(val, num, len)) {
            return false;
        }

        if(!m_util_a.is_int(num)) {
            return false;
        }
        num_res = num;

        if(!m_util_s.str.is_length(len, str) || str->hash() != s->hash()) {
            return false;
        } 
        
        return true;
    }

    expr_ref len_to_expr(const LenNode &node, const std::map<BasicTerm, expr_ref>& variable_map, ast_manager &m, seq_util& m_util_s, arith_util& m_util_a) {
        switch(node.type) {
        case LenFormulaType::LEAF:
            if(node.atom_val.get_type() == BasicTermType::Length)
                return expr_ref(m_util_a.mk_int(rational(node.atom_val.get_name().encode().c_str())), m);
            else if (node.atom_val.get_type() == BasicTermType::Literal) {
                // for literal, get the exact length of it
                return expr_ref(m_util_a.mk_int(node.atom_val.get_name().length()), m);
            } else {
                auto it = variable_map.find(node.atom_val);
                expr_ref var_expr(m);
                if(it == variable_map.end()) {
                    // if the variable is not found, it was introduced in the preprocessing/decision procedure
                    // (either as a string or int var), i.e. we can just create a new z3 variable with the same name 
                    var_expr = mk_int_var(node.atom_val.get_name().encode(), m, m_util_a);
                } else {
                    if (m_util_s.is_string(it->second.get()->get_sort())) {
                        // for string variables we want its length
                        var_expr = expr_ref(m_util_s.str.mk_length(it->second), m);
                    } else {
                        // we assume here that all other variables are int, so they map into the predicate they represent 
                        var_expr = it->second;
                    }
                }
                return var_expr;
            }

        case LenFormulaType::PLUS: {
            if (node.succ.size() == 0)
                return expr_ref(m_util_a.mk_int(0), m);
            expr_ref plus = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            for(size_t i = 1; i < node.succ.size(); i++) {
                plus = m_util_a.mk_add(plus, len_to_expr(node.succ[i], variable_map, m, m_util_s, m_util_a));
            }
            return plus;
        }

        case LenFormulaType::TIMES: {
            if (node.succ.size() == 0)
                return expr_ref(m_util_a.mk_int(1), m);
            expr_ref times = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            for(size_t i = 1; i < node.succ.size(); i++) {
                times = m_util_a.mk_mul(times, len_to_expr(node.succ[i], variable_map, m, m_util_s, m_util_a));
            }
            return times;
        }

        case LenFormulaType::EQ: {
            assert(node.succ.size() == 2);
            expr_ref left = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            expr_ref right = len_to_expr(node.succ[1], variable_map, m, m_util_s, m_util_a);
            return expr_ref(m_util_a.mk_eq(left, right), m);
        }

        case LenFormulaType::NEQ: {
            assert(node.succ.size() == 2);
            expr_ref left = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            expr_ref right = len_to_expr(node.succ[1], variable_map, m, m_util_s, m_util_a);
            return expr_ref(m.mk_not(m_util_a.mk_eq(left, right)), m);
        }

        case LenFormulaType::LEQ: {
            assert(node.succ.size() == 2);
            expr_ref left = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            expr_ref right = len_to_expr(node.succ[1], variable_map, m, m_util_s, m_util_a);
            return expr_ref(m_util_a.mk_le(left, right), m);
        }

        case LenFormulaType::LT: {
            assert(node.succ.size() == 2);
            expr_ref left = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            expr_ref right = len_to_expr(node.succ[1], variable_map, m, m_util_s, m_util_a);
            // LIA solver fails if we use "L < R" for some reason (it cannot be internalized in smt::theory_lra::imp::internalize_atom, as it expects only <= or >=); we use "!(R <= L)" instead
            return expr_ref(m.mk_not(m_util_a.mk_le(right, left)), m);
        }

        case LenFormulaType::NOT: {
            assert(node.succ.size() == 1);
            expr_ref left = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            return expr_ref(m.mk_not(left), m);
        }

        case LenFormulaType::AND: {
            if(node.succ.size() == 0)
                return expr_ref(m.mk_true(), m);
            expr_ref andref = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            for(size_t i = 1; i < node.succ.size(); i++) {
                andref = m.mk_and(andref, len_to_expr(node.succ[i], variable_map, m, m_util_s, m_util_a));
            }
            return andref;
        }

        case LenFormulaType::OR: {
            if(node.succ.size() == 0)
                return expr_ref(m.mk_false(), m);
            expr_ref orref = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            for(size_t i = 1; i < node.succ.size(); i++) {
                orref = m.mk_or(orref, len_to_expr(node.succ[i], variable_map, m, m_util_s, m_util_a));
            }
            return orref;
        }

        case LenFormulaType::FORALL: {
            expr_ref varref = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            expr_ref bodyref = len_to_expr(node.succ[1], variable_map, m, m_util_s, m_util_a);

            ptr_vector<sort> sorts;
            svector<symbol> names;
            app * var = to_app(varref);
            sorts.push_back(var->get_sort());
            names.push_back(var->get_name());

            return expr_ref(m.mk_quantifier(quantifier_kind::forall_k, sorts.size(), sorts.data(), names.data(), bodyref), m);
        }

        case LenFormulaType::TRUE: {
            return expr_ref(m.mk_true(), m);
        }

        case LenFormulaType::FALSE: {
            return expr_ref(m.mk_false(), m);
        }

        default:
            throw_error("Unexpected length formula type");
            return {{}, m};
        }
    }
}
