#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"

#include "theory_str_noodler.h"
#include "decision_procedure.h"

namespace smt::noodler {
    /// @brief Class for model generation of string variables that are in decision procedure dec_proc
    class theory_str_noodler::noodler_var_value_proc : public model_value_proc {
        // the variable whose model we want to generate
        BasicTerm str_var;
        // all variables whose arithmetic model we need (if they are string, we need their length) to generate mdoel for str_var
        std::vector<BasicTerm> needed_vars;
        theory_str_noodler& th;
    public:
        noodler_var_value_proc(BasicTerm str_var, theory_str_noodler& th) : str_var(str_var), needed_vars(th.dec_proc->get_len_vars_for_model(str_var)), th(th) {}

        void get_dependencies(buffer<model_value_dependency> & result) override {
            for (const BasicTerm& var : needed_vars) {
                expr_ref arith_var(th.m);
                // the following is similar to code in len_node_to_z3_formula()
                if(!th.var_name.contains(var)) {
                    // if the variable is not found, it was introduced in the preprocessing/decision procedure
                    // (either as a string or int var), i.e. we can just create a new z3 variable with the same name 
                    arith_var = th.mk_int_var(var.get_name().encode());
                } else {
                    arith_var = th.var_name.at(var); // for int var, we just take the var
                    if (th.m_util_s.is_string(arith_var->get_sort())) {
                        // for string var, we want its length
                        arith_var = expr_ref(th.m_util_s.str.mk_length(arith_var), th.m);
                    }
                }
                result.push_back(model_value_dependency(th.ctx.get_enode(arith_var)));
            }
        }

        app * mk_value(model_generator & m, expr_ref_vector const & values) override {
            // we create a function that takes some var from needed_vars and returns their model
            std::map<BasicTerm,rational> var_to_arith_model;
            SASSERT(values.size() == needed_vars.size());
            for (unsigned i = 0; i < needed_vars.size(); ++i) {
                bool is_int;
                rational val(0);
                VERIFY(th.m_util_a.is_numeral(values[i], val, is_int) && is_int);
                STRACE("str-model", tout << "Arith model of " << needed_vars[i] << " is " << val << std::endl;);
                var_to_arith_model[needed_vars[i]] = val;
            }

            return th.m_util_s.str.mk_string(th.dec_proc->get_model(str_var, var_to_arith_model));
        }
    };

    /// @brief Class for model generation of string variables that are not in decision procedure dec_proc (so their value does not matter, only constraint is their length)
    class theory_str_noodler::str_var_value_proc : public model_value_proc {
        expr* str_var; // the variable whose model we want to generate
        enode* str_var_length_enode; // the enode value of '(str.len str_var)'
        bool length_relevant = false; // do we actually need the length of str_var?
        seq_util& m_util_s;
        arith_util& m_util_a;
    public:
        str_var_value_proc(expr* str_var, context& ctx, seq_util& m_util_s, arith_util& m_util_a) : str_var(str_var), m_util_s(m_util_s), m_util_a(m_util_a) {
            if (ctx.e_internalized(m_util_s.str.mk_length(str_var))) {
                str_var_length_enode = ctx.get_enode(m_util_s.str.mk_length(str_var));
                length_relevant = ctx.is_relevant(str_var_length_enode);
            }
        }

        void get_dependencies(buffer<model_value_dependency> & result) override {
            // we just need the length of str_var (if the length is relevant)
            if (length_relevant) {
                result.push_back(model_value_dependency(str_var_length_enode));
            }
        }
    
        app * mk_value(model_generator & m, expr_ref_vector const & values) override {
            if (!length_relevant) {
                // because the length is not relevant, we can return anything, so we return empty string
                return m_util_s.str.mk_string(zstring());
            } else {
                // values[0] contain the length of str_var, so we return some string of this length
                bool is_int;
                rational val(0);
                SASSERT(values.size() == 1);
                VERIFY(m_util_a.is_numeral(values[0], val, is_int) && is_int);
                std::vector<unsigned> res(val.get_unsigned(), 'a'); // we can return anything, so we will just fill it with 'a'
                return m_util_s.str.mk_string(zstring(res.size(), res.data()));
            }
        }
    };

    /// @brief Class for model generation of concatenation
    class theory_str_noodler::concat_var_value_proc : public model_value_proc {
        seq_util& m_util_s;
        svector<model_value_dependency> m_dependencies;
    public:
        concat_var_value_proc(expr* str_concat, ast_manager& m, context& ctx, seq_util& m_util_s) : m_util_s(m_util_s) {
            // for concatenation, we just recursively get the models for arguments and then concatenate them
            expr_ref_vector concats(m);
            enode* str_concat_enode = ctx.get_enode(str_concat);
            STRACE("str-model-concat", tout << "Dependencies for concat " << mk_pp(str_concat, m) << " (#" << str_concat_enode->get_owner_id() << "):";);
            m_util_s.str.get_concat(str_concat, concats);
            for (auto concat : concats) {
                enode* concat_enode = ctx.get_enode(concat);
                STRACE("str-model-concat", tout << " " << mk_pp(concat, m) << " (#" << concat_enode->get_root()->get_owner_id() << ")";);
                if (concat_enode->get_root() == str_concat_enode) {
                    // this should not happen
                    util::throw_error("Enode for some concatenation is the representant of enode of one of its arguments");
                }
                m_dependencies.push_back(model_value_dependency(concat_enode));
            }
            STRACE("str-model-concat", tout << "\n";);
        }

        void get_dependencies(buffer<model_value_dependency> & result) override {
            // the dependencies are the arguments
            result.append(m_dependencies.size(), m_dependencies.data());
        }
    
        app * mk_value(model_generator & m, expr_ref_vector const & values) override {
            // concatenate the models of arguments
            zstring res;
            for (auto value : values) {
                zstring value_string;
                VERIFY(m_util_s.str.is_string(value, value_string));
                res = res + value_string;
            }
            return m_util_s.str.mk_string(res);
        }
    };


    model_value_proc* theory_str_noodler::model_of_string_var(app* str_var) {
        BasicTerm var = util::get_variable_basic_term(str_var);
        if (relevant_vars.contains(var)) {
            // for relevant (string) var, we get the model from the decision procedure that returned sat
            return alloc(noodler_var_value_proc, var, *this);
        } else {
            // for non-relevant, we cannot get them from the decision procedure, but because they are not relevant, we can return anything (restricted by length)
            return alloc(str_var_value_proc, str_var, ctx, m_util_s, m_util_a);
        }
    }

    model_value_proc* theory_str_noodler::mk_value(enode *const n, model_generator &mg) {
        // it seems here we only get string literals/vars, concats (whose arguments can be something more complex, but should be replacable by a var), from_int/from_code and regex literals/vars (vars probably not, only if we fix disequations with unrestricted regex vars)
        app *tgt = n->get_expr();
        STRACE("str", tout << "mk_value: getting model for " << mk_pp(tgt, m) << " sort is " << mk_pp(tgt->get_sort(), m) << "\n";);

        if (m_util_s.is_re(tgt)) {
            // if tgt is regular
            if (util::is_variable(tgt)) {
                util::throw_error("unrestricted regex vars unsupported"); // (should not be able to come here, as this should be handled by dec proc)
                return alloc(expr_wrapper_proc, tgt); // we return something so that we do not get warning
            } else {
                // for regex literal (regex stuff in z3 is either regex var or literal), we just return the regex
                return alloc(expr_wrapper_proc, tgt);
            }
        } else if (m_util_s.str.is_string(tgt)) {
            // for string literal, we just return the string
            return alloc(expr_wrapper_proc, tgt);
        } else if (util::is_str_variable(tgt, m_util_s)) {
            return model_of_string_var(tgt);
        } else if (m_util_s.str.is_concat(tgt)) {
            // check if tgt is not in a class of enodes that contain some string literal (see PR #174)
            enode* tgt_enode = ctx.get_enode(tgt);
            for (auto tgt_enode_it = tgt_enode->begin(); tgt_enode_it != tgt_enode->end(); ++tgt_enode_it) {
                app* cur_app = (*tgt_enode_it)->get_expr();
                if (m_util_s.str.is_string(cur_app)) {
                    // if the class contains string literal, return it directly
                    return alloc(expr_wrapper_proc, cur_app);
                }
            }
            return alloc(concat_var_value_proc, tgt, m, ctx, m_util_s);
        } else {
            // for complex string functions (nothing else should be able to come into mk_value), we should be able to find vars that replace them in predicate_replace
            if (predicate_replace.contains(tgt)) {
                expr* str_var = predicate_replace[to_expr(tgt)];
                // NOTE maybe we should create another version of model_value_proc that takes str_var and just add it as a dependency, so that we are not trying to get model of str_var twice (once here, once for a call mk_value(str_var))
                return model_of_string_var(to_app(str_var));
            } else {
                // we should not get some string complex function that is not in predicate_replace
                UNREACHABLE();
                return alloc(expr_wrapper_proc, tgt); // we return something so that we do not get warning
            }
        }
    }

    void theory_str_noodler::init_model(model_generator &mg) {
        STRACE("str", tout << "init_model\n");
    }

    void theory_str_noodler::finalize_model(model_generator &mg) {
        STRACE("str", tout << "finalize_model\n";);
    }
}