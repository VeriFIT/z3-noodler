#ifndef _VAR_UNION_FIND_
#define _VAR_UNION_FIND_

#include <functional>
#include <list>
#include <set>
#include <stack>
#include <map>
#include <memory>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "smt/params/smt_params.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_noodler_params.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"

namespace smt::noodler {

    typedef std::vector<std::set<BasicTerm>> BasicTermEqiv;

    static bool ec_are_equal(const BasicTermEqiv& ec, const BasicTerm& t1, const BasicTerm& t2) {
        for(const auto& st: ec) {
            if(st.find(t1) != st.end() && st.find(t2) != st.end()) {
                return true;
            }
        }
        return false;
    }

    /**
     * @brief Class for union-find like data structure. Allows to handle equivalence classes of 
     * z3 expressions. It is implemented naively so-far.
     * 
     */
    class var_union_find {

        obj_map<expr, obj_hashtable<expr>> un_find;
        arith_util& m_util_a;

    public:
        var_union_find(arith_util& m_util_a) : un_find(), m_util_a(m_util_a) { }

        /**
         * @brief Add new item to the equivalence
         * 
         * @param key Key of the element. Each element @p val has a key (e.g., 
         * length term) that is then used for equivalence class merging.
         * @param val Value (variable) associated with the key.
         */
        void add(const expr_ref& key, const expr_ref& val) {
            obj_hashtable<expr> found;
            if(this->un_find.find(key, found)) {
                this->un_find[key].insert(val);
            } else {
                found.insert(val);
                this->un_find.insert(key, found);
            }
        }

        /**
         * @brief Get the equivalence classes
         */
        const obj_map<expr, obj_hashtable<expr>>& get_equivalence() const {
            return this->un_find;
        }

        /**
         * @brief Get the equivalence classes where each z3 term is replaced with the 
         * equivalent BasicTerm object.
         * 
         * @return Equivalence classes consisting of BasicTerms
         */
        BasicTermEqiv get_equivalence_bt(const AutAssignment& aut_ass) const {
            std::vector<std::set<BasicTerm>> ret;
            for(const auto& t : this->un_find) {
                std::set<BasicTerm> st;
                int len = -1;
                rational val;
                if(this->m_util_a.is_numeral(t.m_key, val)) {
                    len = val.get_int32();
                }
                for (const auto& s : t.m_value) {
                    std::string var = to_app(s)->get_decl()->get_name().str();
                    BasicTerm bvar(BasicTermType::Variable, var);
                    
                    if(len != -1 && len > 1) {
                        std::set<std::pair<int, int>> aut_constr = mata::strings::get_word_lengths(*aut_ass.at(bvar));
                        if(aut_constr.size() > 1 || !aut_constr.contains({len, 0})) {
                            continue;
                        }
                    }
                    
                    st.insert(bvar);  
                }
                ret.push_back(st);
            }
            return ret;
        }

    };

}

#endif