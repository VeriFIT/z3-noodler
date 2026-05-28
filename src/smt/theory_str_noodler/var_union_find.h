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

#include "params/smt_params.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "params/theory_str_noodler_params.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "smt/smt_context.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "smt/theory_str_noodler/expr_solver.h"

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

        // Map key -> (val -> precise)
        // precise=true means we trust the (key,val) relation without requiring
        // e-graph or LIA-based equivalence confirmation in get_equivalence_bt().
        obj_map<expr, obj_map<expr, bool>> un_find;
        arith_util& m_util_a;
        ast_manager& m;

        // Keep references to keys/values used in this structure so that expr* stored
        // in internal maps stays valid across Z3's GC.
        expr_ref_vector m_pinned;

        std::map<expr*, int> key_to_value; // -1 means key is not a numeral

        // --- scoping trail ---
        //
        // Scoping (push_scope / pop_scope) follows the standard SMT trail pattern:
        //
        //  m_trail        — ordered log of every mutation made to `un_find` and
        //                   `key_to_value` since the last push_scope().  Each entry
        //                   carries enough information to reverse the change.  Entries
        //                   are only appended while at least one scope is active (i.e.
        //                   while m_scope_trail is non-empty), so there is zero overhead
        //                   at the base level.
        //
        //  m_scope_trail  — stack of checkpoints: each push_scope() records the
        //                   current size of m_trail here.  pop_scope() reads the top
        //                   checkpoint to know how far back to replay the undo log.
        //
        //  m_pinned_trail — parallel stack for m_pinned (the expr_ref_vector that
        //                   holds reference counts so Z3's GC cannot collect expr*
        //                   pointers stored in un_find / key_to_value).  Each
        //                   push_scope() records the current size of m_pinned here;
        //                   pop_scope() shrinks m_pinned back to that size, releasing
        //                   the GC pins acquired inside the popped scope.

        // Tags the kind of mutation recorded in an UndoEntry.
        enum class UndoKind {
            NEW_KEY,        // a fresh key was inserted into un_find
            NEW_VAL,        // a fresh value was added to an existing key's inner map
            UPDATE_PRECISE  // the `precise` flag of an existing (key, val) pair changed
        };

        // One reversible mutation recorded on m_trail.
        struct UndoEntry {
            UndoKind kind;
            expr* key;
            expr* val;        // used by NEW_VAL and UPDATE_PRECISE
            bool old_precise; // used by UPDATE_PRECISE: the value to restore on undo
        };

        // Log of reversible mutations; entries are appended by add() and consumed
        // (in reverse) by pop_scope().
        std::vector<UndoEntry> m_trail;
        // Sizes of m_trail at each push_scope() — forms the scope checkpoint stack.
        std::vector<unsigned> m_scope_trail;
        // Sizes of m_pinned at each push_scope() — tracks which GC pins to release
        // when the corresponding scope is popped.
        std::vector<unsigned> m_pinned_trail;

    public:
        var_union_find(arith_util& m_util_a) : un_find(), m_util_a(m_util_a), m(m_util_a.get_manager()), m_pinned(m) { }

        /**
         * @brief Add new item to the equivalence
         *
         * @param key Key of the element. Each element @p val has a key (e.g.,
         * length term) that is then used for equivalence class merging.
         * @param val Value (variable) associated with the key.
         * @param precise If true, the (key,val) relation is considered precise
         */
        void add(const expr_ref& key, const expr_ref& val, bool precise = true) {
            m_pinned.push_back(key);
            m_pinned.push_back(val);

            if (this->un_find.contains(key)) {
                bool already_precise = false;
                if (this->un_find[key].find(val, already_precise)) {
                    bool new_precise = already_precise || precise;
                    if (new_precise != already_precise) {
                        if (!m_scope_trail.empty())
                            m_trail.push_back({UndoKind::UPDATE_PRECISE, key, val, already_precise});
                        this->un_find[key].insert(val, new_precise);
                    }
                }
                else {
                    if (!m_scope_trail.empty())
                        m_trail.push_back({UndoKind::NEW_VAL, key, val, false});
                    this->un_find[key].insert(val, precise);
                }
            }
            else {
                if (!m_scope_trail.empty())
                    m_trail.push_back({UndoKind::NEW_KEY, key, nullptr, false});
                obj_map<expr, bool> found;
                found.insert(val, precise);
                this->un_find.insert(key, found);
            }

            // we remember the value of key now, because sometimes it happened that the expr* for key stopped being a valid expression in z3
            // and if we did the following in get_equivalence_bt() we would get segfault
            rational rat;
            if(this->m_util_a.is_numeral(key, rat)) {
                key_to_value[key] = rat.get_int32();
            } else {
                key_to_value[key] = -1;
            }
        }

        /**
         * @brief Open a new backtracking scope.
         *
         * Records checkpoints for both the undo log (m_scope_trail) and the GC-pin
         * vector (m_pinned_trail).  Subsequent calls to add() will append undo entries
         * to m_trail so that all changes made inside this scope can be reversed by
         * pop_scope().
         */
        void push_scope() {
            m_scope_trail.push_back(m_trail.size());
            m_pinned_trail.push_back(m_pinned.size());
        }

        /**
         * @brief Close and undo @p num_scopes backtracking scopes.
         *
         * For each scope being popped the method:
         *  1. Reads the m_trail checkpoint saved by the corresponding push_scope().
         *  2. Replays the undo log in reverse order, inverting every mutation that
         *     add() recorded since that push_scope():
         *       - NEW_KEY       → remove the key from un_find and key_to_value
         *       - NEW_VAL       → remove the value from the key's inner map
         *       - UPDATE_PRECISE→ restore the previous `precise` flag
         *  3. Reads the m_pinned checkpoint and shrinks m_pinned back to that size,
         *     releasing the reference counts on expr* objects that were pinned inside
         *     the popped scope so Z3's GC may reclaim them.
         */
        void pop_scope(unsigned num_scopes) {
            for (unsigned i = 0; i < num_scopes; ++i) {
                SASSERT(!m_scope_trail.empty());
                unsigned trail_sz = m_scope_trail.back();
                m_scope_trail.pop_back();
                unsigned pinned_sz = m_pinned_trail.back();
                m_pinned_trail.pop_back();

                // Undo trail entries in reverse order before shrinking m_pinned,
                // because the expr* pointers in UndoEntry must still be valid.
                while (m_trail.size() > trail_sz) {
                    const UndoEntry& e = m_trail.back();
                    switch (e.kind) {
                    case UndoKind::NEW_KEY:
                        // The entire key bucket was added in this scope — remove it.
                        un_find.remove(e.key);
                        key_to_value.erase(e.key);
                        break;
                    case UndoKind::NEW_VAL:
                        // A new value was inserted into an existing key's bucket.
                        un_find[e.key].remove(e.val);
                        break;
                    case UndoKind::UPDATE_PRECISE:
                        // The precise flag was flipped; restore the old value.
                        un_find[e.key].insert(e.val, e.old_precise);
                        break;
                    }
                    m_trail.pop_back();
                }

                // Release GC pins for all expr* objects added during this scope.
                m_pinned.shrink(pinned_sz);
            }
        }

        /**
         * @brief Get the equivalence classes
         */
        const obj_map<expr, obj_map<expr, bool>>& get_equivalence() const {
            return this->un_find;
        }

        /**
         * @brief Get the equivalence classes where each z3 term is replaced with the 
         * equivalent BasicTerm object.
         * 
         * @return Equivalence classes consisting of BasicTerms
         */
        BasicTermEqiv get_equivalence_bt(const AutAssignment& aut_ass, smt::context& ctx, seq_util& m_util_s) const {
            std::vector<std::set<BasicTerm>> ret;
            int_expr_solver lia_solver(ctx.get_manager(), ctx.get_fparams());

            for (const auto& t : this->un_find) {
                int len = key_to_value.at(t.m_key);

                // Internalize key lazily only if we need equivalence checks.
                enode* key_n = nullptr;

                // Basic term in the equivalence class
                std::set<BasicTerm> st;
                for (const auto& s : t.m_value) {
                    expr* var = s.m_key;
                    bool precise = s.m_value;
                    // we consider only variables (not concatenation or other complex terms)
                    // therefore, s = variable
                    if(!is_app(var) || to_app(var)->get_num_args() != 0) {
                        continue;
                    }
                    BasicTerm bvar = util::get_variable_basic_term(var);
                    if (len > 1) {
                        std::set<std::pair<int, int>> aut_constr = mata::applications::strings::get_word_lengths(*aut_ass.at(bvar));
                        if (aut_constr.size() > 1 || !aut_constr.contains({len, 0})) {
                            continue;
                        }
                    }

                    // If the relation is marked precise, we accept it without
                    // e-graph root comparison or LIA fallback.
                    if (precise) {
                        st.insert(bvar);
                        continue;
                    }

                    if (!key_n) {
                        ctx.ensure_internalized(t.m_key);
                        key_n = ctx.find_enode(t.m_key);
                        if (!key_n) {
                            continue;
                        }
                    }

                    // create a term |s|
                    expr_ref len_term(m_util_s.str.mk_length(var), ctx.get_manager());
                    ctx.ensure_internalized(len_term);
                    enode* n = ctx.find_enode(len_term);
                    if (!n) {
                        continue;
                    }

                    // key and s are not in the same equivalence class. We try to resolve using LIA solver.
                    if (key_n->get_root() != n->get_root()) {
                        // enodes are sometimes not precise (they do not relate terms to 
                        // the same equivalence class even though they are indeed equivalent).
                        // Fallback: if key != |s| is UNSAT in the current arithmetic context,
                        // then key and |s| are equivalent even if the e-graph didn't merge them.
                        bool lia_implies_eq = false;
                        if (m_util_a.is_int(t.m_key) && m_util_a.is_int(len_term)) {
                            ast_manager& m = ctx.get_manager();
                            expr_ref neq(m.mk_not(m.mk_eq(t.m_key, len_term)), m);
                            lia_solver.initialize(ctx);
                            lbool res = lia_solver.check_sat(neq);
                            lia_implies_eq = (res == l_false);
                        }
                        if (!lia_implies_eq) {
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
