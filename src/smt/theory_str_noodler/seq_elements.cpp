#include "seq_elements.h"

#include <algorithm>

#include "ast/bv_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "smt/smt_enode.h"

#include "aut_assignment.h"
#include "util.h"

namespace smt::noodler {

    SeqElementAbstraction::SeqElementAbstraction(ast_manager& m, seq_util& m_util_s, context& ctx)
        : m(m), m_util_s(m_util_s), ctx(ctx), pinned(m) {}

    bool SeqElementAbstraction::enumerate_values(sort* elem_sort, ptr_vector<expr>& values) {
        bv_util bv(m);
        datatype::util dt(m);
        if (m.is_bool(elem_sort)) {
            values.push_back(m.mk_false());
            values.push_back(m.mk_true());
        } else if (bv.is_bv_sort(elem_sort)) {
            unsigned width = bv.get_bv_size(elem_sort);
            SASSERT(width < 32 && (1u << width) <= MAX_ENUM_SORT_SIZE);
            for (unsigned i = 0; i < (1u << width); ++i) {
                values.push_back(bv.mk_numeral(rational(i), width));
            }
        } else if (dt.is_datatype(elem_sort) && dt.is_enum_sort(elem_sort)) {
            for (func_decl* constructor : *dt.get_datatype_constructors(elem_sort)) {
                values.push_back(m.mk_const(constructor));
            }
        } else {
            return false;
        }
        for (expr* v : values) {
            pinned.push_back(v);
        }
        return true;
    }

    unsigned SeqElementAbstraction::get_sort_index(sort* elem_sort) {
        unsigned index;
        if (sort_to_index.find(elem_sort, index)) {
            return index;
        }

        SortInfo info;
        info.elem_sort = elem_sort;
        if (m_util_s.is_re(elem_sort) || m_util_s.is_ratrel(elem_sort)) {
            util::throw_error("unsupported element sort of a sequence (regexes or rational relations)");
        } else if (m_util_s.is_seq(elem_sort) || elem_sort->is_infinite() || elem_sort->is_very_big()) {
            // infinite (or very big) sort, we can always find fresh values for symbols not representing classes
            info.finite = false;
        } else {
            uint64_t size = elem_sort->get_num_elements().size();
            if (size <= MAX_ENUM_SORT_SIZE) {
                if (!enumerate_values(elem_sort, info.values)) {
                    util::throw_error("unsupported finite element sort of a sequence (we cannot enumerate its values)");
                }
                info.finite = true;
            } else if (size > static_cast<uint64_t>(zstring::max_char()) + 3) {
                // The sort has more values than we can have symbols. Therefore, we can always find a fresh value
                // for each symbol not representing some class, so we can handle it as an infinite sort.
                info.finite = false;
            } else {
                util::throw_error("unsupported finite element sort of a sequence (too large for enumerating its values)");
            }
        }

        index = sorts.size();
        sorts.push_back(std::move(info));
        symbol_to_class.emplace_back();
        sort_to_index.insert(elem_sort, index);
        return index;
    }

    void SeqElementAbstraction::register_seq_sort(sort* seq_sort) {
        sort* elem_sort = nullptr;
        if (m_util_s.is_seq(seq_sort, elem_sort) && !m_util_s.is_string(seq_sort)) {
            get_sort_index(elem_sort);
        }
    }

    void SeqElementAbstraction::collect(expr* e) {
        SASSERT(!classes_built);
        ptr_vector<expr> todo;
        todo.push_back(e);
        while (!todo.empty()) {
            expr* cur = todo.back();
            todo.pop_back();
            if (!is_app(cur) || visited.contains(cur)) {
                continue;
            }
            visited.insert(cur);
            pinned.push_back(cur);

            app* cur_app = to_app(cur);
            sort* cur_sort = cur->get_sort();
            if (m_util_s.is_seq(cur_sort)) {
                register_seq_sort(cur_sort);
            } else if (sort* seq_sort; m_util_s.is_re(cur_sort, seq_sort)) {
                register_seq_sort(seq_sort);
            }

            if (m_util_s.str.is_unit(cur)) {
                expr* elem = cur_app->get_arg(0);
                if (m_util_s.is_string(cur_sort)) {
                    // for strings, units of constant characters are rewritten to string literals
                    util::throw_error("unsupported non-constant character in a string (seq.unit)");
                }
                get_sort_index(elem->get_sort());
                if (!elements_set.contains(elem)) {
                    elements_set.insert(elem);
                    elements.push_back(elem);
                }
                // we do not traverse the element terms (they belong to other theories)
                continue;
            }

            for (expr* arg : *cur_app) {
                todo.push_back(arg);
            }
        }
    }

    enode* SeqElementAbstraction::get_root(expr* e) {
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        return ctx.get_enode(e)->get_root();
    }

    bool SeqElementAbstraction::build_classes(const std::function<void(expr*, const ptr_vector<expr>&)>& add_value_clause) {
        SASSERT(!classes_built);

        for (auto& info : sorts) {
            info.classes.clear();
        }
        root_to_class.reset();

        // group the elements into classes according to the roots of their enodes
        for (expr* elem : elements) {
            unsigned sort_index = sort_to_index[elem->get_sort()];
            SortInfo& info = sorts[sort_index];
            enode* root = get_root(elem);
            std::pair<unsigned, unsigned> cls;
            if (root_to_class.find(root, cls)) {
                ElemClass& elem_class = info.classes[cls.second];
                elem_class.members.push_back(elem);
                if (elem->get_id() < elem_class.rep->get_id()) {
                    elem_class.rep = elem;
                }
            } else {
                ElemClass elem_class;
                elem_class.rep = elem;
                elem_class.members.push_back(elem);
                root_to_class.insert(root, {sort_index, static_cast<unsigned>(info.classes.size())});
                info.classes.push_back(std::move(elem_class));
            }
        }

        // order classes by their representatives (so that the assigned symbols are deterministic)
        for (unsigned sort_index = 0; sort_index < sorts.size(); ++sort_index) {
            SortInfo& info = sorts[sort_index];
            std::sort(info.classes.begin(), info.classes.end(), [](const ElemClass& a, const ElemClass& b) {
                return a.rep->get_id() < b.rep->get_id();
            });
            for (unsigned class_index = 0; class_index < info.classes.size(); ++class_index) {
                root_to_class.insert(get_root(info.classes[class_index].rep), {sort_index, class_index});
            }
        }

        bool all_decided = true;
        for (SortInfo& info : sorts) {
            if (info.finite) {
                // each class must be equal to some value
                for (ElemClass& elem_class : info.classes) {
                    if (m.is_bool(info.elem_sort)) {
                        lbool assignment = ctx.find_assignment(elem_class.rep);
                        // the element must be relevant, otherwise its assignment need not be respected
                        // by other theories (and hence by the model)
                        if (assignment == l_undef || !ctx.is_relevant(elem_class.rep)) {
                            ctx.mark_as_relevant(elem_class.rep);
                            all_decided = false;
                        } else {
                            elem_class.value_index = (assignment == l_true) ? 1 : 0;
                        }
                        continue;
                    }
                    enode* root = get_root(elem_class.rep);
                    bool found = false;
                    for (unsigned value_index = 0; value_index < info.values.size(); ++value_index) {
                        if (get_root(info.values[value_index]) == root) {
                            elem_class.value_index = value_index;
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        add_value_clause(elem_class.rep, info.values);
                        all_decided = false;
                    }
                }
            } else {
                // all classes must be decided to be pairwise distinct
                for (unsigned i = 0; i < info.classes.size(); ++i) {
                    enode* n1 = ctx.get_enode(info.classes[i].rep);
                    for (unsigned j = i + 1; j < info.classes.size(); ++j) {
                        enode* n2 = ctx.get_enode(info.classes[j].rep);
                        if (m.are_distinct(n1->get_root()->get_expr(), n2->get_root()->get_expr())) {
                            continue;
                        }
                        // We cannot skip pairs with ctx.is_diseq(n1, n2): the disequation might come from
                        // an irrelevant atom, which is ignored by the theory of the elements. ctx.assume_eq
                        // makes the specific atom rep1 = rep2 relevant and returns false once it is
                        // relevant and assigned (this atom is also used in the refinement facts).
                        if (ctx.assume_eq(n1, n2)) {
                            STRACE(str, tout << "seq elements: assuming equality " << mk_pp(n1->get_expr(), m) << " = " << mk_pp(n2->get_expr(), m) << std::endl;);
                            all_decided = false;
                        }
                    }
                }
            }
        }

        classes_built = all_decided;
        return all_decided;
    }

    void SeqElementAbstraction::assign_symbols(regex::Alphabet& alph) {
        SASSERT(classes_built);
        std::set<mata::Symbol> used(alph.begin(), alph.end());
        // do not use digits and '.' as they can be added for conversions
        for (mata::Symbol s = AutAssignment::DIGIT_SYMBOL_START; s <= AutAssignment::DIGIT_SYMBOL_END; ++s) {
            used.insert(s);
        }
        used.insert(AutAssignment::REAL_NUMBER_DELIMITER);

        mata::Symbol next = zstring::max_char();
        bool exhausted = false;
        auto alloc_symbol = [&]() -> mata::Symbol {
            while (!exhausted && used.contains(next)) {
                if (next == 0) {
                    exhausted = true;
                } else {
                    --next;
                }
            }
            if (exhausted) {
                util::throw_error("not enough symbols for representing elements of sequences");
            }
            mata::Symbol res = next;
            used.insert(res);
            alph.insert(res);
            return res;
        };

        for (unsigned sort_index = 0; sort_index < sorts.size(); ++sort_index) {
            SortInfo& info = sorts[sort_index];
            std::map<mata::Symbol, unsigned>& sym_map = symbol_to_class[sort_index];
            sym_map.clear();
            if (info.finite) {
                info.value_symbols.clear();
                for (unsigned value_index = 0; value_index < info.values.size(); ++value_index) {
                    mata::Symbol s = alloc_symbol();
                    info.value_symbols.push_back(s);
                    sym_map[s] = value_index;
                }
                for (ElemClass& elem_class : info.classes) {
                    elem_class.symbol = info.value_symbols[elem_class.value_index];
                }
            } else {
                for (unsigned class_index = 0; class_index < info.classes.size(); ++class_index) {
                    mata::Symbol s = alloc_symbol();
                    info.classes[class_index].symbol = s;
                    sym_map[s] = class_index;
                }
            }
        }
        symbols_assigned = true;
        STRACE(str, display(tout););
    }

    mata::Symbol SeqElementAbstraction::get_symbol(expr* elem) {
        SASSERT(symbols_assigned);
        std::pair<unsigned, unsigned> cls;
        if (!root_to_class.find(get_root(elem), cls)) {
            util::throw_error("element of a sequence was not collected");
        }
        return sorts[cls.first].classes[cls.second].symbol;
    }

    zstring SeqElementAbstraction::get_word(expr* seq_term) {
        zstring res;
        if (m_util_s.str.is_string(seq_term, res)) {
            return res;
        }
        if (m_util_s.str.is_empty(seq_term)) {
            return zstring();
        }
        if (m_util_s.str.is_unit(seq_term)) {
            return zstring(get_symbol(to_app(seq_term)->get_arg(0)));
        }
        if (m_util_s.str.is_concat(seq_term)) {
            for (expr* arg : *to_app(seq_term)) {
                res = res + get_word(arg);
            }
            return res;
        }
        util::throw_error("we support only ground sequences in regexes");
        return res;
    }

    expr_ref SeqElementAbstraction::translate_regex(expr* re) {
        sort* seq_sort = nullptr;
        if (!m_util_s.is_re(re, seq_sort) || m_util_s.is_string(seq_sort)) {
            return expr_ref(re, m);
        }

        expr* cached;
        if (translated_regexes.find(re, cached)) {
            return expr_ref(cached, m);
        }

        if (!is_app(re) || to_app(re)->get_family_id() != m_util_s.get_family_id()) {
            util::throw_error("unsupported regex over sequences (only regex operations over ground sequences are supported)");
        }
        app* re_app = to_app(re);
        sort* str_re_sort = m_util_s.re.mk_re(m_util_s.mk_string_sort());

        expr_ref result(m);
        if (m_util_s.re.is_to_re(re_app)) {
            result = m_util_s.re.mk_to_re(m_util_s.str.mk_string(get_word(re_app->get_arg(0))));
        } else if (m_util_s.re.is_full_char(re_app)) {
            result = m_util_s.re.mk_full_char(nullptr);
        } else if (m_util_s.re.is_full_seq(re_app)) {
            result = m_util_s.re.mk_full_seq(str_re_sort);
        } else if (m_util_s.re.is_empty(re_app)) {
            result = m_util_s.re.mk_empty(str_re_sort);
        } else if (m_util_s.re.is_range(re_app) || m_util_s.re.is_of_pred(re_app)) {
            util::throw_error("unsupported regex over sequences (re.range or re.of_pred)");
        } else {
            expr_ref_vector args(m);
            for (expr* arg : *re_app) {
                args.push_back(translate_regex(arg));
            }
            func_decl* decl = re_app->get_decl();
            result = m.mk_app(m_util_s.get_family_id(), decl->get_decl_kind(), decl->get_num_parameters(), decl->get_parameters(), args.size(), args.data());
        }
        pinned.push_back(re);
        pinned.push_back(result);
        translated_regexes.insert(re, result);
        return result;
    }

    void SeqElementAbstraction::get_facts(expr_ref_vector& facts) {
        SASSERT(classes_built);
        for (const SortInfo& info : sorts) {
            for (const ElemClass& elem_class : info.classes) {
                for (expr* member : elem_class.members) {
                    if (member != elem_class.rep) {
                        facts.push_back(ctx.mk_eq_atom(member, elem_class.rep));
                    }
                }
                if (info.finite) {
                    if (m.is_bool(info.elem_sort)) {
                        facts.push_back(elem_class.value_index == 1 ? elem_class.rep : m.mk_not(elem_class.rep));
                    } else {
                        facts.push_back(ctx.mk_eq_atom(elem_class.rep, info.values[elem_class.value_index]));
                    }
                }
            }
            if (!info.finite) {
                for (unsigned i = 0; i < info.classes.size(); ++i) {
                    for (unsigned j = i + 1; j < info.classes.size(); ++j) {
                        expr* rep1 = info.classes[i].rep;
                        expr* rep2 = info.classes[j].rep;
                        if (m.are_distinct(rep1, rep2)) {
                            continue;
                        }
                        facts.push_back(m.mk_not(ctx.mk_eq_atom(rep1, rep2)));
                    }
                }
            }
        }
    }

    bool SeqElementAbstraction::is_finite_seq_sort(sort* seq_sort) const {
        sort* elem_sort = nullptr;
        unsigned index;
        if (!m_util_s.is_seq(seq_sort, elem_sort) || m_util_s.is_string(seq_sort) || !sort_to_index.find(elem_sort, index)) {
            return false;
        }
        return sorts[index].finite;
    }

    const std::vector<mata::Symbol>& SeqElementAbstraction::get_finite_symbols(sort* seq_sort) const {
        sort* elem_sort = nullptr;
        VERIFY(m_util_s.is_seq(seq_sort, elem_sort));
        unsigned index = 0;
        VERIFY(sort_to_index.find(elem_sort, index));
        SASSERT(sorts[index].finite);
        return sorts[index].value_symbols;
    }

    void SeqElementAbstraction::get_model_dependencies(sort* seq_sort, std::vector<enode*>& deps) {
        sort* elem_sort = nullptr;
        VERIFY(m_util_s.is_seq(seq_sort, elem_sort));
        unsigned index;
        if (!sort_to_index.find(elem_sort, index) || sorts[index].finite) {
            return;
        }
        for (const ElemClass& elem_class : sorts[index].classes) {
            deps.push_back(ctx.get_enode(elem_class.rep));
        }
    }

    expr_ref SeqElementAbstraction::mk_seq_value(sort* seq_sort, const zstring& word, expr* const* dep_values, unsigned num_dep_values, model_generator& mg) {
        sort* elem_sort = nullptr;
        VERIFY(m_util_s.is_seq(seq_sort, elem_sort));
        unsigned sort_index = get_sort_index(elem_sort);
        const SortInfo& info = sorts[sort_index];
        const std::map<mata::Symbol, unsigned>& sym_map = symbol_to_class[sort_index];

        ptr_vector<expr> elems;
        for (unsigned i = 0; i < word.length(); ++i) {
            mata::Symbol symbol = word[i];
            auto it = sym_map.find(symbol);
            if (info.finite) {
                if (it == sym_map.end()) {
                    util::throw_error("model of a sequence over a finite sort contains a symbol not representing any value");
                }
                elems.push_back(info.values[it->second]);
            } else if (it != sym_map.end()) {
                SASSERT(it->second < num_dep_values);
                elems.push_back(dep_values[it->second]);
            } else {
                // symbol not representing any class, it represents a fresh value
                auto key = std::make_pair(sort_index, symbol);
                auto anon_it = anonymous_values.find(key);
                if (anon_it == anonymous_values.end()) {
                    expr* fresh = mg.get_model().get_fresh_value(elem_sort);
                    if (fresh == nullptr) {
                        util::throw_error("cannot construct a fresh element value for a sequence model");
                    }
                    pinned.push_back(fresh);
                    anon_it = anonymous_values.emplace(key, fresh).first;
                }
                elems.push_back(anon_it->second);
            }
        }
        return mk_seq_from_elems(m, m_util_s, seq_sort, elems);
    }

    expr_ref SeqElementAbstraction::mk_seq_from_elems(ast_manager& m, seq_util& m_util_s, sort* seq_sort, const ptr_vector<expr>& elems) {
        if (elems.empty()) {
            return expr_ref(m_util_s.str.mk_empty(seq_sort), m);
        }
        expr_ref res(m_util_s.str.mk_unit(elems.back()), m);
        for (unsigned i = elems.size() - 1; i-- > 0; ) {
            res = m_util_s.str.mk_concat(m_util_s.str.mk_unit(elems[i]), res);
        }
        return res;
    }

    bool SeqElementAbstraction::get_elems_of_value(seq_util& m_util_s, expr* seq_value, ptr_vector<expr>& elems) {
        if (m_util_s.str.is_empty(seq_value)) {
            return true;
        }
        if (m_util_s.str.is_unit(seq_value)) {
            elems.push_back(to_app(seq_value)->get_arg(0));
            return true;
        }
        if (m_util_s.str.is_concat(seq_value)) {
            for (expr* arg : *to_app(seq_value)) {
                if (!get_elems_of_value(m_util_s, arg, elems)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    void SeqElementAbstraction::display(std::ostream& out) const {
        out << "Sequence element abstraction:" << std::endl;
        for (const SortInfo& info : sorts) {
            out << "  element sort " << mk_pp(info.elem_sort, m) << (info.finite ? " (finite)" : " (infinite)") << std::endl;
            if (info.finite) {
                for (unsigned i = 0; i < info.values.size() && i < info.value_symbols.size(); ++i) {
                    out << "    value " << mk_pp(info.values[i], m) << " -> " << info.value_symbols[i] << std::endl;
                }
            }
            for (const ElemClass& elem_class : info.classes) {
                out << "    class of " << mk_pp(elem_class.rep, m) << " -> " << elem_class.symbol << " members:";
                for (expr* member : elem_class.members) {
                    out << " " << mk_pp(member, m);
                }
                out << std::endl;
            }
        }
    }
}
