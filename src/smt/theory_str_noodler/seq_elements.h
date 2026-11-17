/**
 * @file seq_elements.h
 * @brief Abstraction of elements of generic sequences (Seq T) by automata symbols.
 *
 * The decision procedures of Noodler work with words over a finite alphabet of (Mata) symbols. For strings,
 * symbols are the code points of characters. For generic sequences (Seq T), elements are arbitrary terms of
 * sort T (owned by other theories). We abstract them as follows:
 *   - each element term e occurring in (seq.unit e) is mapped to a symbol given by the E-class of e,
 *   - Z3 is forced to decide all equalities between the element terms (i.e., the classes), so that
 *     distinct symbols correspond to distinct values of the elements,
 *   - for an infinite (or very large) sort T, any other symbol (a symbol not representing any class) occurring in
 *     a model of a sequence variable corresponds to a fresh value of T (different from values of all classes and
 *     of all other such symbols),
 *   - for a small finite sort T, all values of T are enumerated (each value gets its own symbol), each element
 *     term must be equal to one of the values, and every sequence variable of sort (Seq T) is restricted to words
 *     over the symbols of the values of T.
 * Generic sequences are then handled by the decision procedures in the same way as strings.
 */

#ifndef _NOODLER_SEQ_ELEMENTS_H_
#define _NOODLER_SEQ_ELEMENTS_H_

#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <vector>

#include <mata/alphabet.hh>

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"

#include "regex.h"

namespace smt::noodler {

    class SeqElementAbstraction {
    public:
        /// Maximal cardinality of a finite element sort whose values are enumerated.
        static constexpr unsigned MAX_ENUM_SORT_SIZE = 256;

        /// Class of element terms (all its members are equal in the current assignment).
        struct ElemClass {
            /// The representative of the class (the collected member with the smallest id).
            expr* rep;
            /// The collected element terms in this class.
            ptr_vector<expr> members;
            /// The symbol representing the class.
            mata::Symbol symbol = 0;
            /// For finite sorts: index of the value of the class (in SortInfo::values).
            unsigned value_index = 0;
        };

        /// Information about one element sort T (of some (Seq T) occurring in the formula).
        struct SortInfo {
            sort* elem_sort;
            /// Are the values of the sort enumerated (small finite sort)?
            bool finite = false;
            /// Enumerated values (only for finite sorts).
            ptr_vector<expr> values;
            /// Symbols of the enumerated values (only for finite sorts), values_symbols[i] is the symbol of values[i].
            std::vector<mata::Symbol> value_symbols;
            /// Classes of the element terms of this sort.
            std::vector<ElemClass> classes;
        };

    private:
        ast_manager& m;
        seq_util& m_util_s;
        context& ctx;
        /// Keeps alive all expressions created/stored by this class.
        expr_ref_vector pinned;

        /// Collected element terms (arguments of seq.unit), in the order of collection.
        ptr_vector<expr> elements;
        obj_hashtable<expr> elements_set;
        /// Visited expressions during collection.
        obj_hashtable<expr> visited;

        /// Information about element sorts.
        std::vector<SortInfo> sorts;
        obj_map<sort, unsigned> sort_to_index;

        /// Maps (the root of the enode of) element terms to (sort index, class index).
        obj_map<enode, std::pair<unsigned, unsigned>> root_to_class;
        /// Maps symbols of classes/values to (sort index, class index/value index) for each sort.
        std::vector<std::map<mata::Symbol, unsigned>> symbol_to_class;

        bool classes_built = false;
        bool symbols_assigned = false;

        /// Cache for translations of regexes.
        obj_map<expr, expr*> translated_regexes;

        /// Fresh values for symbols not representing any class (for the current model).
        std::map<std::pair<unsigned, mata::Symbol>, expr*> anonymous_values;

        /// Returns index of the sort info of the element sort @p elem_sort (registers it if needed).
        unsigned get_sort_index(sort* elem_sort);
        /// Enumerates values of the finite sort @p elem_sort, returns false if it is not possible.
        bool enumerate_values(sort* elem_sort, ptr_vector<expr>& values);
        enode* get_root(expr* e);

    public:
        SeqElementAbstraction(ast_manager& m, seq_util& m_util_s, context& ctx);

        /**
         * @brief Register a sequence sort @p seq_sort used in the formula (generic sequence sorts register their element sort).
         *
         * String sort is ignored (characters are handled as usual symbols).
         */
        void register_seq_sort(sort* seq_sort);

        /**
         * @brief Collect element terms (arguments of seq.unit) of generic sequences occurring in @p e.
         *
         * Traverses sequence terms, regexes and predicates over them, but not the element terms themselves.
         * Also registers sequence sorts of all encountered sequence terms.
         */
        void collect(expr* e);

        /// Is there no generic sequence sort (and thus nothing to abstract)?
        bool empty() const { return sorts.empty(); }

        /**
         * @brief Build the classes of collected element terms and make sure that their (dis)equalities are decided.
         *
         * For infinite sorts, if the equality of some pair of classes is not decided yet, it calls ctx.assume_eq.
         * For finite sorts, if some element term is not equal to any of the values, it calls @p add_value_clause,
         * which should add the clause e = v_1 || ... || e = v_k.
         *
         * @return true if everything is decided (the classes are built), false if some decisions were requested
         * (the caller should return FC_CONTINUE).
         */
        bool build_classes(const std::function<void(expr*, const ptr_vector<expr>&)>& add_value_clause);

        /**
         * @brief Assign symbols to classes/values.
         *
         * The symbols are taken from the largest ones (zstring::max_char() downward), skipping the symbols in @p alph
         * (symbols used by strings) and digits. The assigned symbols are inserted into @p alph.
         */
        void assign_symbols(regex::Alphabet& alph);

        /// Get the symbol of an element term @p elem (classes must be built and symbols assigned).
        mata::Symbol get_symbol(expr* elem);

        /**
         * @brief Get the word (over symbols) represented by a ground generic sequence term @p seq_term (consisting
         * of seq.unit, seq.empty and concatenations).
         *
         * Throws an error if @p seq_term is not ground.
         */
        zstring get_word(expr* seq_term);

        /**
         * @brief Translates a regex @p re over a generic sequence sort into an equivalent string regex over the symbols.
         *
         * The units are replaced by their symbols. String regexes are returned unchanged.
         */
        expr_ref translate_regex(expr* re);

        /**
         * @brief Get facts about elements the abstraction relies on (equalities of members with representatives,
         * disequalities of representatives, equalities with values).
         *
         * All facts are true in the current assignment.
         */
        void get_facts(expr_ref_vector& facts);

        /// Is @p seq_sort a sequence over a finite sort with enumerated values?
        bool is_finite_seq_sort(sort* seq_sort) const;
        /// Symbols of the values of the element sort of @p seq_sort (which must be a sequence over a finite enumerated sort).
        const std::vector<mata::Symbol>& get_finite_symbols(sort* seq_sort) const;

        /**
         * @brief Get the enodes whose model values are needed for constructing models of sequences of sort @p seq_sort.
         */
        void get_model_dependencies(sort* seq_sort, std::vector<enode*>& deps);

        /**
         * @brief Construct a model value of sort @p seq_sort for the word @p word.
         *
         * @param dep_values model values of the dependencies obtained from get_model_dependencies (in the same order).
         */
        expr_ref mk_seq_value(sort* seq_sort, const zstring& word, expr* const* dep_values, unsigned num_dep_values, model_generator& mg);

        /// Forget the fresh values of symbols that do not represent classes (should be called for each new model).
        void reset_model() { anonymous_values.clear(); }

        /**
         * @brief Construct a sequence value of sort @p seq_sort from the values @p elems (a concatenation of units).
         */
        static expr_ref mk_seq_from_elems(ast_manager& m, seq_util& m_util_s, sort* seq_sort, const ptr_vector<expr>& elems);

        /**
         * @brief Collect element values of a sequence value @p seq_value (a concatenation of units).
         *
         * @return false if @p seq_value is not of this form.
         */
        static bool get_elems_of_value(seq_util& m_util_s, expr* seq_value, ptr_vector<expr>& elems);

        void display(std::ostream& out) const;
    };
}

#endif
