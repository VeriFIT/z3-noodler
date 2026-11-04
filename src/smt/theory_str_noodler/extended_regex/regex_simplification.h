#pragma once

#include "regex_ast.h"

#include <cstddef>
#include <vector>

namespace smt::noodler::extended_regex {
    // ================== AST SIMPLIFICATIONS ==================
    //
    // Passes on the common AST that keep the strings matched by the regex (and its captures), but remove anchors and
    // lookarounds that would otherwise need fresh variables and word equations in the generated formula.

    /**
     * @brief Make the matching semantics explicit in @p root and simplify its top-level alternatives.
     *
     * After this pass, @p root is matched against the whole string, i.e., build_rcg() is called without engine
     * semantics. For every top-level alternative:
     *   - leading START_OF_TEXT and trailing END_OF_TEXT anchors are removed, since the alternative is matched from the
     *     start to the end of the string,
     *   - on a side matched at the start or the end of the string (anchored, or any side without engine semantics),
     *     the lookarounds testing a single character beyond the string are evaluated (see simplify_string_boundary()),
     *   - with @p engine_semantics, Sigma* is added on each side without an anchor, after the terms next to it are
     *     trimmed (see trim_open_side()).
     * Alternatives that cannot match are removed.
     *
     * @param root The root of the AST, replaced by the simplified AST.
     * @param engine_semantics Whether the regex matches a substring of the string (str.ecma_engine_semantics).
     */
    void make_matching_explicit(NodeRef& root, bool engine_semantics);

    /**
     * @brief Fold the lookarounds testing a single character into the neighbouring character sets, in all
     * concatenations of @p node.
     *
     * A lookaround testing a set S folds into the set C of the character it tests: (?=S)C and C(?<=S) become C∩S,
     * (?!S)C and C(?<!S) become C\S. The tested iteration of a repetition of a set is peeled off and folded. An
     * alternation whose alternatives all end (start) with such a lookahead (lookbehind), e.g., a word boundary, takes a
     * following (preceding) set into its alternatives, and the alternatives whose set becomes empty are removed.
     *
     * @param node The AST in which the lookarounds are folded.
     */
    void fold_lookarounds(NodeRef& node);

    /**
     * @brief Return true if @p node contains no capture group, backreference, lookaround or anchor, i.e., it is a
     * regular pattern that does not influence the rest of the regex.
     */
    bool is_pure_regular(const Node& node);

    /**
     * @brief Return true if the pure regular pattern @p node matches the empty string.
     */
    bool is_nullable(const Node& node);

    /**
     * @brief Make the AST of Sigma*, i.e., of any string.
     */
    NodeRef make_sigma_star();

    /**
     * @brief Turn @p node into a concatenation if it is not one, and return its terms.
     */
    std::vector<NodeRef>& as_terms(NodeRef& node);

    /**
     * @brief Replace the concatenation terms[@p index] by its own terms.
     */
    void splice_concatenation(std::vector<NodeRef>& terms, std::size_t index);

    /**
     * @brief Remove the START_OF_TEXT (if @p at_start) or END_OF_TEXT anchors at the start (end) of @p terms.
     *
     * @return true if an anchor was removed, i.e., @p terms is matched at the start (end) of the string.
     */
    bool remove_string_anchors(std::vector<NodeRef>& terms, bool at_start);

    /**
     * @brief Get the set tested by @p node if it is a lookaround in @p direction testing a single character, nullptr
     * otherwise. The polarity of the lookaround is stored to @p is_positive.
     */
    const CharSet* get_single_char_lookaround(const Node& node, LookaroundDirection direction, bool& is_positive);

    /**
     * @brief Return the characters of @p chars that pass a lookaround testing @p tested, positive if @p is_positive.
     */
    CharSet apply_lookaround(const CharSet& chars, const CharSet& tested, bool is_positive);

    /**
     * @brief Trim the terms at the start (if @p at_start) or the end of @p terms, which Sigma* is put next to.
     *
     * A pure regular nullable term is removed (Sigma*·N = Sigma*) and a pure regular repetition is cut to its minimum
     * (Sigma*·X{m,n} = Sigma*·X{m}), the other iterations are matched by Sigma*.
     */
    void trim_open_side(std::vector<NodeRef>& terms, bool at_start);

    /**
     * @brief Evaluate the lookbehinds (if @p at_start) or lookaheads testing a single character at the start (end) of
     * @p terms, which is matched at the start (end) of the string: there is no character to test, so a negative
     * lookaround holds and is removed, a positive one fails. Alternations there are simplified recursively.
     *
     * @return false if @p terms cannot match at the start (end) of the string.
     */
    bool simplify_string_boundary(std::vector<NodeRef>& terms, bool at_start);

    /**
     * @brief Take the set @p chars that follows (if @p into_end) or precedes @p alternation into its alternatives, if
     * all of them end (start) with a lookahead (lookbehind) testing a single character, which @p chars is folded into.
     *
     * @return true if @p chars was taken into the alternatives.
     */
    bool distribute_char_set(Alternation& alternation, const CharSet& chars, bool into_end);

    /**
     * @brief Fold terms[@p index] and terms[@p index + 1] of a concatenation, see fold_lookarounds().
     *
     * @return true if the terms were changed.
     */
    bool fold_adjacent_terms(std::vector<NodeRef>& terms, std::size_t index);
}  // namespace smt::noodler::extended_regex
