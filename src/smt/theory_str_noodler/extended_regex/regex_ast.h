#pragma once

#include "char_set.h"

#include <cstdint>
#include <limits>
#include <memory>
#include <string>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

namespace smt::noodler::extended_regex {
    // ================== COMMON REGEX AST ==================
    //
    // The AST shared by all regex flavors. Its nodes are primitives common to the flavors, a frontend of a flavor
    // translates the constructs of its syntax into them while parsing (e.g., the dot, class escapes and character
    // classes into CharSet, a word boundary into lookarounds). The semantics in which flavors differ is given by
    // explicit parameters of the nodes, so the backend does not depend on any flavor.

    using GroupID = uint32_t;

    // The upper bound of a repetition that has no upper bound
    constexpr uint64_t UNBOUNDED = std::numeric_limits<uint64_t>::max();

    struct Node;
    using NodeRef = std::unique_ptr<Node>;

    /**
     * A sequence of terms. The empty concatenation matches the empty string.
     */
    struct Concatenation {
        std::vector<NodeRef> terms;
    };

    /**
     * A choice between alternatives.
     */
    struct Alternation {
        std::vector<NodeRef> alternatives;
    };

    /**
     * A repetition {min,max} of a subpattern. Greedy and lazy repetitions match the same strings, so they are not
     * distinguished.
     *
     * The parameters matter only if the subpattern contains capture groups:
     *   - `resets_captures`: the captures inside the subpattern are reset at the start of every iteration (ES2020
     *     RepeatMatcher, step 4),
     *   - `rejects_empty_iterations`: an iteration beyond the minimum that matches the empty string fails (ES2020
     *     RepeatMatcher, step 2.b).
     */
    struct Repetition {
        NodeRef child;
        uint64_t min = 0;
        uint64_t max = UNBOUNDED;
        bool resets_captures = false;
        bool rejects_empty_iterations = false;
    };

    /**
     * A capture group. Named groups are translated to numbered ones by the frontends.
     */
    struct Capture {
        GroupID id;
        NodeRef child;
    };

    /**
     * A backreference to the capture group `id`.
     *
     * If `unset_matches_empty` is set, a backreference to a group without a capture (the group was not entered yet,
     * is still open, or its capture was reset) matches the empty string (ES2020 BackreferenceMatcher), otherwise it
     * fails.
     */
    struct Backreference {
        GroupID id;
        bool unset_matches_empty = false;
    };

    enum class LookaroundDirection {
        FORWARD,
        BACKWARD
    };

    /**
     * A lookahead (FORWARD) or lookbehind (BACKWARD) assertion, positive or negative.
     */
    struct Lookaround {
        NodeRef child;
        LookaroundDirection direction;
        bool is_positive;
    };

    /**
     * An assertion of the start or the end of the whole text.
     */
    enum class Anchor {
        START_OF_TEXT,
        END_OF_TEXT
    };

    /**
     * A node of the common AST. A CharSet node matches exactly one character from the set, a literal character is
     * a set with one character.
     */
    struct Node {
        std::variant<CharSet, Concatenation, Alternation, Repetition, Capture, Backreference, Lookaround, Anchor>
            content;
    };

    template<typename T>
    NodeRef make_node(T content) {
        return std::make_unique<Node>(Node {std::move(content)});
    }

    // Visitor built from lambdas for std::visit
    template<typename... Fs>
    struct overloaded : Fs... {
        using Fs::operator()...;
    };

    template<typename... Fs>
    overloaded(Fs...) -> overloaded<Fs...>;

    /**
     * @brief Make a word boundary (or its negation if @p is_negated) for the word characters @p word_chars, i.e.,
     * \b = (?<=\w)(?!\w)|(?<!\w)(?=\w) and \B = (?<=\w)(?=\w)|(?<!\w)(?!\w).
     *
     * @param word_chars The word characters of the flavor (\w).
     * @param is_negated True for \B, false for \b.
     * @return NodeRef The AST of the word boundary.
     */
    NodeRef make_word_boundary(const CharSet& word_chars, bool is_negated);

    /**
     * @brief Call @p f on the reference (NodeRef) to every child of @p node.
     */
    template<typename NodeT, typename F>
    void for_each_child(NodeT& node, F&& f) {
        std::visit(
            [&](auto& content) {
                using T = std::decay_t<decltype(content)>;
                if constexpr (std::is_same_v<T, Concatenation>) {
                    for (auto& term : content.terms) {
                        f(term);
                    }
                }
                else if constexpr (std::is_same_v<T, Alternation>) {
                    for (auto& alternative : content.alternatives) {
                        f(alternative);
                    }
                }
                else if constexpr (std::is_same_v<T, Repetition> || std::is_same_v<T, Capture> ||
                                   std::is_same_v<T, Lookaround>) {
                    f(content.child);
                }
            },
            node.content);
    }

    /**
     * @brief Serialize the AST @p node, e.g., (SEQ (LIT 'a') (QUANT {0,inf} (SET 'a'-'z'))).
     *
     * The parameters of repetitions and backreferences are not serialized, they show up in the RCG.
     */
    std::string serialize(const Node& node);

    /**
     * @brief Recursively collect IDs of all backreferences in the AST @p node.
     *
     * The result is passed to strip_unreferenced_captures().
     *
     * @param refs Set to which every backreference ID found in the AST is added.
     */
    void collect_backrefs(const Node& node, std::unordered_set<GroupID>& refs);

    /**
     * @brief Recursively collect IDs of all capture groups in the AST @p node.
     *
     * Used when unrolling a repetition to find the captures that are reset at the start of every iteration.
     *
     * @param gids Vector to which every capture group ID found in the AST is appended.
     */
    void collect_capture_groups(const Node& node, std::vector<GroupID>& gids);

    /**
     * @brief Replace every capture group whose ID is not in @p referenced by its subpattern.
     *
     * Captures that are never referenced do not influence which strings match, removing them leads to fewer
     * unsupported regex structure errors.
     *
     * @param node       The AST in which the groups are replaced.
     * @param referenced The IDs of the referenced capture groups (see collect_backrefs()).
     */
    void strip_unreferenced_captures(NodeRef& node, const std::unordered_set<GroupID>& referenced);

    /**
     * Lookarounds enclosing the capture groups and backreferences of a regex, collected by collect_lookaround_scopes().
     * Every list holds the enclosing lookarounds from the outermost to the innermost one.
     */
    struct LookaroundScopes {
        std::unordered_map<GroupID, std::vector<const Lookaround*>> group_scopes;
        std::vector<std::pair<GroupID, std::vector<const Lookaround*>>> backref_scopes;
    };

    /**
     * @brief Recursively collect the lookarounds enclosing every capture group and backreference in @p node.
     *
     * Used by check_lookaround_backrefs().
     *
     * @param enclosing The lookarounds enclosing @p node, from the outermost to the innermost one.
     * @param scopes    The collected lookaround scopes of capture groups and backreferences.
     */
    void collect_lookaround_scopes(const Node& node, std::vector<const Lookaround*>& enclosing,
                                   LookaroundScopes& scopes);

    /**
     * @brief Throw "unsupported" if a backreference refers to a capture group inside a lookaround that does not
     * enclose the backreference, or to a capture group inside a lookbehind.
     *
     * The captures made inside a successful positive lookaround are kept, taken from its first inner match in
     * backtracking order (e.g., ES2020 lookarounds are atomic). The DFS evaluates a non-regular lookaround in a nested
     * search and discards its captures, so such a backreference would wrongly match the empty string.
     *
     * Some flavors (e.g., ES2020) match a lookbehind from right to left, so captures and backreferences inside it are
     * evaluated in the reverse order. The DFS traverses the lookbehind from left to right and would resolve such a
     * backreference against the wrong capture.
     *
     * @param root The root of the AST.
     */
    void check_lookaround_backrefs(const Node& root);
}  // namespace smt::noodler::extended_regex
