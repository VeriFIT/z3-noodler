#include "regex_simplification.h"

#include <algorithm>
#include <iterator>

namespace smt::noodler::extended_regex {
    void make_matching_explicit(NodeRef& root, const bool engine_semantics) {
        // A concatenation of a single term (e.g., a group around the whole regex) is the term itself
        while (auto* concatenation = std::get_if<Concatenation>(&root->content)) {
            if (concatenation->terms.size() != 1) {
                break;
            }
            NodeRef term = std::move(concatenation->terms[0]);
            root = std::move(term);
        }

        std::vector<NodeRef> alternatives;
        if (auto* alternation = std::get_if<Alternation>(&root->content)) {
            alternatives = std::move(alternation->alternatives);
        }
        else {
            alternatives.push_back(std::move(root));
        }

        // Remove the anchors and evaluate the lookarounds at the boundaries of the string
        struct MatchingAlternative {
            NodeRef node;
            bool anchored_start;
            bool anchored_end;
        };
        std::vector<MatchingAlternative> matching;
        for (NodeRef& alternative : alternatives) {
            std::vector<NodeRef>& terms = as_terms(alternative);
            const bool anchored_start = remove_string_anchors(terms, true);
            const bool anchored_end = remove_string_anchors(terms, false);
            if ((anchored_start || !engine_semantics) && !simplify_string_boundary(terms, true)) {
                continue;
            }
            if ((anchored_end || !engine_semantics) && !simplify_string_boundary(terms, false)) {
                continue;
            }
            matching.push_back({std::move(alternative), anchored_start, anchored_end});
        }
        if (matching.empty()) {
            // An empty set of characters matches nothing
            root = make_node(CharSet {});
            return;
        }

        // With engine semantics, Sigma* is added on the open sides. If all alternatives are open on a side, a single
        // Sigma* is put around the alternation, otherwise each open alternative gets its own.
        const bool open_start = engine_semantics && std::ranges::none_of(matching, [](const MatchingAlternative& alt) {
                                    return alt.anchored_start;
                                });
        const bool open_end = engine_semantics && std::ranges::none_of(matching, [](const MatchingAlternative& alt) {
                                  return alt.anchored_end;
                              });
        std::vector<NodeRef> result_alternatives;
        for (MatchingAlternative& alternative : matching) {
            std::vector<NodeRef>& terms = std::get<Concatenation>(alternative.node->content).terms;
            if (engine_semantics && !alternative.anchored_start) {
                trim_open_side(terms, true);
                if (!open_start) {
                    terms.insert(terms.begin(), make_sigma_star());
                }
            }
            if (engine_semantics && !alternative.anchored_end) {
                trim_open_side(terms, false);
                if (!open_end) {
                    terms.push_back(make_sigma_star());
                }
            }
            result_alternatives.push_back(std::move(alternative.node));
        }

        if (result_alternatives.size() == 1) {
            root = std::move(result_alternatives[0]);
        }
        else {
            root = make_node(Alternation {std::move(result_alternatives)});
        }
        if (open_start || open_end) {
            Concatenation wrapped;
            if (open_start) {
                wrapped.terms.push_back(make_sigma_star());
            }
            wrapped.terms.push_back(std::move(root));
            if (open_end) {
                wrapped.terms.push_back(make_sigma_star());
            }
            root = make_node(std::move(wrapped));
        }
    }

    void fold_lookarounds(NodeRef& node) {
        for_each_child(*node, [](NodeRef& child) {
            fold_lookarounds(child);
        });
        auto* concatenation = std::get_if<Concatenation>(&node->content);
        if (concatenation == nullptr) {
            return;
        }
        // Nested concatenations are not flattened: merging their regular terms with the neighbouring ones (e.g., Sigma*)
        // into a single match edge made the formulas harder to solve
        std::vector<NodeRef>& terms = concatenation->terms;
        for (std::size_t i = 0; i + 1 < terms.size();) {
            if (fold_adjacent_terms(terms, i)) {
                // The folded term can be folded with its left neighbour again
                i = (i > 0) ? i - 1 : 0;
            }
            else {
                ++i;
            }
        }
    }

    bool is_pure_regular(const Node& node) {
        if (std::holds_alternative<Capture>(node.content) || std::holds_alternative<Backreference>(node.content) ||
            std::holds_alternative<Lookaround>(node.content) || std::holds_alternative<Anchor>(node.content)) {
            return false;
        }
        bool is_pure = true;
        for_each_child(node, [&](const NodeRef& child) {
            is_pure = is_pure && is_pure_regular(*child);
        });
        return is_pure;
    }

    bool is_nullable(const Node& node) {
        return std::visit(overloaded {
                              [](const CharSet&) {
                                  return false;
                              },
                              [](const Concatenation& concatenation) {
                                  return std::ranges::all_of(concatenation.terms, [](const NodeRef& term) {
                                      return is_nullable(*term);
                                  });
                              },
                              [](const Alternation& alternation) {
                                  return std::ranges::any_of(alternation.alternatives, [](const NodeRef& alternative) {
                                      return is_nullable(*alternative);
                                  });
                              },
                              [](const Repetition& repetition) {
                                  return repetition.min == 0 || is_nullable(*repetition.child);
                              },
                              [](const Capture& capture) {
                                  return is_nullable(*capture.child);
                              },
                              // Not pure regular, never removed
                              [](const Backreference&) {
                                  return false;
                              },
                              [](const Lookaround&) {
                                  return false;
                              },
                              [](const Anchor) {
                                  return false;
                              },
                          },
                          node.content);
    }

    NodeRef make_sigma_star() {
        return make_node(Repetition {make_node(CharSet::all()), 0, UNBOUNDED});
    }

    std::vector<NodeRef>& as_terms(NodeRef& node) {
        if (!std::holds_alternative<Concatenation>(node->content)) {
            Concatenation concatenation;
            concatenation.terms.push_back(std::move(node));
            node = make_node(std::move(concatenation));
        }
        return std::get<Concatenation>(node->content).terms;
    }

    void splice_concatenation(std::vector<NodeRef>& terms, const std::size_t index) {
        std::vector<NodeRef> inner = std::move(std::get<Concatenation>(terms[index]->content).terms);
        terms.erase(terms.begin() + static_cast<std::ptrdiff_t>(index));
        terms.insert(terms.begin() + static_cast<std::ptrdiff_t>(index), std::make_move_iterator(inner.begin()),
                     std::make_move_iterator(inner.end()));
    }

    bool remove_string_anchors(std::vector<NodeRef>& terms, const bool at_start) {
        const Anchor anchor = at_start ? Anchor::START_OF_TEXT : Anchor::END_OF_TEXT;
        bool removed = false;
        while (!terms.empty()) {
            const std::size_t index = at_start ? 0 : terms.size() - 1;
            if (std::holds_alternative<Concatenation>(terms[index]->content)) {
                splice_concatenation(terms, index);
                continue;
            }
            const auto* term_anchor = std::get_if<Anchor>(&terms[index]->content);
            if (term_anchor == nullptr || *term_anchor != anchor) {
                break;
            }
            terms.erase(terms.begin() + static_cast<std::ptrdiff_t>(index));
            removed = true;
        }
        return removed;
    }

    const CharSet* get_single_char_lookaround(const Node& node, const LookaroundDirection direction,
                                              bool& is_positive) {
        const auto* lookaround = std::get_if<Lookaround>(&node.content);
        if (lookaround == nullptr || lookaround->direction != direction) {
            return nullptr;
        }
        const auto* tested = std::get_if<CharSet>(&lookaround->child->content);
        if (tested != nullptr) {
            is_positive = lookaround->is_positive;
        }
        return tested;
    }

    CharSet apply_lookaround(const CharSet& chars, const CharSet& tested, const bool is_positive) {
        // C∩S = ~(~C ∪ ~S) and C\S = ~(~C ∪ S)
        CharSet result = chars.complement();
        result.add(is_positive ? tested.complement() : tested);
        return result.complement();
    }

    void trim_open_side(std::vector<NodeRef>& terms, const bool at_start) {
        while (!terms.empty()) {
            const std::size_t index = at_start ? 0 : terms.size() - 1;
            Node& term = *terms[index];
            if (std::holds_alternative<Concatenation>(term.content)) {
                splice_concatenation(terms, index);
                continue;
            }
            if (!is_pure_regular(term)) {
                return;
            }
            if (is_nullable(term)) {
                terms.erase(terms.begin() + static_cast<std::ptrdiff_t>(index));
                continue;
            }
            if (auto* repetition = std::get_if<Repetition>(&term.content)) {
                repetition->max = repetition->min;
            }
            return;
        }
    }

    bool simplify_string_boundary(std::vector<NodeRef>& terms, const bool at_start) {
        const LookaroundDirection direction = at_start ? LookaroundDirection::BACKWARD : LookaroundDirection::FORWARD;
        while (!terms.empty()) {
            const std::size_t index = at_start ? 0 : terms.size() - 1;
            Node& term = *terms[index];
            if (std::holds_alternative<Concatenation>(term.content)) {
                splice_concatenation(terms, index);
                continue;
            }
            bool is_positive = false;
            if (get_single_char_lookaround(term, direction, is_positive) != nullptr) {
                if (is_positive) {
                    return false;
                }
                terms.erase(terms.begin() + static_cast<std::ptrdiff_t>(index));
                continue;
            }
            if (auto* alternation = std::get_if<Alternation>(&term.content)) {
                // Every alternative of the alternation is matched at the boundary of the string as well
                std::vector<NodeRef> alternatives;
                for (NodeRef& alternative : alternation->alternatives) {
                    if (simplify_string_boundary(as_terms(alternative), at_start)) {
                        alternatives.push_back(std::move(alternative));
                    }
                }
                if (alternatives.empty()) {
                    return false;
                }
                if (alternatives.size() == 1) {
                    // A concatenation, spliced in the next iteration
                    NodeRef alternative = std::move(alternatives[0]);
                    terms[index] = std::move(alternative);
                    continue;
                }
                alternation->alternatives = std::move(alternatives);
            }
            return true;
        }
        return true;
    }

    bool distribute_char_set(Alternation& alternation, const CharSet& chars, const bool into_end) {
        const LookaroundDirection direction = into_end ? LookaroundDirection::FORWARD : LookaroundDirection::BACKWARD;
        for (NodeRef& alternative : alternation.alternatives) {
            std::vector<NodeRef>& terms = as_terms(alternative);
            bool is_positive = false;
            if (terms.empty() ||
                get_single_char_lookaround(*(into_end ? terms.back() : terms.front()), direction, is_positive) ==
                    nullptr) {
                return false;
            }
        }

        std::vector<NodeRef> alternatives;
        for (NodeRef& alternative : alternation.alternatives) {
            std::vector<NodeRef>& terms = std::get<Concatenation>(alternative->content).terms;
            NodeRef& lookaround = into_end ? terms.back() : terms.front();
            bool is_positive = false;
            const CharSet* tested = get_single_char_lookaround(*lookaround, direction, is_positive);
            CharSet folded = apply_lookaround(chars, *tested, is_positive);
            if (folded.is_empty()) {
                // The alternative cannot match
                continue;
            }
            lookaround = make_node(std::move(folded));
            alternatives.push_back(std::move(alternative));
        }
        alternation.alternatives = std::move(alternatives);
        return true;
    }

    bool fold_adjacent_terms(std::vector<NodeRef>& terms, const std::size_t index) {
        Node& left = *terms[index];
        Node& right = *terms[index + 1];
        bool is_positive = false;

        // (?=S)C, (?!S)C and the first iteration of (?=S)C{m,n}
        if (const CharSet* tested = get_single_char_lookaround(left, LookaroundDirection::FORWARD, is_positive)) {
            if (auto* chars = std::get_if<CharSet>(&right.content)) {
                *chars = apply_lookaround(*chars, *tested, is_positive);
                terms.erase(terms.begin() + static_cast<std::ptrdiff_t>(index));
                return true;
            }
            auto* repetition = std::get_if<Repetition>(&right.content);
            if (repetition != nullptr && repetition->min > 0 && std::holds_alternative<CharSet>(repetition->child->content)) {
                NodeRef first =
                    make_node(apply_lookaround(std::get<CharSet>(repetition->child->content), *tested, is_positive));
                repetition->min--;
                if (repetition->max != UNBOUNDED) {
                    repetition->max--;
                }
                terms[index] = std::move(first);
                return true;
            }
        }

        // C(?<=S), C(?<!S) and the last iteration of C{m,n}(?<=S)
        if (const CharSet* tested = get_single_char_lookaround(right, LookaroundDirection::BACKWARD, is_positive)) {
            if (auto* chars = std::get_if<CharSet>(&left.content)) {
                *chars = apply_lookaround(*chars, *tested, is_positive);
                terms.erase(terms.begin() + static_cast<std::ptrdiff_t>(index + 1));
                return true;
            }
            auto* repetition = std::get_if<Repetition>(&left.content);
            if (repetition != nullptr && repetition->min > 0 && std::holds_alternative<CharSet>(repetition->child->content)) {
                NodeRef last =
                    make_node(apply_lookaround(std::get<CharSet>(repetition->child->content), *tested, is_positive));
                repetition->min--;
                if (repetition->max != UNBOUNDED) {
                    repetition->max--;
                }
                terms[index + 1] = std::move(last);
                return true;
            }
        }

        // A set after (before) an alternation whose alternatives end (start) with a lookahead (lookbehind), e.g., a word
        // boundary
        for (const bool into_end : {true, false}) {
            auto* alternation = std::get_if<Alternation>(&(into_end ? left : right).content);
            const auto* chars = std::get_if<CharSet>(&(into_end ? right : left).content);
            if (alternation == nullptr || chars == nullptr || !distribute_char_set(*alternation, *chars, into_end)) {
                continue;
            }
            // The alternation is at index after the set is removed
            terms.erase(terms.begin() + static_cast<std::ptrdiff_t>(into_end ? index + 1 : index));
            if (alternation->alternatives.size() == 1) {
                NodeRef alternative = std::move(alternation->alternatives[0]);
                terms[index] = std::move(alternative);
                splice_concatenation(terms, index);
            }
            return true;
        }
        return false;
    }
}  // namespace smt::noodler::extended_regex
