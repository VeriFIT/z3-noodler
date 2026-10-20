#include "regex_ast.h"

#include "smt/theory_str_noodler/util.h"

#include <algorithm>

namespace smt::noodler::extended_regex {
    NodeRef make_word_boundary(const CharSet& word_chars, const bool is_negated) {
        // A word boundary is a position where one side is a word character and the other one is not. This is
        // modelled as two alternatives, each a chain of a lookbehind and a lookahead.
        auto make_lookaround = [&](const LookaroundDirection direction, const bool is_positive) {
            return make_node(Lookaround {make_node(word_chars), direction, is_positive});
        };

        Concatenation word_before;
        word_before.terms.push_back(make_lookaround(LookaroundDirection::BACKWARD, true));
        word_before.terms.push_back(make_lookaround(LookaroundDirection::FORWARD, is_negated));

        Concatenation no_word_before;
        no_word_before.terms.push_back(make_lookaround(LookaroundDirection::BACKWARD, false));
        no_word_before.terms.push_back(make_lookaround(LookaroundDirection::FORWARD, !is_negated));

        Alternation boundary;
        boundary.alternatives.push_back(make_node(std::move(word_before)));
        boundary.alternatives.push_back(make_node(std::move(no_word_before)));
        return make_node(std::move(boundary));
    }

    NodeRef make_line_start(const CharSet& line_terminators) {
        // The start of the text or the position after a line terminator, i.e., the position not preceded by any
        // other character
        return make_node(Lookaround {make_node(line_terminators.complement()), LookaroundDirection::BACKWARD, false});
    }

    NodeRef make_line_end(const CharSet& line_terminators) {
        // The end of the text or the position before a line terminator, i.e., the position not followed by any other
        // character
        return make_node(Lookaround {make_node(line_terminators.complement()), LookaroundDirection::FORWARD, false});
    }

    std::string serialize(const Node& node) {
        return std::visit(overloaded {
                              [](const CharSet& chars) -> std::string {
                                  Z3Char ch;
                                  if (chars.is_single(ch)) {
                                      return "(LIT " + serialize_char(ch) + ")";
                                  }
                                  const std::string serialized_chars = chars.serialize();
                                  return serialized_chars.empty() ? "(SET)" : "(SET " + serialized_chars + ")";
                              },
                              [](const Concatenation& concatenation) -> std::string {
                                  std::string res = "(SEQ";
                                  for (const NodeRef& term : concatenation.terms) {
                                      res += " " + serialize(*term);
                                  }
                                  return res + ")";
                              },
                              [](const Alternation& alternation) -> std::string {
                                  std::string res = "(DISJ";
                                  for (const NodeRef& alternative : alternation.alternatives) {
                                      res += " " + serialize(*alternative);
                                  }
                                  return res + ")";
                              },
                              [](const Repetition& repetition) -> std::string {
                                  const std::string max_str =
                                      (repetition.max == UNBOUNDED) ? "inf" : std::to_string(repetition.max);
                                  return "(QUANT {" + std::to_string(repetition.min) + "," + max_str + "} " +
                                         serialize(*repetition.child) + ")";
                              },
                              [](const Capture& capture) -> std::string {
                                  return "(GROUP #" + std::to_string(capture.id) + " " + serialize(*capture.child) +
                                         ")";
                              },
                              [](const Backreference& backref) -> std::string {
                                  return "(BACKREF " + std::to_string(backref.id) + ")";
                              },
                              [](const Lookaround& lookaround) -> std::string {
                                  std::string label;
                                  if (lookaround.direction == LookaroundDirection::FORWARD) {
                                      label = lookaround.is_positive ? "?=" : "?!";
                                  }
                                  else {
                                      label = lookaround.is_positive ? "?<=" : "?<!";
                                  }
                                  return "(ASSERT " + label + " " + serialize(*lookaround.child) + ")";
                              },
                              [](const Anchor anchor) -> std::string {
                                  return (anchor == Anchor::START_OF_TEXT) ? "(ASSERT '^')" : "(ASSERT '$')";
                              },
                          },
                          node.content);
    }

    void collect_backrefs(const Node& node, std::unordered_set<GroupID>& refs) {
        if (const auto* backref = std::get_if<Backreference>(&node.content)) {
            refs.insert(backref->id);
        }
        for_each_child(node, [&](const NodeRef& child) {
            collect_backrefs(*child, refs);
        });
    }

    void collect_capture_groups(const Node& node, std::vector<GroupID>& gids) {
        if (const auto* capture = std::get_if<Capture>(&node.content)) {
            gids.push_back(capture->id);
        }
        for_each_child(node, [&](const NodeRef& child) {
            collect_capture_groups(*child, gids);
        });
    }

    void strip_unreferenced_captures(NodeRef& node, const std::unordered_set<GroupID>& referenced) {
        // The subpattern of a removed group can be an unreferenced group again
        for (auto* capture = std::get_if<Capture>(&node->content);
             capture != nullptr && !referenced.contains(capture->id); capture = std::get_if<Capture>(&node->content)) {
            node = std::move(capture->child);
        }
        for_each_child(*node, [&](NodeRef& child) {
            strip_unreferenced_captures(child, referenced);
        });
    }

    void collect_lookaround_scopes(const Node& node, std::vector<const Lookaround*>& enclosing,
                                   LookaroundScopes& scopes) {
        if (const auto* capture = std::get_if<Capture>(&node.content)) {
            scopes.group_scopes[capture->id] = enclosing;
        }
        else if (const auto* backref = std::get_if<Backreference>(&node.content)) {
            scopes.backref_scopes.emplace_back(backref->id, enclosing);
        }
        else if (const auto* lookaround = std::get_if<Lookaround>(&node.content)) {
            enclosing.push_back(lookaround);
            collect_lookaround_scopes(*lookaround->child, enclosing, scopes);
            enclosing.pop_back();
            return;
        }
        for_each_child(node, [&](const NodeRef& child) {
            collect_lookaround_scopes(*child, enclosing, scopes);
        });
    }

    void check_lookaround_backrefs(const Node& root) {
        std::vector<const Lookaround*> enclosing;
        LookaroundScopes scopes;
        collect_lookaround_scopes(root, enclosing, scopes);

        for (const auto& [gid, backref_scope] : scopes.backref_scopes) {
            if (!scopes.group_scopes.contains(gid) || scopes.group_scopes.at(gid).empty()) {
                continue;
            }
            // Lookarounds enclosing the group are nested in each other, so if the innermost one encloses the
            // backreference, all of them do
            const Lookaround* innermost = scopes.group_scopes.at(gid).back();
            if (std::ranges::find(backref_scope, innermost) == backref_scope.end()) {
                util::throw_error("Unsupported: backreference to a capture group inside a lookaround that does not "
                                  "contain the backreference");
            }
            if (innermost->direction == LookaroundDirection::BACKWARD) {
                util::throw_error("Unsupported: backreference to a capture group inside a lookbehind (lookbehinds "
                                  "are matched from right to left)");
            }
        }
    }
}  // namespace smt::noodler::extended_regex
