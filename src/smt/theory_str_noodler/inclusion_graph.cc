#include "inclusion_graph.h"
#include "util.h"

namespace {
    using namespace smt::noodler;

    bool have_same_var(const std::vector<BasicTerm>& first_side, const std::vector<BasicTerm>& second_side) {
        for (const auto& first_side_term: first_side) {
            if (first_side_term.is_variable()) {
                for (const auto& second_side_term: second_side) {
                    if (first_side_term == second_side_term) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    bool have_some_var_twice(const std::vector<BasicTerm>& v) {
        std::set<BasicTerm> vars_in_v;
        for (const BasicTerm& var : v) {
            if (var.is_variable()) {
                if (vars_in_v.contains(var)) {
                    return true;
                }
                vars_in_v.insert(var);
            }
        }
        return false;
    }

} // Anonymous namespace.

const smt::noodler::FormulaGraph::NodeSet smt::noodler::FormulaGraph::empty_nodes = smt::noodler::FormulaGraph::NodeSet();

void smt::noodler::FormulaGraph::add_inclusion_graph_edges() {
    for (auto& source_node: get_nodes() ) {
        for (auto& target_node: get_nodes()) {
            if (source_node == target_node) { // we do not want self-loops (difference from FM'23)
                continue;
            }

            if (have_same_var(source_node.get_real_left_side(), target_node.get_real_right_side())) {
                // Have same var, automatically add a new edge.
                add_edge(source_node, target_node);
            }
        }
    }
}

FormulaGraph smt::noodler::FormulaGraph::create_inclusion_graph(const Formula& formula, std::unordered_set<BasicTerm> length_vars) {
    FormulaGraph splitting_graph{ create_simplified_splitting_graph(formula) };
    return create_inclusion_graph(splitting_graph, length_vars);
}

FormulaGraph smt::noodler::FormulaGraph::create_simplified_splitting_graph(const Formula& formula) {
    FormulaGraph graph;

    // Add all nodes which are not already present in direct and switched form.
    for (const auto& predicate: formula.get_predicates()) {
        // we skip trivial equations of the form x = x
        if(predicate.is_equation() && predicate.get_left_side() == predicate.get_right_side()) {
            continue;
        }
        graph.add_node(predicate, false);
        graph.add_node(predicate, true);
    }

    if (graph.nodes.empty()) {
        return FormulaGraph{};
    }

    for (const FormulaGraphNode &source_node: graph.get_nodes() ) {
        for (const FormulaGraphNode &target_node: graph.get_nodes()) {
            // we want to add edge whenever the left side of source contains some variable of right side of target
            // however, if the two nodes are created from the same predicate, just in reversed form
            // we need to have two different "occurrences" of the same var, so we just check
            // if one of the two sides (which should be equal) contain some variable twice
            if (have_same_var(source_node.get_real_left_side(), target_node.get_real_right_side())
                && !(target_node.is_reverse_of(source_node) && !have_some_var_twice(source_node.get_real_left_side())))
            {
                    graph.add_edge(source_node, target_node);
            }
        }
    }

    return graph;
}

FormulaGraph smt::noodler::FormulaGraph::create_inclusion_graph(FormulaGraph& simplified_splitting_graph, std::unordered_set<BasicTerm> length_vars) {
    FormulaGraph inclusion_graph{};

    NodeSet erased_nodes;
    while (true) {
        std::map<FormulaGraphNode, unsigned> init_nodes_with_score;

        for (const FormulaGraphNode& node: simplified_splitting_graph.get_nodes()) {
            if (!erased_nodes.contains(node) && simplified_splitting_graph.inverse_edges[node].empty()) { // if node is initial (has no transitions going into it)
                unsigned num_of_splits_on_left = node.get_real_left_side().size();
                unsigned num_of_splits_on_right = 0;
                bool last_was_length = true;
                for (const BasicTerm& right_var : node.get_real_right_side()) {
                    if (length_vars.contains(right_var)) {
                        ++num_of_splits_on_right;
                        last_was_length = true;
                    } else {
                        if (last_was_length) {
                            ++num_of_splits_on_right;
                        }
                        last_was_length = false;
                    }
                }
                init_nodes_with_score[node] = num_of_splits_on_left*num_of_splits_on_right;
            }
        }

        if (init_nodes_with_score.empty()) {
            // there is no initial node anymore
            break;
        }

        auto best_score_it = init_nodes_with_score.begin();
        for (auto it = init_nodes_with_score.begin(); it != init_nodes_with_score.end(); ++it) {
            if (it->second > best_score_it->second) { //score of this node is better
                best_score_it = it;
            }
        }

        const FormulaGraphNode& best_initial_node = best_score_it->first;
        inclusion_graph.nodes.push_back(best_initial_node);
        STRACE("str", tout << "Added node " << best_initial_node.print() << " to the graph without the reversed inclusion." << std::endl;);
        SCTRACE("str-nfa", best_initial_node.get_predicate().is_transducer(), tout << "Transducer T" << best_initial_node.get_predicate().get_transducer() << ":\n" << best_initial_node.get_predicate().get_transducer()->print_to_dot(true););
        inclusion_graph.nodes_not_on_cycle.insert(best_initial_node); // the inserted node cannot be on the cycle, because it is either initial or all nodes leading to it were not on cycle

        FormulaGraphNode reversed_node{ best_initial_node.get_reversed() };

        // Remove edges of node and switched node.
        erased_nodes.insert(best_initial_node);
        simplified_splitting_graph.remove_edges_with(best_initial_node);
        erased_nodes.insert(reversed_node);
        simplified_splitting_graph.remove_edges_with(reversed_node);

    }

    // we add rest of the nodes (the ones on the cycles) to the inclusion graph
    for (auto& node: simplified_splitting_graph.get_nodes()) {
        if (!erased_nodes.contains(node)) {
            inclusion_graph.nodes.push_back(node);
            STRACE("str", tout << "Added node " << node.print() << " to the graph with its reversed inclusion." << std::endl;);
            SCTRACE("str-nfa", node.get_predicate().is_transducer(), tout << "Transducer T" << node.get_predicate().get_transducer() << ":\n" << *node.get_predicate().get_transducer(););
        }
    }

    inclusion_graph.add_inclusion_graph_edges();

    return inclusion_graph;
}

void FormulaGraph::print_to_dot(std::ostream &output_stream) const {
    auto escape_quotes = [](const std::string& s) {
        std::string escaped;
        for (char c : s) {
            if (c == '"')
                escaped += "\\\"";
            else
                escaped += c;
        }
        return escaped;
    };
    output_stream << "digraph inclusionGraph {\nnode [shape=none];\n";
    for (const FormulaGraphNode& node : nodes) {
        output_stream << "\"" << escape_quotes(node.print()) << "\" -> {";
        for (const FormulaGraphNode& target : get_edges_from(node)) {
            output_stream << "\"" << escape_quotes(target.print()) << "\" ";
        }
        output_stream << "} [label=\"\"]\n";
    }
    output_stream << "}" << std::endl;
}
