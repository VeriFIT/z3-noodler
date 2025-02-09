#include "inclusion_graph.h"
#include "util.h"

namespace {
    using namespace smt::noodler;

    bool have_same_var(const std::vector<BasicTerm>& first_side, const std::vector<BasicTerm>& second_side) {
        for (const auto& first_side_term: first_side) {
            for (const auto& second_side_term: second_side) {
                if (first_side_term == second_side_term) {
                    if (first_side_term.is_variable()) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /**
     * Convert graph node into string representation.
     * @param node Node to convert.
     * @return String representation of @p node.
     */
    std::string conv_node_to_string(const std::shared_ptr<GraphNode>& node) {
        auto& predicate{ node->get_predicate() };
        std::string result{};
        switch (predicate.get_type()) {
            case PredicateType::NotContains: {
                util::throw_error("Decision procedure can handle only equations and disequations");
            }
            // TODO: handle transducers
            case PredicateType::Equation:
            case PredicateType::Inequation: {
                std::string left_side{};
                for (auto& item : predicate.get_left_side()) {
                    if (!left_side.empty()) { left_side += " "; }
                    left_side += item.to_string();
                }

                std::string right_side{};
                for (auto& item : predicate.get_right_side()) {
                    if (!right_side.empty()) { right_side += " "; }
                    right_side += item.to_string();
                }
                result = left_side;
                if (predicate.get_type() == PredicateType::Inequation) {
                    result += " !";
                } else {
                    result += " ";
                }
                result += "<= ";
                result += right_side;
                break;
            }
        }
        return result;
    }
} // Anonymous namespace.

const smt::noodler::Graph::Nodes smt::noodler::Graph::empty_nodes = smt::noodler::Graph::Nodes();

Graph smt::noodler::Graph::deep_copy() const {
    std::unordered_map<std::shared_ptr<GraphNode>, std::shared_ptr<GraphNode>> node_mapping;
    return deep_copy(node_mapping);
}

Graph smt::noodler::Graph::deep_copy(std::unordered_map<std::shared_ptr<GraphNode>, std::shared_ptr<GraphNode>> &node_mapping) const {
    Graph new_graph;

    for (const auto &this_node : get_nodes()) {
        node_mapping[this_node] = new_graph.add_node(this_node->get_predicate());
    }

    for (const auto &edge : get_edges()) {
        const auto &source = edge.first;
        for (const auto &target : edge.second) {
            new_graph.add_edge(node_mapping[source], node_mapping[target]);
        }
    }

    for (const auto &node_not_on_cycle : nodes_not_on_cycle) {
        if (get_nodes().count(node_not_on_cycle) > 0) {
            new_graph.nodes_not_on_cycle.insert(node_mapping.at(node_not_on_cycle));
        }
    }

    return new_graph;
}

void smt::noodler::Graph::add_inclusion_graph_edges() {
    for (auto& source_node: get_nodes() ) {
        for (auto& target_node: get_nodes()) {
            if (source_node == target_node) { // we do not want self-loops (difference from FM'23)
                continue;
            }

            auto& source_predicate{ source_node->get_predicate() };
            auto& target_predicate{ target_node->get_predicate() };
            auto& source_left_side{ source_predicate.get_left_side() };
            auto& target_right_side{ target_predicate.get_right_side() };

            if (have_same_var(source_left_side, target_right_side)) {
                // Have same var, automatically add a new edge.
                add_edge(source_node, target_node);
            }
        }
    }
}

void smt::noodler::Graph::substitute_vars(const std::unordered_map<BasicTerm, std::vector<BasicTerm>> &substitution_map, std::unordered_set<std::shared_ptr<GraphNode>> &out_deleted_nodes) {
    auto substitute_vector = [&substitution_map](std::vector<BasicTerm> &vector) {
        std::vector<BasicTerm> result;
        for (const BasicTerm &var : vector) {
            if (substitution_map.count(var) == 0) {
                result.push_back(var);
            } else {
                const auto &to_this = substitution_map.at(var);
                result.insert(result.end(), to_this.begin(), to_this.end());
            }
        }
        return result;
    };

    for (std::shared_ptr<GraphNode> node : get_nodes()) {
        Predicate &node_predicate = node->get_predicate();
        std::vector<BasicTerm> new_left_side = substitute_vector(node_predicate.get_left_side());
        std::vector<BasicTerm> new_right_side = substitute_vector(node_predicate.get_right_side());
        node_predicate.set_left_side(std::move(new_left_side));
        node_predicate.set_right_side(std::move(new_right_side));
    }

    // merge same nodes and delete nodes with the same right and left side
    std::set<GraphNode> unique_nodes;
    for (const auto &node : get_nodes()) {
        if (node->get_predicate().get_left_side() == node->get_predicate().get_right_side()) {
            out_deleted_nodes.insert(node);
        }

        if (unique_nodes.count(*node) == 0) {
            unique_nodes.insert(*node);
        } else {
            out_deleted_nodes.insert(node);
        }
    }
    for (const auto &node : out_deleted_nodes) {
        nodes.erase(node);
    }
}

Graph smt::noodler::Graph::create_inclusion_graph(const Formula& formula, std::deque<std::shared_ptr<GraphNode>> &out_node_order) {
    Graph splitting_graph{ create_simplified_splitting_graph(formula) };
    return create_inclusion_graph(splitting_graph, out_node_order);
}

Graph smt::noodler::Graph::create_simplified_splitting_graph(const Formula& formula) {
    Graph graph;

    // Add all nodes which are not already present in direct and switched form.
    for (const auto& predicate: formula.get_predicates()) {
        // we skip trivial equations of the form x = x
        if(predicate.get_left_side() == predicate.get_right_side()) {
            continue;
        }
        graph.add_node(predicate);
        graph.add_node(predicate.get_switched_sides_predicate());
    }

    if (graph.nodes.empty()) {
        return Graph{};
    }

    for (auto &source_node: graph.get_nodes() ) {
        for (auto &target_node: graph.get_nodes()) {
            auto& source_predicate{ source_node->get_predicate() };
            auto& target_predicate{ target_node->get_predicate() };
            auto& source_left_side{ source_predicate.get_left_side() };
            auto& source_right_side{ source_predicate.get_right_side() };
            auto& target_left_side{ target_predicate.get_left_side() };
            auto& target_right_side{ target_predicate.get_right_side() };

            if (!have_same_var(source_left_side, target_right_side)) {
                continue;
            } else if (source_left_side == target_right_side) {
                // Have same var and sides are equal.

                if (source_right_side == target_left_side) { // In the same equation.
                    if (!source_predicate.mult_occurr_var_side(Predicate::EquationSideType::Left)) {
                        // Does not have multiple occurrences of one var. Hence, cannot have an edge.
                        continue;
                    }
                } else {
                    // In different equation.
                }
            } else {
                // Have same var and sides are not equal, automatically add a new edge.
            }

            graph.add_edge(source_node, target_node);
        }
    }

    return graph;
}

Graph smt::noodler::Graph::create_inclusion_graph(const Formula& formula) {
    std::deque<std::shared_ptr<GraphNode>> out_node_order;
    return create_inclusion_graph(formula, out_node_order);
}

Graph smt::noodler::Graph::create_inclusion_graph(Graph& simplified_splitting_graph, std::deque<std::shared_ptr<GraphNode>> &out_node_order) {
    Graph inclusion_graph{};

    bool splitting_graph_changed{ true };
    while(splitting_graph_changed) {
        splitting_graph_changed = false;

        for (auto& node: simplified_splitting_graph.get_nodes()) {
            if (simplified_splitting_graph.inverse_edges.count(node) == 0) {
                inclusion_graph.nodes.insert(node);
                STRACE("str", tout << "Added node " << node->get_predicate() << " to the graph without the reversed inclusion." << std::endl;);
                inclusion_graph.nodes_not_on_cycle.insert(node); // the inserted node cannot be on the cycle, because it is either initial or all nodes leading to it were not on cycle

                out_node_order.push_back(node);

                auto switched_node{ simplified_splitting_graph.get_node(node->get_predicate().get_switched_sides_predicate()) };

                // Remove edges of node and switched node.
                simplified_splitting_graph.remove_edges_with(node);
                simplified_splitting_graph.remove_edges_with(switched_node);

                // we can erase nodes, because we are breaking from the for loop (so no problem with invalidating iterators)
                simplified_splitting_graph.nodes.erase(node);
                simplified_splitting_graph.nodes.erase(switched_node);

                splitting_graph_changed = true;
                break;
            }
        }
    }

    // we add rest of the nodes (the ones on the cycle) to the inclusion graph
    for (auto& node: simplified_splitting_graph.get_nodes()) {
        out_node_order.push_back(node);
        STRACE("str", tout << "Added node " << node->get_predicate() << " to the graph with its reversed inclusion." << std::endl;);
    }
    inclusion_graph.nodes.merge(simplified_splitting_graph.nodes);

    inclusion_graph.add_inclusion_graph_edges();

    return inclusion_graph;
}

void Graph::print_to_dot(std::ostream &output_stream) const {
    output_stream << "digraph inclusionGraph {\nnode [shape=none];\n";
    for (const auto& edge : edges) {
        output_stream << "\"" << conv_node_to_string(edge.first) << "\" -> {";
        for (const auto& target : edge.second) {
            output_stream << "\"" << conv_node_to_string(target) << "\" ";
        }
        output_stream << "} [label=\"\"]\n";
    }
    output_stream << "}" << std::endl;
}
