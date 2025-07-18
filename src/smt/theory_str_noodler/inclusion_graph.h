
#ifndef Z3_INCLUSION_GRAPH_H
#define Z3_INCLUSION_GRAPH_H

#include <optional>
#include <deque>
#include <algorithm>

#include "formula.h"

namespace smt::noodler {

    //----------------------------------------------------------------------------------------------------------------------------------

    class FormulaGraphNode {
    public:
        FormulaGraphNode() = delete;
        explicit FormulaGraphNode(Predicate predicate, bool is_reversed = false) : node_predicate(predicate), reversed(is_reversed) {
            SASSERT(predicate.is_transducer() || predicate.is_equation());
        }

        /**
         * @brief Get the predicate of this node (without reversing)
         */
        [[nodiscard]] const Predicate& get_predicate() const { return node_predicate; }

        /**
         * @brief Get the "real" predicate represented by this node, taking into account whether it is reversed
         */
        [[nodiscard]] Predicate get_real_predicate() const {
            if (!is_reversed()) {
                return node_predicate;
            } else {
                return node_predicate.get_switched_sides_predicate();
            }
        }
        [[nodiscard]] bool is_reversed() const { return reversed; }

        /**
         * @brief Get the "real" left side of this node, taking into account whether it is reversed
         */
        [[nodiscard]] const std::vector<BasicTerm>& get_real_left_side() const {
            if (node_predicate.is_transducer()) {
                // for trasnducer, left side is output
                if (!is_reversed()) {
                    return node_predicate.get_output();
                } else {
                    return node_predicate.get_input();
                }
            } else {
                // for inclusions, left side is left side
                if (!is_reversed()) {
                    return node_predicate.get_left_side();
                } else {
                    return node_predicate.get_right_side();
                }
            }
        }

        /**
         * @brief Get the "real" right side of this node, taking into account whether it is reversed
         */
        [[nodiscard]] const std::vector<BasicTerm>& get_real_right_side() const {
            if (node_predicate.is_transducer()) {
                // for predicate, right side is input
                if (!is_reversed()) {
                    return node_predicate.get_input();
                } else {
                    return node_predicate.get_output();
                }
            } else  {
                // for inclusions, right side is right side
                if (!is_reversed()) {
                    return node_predicate.get_right_side();
                } else {
                    return node_predicate.get_left_side();
                }
            }
        }

        /**
         * @brief Checks if this node is reversion of @p other node
         */
        [[nodiscard]] bool is_reverse_of(const FormulaGraphNode& other) const {
            return (node_predicate == other.node_predicate && reversed != other.reversed);
        }

        /**
         * @brief Get the reversed node of this node
         */
        [[nodiscard]] FormulaGraphNode get_reversed() const {
            return FormulaGraphNode(get_predicate(), !reversed);
        }

        [[nodiscard]] std::string print() const {
            std::ostringstream output;
            output << get_real_left_side();
            if (node_predicate.is_equation()) {
                // inclusion
                output << " ⊆ " << get_real_right_side();
            } else {
                //transducer, we name them based on the raw pointer
                output << " = T" << node_predicate.get_transducer().get();
                if (is_reversed()) {
                    output << "^-1";
                }
                output << "(" << get_real_right_side() << ")";
            }
            return output.str();
        }

        auto operator<=>(const FormulaGraphNode& other) const = default;

    private:
        Predicate node_predicate;
        bool reversed = false;
    }; // Class FormulaGraphNode.

    class FormulaGraph {
    public:
        using Nodes = std::vector<FormulaGraphNode>;
        using NodeSet = std::set<FormulaGraphNode>;
        using Edges = std::map<FormulaGraphNode,NodeSet>;
    private:
        Nodes nodes;
        Edges edges;
        Edges inverse_edges;
        static const NodeSet empty_nodes;
        // set of nodes that are NOT on some cycle
        // it is guaranteed to be correct ONLY after creating inclusion graph???
        NodeSet nodes_not_on_cycle;

    public:

        const Nodes& get_nodes() const { return nodes; }

        bool contains_node(const FormulaGraphNode& node) const {
            for (const FormulaGraphNode& node_of_graph : nodes) {
                if (node == node_of_graph) {
                    return true;
                }
            }
            return false;
        }

        void add_edge(const FormulaGraphNode& source, const FormulaGraphNode& target) {
            edges[source].insert(target);
            inverse_edges[target].insert(source);
        }

        void remove_edge(const FormulaGraphNode& source, const FormulaGraphNode& target) {
            edges[source].erase(target);
            inverse_edges[target].erase(source);
        }

        void remove_edges_from(const FormulaGraphNode& source) {
            for (const FormulaGraphNode& target : get_edges_from(source)) {
                inverse_edges[target].erase(source);
            }
            edges.erase(source);
        }

        void remove_edges_to(const FormulaGraphNode& target) {
            for (const FormulaGraphNode& source : get_edges_to(target)) {
                edges[source].erase(target);
            }
            inverse_edges.erase(target);
        }

        void remove_edges_with(const FormulaGraphNode& node) {
            remove_edges_from(node);
            remove_edges_to(node);
        }

        void remove_all_edges() {
            edges.clear();
            inverse_edges.clear();
        }

        size_t get_num_of_edges() const {
            size_t num_of_edges{ 0 };
            for (const auto& edge_set: edges) {
                num_of_edges += edge_set.second.size();
            }
            return num_of_edges;
        }

        const Edges& get_edges() const { return edges; }

        const NodeSet& get_edges_from(const FormulaGraphNode& source) const {
            SASSERT(contains_node(source));
            if (edges.contains(source)) {
                return edges.at(source);
            } else {
                return empty_nodes;
            }
        }

        const NodeSet& get_edges_to(const FormulaGraphNode& target) const {
            SASSERT(contains_node(target));
            if (inverse_edges.contains(target)) {
                return inverse_edges.at(target);
            } else {
                return empty_nodes;
            }
        }

        /**
         * @brief Adds node with @p predicate to graph (even if a node with such predicate exists in graph).
         * 
         * @return The node that was added 
         */
        const FormulaGraphNode& add_node(const Predicate& predicate, bool is_reversed = false) {
            nodes.push_back(FormulaGraphNode(predicate, is_reversed));
            return nodes.back();
        }

        /**
         * @brief Removes node from the graph
         * 
         * Invalidates iterator in nodes.
         */
        void remove_node(const FormulaGraphNode& node) {
            remove_edges_with(node);
            for (auto iter = nodes.begin(); iter != nodes.end(); ++iter) {
                if (*iter == node) {
                    nodes.erase(iter);
                    return;
                }
            }
        }

        bool is_on_cycle(const FormulaGraphNode& node) const {
            SASSERT(contains_node(node));
            return (nodes_not_on_cycle.count(node) == 0);
        }

        /**
         * @brief Check if the inclusion graph is cyclic.
         * 
         * @return true <-> the inclusion graph contains a cycle.
         */
        bool is_cyclic() const {
            return this->nodes.size() != this->nodes_not_on_cycle.size();
        }

        void set_is_on_cycle(const FormulaGraphNode& node, bool is_on_cycle) {
            SASSERT(contains_node(node));
            if (!is_on_cycle) {
                nodes_not_on_cycle.insert(node);
            }
        }

        // adds edges so that inclusions x and y where left side of x shares variable with right side of y have edge from x to y
        void add_inclusion_graph_edges();

        /**
         * @brief Create a simplified splitting graph for @p formula
         * 
         * The set of nodes will have the same order as the predicates in the formula
         * where reversed node will always follow the normal one.
         * 
         * Assumes that formula does not contain same equalities (with swapped sides).
         * 
          * @param formula must contain only equations and transducers
          * @return splitting graph
          */
        static FormulaGraph create_simplified_splitting_graph(const Formula& formula);

        /**
         * @brief Create an inclusion graph from splitting graph
         */
        static FormulaGraph create_inclusion_graph(FormulaGraph& simplified_splitting_graph);


        /**
         * @brief Create an inclusion graph for @p formula
         * 
         * The set of nodes will be ordered compatible with the topological
         * order of the strongly connected components.
         * 
         * Assumes that formula does not contain same equalities (with swapped sides).
         * 
         * @param formula must contain only equations and transducers
         * @return the inclusion graph 
         */
        static FormulaGraph create_inclusion_graph(const Formula& formula);

        /**
         * Print the inclusion graph in a DOT format.
         * @param output_stream Stream to print the graph to.
         */
        void print_to_dot(std::ostream &output_stream) const;
    }; // Class FormulaGraph.
}


#endif //Z3_INCLUSION_GRAPH_H
