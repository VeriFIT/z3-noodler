
#ifndef Z3_INCLUSION_GRAPH_H
#define Z3_INCLUSION_GRAPH_H

#include <optional>
#include <deque>
#include <algorithm>

#include "formula.h"

namespace smt::noodler {

    //----------------------------------------------------------------------------------------------------------------------------------

    class GraphNode {
    public:
        GraphNode() = default;
        explicit GraphNode(const Predicate& predicate) : node_predicate(predicate) {}

        void set_predicate(const Predicate& predicate) { this->node_predicate = predicate; }
        [[nodiscard]] Predicate& get_predicate() { return node_predicate; }
        [[nodiscard]] const Predicate& get_predicate() const { return node_predicate; }

        struct HashFunction {
            size_t operator()(const GraphNode& graph_node) const {
                return Predicate::HashFunction()(graph_node.node_predicate);
            }
        };

        [[nodiscard]] bool equals(const GraphNode& other) const {
            return this->node_predicate.strong_equals(other.node_predicate);
        }

    private:
        Predicate node_predicate;

        // TODO: Add additional attributes such as cost, etc.
    }; // Class GraphNode.

    static bool operator==(const GraphNode& lhs, const GraphNode& rhs) { return lhs.equals(rhs); }
    static bool operator!=(const GraphNode& lhs, const GraphNode& rhs) { return !(lhs == rhs); }
    static bool operator<(const GraphNode& lhs, const GraphNode& rhs) {
        if (lhs.get_predicate() < rhs.get_predicate()) {
            return true;
        }
        return false;
    }
    static bool operator>(const GraphNode& lhs, const GraphNode& rhs) { return !(lhs < rhs); }

    //----------------------------------------------------------------------------------------------------------------------------------


    class Graph {
    public:
        using Nodes = std::unordered_set<std::shared_ptr<GraphNode>>;
        using Edges = std::unordered_map<std::shared_ptr<GraphNode>, Nodes>;
    private:
        Nodes nodes;
        Edges edges;
        Edges inverse_edges;
        static const Nodes empty_nodes;
        // set of nodes that are NOT on some cycle
        // it is guaranteed to be correct ONLY after creating inclusion graph???
        std::unordered_set<std::shared_ptr<GraphNode>> nodes_not_on_cycle;

        void remove_edge_from_edges(std::shared_ptr<GraphNode> source, std::shared_ptr<GraphNode> target) {
            if (edges.count(source) == 0) {
                return;
            }

            Nodes &source_edges = edges.at(source);
            source_edges.erase(target);
            if (source_edges.empty()) {
                edges.erase(source);
            }
        }

        void remove_edge_from_inverse_edges(std::shared_ptr<GraphNode> source, std::shared_ptr<GraphNode> target) {
            if (inverse_edges.count(target) == 0) {
                return;
            }

            Nodes &target_edges = inverse_edges.at(target);
            target_edges.erase(source);
            if (target_edges.empty()) {
                inverse_edges.erase(target);
            }
        }

    public:

        const Nodes& get_nodes() const { return nodes; }

        void add_edge(std::shared_ptr<GraphNode> source, std::shared_ptr<GraphNode> target) {
            edges[source].insert(target);
            inverse_edges[target].insert(source);
        }

        void remove_edge(std::shared_ptr<GraphNode> source, std::shared_ptr<GraphNode> target) {
            remove_edge_from_edges(source, target);
            remove_edge_from_inverse_edges(source, target);
        }

        void remove_edges_from(std::shared_ptr<GraphNode> source) {
            for (const auto &target : edges[source]) {
                remove_edge_from_inverse_edges(source, target);
            }
            edges.erase(source);
        }

        void remove_edges_to(std::shared_ptr<GraphNode> target) {
            for (auto& source: get_edges_to(target)) {
                remove_edge_from_edges(source, target);
            }
            inverse_edges.erase(target);
        }

        void remove_edges_with(std::shared_ptr<GraphNode> node) {
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

        const Nodes& get_edges_from(std::shared_ptr<GraphNode> source) {
            if (edges.count(source) != 0) {
                return edges.at(source);
            } else {
                return empty_nodes;
            }
        }

        const Nodes& get_edges_to(std::shared_ptr<GraphNode> target) const {
            if (inverse_edges.count(target) != 0) {
                return inverse_edges.at(target);
            } else {
                return empty_nodes;
            }
        }

        std::shared_ptr<GraphNode> get_node(const Predicate& predicate) {
            auto node = std::find_if(nodes.begin(), nodes.end(), [&predicate](const std::shared_ptr<GraphNode> &el){ return (el->get_predicate().strong_equals(predicate));});
            if (node == nodes.end()) { return nullptr; }
            return *node;
        }

        /**
         * @brief adds node with predicate to graph (even if a node with such predicate exists in graph)
         *
         * @return the newly added node
         */
        std::shared_ptr<GraphNode> add_node(const Predicate& predicate) {
            // TODO check if added node already does not exists??? by calling get_node?
            std::shared_ptr<GraphNode> new_node = std::make_shared<GraphNode>(predicate);
            nodes.insert(new_node);
            return new_node;
        }

        /**
         * @brief adds node with predicate to graph (even if a node with such predicate exists in graph)
         *
         * @return the newly added node
         */
        std::shared_ptr<GraphNode> add_node(const std::vector<BasicTerm> &left_side, const std::vector<BasicTerm> &right_side) {
            return add_node(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>> {left_side, right_side}));
        }

        void remove_node(const std::shared_ptr<GraphNode> node) {
            remove_edges_with(node);
            nodes.erase(node);
        }

        bool is_on_cycle(const std::shared_ptr<GraphNode> &node) {
            assert(nodes.count(node) > 0);
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

        void set_is_on_cycle(const std::shared_ptr<GraphNode> &node, bool is_on_cycle) {
            assert(nodes.count(node) > 0);
            if (!is_on_cycle) {
                nodes_not_on_cycle.insert(node);
            }
        }

        // adds edges so that inclusions x and y where left side of x shares variable with right side of y have edge from x to y
        void add_inclusion_graph_edges();

        // makes a deep copy of the garph, i.e. returned graph is semantically same as this graph, but the pointers to nodes are different
        Graph deep_copy() const;
        // node_mapping - maps pointers of this graph into pointers of the returned graph (i.e. the same inclusion is mapped to the same inclusion)
        Graph deep_copy(std::unordered_map<std::shared_ptr<GraphNode>, std::shared_ptr<GraphNode>> &node_mapping) const;

        // all these assume that formula does not contain same equalities
        static Graph create_inclusion_graph(const Formula& formula);
        static Graph create_inclusion_graph(const Formula& formula, std::deque<std::shared_ptr<GraphNode>> &out_node_order);
        static Graph create_simplified_splitting_graph(const Formula& formula);
        static Graph create_inclusion_graph(Graph& simplified_splitting_graph, std::deque<std::shared_ptr<GraphNode>> &out_node_order);

        /**
         * Print the inclusion graph in a DOT format.
         * @param output_stream Stream to print the graph to.
         */
        void print_to_dot(std::ostream &output_stream) const;
    }; // Class Graph.
}


#endif //Z3_INCLUSION_GRAPH_H
