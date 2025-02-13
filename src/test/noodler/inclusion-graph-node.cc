#include <iostream>

#include <catch2/catch_test_macros.hpp>
#include <mata/nfa/nfa.hh>
#include <mata/nft/nft.hh>

#include "smt/theory_str_noodler/inclusion_graph.h"

using namespace smt::noodler;

bool graph_nodes_are_equal_to(const Graph::Nodes &graph_nodes, const std::set<GraphNode> &nodes_to_compare) {
    std::set<GraphNode> graph_nodes_set;
    for (const auto &node : graph_nodes) {
        graph_nodes_set.insert(*node);
    }
    return graph_nodes_set == nodes_to_compare;
}

TEST_CASE( "Inclusion graph node", "[noodler]" ) {
    auto predicate{ Predicate(PredicateType::Equation) };
    auto predicate_ineq{ Predicate(PredicateType::Inequation) };
    CHECK(predicate.get_type() == PredicateType::Equation);

    constexpr auto term_name{ "x_1" };
    auto term{ BasicTerm(BasicTermType::Variable, term_name) };
    CHECK(term.get_name() == term_name);

    auto& left{ predicate.get_left_side() };
    left.emplace_back(term);
    left.emplace_back( BasicTermType::Literal, "lit" );
    left.emplace_back(term);
    CHECK(predicate.mult_occurr_var_side(Predicate::EquationSideType::Left));

    auto& left_alt{ predicate.get_side(Predicate::EquationSideType::Left) };
    CHECK(left == left_alt);

    CHECK(predicate.is_eq_or_ineq());
    CHECK(predicate.get_side_vars(Predicate::EquationSideType::Left) == std::set<BasicTerm>{ term });
    CHECK(predicate.get_side_vars(Predicate::EquationSideType::Right).empty());

    CHECK(predicate != predicate_ineq);

    BasicTerm term_lit{ BasicTermType::Literal, "3"};
    BasicTerm term_lit2{ BasicTermType::Literal, "5"};
    BasicTerm term_var{ BasicTermType::Variable, "4"};
    BasicTerm term_var2{ BasicTermType::Variable, "6"};
    CHECK(term_lit < term_lit2);
    CHECK(term_lit2 > term_lit);
    CHECK(term_var < term_lit2);
    CHECK(term_var < term_lit);
    CHECK(term_var < term_var2);
    CHECK(term_var2 > term_var);
    CHECK(term_var == term_var);
    CHECK(term_var2 < term_lit);
    CHECK(term_var2 < term_lit2);
    CHECK(term != term_var);
}

TEST_CASE("Conversion to strings", "[noodler]") {
    CHECK(smt::noodler::to_string(BasicTermType::Literal) == "Literal");
    CHECK(smt::noodler::to_string(BasicTermType::Variable) == "Variable");
    CHECK(BasicTerm{ BasicTermType::Literal }.to_string() == "\"\"");
    CHECK(BasicTerm{ BasicTermType::Literal, "4" }.to_string() == "\"4\"");
    CHECK(BasicTerm{ BasicTermType::Variable, "x_42" }.to_string() == "x_42");

    auto pred{ Predicate{ PredicateType::Equation, {
        { { BasicTermType::Literal, "4" }, { BasicTermType::Variable, "x_42" } } ,
        { { BasicTermType::Variable, "xyz" }, { BasicTermType::Variable, "y_58" } },
    } } };

    CHECK(pred.to_string() == "Equation: \"4\" x_42 = xyz y_58");

    auto pred_ineq{ Predicate{ PredicateType::Inequation, {
            { { BasicTermType::Literal, "4" }, { BasicTermType::Variable, "x_42" } } ,
            { { BasicTermType::Variable, "xyz" }, { BasicTermType::Variable, "y_58" } },
    } } };

    CHECK(pred_ineq.to_string() == "Inequation: \"4\" x_42 != xyz y_58");

    CHECK(pred_ineq.get_vars() == std::set{
          BasicTerm{ BasicTermType::Variable, "x_42" },
          BasicTerm{ BasicTermType::Variable, "xyz" },
          BasicTerm{ BasicTermType::Variable, "y_58" }
    } );
}

TEST_CASE("Mata integration", "[noodler]") {
    auto nfa = mata::nfa::Nfa(3);
    nfa.initial = { 0, 1};
    nfa.final = { 3, 1};
    nfa.delta.add(0, 42, 1);
    nfa.delta.add(1, 42, 2);
    CHECK(nfa.final[1]);
    CHECK(!nfa.final[0]);
    CHECK(nfa.delta.contains(0, 42, 1));
    CHECK(!nfa.delta.contains(1, 42, 1));
    CHECK(!nfa.delta.empty());
}

TEST_CASE("Graph::get_edges_to", "[noodler]") {
    Graph graph;
    Formula formula;
    BasicTerm x{ BasicTermType::Variable, "x" };
    BasicTerm y{ BasicTermType::Variable, "y" };
    Predicate predicate{ PredicateType::Equation, { { x }, { x, y } } };
    Predicate predicate2{ PredicateType::Equation, { { x, y }, { y, x } } };

    formula.add_predicate(predicate);
    formula.add_predicate(predicate2);
    graph = Graph::create_simplified_splitting_graph(formula);
    auto target{ graph.get_node(predicate) };
    REQUIRE(target != nullptr);
    auto edges_to_target{ graph.get_edges_to(target) };
    REQUIRE(graph.get_node(predicate) != nullptr);
    CHECK(edges_to_target.find(graph.get_node(predicate)) != edges_to_target.end());
    REQUIRE(graph.get_node(predicate2) != nullptr);
    CHECK(edges_to_target.find(graph.get_node(predicate2)) != edges_to_target.end());
    REQUIRE(graph.get_node(predicate2.get_switched_sides_predicate()) != nullptr);
    CHECK(edges_to_target.find(graph.get_node(predicate2.get_switched_sides_predicate())) != edges_to_target.end());
}

TEST_CASE("Inclusion graph", "[noodler]") {
    Graph graph;
    Formula formula;

    BasicTerm u{ BasicTermType::Variable, "u" };
    BasicTerm v{ BasicTermType::Variable, "v" };
    BasicTerm x{ BasicTermType::Variable, "x" };
    BasicTerm y{ BasicTermType::Variable, "y" };
    BasicTerm z{ BasicTermType::Variable, "z" };

    SECTION("u = z && v = u && x = uvx") {
        Predicate predicate{ PredicateType::Equation, { { u }, { z } } };
        Predicate predicate2{ PredicateType::Equation, { { v }, { u } } };
        Predicate predicate3{ PredicateType::Equation, { { x }, { u, v, x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        formula.add_predicate(predicate3);
        graph = Graph::create_inclusion_graph(formula);
        CHECK(graph.get_nodes().size() == 5);
        CHECK(graph.get_edges().size() == 5);
        CHECK(graph.get_num_of_edges() == 10);
    }

    SECTION("x = xy && xy = yx") {
        Predicate predicate{ PredicateType::Equation, { { x }, { x, y } } };
        Predicate predicate2{ PredicateType::Equation, { { x, y }, { y, x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = Graph::create_inclusion_graph(formula);
        CHECK(graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
                GraphNode{ predicate2 }, GraphNode{ predicate2.get_switched_sides_predicate() },
        }));
        CHECK(graph.get_edges().size() == 4);
        CHECK(graph.get_num_of_edges() == 12);
    }

    SECTION("x = yx") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y, x } } };

        formula.add_predicate(predicate);
        graph = Graph::create_inclusion_graph(formula);
        CHECK(graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
        }));
        CHECK(graph.get_edges().size() == 2);
        CHECK(graph.get_num_of_edges() == 2);
    }

    // SECTION("x = xy twice") {
    //     Predicate predicate{ PredicateType::Equation, { { x }, { x, y } } };
    //     Predicate predicate{ PredicateType::Equation, { { x }, { x, y } } };

    //     formula.add_predicate(predicate);
    //     CHECK_THROWS(Graph::create_inclusion_graph(formula)); // Catch2 cannot catch failing assert.
    // }

    // SECTION("x = x") {
    //     Predicate predicate{ PredicateType::Equation, { { x }, { x } } };

    //     formula.add_predicate(predicate);
    //     CHECK_THROWS(Graph::create_inclusion_graph(formula)); // Catch2 cannot catch failing assert.
    // }

    SECTION("x=y && u = x") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y } } };
        Predicate predicate2{ PredicateType::Equation, { { u }, { x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = Graph::create_inclusion_graph(formula);
        CHECK(graph.get_nodes().size() == 2);
        CHECK(
            !(graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{
                GraphNode{ predicate.get_switched_sides_predicate() },
                GraphNode{ predicate2 },
        }))
        );
        CHECK((graph.get_edges().empty() || graph.get_edges().size() == 1));
    }

    SECTION("x=yx && u = x") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y, x } } };
        Predicate predicate2{ PredicateType::Equation, { { u }, { x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = Graph::create_inclusion_graph(formula);
        CHECK(graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
                GraphNode{ predicate2.get_switched_sides_predicate() },
        }));
        CHECK(graph.get_edges().size() == 3);
        CHECK(graph.get_num_of_edges() == 4);
    }

    SECTION("x=y && u = v") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y } } };
        Predicate predicate2{ PredicateType::Equation, { { u }, { v } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = Graph::create_inclusion_graph(formula);
        CHECK(!graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{
                GraphNode{ predicate },
                GraphNode{ predicate.get_switched_sides_predicate() },
        }));
        CHECK(!graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{
                GraphNode{ predicate2 },
                GraphNode{ predicate2.get_switched_sides_predicate() },
        }));
        CHECK(graph.get_nodes().size() == 2);
        CHECK(graph.get_edges().empty());
    }
}

TEST_CASE("Splitting graph", "[noodler]") {
    Graph graph;
    Formula formula;

    BasicTerm u{ BasicTermType::Variable, "u" };
    BasicTerm v{ BasicTermType::Variable, "v" };
    BasicTerm x{ BasicTermType::Variable, "x" };
    BasicTerm y{ BasicTermType::Variable, "y" };

    SECTION("yx=xy") {
        Predicate predicate{ PredicateType::Equation, { { x, y }, {y, x} } };
        CHECK(predicate.to_string() == "Equation: x y = y x");

        formula.add_predicate(predicate);
        graph = Graph::create_simplified_splitting_graph(formula);
        CHECK(graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{ GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() } }));
        REQUIRE(graph.get_edges().size() == 2);
        CHECK(graph.get_edges().begin()->first == *graph.get_edges().begin()->second.begin());
        CHECK((++graph.get_edges().begin())->first == *(++graph.get_edges().begin())->second.begin());
    }

    // SECTION("xx=xx") {
    //     Predicate predicate{ PredicateType::Equation, { { x, x }, {x, x} } };
    //     CHECK(predicate.to_string() == "Equation: x x = x x");

    //     formula.add_predicate(predicate);
    //     CHECK_THROWS(Graph::create_simplified_splitting_graph(formula)); // Catch2 cannot catch failing assert.
    // }

    SECTION("x=xy") {
        Predicate predicate{ PredicateType::Equation, { { x }, {x, y} } };
        CHECK(predicate.to_string() == "Equation: x = x y");

        Formula formula;
        formula.add_predicate(predicate);
        graph = Graph::create_simplified_splitting_graph(formula);
        CHECK(graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{ GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() } }));
        REQUIRE(graph.get_edges().size() == 2);
        CHECK(graph.get_edges().begin()->first == *graph.get_edges().begin()->second.begin());
        CHECK((++graph.get_edges().begin())->first == *(++graph.get_edges().begin())->second.begin());
    }

    SECTION("x=xy && xy = yx") {
        Predicate predicate{ PredicateType::Equation, { { x }, { x, y } } };
        Predicate predicate2{ PredicateType::Equation, { { x, y }, { y, x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = Graph::create_simplified_splitting_graph(formula);
        CHECK(graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{
            GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
            GraphNode{ predicate2 }, GraphNode{ predicate2.get_switched_sides_predicate() },
        }));
        CHECK(graph.get_edges().size() == 4);
        CHECK(graph.get_num_of_edges() == 12);
    }

    SECTION("x=y && x = u") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y } } };
        Predicate predicate2{ PredicateType::Equation, { { x }, { u } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = Graph::create_simplified_splitting_graph(formula);
        CHECK(graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
                GraphNode{ predicate2 }, GraphNode{ predicate2.get_switched_sides_predicate() },
        }));
        CHECK(graph.get_edges().size() == 2);
        CHECK(graph.get_num_of_edges() == 2);
    }

    SECTION("x=yx && u = x") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y, x } } };
        Predicate predicate2{ PredicateType::Equation, { { u }, { x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = Graph::create_simplified_splitting_graph(formula);
        CHECK(graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
                GraphNode{ predicate2 }, GraphNode{ predicate2.get_switched_sides_predicate() },
        }));
        CHECK(graph.get_edges().size() == 3);
        CHECK(graph.get_num_of_edges() == 6);
    }

    SECTION("x=y && u = v") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y } } };
        Predicate predicate2{ PredicateType::Equation, { { u }, { v } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = Graph::create_simplified_splitting_graph(formula);
        CHECK(graph_nodes_are_equal_to(graph.get_nodes(), std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
                GraphNode{ predicate2 }, GraphNode{ predicate2.get_switched_sides_predicate() },
        }));
        CHECK(graph.get_edges().empty());
    }
}

TEST_CASE("print_to_dot()") {
    Graph graph;
    Formula formula;

    BasicTerm u{ BasicTermType::Variable, "u" };
    BasicTerm v{ BasicTermType::Variable, "v" };
    BasicTerm x{ BasicTermType::Variable, "x" };
    BasicTerm y{ BasicTermType::Variable, "y" };
    BasicTerm z{ BasicTermType::Variable, "z" };

    Predicate predicate{ PredicateType::Equation, { { u }, { z } } };
    Predicate predicate2{ PredicateType::Equation, { { v }, { u } } };
    Predicate predicate3{ PredicateType::Equation, { { x }, { u, v, x } } };

    formula.add_predicate(predicate);
    formula.add_predicate(predicate2);
    formula.add_predicate(predicate3);
    graph = Graph::create_inclusion_graph(formula);
    std::stringstream stream;
    graph.print_to_dot(stream);
    CHECK(!stream.str().empty());
}

TEST_CASE("Inclusion graph with transducers", "[noodler]") {
    Graph graph;
    Formula formula;

    BasicTerm u{ BasicTermType::Variable, "u" };
    BasicTerm v{ BasicTermType::Variable, "v" };
    BasicTerm x{ BasicTermType::Variable, "x" };
    BasicTerm y{ BasicTermType::Variable, "y" };
    BasicTerm z{ BasicTermType::Variable, "z" };

    mata::nft::Nft nft1{2};
    nft1.initial = {0};
    nft1.final = {1};
    nft1.insert_word_by_parts(0, { {'a'}, {'b'} } , 1);

    mata::nft::Nft nft2{2};
    nft2.initial = {0};
    nft2.final = {1};
    nft2.insert_word_by_parts(0, { {'c'}, {'d'} } , 1);


    SECTION("T(x,y) && S(zz,yu)") {
        Predicate p1{ PredicateType::Transducer, { { x }, { y } }, std::make_shared<mata::nft::Nft>(nft1) };
        Predicate p2{ PredicateType::Transducer, { { z, z }, { y, u } }, std::make_shared<mata::nft::Nft>(nft2) };

        Formula formula;
        formula.add_predicate(p1);
        formula.add_predicate(p2);
        graph = Graph::create_inclusion_graph(formula);

        CHECK(graph.get_nodes().size() == 2);
        CHECK(graph.get_num_of_edges() == 1);
        CHECK(!graph.is_cyclic());
    }

    SECTION("x=y && T(zz,yu)") {
        Predicate p1{ PredicateType::Equation, { { x }, { y } } };
        Predicate p2{ PredicateType::Transducer, { { z, z }, { y, u } }, std::make_shared<mata::nft::Nft>(nft2) };

        Formula formula;
        formula.add_predicate(p1);
        formula.add_predicate(p2);
        graph = Graph::create_inclusion_graph(formula);

        CHECK(graph.get_nodes().size() == 2);
        CHECK(graph.get_num_of_edges() == 1);
        CHECK(!graph.is_cyclic());
    }

    SECTION("T(x,x)") {
        Predicate p1{ PredicateType::Transducer, { { x }, { x } }, std::make_shared<mata::nft::Nft>(nft2) };

        Formula formula;
        formula.add_predicate(p1);
        graph = Graph::create_inclusion_graph(formula);

        CHECK(graph.get_nodes().size() == 2);
        CHECK(graph.get_num_of_edges() == 2);
        CHECK(graph.is_cyclic());
    }

    SECTION("T(x,y) && x=y") {
        Predicate p1{ PredicateType::Transducer, { { x }, { y } }, std::make_shared<mata::nft::Nft>(nft2) };
        Predicate p2{ PredicateType::Equation, { { x }, { y } } };

        Formula formula;
        formula.add_predicate(p1);
        formula.add_predicate(p2);
        graph = Graph::create_inclusion_graph(formula);

        CHECK(graph.get_nodes().size() == 4);
        CHECK(graph.get_num_of_edges() == 8);
        CHECK(graph.is_cyclic());
    }

    SECTION("T(x,y) && x=z") {
        Predicate p1{ PredicateType::Transducer, { { x }, { y } }, std::make_shared<mata::nft::Nft>(nft2) };
        Predicate p2{ PredicateType::Equation, { { x }, { z } } };

        Formula formula;
        formula.add_predicate(p1);
        formula.add_predicate(p2);
        graph = Graph::create_inclusion_graph(formula);

        CHECK(graph.get_nodes().size() == 2);
        CHECK(graph.get_num_of_edges() == 1);
        CHECK(!graph.is_cyclic());
    }
}