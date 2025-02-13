#include <iostream>

#include <catch2/catch_test_macros.hpp>

#include <smt/theory_str_noodler/formula_preprocess.h>
#include <smt/theory_str_noodler/theory_str_noodler.h>
#include <mata/parser/re2parser.hh>
#include <mata/nft/nft.hh>

using namespace smt::noodler;

static mata::nfa::Nfa regex_to_nfa(const std::string& regex) {
    mata::nfa::Nfa aut;
    mata::parser::create_nfa(&aut, regex);
    return aut;
}

TEST_CASE( "Preprocess to strings", "[noodler]" ) {
    BasicTerm term{ BasicTermType::Variable, "x_6"};
    BasicTerm lit (BasicTermType::Literal, "lit" );
    BasicTerm term2{ BasicTerm(BasicTermType::Variable, "x_2") };
    Predicate predicate1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({term, term, lit}), std::vector<BasicTerm>({lit, term2, term2}) })   );

    BasicTerm term_lit{ BasicTermType::Literal, "3"};
    BasicTerm term_lit2{ BasicTermType::Literal, "5"};
    BasicTerm term_var{ BasicTermType::Variable, "x_4"};
    BasicTerm term_var2{ BasicTermType::Variable, "x_6"};

    Predicate predicate2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({term_lit, term_var}), std::vector<BasicTerm>({term_lit2, term_var2}) })  );

    Formula conj;
    conj.add_predicate(predicate1);
    conj.add_predicate(predicate2);
    FormulaVar fvar(conj);

    VarNode v1{BasicTerm(BasicTermType::Variable, "x_1"), 0, -1};
    VarNode v2{BasicTerm(BasicTermType::Variable, "x_1"), 0, -1};

    CHECK(v1 == v2);
    INFO(fvar.to_string());
    CHECK(fvar.get_var_positions(predicate1, 0, true) == std::set<VarNode>({
        VarNode{term, 0, -1 },
        VarNode{term, 0, -2 },
        VarNode{lit, 0, -3 },
        VarNode{lit, 0, 1 },
        VarNode{term2, 0, 2 },
        VarNode{term2, 0, 3} }));
}

TEST_CASE( "Remove regular", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};

    AutAssignment aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|b)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("(a|b)*")},
        {x4, regex_to_nfa("(a|b)*")},
        {x5, regex_to_nfa("a*")},
        {x6, regex_to_nfa("(a|b)*")},
        {a, regex_to_nfa("a")},
        {b, regex_to_nfa("b")},
    });

    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x1, x1}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2, x6, a}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x3, b, x4, b}), std::vector<BasicTerm>({x2}) })  );
    Predicate eq4(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x5}), std::vector<BasicTerm>({x4}) })  );
    Predicate ieq1(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x6}), std::vector<BasicTerm>({b}) })  );

    Formula conj;
    conj.add_predicate(eq1);
    conj.add_predicate(eq2);
    conj.add_predicate(eq3);
    conj.add_predicate(eq4);
    conj.add_predicate(ieq1);
    FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
    prep.remove_regular();

    AutAssignment ret = prep.get_aut_assignment();
    CHECK(prep.get_dependency() == Dependency({{2, {3}}}));
    CHECK(prep.get_flat_dependency() == Dependency({{2, {3}}, {3, {}}}));
    CHECK(mata::nfa::are_equivalent(*ret.at(x4), regex_to_nfa("a*")));
    CHECK(mata::nfa::are_equivalent(*ret.at(x5), regex_to_nfa("a*")));
    CHECK(mata::nfa::are_equivalent(*ret.at(x2), regex_to_nfa("(a|b)*b(a*)b")));
    CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({eq1, eq2, ieq1}));

    SECTION("length vars") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(eq2);
        FormulaPreprocessor prep(conj, aut_ass, {x2}, {}, {});
        prep.remove_regular();
        CHECK(prep.get_dependency() == Dependency({}));
        CHECK(prep.get_flat_dependency() == Dependency({}));
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            eq1, eq2
        }));
    }
}

TEST_CASE( "Generate identities", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};
    AutAssignment aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|b)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("(a|b)*")},
        {x4, regex_to_nfa("(a|b)*")},
        {x5, regex_to_nfa("(a|b)*")},
        {x6, regex_to_nfa("(a|b)*")},
        {a, regex_to_nfa("a")},
        {b, regex_to_nfa("b")},
    });

    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1, a, x1}), std::vector<BasicTerm>({y1, x1, x1}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1, b}), std::vector<BasicTerm>({x2, b}) })  );
    Predicate ieq1(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1, b}), std::vector<BasicTerm>({x2, b}) })  );

    Formula conj;
    conj.add_predicate(eq1);
    conj.add_predicate(eq2);
    conj.add_predicate(ieq1);
    FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
    prep.generate_identities();
    std::set<Predicate> res;
    res.insert(ieq1);
    res.insert(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a}), std::vector<BasicTerm>({x1}) })  ));
    res.insert(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2}) })  ));
    CHECK(prep.get_formula().get_predicates_set() == res);
}

TEST_CASE( "Replace", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};
    AutAssignment aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|b)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("(a|b)*")},
        {x4, regex_to_nfa("(a|b)*")},
        {x5, regex_to_nfa("(a|b)*")},
        {x6, regex_to_nfa("(a|b)*")},
        {a, regex_to_nfa("a")},
        {b, regex_to_nfa("b")},
    });

    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1, a, x1}), std::vector<BasicTerm>({y1, x1, x1}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2, b}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({y1, b}) })  );
    Predicate eq4(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x2}) })  );
    Predicate ieq1(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x2}) })  );

    Predicate res;
    CHECK(eq1.replace(Concat({y1}), std::vector<BasicTerm>({y1, a, x1}), res));
    CHECK(res == Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1, a, x1, a, x1}), std::vector<BasicTerm>({y1, a, x1, x1, x1}) })  ));
    CHECK(eq1.replace(Concat({x1}), std::vector<BasicTerm>(), res));
    CHECK(res == Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1, a}), std::vector<BasicTerm>({y1}) })  ));
    CHECK(eq2.replace(Concat({x1}), std::vector<BasicTerm>(), res));
    CHECK(res == Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>(), std::vector<BasicTerm>({x2, b}) })  ));
    CHECK(!eq2.replace(Concat({x3}), std::vector<BasicTerm>(), res));
    CHECK(eq4.replace(Concat({x2}), std::vector<BasicTerm>({x1}), res));
    CHECK(res == Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x1}) })  ));
    CHECK(ieq1.replace(Concat({x2}), std::vector<BasicTerm>({x1}), res));
    CHECK(res == Predicate(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x1}) })  ));

    Formula conj;
    conj.add_predicate(eq1);
    conj.add_predicate(eq3);
    FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
    prep.replace(Concat({y1}), std::vector<BasicTerm>({y1, a, x1}));
    Formula res_conj;
    res_conj.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1, a, x1, a, x1}), std::vector<BasicTerm>({y1, a, x1, x1, x1}) })));
    res_conj.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({y1, a, x1, b}) })));
    FormulaPreprocessor prep_res(res_conj, aut_ass, {}, {}, {});
    INFO(prep.get_formula().to_string());
    INFO(prep_res.get_formula().to_string());
    CHECK(prep.get_formula().get_varmap() == prep_res.get_formula().get_varmap());
}

TEST_CASE( "Replace 2", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};
    AutAssignment aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|b)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("(a|b)*")},
        {x4, regex_to_nfa("(a|b)*")},
        {x5, regex_to_nfa("(a|b)*")},
        {x6, regex_to_nfa("(a|b)*")},
        {a, regex_to_nfa("a")},
        {b, regex_to_nfa("b")},
    });

    Predicate eq4(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x2}) })  );
    Predicate eq5(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2}) })  );
    Predicate eq6(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) })  );
    Predicate ieq1(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2}) })  );
    Predicate eq7(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4, b}), std::vector<BasicTerm>({x1, x1, x2}) })  );
    Formula conj2;
    conj2.add_predicate(eq4);
    conj2.add_predicate(eq5);
    conj2.add_predicate(eq6);
    conj2.add_predicate(ieq1);
    FormulaPreprocessor prep2(conj2, aut_ass, {}, {}, {});
    prep2.replace(Concat({x2}), std::vector<BasicTerm>({x1}));
    prep2.remove_trivial();
    prep2.clean_varmap();
    Formula res_conj2;
    res_conj2.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x1}) })));
    res_conj2.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x1}) })));
    res_conj2.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) })));
    res_conj2.add_predicate(Predicate(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x1}) })));
    FormulaPreprocessor prep_res2(res_conj2, aut_ass, {}, {}, {});
    INFO(prep2.to_string());
    CHECK(prep2.get_formula().get_varmap() == prep_res2.get_formula().get_varmap());

    // replace
    Predicate res;
    eq7.replace(std::vector<BasicTerm>({x3, x4, b}), std::vector<BasicTerm>({y1}), res);
    CHECK(res == Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, y1}), std::vector<BasicTerm>({x1, x1, x2}) })  ));
}

TEST_CASE( "Propagate variables", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};
    AutAssignment aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|c)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("(b|c)*")},
        {x4, regex_to_nfa("(a|b)*")},
        {x5, regex_to_nfa("(a|b)*")},
        {x6, regex_to_nfa("(a|b)*")},
        {a, regex_to_nfa("a")},
        {b, regex_to_nfa("b")},
    });

    mata::nft::Nft nft{2};
    nft.initial = {0};
    nft.final = {1};
    nft.insert_word_by_parts(0, { {'a'}, {'b'} } , 1);

    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x2}) })  );
    Predicate ieq1(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1, x1}), std::vector<BasicTerm>({x3, x2}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) })  );
    Predicate tr1(PredicateType::Transducer, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) }), std::make_shared<mata::nft::Nft>(nft) );
    Predicate tr2(PredicateType::Transducer, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x1}) }), std::make_shared<mata::nft::Nft>(nft) );

    SECTION("(In)equations") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(ieq1);
        conj.add_predicate(eq2);
        conj.add_predicate(eq3);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});

        prep.propagate_variables();
        prep.clean_varmap();
        INFO(prep.to_string());

        Formula res_conj;
        res_conj.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x1, x4}), std::vector<BasicTerm>({b, x1, x1}) })));
        res_conj.add_predicate(Predicate(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1, x1}), std::vector<BasicTerm>({x1, x1}) })));
        FormulaPreprocessor prep_res(res_conj, aut_ass, {}, {}, {});

        AutAssignment ret = prep.get_aut_assignment();
        CHECK(mata::nfa::are_equivalent(*ret.at(x1), regex_to_nfa("")));
        CHECK(mata::nfa::are_equivalent(*ret.at(x2), regex_to_nfa("(a|b)*")));
        CHECK(mata::nfa::are_equivalent(*ret.at(x3), regex_to_nfa("(b|c)*")));
        CHECK(prep.get_formula().get_varmap() == prep_res.get_formula().get_varmap());
        CHECK(prep.get_formula().get_predicates_set() == prep_res.get_formula().get_predicates_set());
        CHECK(prep.get_dependency() == Dependency({{0, {2,3}}, {1, {2,3}}, {3, {2}}}));
    }

    SECTION("Transducers") {
        Formula conj;
        conj.add_predicate(tr1);
        conj.add_predicate(eq3);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});

        prep.propagate_variables();
        prep.clean_varmap();
        INFO(prep.to_string());

        Formula res_conj;
        res_conj.add_predicate(tr2);
        FormulaPreprocessor prep_res(res_conj, aut_ass, {}, {}, {});

        CHECK(prep.get_formula().get_varmap() == prep_res.get_formula().get_varmap());
        CHECK(prep.get_modified_formula() == res_conj);
    }
    
}

TEST_CASE( "Remove duplicates", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};
    AutAssignment aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|b)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("(a|b)*")},
        {x4, regex_to_nfa("(a|b)*")},
        {x5, regex_to_nfa("(a|b)*")},
        {x6, regex_to_nfa("(a|b)*")},
        {a, regex_to_nfa("a")},
        {b, regex_to_nfa("b")},
    });
    mata::nft::Nft nft{2};
    nft.initial = {0};
    nft.final = {1};
    nft.insert_word_by_parts(0, { {'a'}, {'b'} } , 1);

    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x2}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x2}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) })  );
    Predicate ieq1(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) })  );
    Predicate ieq2(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) })  );
    Predicate tr1(PredicateType::Transducer, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) }), std::make_shared<mata::nft::Nft>(nft) );
    Predicate tr2(PredicateType::Transducer, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) }), std::make_shared<mata::nft::Nft>(nft)  );
    Formula conj;
    conj.add_predicate(eq1);
    conj.add_predicate(eq3);
    conj.add_predicate(ieq1);
    conj.add_predicate(tr1);
    conj.add_predicate(eq2);
    conj.add_predicate(ieq2);
    conj.add_predicate(tr2);
    FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});

    Formula res_conj;
    res_conj.add_predicate(eq1);
    res_conj.add_predicate(eq3);
    res_conj.add_predicate(ieq1);
    res_conj.add_predicate(tr1);
    FormulaPreprocessor prep_res(res_conj, aut_ass, {}, {}, {});

    INFO(prep.to_string());
    INFO(prep_res.to_string());
    CHECK(prep.get_formula().get_varmap() == prep_res.get_formula().get_varmap());
    CHECK(prep.get_formula().get_predicates_set() == prep_res.get_formula().get_predicates_set());
}


TEST_CASE( "Sublists", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};
    AutAssignment aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|b)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("(a|b)*")},
        {x4, regex_to_nfa("(a|b)*")},
        {x5, regex_to_nfa("(a|b)*")},
        {x6, regex_to_nfa("(a|b)*")},
        {a, regex_to_nfa("a")},
        {b, regex_to_nfa("b")},
    });

    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4, b}), std::vector<BasicTerm>({x1, x1, x2}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({b, x3, x4, b}), std::vector<BasicTerm>({x2, x1, x2}) })  );
    // transducer itself is not important for this case
    Predicate tr2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({b, x3, x4, b}), std::vector<BasicTerm>({x2, x1, x2}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x5, x1, x2, x3}), std::vector<BasicTerm>({x4, x1, x2}) })  );
    Predicate eq4(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x5, x1, x2, x3}), std::vector<BasicTerm>({x4, a, b}) })  );

    SECTION("sub1") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(eq2);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        std::map<Concat, unsigned> res;
        prep.get_regular_sublists(res);
        CHECK(res == std::map<Concat, unsigned>({ {std::vector<BasicTerm>({x3, x4, b}), 2}  }));
    }

    SECTION("sub1 with transducers") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(tr2);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        std::map<Concat, unsigned> res;
        prep.get_regular_sublists(res);
        CHECK(res == std::map<Concat, unsigned>({ {std::vector<BasicTerm>({x3, x4, b}), 2}  }));
    }

    SECTION("sub2") {
        Formula conj;
        std::map<Concat, unsigned> res;
        conj.add_predicate(eq3);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.get_regular_sublists(res);
        CHECK(res == std::map<Concat, unsigned>({ {std::vector<BasicTerm>({x1, x2}), 2}  }));
    }

    SECTION("sub3") {
        Formula conj;
        std::map<Concat, unsigned> res;
        conj.add_predicate(eq4);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.get_regular_sublists(res);
        CHECK(res == std::map<Concat, unsigned>({ {std::vector<BasicTerm>({x5, x1, x2, x3}), 1}, {std::vector<BasicTerm>({x4, a, b}), 1}  }));
    }
}

TEST_CASE( "Reduce regular", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};
    BasicTerm tmp0{BasicTermType::Variable, "regular_seq!n0"};
    BasicTerm tmp1{BasicTermType::Variable, "regular_seq!n1"};
    AutAssignment aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|b)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("a*")},
        {x4, regex_to_nfa("b*")},
        {x5, regex_to_nfa("(a|b)*")},
        {x6, regex_to_nfa("(a|b)*")},
        {a, regex_to_nfa("a")},
        {b, regex_to_nfa("b")},
    });

    mata::nft::Nft nft{2, {0}, {1}};
    nft.insert_word_by_parts(0, { {'a'}, {'b'} } , 1);

    Predicate eq1(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4, b}), std::vector<BasicTerm>({x1, x1, x2}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x2, x1, x2}), std::vector<BasicTerm>({b, x3, x4, b}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x5, x1, x2, x3}), std::vector<BasicTerm>({x4, x1, x2}) })  );
    Predicate eq4(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x5, x1, x2, x3}), std::vector<BasicTerm>({x4, a, b}) })  );
    Predicate tr4(PredicateType::Transducer, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x5, x1, x2, x3}), std::vector<BasicTerm>({x4, a, b}) }), std::make_shared<mata::nft::Nft>(nft)  );

    
    SECTION("basic") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(eq2);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.reduce_regular_sequence(2);
        AutAssignment ret = prep.get_aut_assignment();
        CHECK(mata::nfa::are_equivalent(*ret.at(tmp0), regex_to_nfa("a*b*b")));
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, tmp0}), std::vector<BasicTerm>({x1, x1, x2}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x2, x1, x2}), std::vector<BasicTerm>({b, tmp0}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({tmp0}), std::vector<BasicTerm>({x3, x4, b}) })  )
        }));
        CHECK(prep.get_dependency().empty());
        CHECK(prep.get_flat_dependency().empty());
    }

    SECTION("two fresh") {
        Formula conj;
        conj.add_predicate(eq4);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.reduce_regular_sequence(1);
        AutAssignment ret = prep.get_aut_assignment();

        tmp0 = BasicTerm{BasicTermType::Variable, "regular_seq!n1"};
        tmp1 = BasicTerm{BasicTermType::Variable, "regular_seq!n2"};
        CHECK(mata::nfa::are_equivalent(*ret.at(tmp0), regex_to_nfa("b*ab")));
        CHECK(mata::nfa::are_equivalent(*ret.at(tmp1), regex_to_nfa("(a|b)*a*")));
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({tmp1}), std::vector<BasicTerm>({x5, x1, x2, x3}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({tmp0}), std::vector<BasicTerm>({x4, a, b}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({tmp1}), std::vector<BasicTerm>({tmp0}) })  )
        }));
        CHECK(prep.get_dependency().empty());
        CHECK(prep.get_flat_dependency().empty());
    }

    SECTION("length vars") {
        Formula conj;
        conj.add_predicate(eq4);
        FormulaPreprocessor prep(conj, aut_ass, {x2}, {}, {});
        prep.reduce_regular_sequence(1);
        AutAssignment ret = prep.get_aut_assignment();

        tmp0 = BasicTerm{BasicTermType::Variable, "regular_seq!n3"};
        tmp1 = BasicTerm{BasicTermType::Variable, "regular_seq!n4"};
        CHECK(mata::nfa::are_equivalent(*ret.at(tmp0), regex_to_nfa("b*ab")));
        CHECK(mata::nfa::are_equivalent(*ret.at(tmp1), regex_to_nfa("(a|b)*a*")));
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({tmp0}), std::vector<BasicTerm>({x4, a, b}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({tmp1}), std::vector<BasicTerm>({tmp0}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({tmp1 }), std::vector<BasicTerm>({x5, x1, x2, x3}) })  )
        }));
        CHECK(prep.get_dependency().empty());
        CHECK(prep.get_flat_dependency().empty());
    }

    SECTION("transducers") {
        Formula conj;
        conj.add_predicate(tr4);
        FormulaPreprocessor prep(conj, aut_ass, {x2}, {}, {});
        prep.reduce_regular_sequence(1);
        AutAssignment ret = prep.get_aut_assignment();

        tmp0 = BasicTerm{BasicTermType::Variable, "regular_seq!n5"};
        tmp1 = BasicTerm{BasicTermType::Variable, "regular_seq!n6"};
        CHECK(mata::nfa::are_equivalent(*ret.at(tmp0), regex_to_nfa("b*ab")));
        CHECK(mata::nfa::are_equivalent(*ret.at(tmp1), regex_to_nfa("(a|b)*a*")));
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({tmp0}), std::vector<BasicTerm>({x4, a, b}) })),
            Predicate(PredicateType::Transducer, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({tmp1}), std::vector<BasicTerm>({tmp0}) }), std::make_shared<mata::nft::Nft>(nft) ),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({tmp1 }), std::vector<BasicTerm>({x5, x1, x2, x3}) })  )
        }));
    }
}

TEST_CASE( "Propagate eps", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm eps{ BasicTermType::Literal, ""};
    BasicTerm b{ BasicTermType::Literal, "b"};
    AutAssignment aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|b)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("(a|b)*")},
        {x4, regex_to_nfa("(a|b)*")},
        {x5, regex_to_nfa("(a|b)*")},
        {x6, regex_to_nfa("(a|b)*")},
        {b, regex_to_nfa("b")},
        {eps, regex_to_nfa("")},
    });

    mata::nft::Nft nft{2, {0}, {1}};
    nft.insert_word_by_parts(0, { {'a'}, {'b'} } , 1);

    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({eps}), std::vector<BasicTerm>({x1, x2}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x2, x1, x2}), std::vector<BasicTerm>({x3, x4}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x3, b, x4}), std::vector<BasicTerm>({x5, x1}) })  );
    Predicate eq4(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({b, x1}), std::vector<BasicTerm>({eps}) })  );
    Predicate ieq1(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({eps}) })  );
    Predicate tr4(PredicateType::Transducer, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x5, x1}), std::vector<BasicTerm>({x2}) }), std::make_shared<mata::nft::Nft>(nft)  );

    SECTION("basic") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(eq2);
        conj.add_predicate(eq3);
        conj.add_predicate(ieq1);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.propagate_eps();
        AutAssignment ret = prep.get_aut_assignment();
        CHECK(mata::nfa::are_equivalent(*ret.at(x1), regex_to_nfa("")));
        CHECK(mata::nfa::are_equivalent(*ret.at(x2), regex_to_nfa("")));
        CHECK(mata::nfa::are_equivalent(*ret.at(x3), regex_to_nfa("")));
        CHECK(mata::nfa::are_equivalent(*ret.at(x4), regex_to_nfa("")));
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({b}), std::vector<BasicTerm>({x5}) })  ),
            Predicate(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({}), std::vector<BasicTerm>({}) })  ),
        }));
        CHECK(prep.get_dependency() == Dependency({{2, {0, 1}}, {3, {0, 1}}}));
    }

    SECTION("empty side") {
        Formula conj;
        conj.add_predicate(eq4);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.propagate_eps();
        AutAssignment ret = prep.get_aut_assignment();
        CHECK(mata::nfa::are_equivalent(*ret.at(x1), regex_to_nfa("")));
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({b}), std::vector<BasicTerm>() })  )
        }));
        CHECK(prep.get_dependency() == Dependency({{0, {0}}}));
    }

    SECTION("transducer constraint") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(tr4);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.propagate_eps();
        AutAssignment ret = prep.get_aut_assignment();
        CHECK(mata::nfa::are_equivalent(*ret.at(x1), regex_to_nfa("")));
        CHECK(mata::nfa::are_equivalent(*ret.at(x2), regex_to_nfa("")));
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Transducer, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x5}), std::vector<BasicTerm>() }), std::make_shared<mata::nft::Nft>(nft) ),
        }));
    }
}

TEST_CASE( "Separate eqs", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm eps{ BasicTermType::Literal, ""};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};
    BasicTerm ab{ BasicTermType::Literal, "ab"};
    AutAssignment aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|b)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("(a|b)*")},
        {x4, regex_to_nfa("(a|b)*")},
        {x5, regex_to_nfa("(a|b)*")},
        {x6, regex_to_nfa("(a|b)*")},
        {b, regex_to_nfa("b")},
    });

    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1, a, x2, x4, a, b, x5, x6}), std::vector<BasicTerm>({x2, b, x1, x5, b, x4, a}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1, a, x2, x4, ab, x5, x6}), std::vector<BasicTerm>({x2, b, x1, x5, b, x4, a}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1, a, x2}), std::vector<BasicTerm>({x2, b, x2}) })  );
    Predicate eq4(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1, a, x2}), std::vector<BasicTerm>({x2, b}) })  );

    SECTION("multiple") {
        Formula conj;
        conj.add_predicate(eq1);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.separate_eqs();
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1, a, x2}), std::vector<BasicTerm>({x2, b, x1}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x4, a, b, x5}), std::vector<BasicTerm>({x5, b, x4, a}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x6}), std::vector<BasicTerm>({eps}) })  )
        }));
    }

    SECTION("longer literals") {
        Formula conj;
        conj.add_predicate(eq2);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.separate_eqs();
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1, a, x2}), std::vector<BasicTerm>({x2, b, x1}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x4, ab, x5}), std::vector<BasicTerm>({x5, b, x4, a}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x6}), std::vector<BasicTerm>({eps}) })  )
        }));
    }

    SECTION("no match 1") {
        Formula conj;
        conj.add_predicate(eq3);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.separate_eqs();
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            eq3
        }));
        CHECK(prep.get_dependency().empty());
    }

    SECTION("no match 2") {
        Formula conj;
        conj.add_predicate(eq4);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.separate_eqs();
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            eq4
        }));
        CHECK(prep.get_dependency().empty());
    }
}

TEST_CASE( "Remove extension", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm tmp_var_0{ BasicTermType::Variable, "__tmp__var_0"};
    BasicTerm tmp_var_1{ BasicTermType::Variable, "__tmp__var_1"};
    BasicTerm eps{ BasicTermType::Literal, ""};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};
    BasicTerm ab{ BasicTermType::Literal, "ab"};
    AutAssignment aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|b)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("(a|b)*")},
        {x4, regex_to_nfa("(a|b)*")},
        {x5, regex_to_nfa("(a|b)*")},
        {x6, regex_to_nfa("(a|b)*")},
        {b, regex_to_nfa("b")},
        {a, regex_to_nfa("a")},
    });

    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x1, x2, a, x4}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x1, x3}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x5, x3}) })  );
    Predicate eq4(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x3, x1}) })  );
    Predicate eq5(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x2, x1}) })  );
    Predicate ieq1(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x1, x2}) })  );

    SECTION("basic") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(eq2);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.remove_extension();
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x2, a, x4}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x3}) })),
        }));
        CHECK(prep.get_dependency().empty());
    }

    SECTION("ineq") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(eq2);
        conj.add_predicate(ieq1);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.remove_extension();
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x1, x2, a, x4}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x1, x3}) })),
            Predicate(PredicateType::Inequation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x1, x2}) })  ),
        }));
        CHECK(prep.get_dependency().empty());
    }

    SECTION("unchanged") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(eq2);
        conj.add_predicate(eq3);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.remove_extension();
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            eq1, eq2, eq3
        }));
        CHECK(prep.get_dependency().empty());
    }

    SECTION("from end") {
        Formula conj;
        conj.add_predicate(eq4);
        conj.add_predicate(eq5);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.remove_extension();
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x2}) })),
            Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x3}) })),
        }));
    }

    aut_ass = AutAssignment({
        {y1, regex_to_nfa("(a|b)*")},
        {x1, regex_to_nfa("(a|b)*")},
        {x2, regex_to_nfa("(a|b)*")},
        {x3, regex_to_nfa("(a|b)*")},
        {x4, regex_to_nfa("(a|b)*")},
        {x5, regex_to_nfa("(a|b)*")},
        {x6, regex_to_nfa("(a|b)*")},
        {b, regex_to_nfa("def")},
        {a, regex_to_nfa("a")},
    });
    SECTION("infeasible") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(eq2);
        FormulaPreprocessor prep(conj, aut_ass, {}, {}, {});
        prep.remove_extension();
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            eq1, eq2
        }));
        CHECK(prep.get_dependency().empty());
    }

    SECTION("length vars") {
        Formula conj;
        conj.add_predicate(eq1);
        conj.add_predicate(eq2);
        FormulaPreprocessor prep(conj, aut_ass, {x1}, {}, {});
        prep.remove_extension();
        CHECK(prep.get_formula().get_predicates_set() == std::set<Predicate>({
            eq1, eq2,
        }));
        CHECK(prep.get_dependency().empty());
    }
}
