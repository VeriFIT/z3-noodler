#include <iostream>
#include <unordered_set>

#include <catch2/catch_test_macros.hpp>
#include <mata/nfa/nfa.hh>
#include <mata/nft/nft.hh>

#include "smt/theory_str_noodler/formula.h"

using namespace smt::noodler;


TEST_CASE( "Transducer predicate", "[noodler]" ) {

    // two-tape transducer by default
    mata::nft::Nft nft{2};
    nft.initial = {0};
    nft.final = {1};
    nft.insert_word_by_parts(0, { {'a'}, {'b'} } , 1);
    CHECK(nft.delta.num_of_states() == 3);
    CHECK(nft.is_tuple_in_lang({ {'a'}, {'b'} }));

    BasicTerm x {BasicTermType::Variable, "x"};
    BasicTerm y {BasicTermType::Variable, "x"};

    SECTION("Switched predicate") {
         // transducer implementing inversion relation
        mata::nft::Nft nft_inv = mata::nft::invert_levels(nft);
        CHECK(nft_inv.is_tuple_in_lang({ {'b'}, {'a'} }));
        CHECK(!nft_inv.is_tuple_in_lang({ {'a'}, {'b'} }));

        Predicate pred_trans { PredicateType::Transducer, { { x }, { y } }, std::make_shared<mata::nft::Nft>(nft) };
        Predicate pred_trans_switch = pred_trans.get_switched_sides_predicate();

        // result
        Predicate switch_res { PredicateType::Transducer, { { y }, { x } }, std::make_shared<mata::nft::Nft>(nft_inv) };
        CHECK(pred_trans_switch == switch_res);
    }

    SECTION("Comparison") {
        mata::nft::Nft nft_other{2};
        nft_other.initial = {0};
        nft_other.final = {1};
        nft_other.insert_word_by_parts(0, { {'c'}, {'d'} } , 1);

        
        Predicate p1 { PredicateType::Transducer, { { x }, { y } }, std::make_shared<mata::nft::Nft>(nft) };
        Predicate p2 { PredicateType::Transducer, { { x }, { y } }, std::make_shared<mata::nft::Nft>(nft_other) };
        Predicate p3 { PredicateType::Transducer, { { x }, { y } }, std::make_shared<mata::nft::Nft>(nft) };
        CHECK(p1 != p2);
        CHECK(!(p1 < p1));
        CHECK(p1 == p1);
        CHECK(p1 == p3);
        CHECK(!(p1 < p3));
        CHECK(!(p3 < p1));

        std::set<Predicate> st{};
        st.insert(p1);
        st.insert(p2);
        st.insert(p3);
        CHECK(st.size() == 2);

        std::unordered_set<Predicate> st_un{};
        st_un.insert(p1);
        st_un.insert(p2);
        st_un.insert(p3);
        CHECK(st_un.size() == 2);
    }

   
}