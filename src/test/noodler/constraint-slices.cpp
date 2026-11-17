#include <string>
#include <vector>

#include <catch2/catch_test_macros.hpp>

#include "smt/theory_str_noodler/constraint_slices.h"

using namespace smt::noodler;

TEST_CASE("compute_independent_slices", "[noodler]") {
    using Slices = std::vector<std::vector<unsigned>>;

    SECTION("no constraints") {
        CHECK(compute_independent_slices(std::vector<std::vector<int>>{}).empty());
    }

    SECTION("all constraints connected, also transitively") {
        // 0: {x, y}, 1: {y, z}, 2: {z}
        std::vector<std::vector<std::string>> vars{ {"x", "y"}, {"y", "z"}, {"z"} };
        CHECK(compute_independent_slices(vars) == Slices{ {0, 1, 2} });
    }

    SECTION("independent constraints, smaller slices first") {
        // 0: {x}, 1: {y}, 2: {x, w}, 3: {}, 4: {w}, 5: {y}
        std::vector<std::vector<std::string>> vars{ {"x"}, {"y"}, {"x", "w"}, {}, {"w"}, {"y"} };
        CHECK(compute_independent_slices(vars) == Slices{ {3}, {1, 5}, {0, 2, 4} });
    }

    SECTION("constraints connected only through a later constraint") {
        // 0: {a}, 1: {b}, 2: {a, b}
        std::vector<std::vector<int>> vars{ {1}, {2}, {1, 2} };
        CHECK(compute_independent_slices(vars) == Slices{ {0, 1, 2} });
    }

    SECTION("constraints without variables are separate slices ordered by index") {
        std::vector<std::vector<int>> vars{ {}, {7}, {}, {7} };
        CHECK(compute_independent_slices(vars) == Slices{ {0}, {2}, {1, 3} });
    }
}
