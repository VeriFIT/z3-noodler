#ifndef _NOODLER_CONSTRAINT_SLICES_H_
#define _NOODLER_CONSTRAINT_SLICES_H_

#include <algorithm>
#include <map>
#include <numeric>
#include <unordered_map>
#include <vector>

namespace smt::noodler {

    /**
     * @brief Split constraints into independent slices.
     *
     * A slice is a connected component of the graph whose nodes are constraints and where two constraints are
     * connected iff they share a variable. Constraints of different slices share no variable, hence a conjunction
     * of constraints is satisfiable iff each slice is satisfiable on its own. In particular, if the conjunction is
     * unsatisfiable, some slice is unsatisfiable and its negation is a valid lemma that does not depend on the
     * constraints of the other slices.
     *
     * Note that the caller has to make sure that the variables capture all dependencies between the constraints
     * (e.g., constraints relating variables implicitly, such as transducers, must not be sliced).
     *
     * @tparam Var type of variables (hashable)
     * @param constraint_vars for each constraint (indexed from 0), the variables it contains
     * @return slices as vectors of indices of constraints (each sorted increasingly), the smaller slices first
     *         (slices of the same size are ordered by their smallest constraint); a constraint without variables
     *         forms a slice on its own
     */
    template<typename Var>
    std::vector<std::vector<unsigned>> compute_independent_slices(const std::vector<std::vector<Var>>& constraint_vars) {
        const unsigned num_constraints = static_cast<unsigned>(constraint_vars.size());

        // union-find over constraints
        std::vector<unsigned> parent(num_constraints);
        std::iota(parent.begin(), parent.end(), 0);
        auto find = [&parent](unsigned i) {
            while (parent[i] != i) {
                parent[i] = parent[parent[i]];
                i = parent[i];
            }
            return i;
        };

        // connect each constraint with the first constraint containing the same variable
        std::unordered_map<Var, unsigned> var_owner;
        for (unsigned i = 0; i < num_constraints; ++i) {
            for (const Var& var : constraint_vars[i]) {
                auto [it, inserted] = var_owner.emplace(var, i);
                if (!inserted) {
                    parent[find(i)] = find(it->second);
                }
            }
        }

        // group constraints by their roots (std::map keeps the slices ordered by their smallest constraint)
        std::map<unsigned, std::vector<unsigned>> slices_by_root;
        std::vector<unsigned> first_of_root(num_constraints, num_constraints);
        for (unsigned i = 0; i < num_constraints; ++i) {
            unsigned root = find(i);
            if (first_of_root[root] == num_constraints) {
                first_of_root[root] = i;
            }
            slices_by_root[first_of_root[root]].push_back(i);
        }

        std::vector<std::vector<unsigned>> slices;
        slices.reserve(slices_by_root.size());
        for (auto& [first, slice] : slices_by_root) {
            slices.push_back(std::move(slice));
        }
        std::stable_sort(slices.begin(), slices.end(), [](const auto& a, const auto& b) { return a.size() < b.size(); });
        return slices;
    }

} // namespace smt::noodler

#endif
