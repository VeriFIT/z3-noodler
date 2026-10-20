#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"

#include <cstdint>
#include <span>
#include <string>
#include <vector>

namespace smt::noodler::extended_regex {
    // A character of a Z3 string, i.e., a code point
    using Z3Char = uint32_t;

    /**
     * A set of characters of Z3 strings, i.e., of the code points from 0 to zstring::max_char().
     *
     * The set is represented by its maximal intervals in increasing order, so equal sets have equal representations.
     * Characters beyond zstring::max_char() cannot occur in Z3 strings, therefore they are never added to the set.
     */
    class CharSet {
    public:
        struct Interval {
            Z3Char lower;
            Z3Char upper;  // inclusive

            bool operator==(const Interval&) const = default;
        };

        CharSet() = default;

        static CharSet single(Z3Char ch);
        static CharSet range(Z3Char lower, Z3Char upper);
        static CharSet of(std::span<const Z3Char> chars);
        // All characters of Z3 strings
        static CharSet all();

        void add(Z3Char ch);
        void add(Z3Char lower, Z3Char upper);
        void add(const CharSet& other);

        // The characters of Z3 strings that are not in this set
        CharSet complement() const;

        bool is_empty() const;
        // Return true if the set contains exactly one character, which is then stored to @p ch
        bool is_single(Z3Char& ch) const;
        // The number of characters in the set
        uint64_t size() const;
        const std::vector<Interval>& get_intervals() const;

        bool operator==(const CharSet&) const = default;

        /**
         * @brief Serialize the set into the list of its intervals, e.g., 'a'-'z' '_'.
         *
         * If the complement of the set has fewer characters than the set, the complement is serialized after '^'
         * instead, e.g., ^ 'a' for all characters except 'a'.
         */
        std::string serialize() const;

        /**
         * @brief Make a regex matching exactly one character from the set.
         *
         * Noodler adds every character of re.range to the alphabet of automata, so a set whose complement has fewer
         * characters is given by the complement, i.e., as (re.inter re.allchar (re.comp complement)).
         *
         * @param util_s Z3 sequence/regex utilities.
         * @param m      The Z3 AST manager.
         * @return app_ref The regex of the set.
         */
        app_ref to_regex(seq_util& util_s, ast_manager& m) const;

    private:
        std::vector<Interval> m_intervals;

        // The union of the regexes of all intervals, null for the empty set
        app* to_union_regex(seq_util& util_s) const;
    };

    /**
     * @brief Serialize the character @p ch in single quotes, characters that are not printable ASCII are given as
     * \u{...}, e.g., 'a' or '\u{a}'.
     */
    std::string serialize_char(Z3Char ch);
}  // namespace smt::noodler::extended_regex
