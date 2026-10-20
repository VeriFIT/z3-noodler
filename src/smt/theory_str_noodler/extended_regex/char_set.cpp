#include "char_set.h"

#include "util/zstring.h"

#include <algorithm>
#include <format>

namespace smt::noodler::extended_regex {
    CharSet CharSet::single(const Z3Char ch) {
        CharSet result;
        result.add(ch);
        return result;
    }

    CharSet CharSet::range(const Z3Char lower, const Z3Char upper) {
        CharSet result;
        result.add(lower, upper);
        return result;
    }

    CharSet CharSet::of(const std::span<const Z3Char> chars) {
        CharSet result;
        for (const Z3Char ch : chars) {
            result.add(ch);
        }
        return result;
    }

    CharSet CharSet::all() {
        return range(0, zstring::max_char());
    }

    void CharSet::add(const Z3Char ch) {
        add(ch, ch);
    }

    void CharSet::add(Z3Char lower, Z3Char upper) {
        upper = std::min<Z3Char>(upper, zstring::max_char());
        if (lower > upper) {
            return;
        }

        // Merge [lower, upper] with all the intervals that overlap it or are adjacent to it. All bounds are at most
        // zstring::max_char(), so adding one to them cannot overflow.
        auto first = std::ranges::find_if(m_intervals, [&](const Interval& interval) {
            return interval.upper + 1 >= lower;
        });
        auto last = first;
        while (last != m_intervals.end() && last->lower <= upper + 1) {
            lower = std::min(lower, last->lower);
            upper = std::max(upper, last->upper);
            ++last;
        }
        first = m_intervals.erase(first, last);
        m_intervals.insert(first, Interval {lower, upper});
    }

    void CharSet::add(const CharSet& other) {
        for (const auto& [lower, upper] : other.m_intervals) {
            add(lower, upper);
        }
    }

    CharSet CharSet::complement() const {
        CharSet result;
        Z3Char next = 0;  // the smallest character that is not covered by the intervals seen so far
        for (const auto& [lower, upper] : m_intervals) {
            if (lower > next) {
                result.m_intervals.push_back({next, lower - 1});
            }
            next = upper + 1;
        }
        if (next <= zstring::max_char()) {
            result.m_intervals.push_back({next, zstring::max_char()});
        }
        return result;
    }

    bool CharSet::is_empty() const {
        return m_intervals.empty();
    }

    bool CharSet::is_single(Z3Char& ch) const {
        if (m_intervals.size() != 1 || m_intervals[0].lower != m_intervals[0].upper) {
            return false;
        }
        ch = m_intervals[0].lower;
        return true;
    }

    uint64_t CharSet::size() const {
        uint64_t result = 0;
        for (const auto& [lower, upper] : m_intervals) {
            result += static_cast<uint64_t>(upper) - lower + 1;
        }
        return result;
    }

    const std::vector<CharSet::Interval>& CharSet::get_intervals() const {
        return m_intervals;
    }

    std::string CharSet::serialize() const {
        const CharSet complement_set = complement();
        const bool is_complement_smaller = complement_set.size() < size();
        std::string result = is_complement_smaller ? "^" : "";
        for (const auto& [lower, upper] : (is_complement_smaller ? complement_set : *this).m_intervals) {
            if (!result.empty()) {
                result += " ";
            }
            result += serialize_char(lower);
            if (upper != lower) {
                result += "-" + serialize_char(upper);
            }
        }
        return result;
    }

    app* CharSet::to_union_regex(seq_util& util_s) const {
        app* result = nullptr;
        for (const auto& [lower, upper] : m_intervals) {
            app* interval_regex = nullptr;
            if (lower == upper) {
                interval_regex = util_s.re.mk_to_re(util_s.str.mk_string(zstring(lower)));
            }
            else {
                interval_regex =
                    util_s.re.mk_range(util_s.str.mk_string(zstring(lower)), util_s.str.mk_string(zstring(upper)));
            }
            result = (result == nullptr) ? interval_regex : util_s.re.mk_union(result, interval_regex);
        }
        return result;
    }

    app_ref CharSet::to_regex(seq_util& util_s, ast_manager& m) const {
        if (is_empty()) {
            return {util_s.re.mk_empty(util_s.re.mk_re(util_s.mk_string_sort())), m};
        }
        const CharSet complement_set = complement();
        if (complement_set.is_empty()) {
            return {util_s.re.mk_full_char(nullptr), m};
        }
        if (complement_set.size() < size()) {
            return {util_s.re.mk_inter(util_s.re.mk_full_char(nullptr),
                                       util_s.re.mk_complement(complement_set.to_union_regex(util_s))),
                    m};
        }
        return {to_union_regex(util_s), m};
    }

    std::string serialize_char(const Z3Char ch) {
        if (ch >= 0x20 && ch <= 0x7E) {
            return std::string("'") + static_cast<char>(ch) + "'";
        }
        return std::format("'\\u{{{:x}}}'", ch);
    }
}  // namespace smt::noodler::extended_regex
