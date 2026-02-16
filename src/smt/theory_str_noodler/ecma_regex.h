#ifndef _NOODLER_ECMA_REGEX_H_
#define _NOODLER_ECMA_REGEX_H_
#include "util/zstring.h"

namespace smt::noodler
{
    struct regex_constraint_graph
    {
    };

    class ecma_regex_handler
    {
    private:
        zstring m_regex;

    public:
        explicit ecma_regex_handler(zstring regex_pattern) : m_regex(std::move(regex_pattern))
        {
        }

        void build_rcg();
        void generate_constraints();
    };
} // namespace smt::noodler

#endif  // _NOODLER_ECMA_REGEX_H_
