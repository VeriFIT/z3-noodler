/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    buffer.cpp

Abstract:

    Test buffers.

Author:

    Leonardo de Moura (leonardo) 2011-03-03.

Revision History:

--*/
#include "util/ptr_scoped_buffer.h"
#include "util/buffer.h"
#include <string>
#include <vector>

typedef std::pair<int, int> point;

template class ptr_scoped_buffer<point>;

static void tst1() {
    ptr_scoped_buffer<point> b;
    ENSURE(b.empty());
    b.push_back(alloc(point, 10, 20));
    ENSURE(!b.empty());
    point * p1 = alloc(point, 30, 20); 
    b.push_back(p1);
    ENSURE(b.get(1) == p1);
    b.push_back(alloc(point, 40, 20));
    ENSURE(b.size() == 3);
    b.pop_back();
    ENSURE(b.get(0) != p1);
    ENSURE(b.get(1) == p1);
    point * p2 = alloc(point, 30, 20); 
    ENSURE(b.get(0) != p2);
    b.set(0, p2);
    ENSURE(b.get(0) == p2);
    ENSURE(b.size() == 2);
    b.push_back(alloc(point, 40, 40));
}

// Appends and copies across the growth boundaries of the inline storage and of the heap storage,
// for a trivially copyable and a non-trivial element type, against std::vector.
template<typename T, typename Make>
static void tst_append(Make make) {
    for (unsigned prefix : {0u, 1u, 15u, 16u, 17u, 40u}) {
        for (unsigned n : {0u, 1u, 15u, 16u, 17u, 31u, 33u, 100u, 1000u}) {
            buffer<T, true, 16> b;
            std::vector<T> expected;
            for (unsigned i = 0; i < prefix; ++i) {
                b.push_back(make(i));
                expected.push_back(make(i));
            }
            std::vector<T> elems;
            for (unsigned i = 0; i < n; ++i)
                elems.push_back(make(prefix + i));
            b.append(n, elems.data());
            expected.insert(expected.end(), elems.begin(), elems.end());
            buffer<T, true, 16> copy(b);
            buffer<T, true, 16> assigned;
            assigned.push_back(make(7));
            assigned = b;
            for (buffer<T, true, 16> const* r : {&b, &copy, &assigned}) {
                ENSURE(r->size() == expected.size());
                for (unsigned i = 0; i < expected.size(); ++i)
                    ENSURE((*r)[i] == expected[i]);
            }
        }
    }
}

void tst_buffer() {
    tst1();
    tst_append<unsigned>([](unsigned i) { return i * 2654435761u; });
    tst_append<std::string>([](unsigned i) { return std::string(i % 40, static_cast<char>('a' + i % 26)); });
}
