#pragma once


#include "util/z3_exception.h"
#include "util/zstring.h"

#include <cstddef>
#include <cstdint>

class zstring_view {
    const uint32_t* m_data = nullptr;
    size_t m_size = 0;

public:
    zstring_view(const zstring& str)
        : m_data(str.begin()),
          m_size(str.length()) { }

    zstring_view() = default;
    zstring_view(const zstring_view& other) = default;

    zstring_view(const uint32_t* str, uint32_t len)
        : m_data(str),
          m_size(len) { }

    size_t length() const {
        return m_size;
    }

    const uint32_t& operator[](const size_t index) const {
        return m_data[index];
    }

    const uint32_t* data() const {
        return m_data;
    }

    const uint32_t* operator+(const uint32_t offset) const {
        if (offset > m_size) {
            // TODO: better exceptions
            throw default_exception("Internal error: zstring_view operator+ offset > size");
        }
        return m_data + offset;
    }
};
