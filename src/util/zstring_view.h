#pragma once


#include "util/zstring.h"

#include <cstddef>
#include <cstdint>

class zstring_view {
    const uint32_t* m_data;
    size_t m_size;

public:
    zstring_view(const zstring& str)
        : m_data(str.begin()),
          m_size(str.length()) { }

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
};
