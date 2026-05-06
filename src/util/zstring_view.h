#pragma once


#include "util/z3_exception.h"
#include "util/zstring.h"

#include <cstddef>
#include <cstdint>
#include <functional>

class zstring_view {
    const uint32_t* m_data = nullptr;
    uint32_t m_size = 0;

public:
    zstring_view(const zstring& str)
        : m_data(str.begin()),
          m_size(str.length()) { }

    zstring_view() = default;
    zstring_view(const zstring_view& other) = default;

    zstring_view(const uint32_t* str, uint32_t len)
        : m_data(str),
          m_size(len) { }

    uint32_t length() const {
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

    bool operator==(const zstring_view other) const {
        if (m_size != other.m_size) {
            return false;
        }
        for (uint32_t i = 0; i < m_size; i++) {
            if (m_data[i] != other.m_data[i]) {
                return false;
            }
        }
        return true;
    }

    bool operator==(const zstring& str) const {
        zstring_view other(str);
        return *this == other;
    }

    zstring to_zstring() const {
        zstring res;
        for (uint32_t i = 0; i < m_size; ++i) {
            res += m_data[i];
        }
        return res;
    }
};

template<>
struct std::hash<zstring_view> {
    size_t operator()(const zstring_view& zv) const {
        std::size_t total_hash = 0;
        for (std::size_t i = 0; i < zv.length(); i++) {
            total_hash += std::hash<uint32_t> {}(zv[i]);
        }
        total_hash += std::hash<uint32_t> {}(zv.length());
        return total_hash;
    }
};
