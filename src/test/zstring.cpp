#include "util/debug.h"
#include "util/trace.h"
#include "util/zstring.h"
#include <iostream>
#include <vector>

// Encode and check for roundtrip all printable ASCII characters.
static void tst_ascii_roundtrip() {
    unsigned ascii_min = 0x20; // ' '
    unsigned ascii_max = 0x7E; // '~'

    for (unsigned i = ascii_min; i <= ascii_max; ++i) {
        zstring input(i);
        std::string expected(1, i);
        bool roundtrip_ok = input.encode() == expected;

        if (!roundtrip_ok) {
            std::cout << "Failed to roundtrip printable ASCII char: " << expected
                      << "\n" << std::flush;
            ENSURE(roundtrip_ok);
        }
    }
}

// Test that control characters are properly escaped.
static void tst_control_chars_escaped() {
    // Test DEL character (0x7F / 127)
    zstring del_char(0x7Fu);
    std::string del_encoded = del_char.encode();
    bool del_ok = del_encoded == "\\u{7f}";
    
    if (!del_ok) {
        std::cout << "Failed to escape DEL character (0x7F): got '" << del_encoded 
                  << "', expected '\\u{7f}'\n" << std::flush;
        ENSURE(del_ok);
    }
    
    // Test a few other control characters below 0x20
    zstring null_char(0x00u);
    std::string null_encoded = null_char.encode();
    bool null_ok = null_encoded == "\\u{0}";
    
    if (!null_ok) {
        std::cout << "Failed to escape NULL character (0x00): got '" << null_encoded 
                  << "', expected '\\u{0}'\n" << std::flush;
        ENSURE(null_ok);
    }
    
    zstring tab_char(0x09u);
    std::string tab_encoded = tab_char.encode();
    bool tab_ok = tab_encoded == "\\u{9}";
    
    if (!tab_ok) {
        std::cout << "Failed to escape TAB character (0x09): got '" << tab_encoded 
                  << "', expected '\\u{9}'\n" << std::flush;
        ENSURE(tab_ok);
    }
}

static zstring tst_mk_zstring(std::string const& s) {
    return zstring(s.c_str());
}

// Compare indexofu and contains with a search at every position, on all strings over {a, b} up to length 7.
static void tst_indexof_exhaustive() {
    std::vector<std::string> words{""};
    for (size_t first = 0; first < words.size(); ++first) {
        if (words[first].size() < 7) {
            words.push_back(words[first] + "a");
            words.push_back(words[first] + "b");
        }
    }
    for (std::string const& text : words) {
        zstring ztext = tst_mk_zstring(text);
        for (std::string const& pattern : words) {
            if (pattern.size() > 4) continue;
            zstring zpattern = tst_mk_zstring(pattern);
            ENSURE(ztext.contains(zpattern) == (text.find(pattern) != std::string::npos));
            for (unsigned offset = 0; offset <= text.size() + 1; ++offset) {
                int expected = -1;
                if (pattern.empty() && offset <= text.size()) expected = offset;
                else if (offset < text.size()) {
                    size_t pos = text.find(pattern, offset);
                    expected = pos == std::string::npos ? -1 : static_cast<int>(pos);
                }
                ENSURE(ztext.indexofu(zpattern, offset) == expected);
            }
        }
    }
}

// A long text and pattern repeating one character, where comparing at every position is quadratic.
static void tst_indexof_repetitive() {
    zstring text = tst_mk_zstring(std::string(200000, ':') + "x");
    ENSURE(text.indexofu(tst_mk_zstring(std::string(50000, ':') + "x"), 0) == 150000);
    ENSURE(!text.contains(tst_mk_zstring(std::string(50000, ':') + "y")));
}

void tst_zstring() {
    tst_ascii_roundtrip();
    tst_control_chars_escaped();
    tst_indexof_exhaustive();
    tst_indexof_repetitive();
}
