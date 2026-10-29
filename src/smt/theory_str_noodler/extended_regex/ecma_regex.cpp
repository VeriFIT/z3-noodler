#include "ecma_regex.h"

#include "smt/theory_str_noodler/util.h"

#include "util/debug.h"
#include "util/zstring_view.h"

#include <algorithm>
#include <array>
#include <string>
#include <variant>

namespace smt::noodler::extended_regex::ecma {
    // ======================= UTILS =======================
    constexpr uint32_t HEX_SEQUENCE_LEN = 2;
    constexpr uint32_t UNICODE_ESCAPE_SEQUENCE_LEN = 4;
    constexpr Z3Char MAX_UNICODE_CODE_POINT = 0x10FFFF;
    constexpr Z3Char BACKSPACE_LITERAL = 8;
    // Quantifiers with finite bounds are translated by materializing that many copies of the subregex, so larger
    // bounds are unsupported.
    constexpr uint64_t MAX_QUANTIFIER_BOUND = 1'000'000;

    constexpr Z3Char CH_HT = 0x0009;      // Horizontal Tab
    constexpr Z3Char CH_VT = 0x000B;      // Vertical Tab
    constexpr Z3Char CH_FF = 0x000C;      // Form Feed
    constexpr Z3Char CH_SP = 0x0020;      // Space
    constexpr Z3Char CH_NBSP = 0x00A0;    // Non-Breaking Space
    constexpr Z3Char CH_ZWNBSP = 0xFEFF;  // Zero Width Non-Breaking Space (BOM)
    constexpr Z3Char CH_OGHAM = 0x1680;   // Ogham Space Mark
    constexpr Z3Char CH_ENQUAD = 0x2000;  // En Quad (first of the spaces U+2000-U+200A)
    constexpr Z3Char CH_HAIRSP = 0x200A;  // Hair Space (last of the spaces U+2000-U+200A)
    constexpr Z3Char CH_NNBSP = 0x202F;   // Narrow No-Break Space
    constexpr Z3Char CH_MMSP = 0x205F;    // Medium Mathematical Space
    constexpr Z3Char CH_IDSP = 0x3000;    // Ideographic Space
    constexpr Z3Char CH_LF = 0x000A;      // Line Feed
    constexpr Z3Char CH_CR = 0x000D;      // Carriage Return
    constexpr Z3Char CH_LS = 0x2028;      // Line Separator
    constexpr Z3Char CH_PS = 0x2029;      // Paragraph Separator

    // https://tc39.es/ecma262/2020/#sec-line-terminators
    constexpr std::array<Z3Char, 4> LINE_TERMINATORS {CH_LF, CH_CR, CH_LS, CH_PS};
    // https://tc39.es/ecma262/2020/#sec-white-space -- USP is every code point of the Unicode (13.0) category Zs, i.e.,
    // SP, NBSP, CH_OGHAM, CH_NNBSP, CH_MMSP, CH_IDSP and the range CH_ENQUAD-CH_HAIRSP, which is not listed here
    constexpr std::array<Z3Char, 10> WHITE_SPACES {CH_HT,     CH_VT,    CH_FF,    CH_SP,   CH_NBSP,
                                                   CH_ZWNBSP, CH_OGHAM, CH_NNBSP, CH_MMSP, CH_IDSP};

    // ================= ECMA REGEX LEXER ===================

    Token ECMALexer::get_next_token() {
        if (m_first_traverse) {
            perform_first_traverse();
            m_first_traverse = false;
        }

        if (m_position >= m_regex.length()) {
            return {TokenType::END_OF_INPUT, {}, zstring_view(nullptr, 0)};
        }

        m_lexeme_start_pos = m_position;

        if (m_in_char_class) {
            return get_token_char_class();
        }
        return get_token_standard();
    }

    bool ECMALexer::is_digit(const Z3Char digit) {
        return digit >= '0' && digit <= '9';
    }

    bool ECMALexer::is_alpha(const Z3Char digit) {
        return (digit >= 'A' && digit <= 'Z') || (digit >= 'a' && digit <= 'z');
    }

    bool ECMALexer::is_alnum(const Z3Char digit) {
        return is_alpha(digit) || is_digit(digit);
    }

    bool ECMALexer::is_hex_digit(const Z3Char digit) {
        return is_digit(digit) || (digit >= 'A' && digit <= 'F') || (digit >= 'a' && digit <= 'f');
    }

    bool ECMALexer::is_octal_digit(const Z3Char digit) {
        return digit >= '0' && digit <= '7';
    }

    bool ECMALexer::is_upper(const Z3Char digit) {
        return digit >= 'A' && digit <= 'Z';
    }

    uint32_t ECMALexer::alphabet_rank(const Z3Char digit) {
        if (is_upper(digit)) {
            return digit - 'A' + 1;
        }
        return digit - 'a' + 1;
    }

    Z3Char ECMALexer::hex2char(const zstring_view number) {
        Z3Char res = 0;
        for (uint32_t pos = 0; pos < number.length(); pos++) {
            const Z3Char hex_digit = number[pos];
            if (hex_digit >= '0' && hex_digit <= '9') {
                res = res * 16 + (hex_digit - '0');
            }
            else if (hex_digit >= 'A' && hex_digit <= 'F') {
                res = res * 16 + (hex_digit - 'A' + 10);
            }
            else {
                res = res * 16 + (hex_digit - 'a' + 10);
            }
        }
        return res;
    }

    Z3Char ECMALexer::oct2char(const zstring_view number) {
        Z3Char res = 0;
        for (uint32_t pos = 0; pos < number.length(); pos++) {
            const Z3Char digit = number[pos];
            if (is_octal_digit(digit)) {
                res = res * 8 + (digit - '0');
            }
        }
        return res;
    }

    Token ECMALexer::make_token(const TokenType type, const TokenPayload& payload) const {
        const uint32_t len = m_position - m_lexeme_start_pos;
        return {type, payload, zstring_view(&m_regex[m_lexeme_start_pos], len)};
    }

    Token ECMALexer::get_hex_escape_seq_token() {
        // hexadecimal escape sequence in format \xHH
        // currently m_position is right after '\x' -- hence the 1
        if (m_position + 1 >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\x'
            return make_token(TokenType::LITERAL, static_cast<Z3Char>('x'));
        }

        const Z3Char first_hex_digit = m_regex[m_position];
        const Z3Char second_hex_digit = m_regex[m_position + 1];

        // if the hex number is not well-formed, then '\x' is a literal 'x' and the rest is parsed separately
        if (!is_hex_digit(first_hex_digit) || !is_hex_digit(second_hex_digit)) {
            m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\x'
            return make_token(TokenType::LITERAL, static_cast<Z3Char>('x'));
        }

        // get decimal value of hex digits after '\x'
        Z3Char hex_val = hex2char(zstring_view(&m_regex[m_lexeme_start_pos + 2], HEX_SEQUENCE_LEN));
        m_position += 2;  // consume both hex digits
        return make_token(TokenType::LITERAL, hex_val);
    }

    Token ECMALexer::get_unicode_escape_seq_token() {
        // unicode escape sequence, handled as with the 'u' flag, in one of the formats
        //   \uHHHH, \uHHHH\uHHHH (surrogate pair encoding a single code point), \u{H...} (code point up to 0x10FFFF)
        // currently m_position is right after '\u'

        // if the sequence is malformed, then '\u' is a literal 'u' and the rest is parsed separately
        auto fallback = [&]() {
            m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\u'
            return make_token(TokenType::LITERAL, static_cast<Z3Char>('u'));
        };

        auto make_code_point_token = [&](const Z3Char code_point) {
            if (code_point > zstring::max_char()) {
                util::throw_error("Unsupported: character in ECMA regex unicode escape sequence exceeds the maximal "
                                  "character of the current string encoding");
            }
            return make_token(TokenType::LITERAL, code_point);
        };

        // reads 4 hex digits starting at pos into code_point; returns false if they are not all valid
        auto read_four_hex_digits = [&](const uint32_t pos, Z3Char& code_point) {
            if (pos + UNICODE_ESCAPE_SEQUENCE_LEN > m_regex.length()) {
                return false;
            }
            for (uint32_t i = 0; i < UNICODE_ESCAPE_SEQUENCE_LEN; i++) {
                if (!is_hex_digit(m_regex[pos + i])) {
                    return false;
                }
            }
            code_point = hex2char(zstring_view(&m_regex[pos], UNICODE_ESCAPE_SEQUENCE_LEN));
            return true;
        };

        // case \u{H...}
        if (m_position < m_regex.length() && m_regex[m_position] == '{') {
            uint32_t pos = m_position + 1;  // skip '{'
            Z3Char code_point = 0;
            while (pos < m_regex.length() && is_hex_digit(m_regex[pos])) {
                code_point = code_point * 16 + hex2char(zstring_view(&m_regex[pos], 1));
                if (code_point > MAX_UNICODE_CODE_POINT) {
                    util::throw_error("ECMA regex syntax error: Code point out of range in unicode escape sequence");
                }
                pos++;
            }
            if (pos == m_position + 1 || pos >= m_regex.length() || m_regex[pos] != '}') {
                return fallback();
            }
            m_position = pos + 1;  // consume hex digits and '}'
            return make_code_point_token(code_point);
        }

        // case \uHHHH
        Z3Char code_point;
        if (!read_four_hex_digits(m_position, code_point)) {
            return fallback();
        }
        m_position += UNICODE_ESCAPE_SEQUENCE_LEN;

        // case \uHHHH\uHHHH -- leading surrogate followed by trailing surrogate encodes a single code point
        const bool is_leading_surrogate = code_point >= 0xD800 && code_point <= 0xDBFF;
        if (is_leading_surrogate && m_position + 1 < m_regex.length() && m_regex[m_position] == '\\' &&
            m_regex[m_position + 1] == 'u') {
            Z3Char trailing;
            if (read_four_hex_digits(m_position + 2, trailing) && trailing >= 0xDC00 && trailing <= 0xDFFF) {
                code_point = 0x10000 + ((code_point - 0xD800) << 10) + (trailing - 0xDC00);
                m_position += 2 + UNICODE_ESCAPE_SEQUENCE_LEN;  // consume '\u' and the hex digits
            }
        }
        return make_code_point_token(code_point);
    }

    Token ECMALexer::get_control_escape_seq_token() {
        // control escape sequence in format \cC, where C is a control character
        // Currently m_position is right after '\c'
        if (m_position >= m_regex.length()) {
            util::throw_error("Syntax error in ECMA regex: Invalid control sequence" + std::string("\\c"));
        }

        const Z3Char control_char = m_regex[m_position];
        m_position++;  // consume the control character

        // [A-Za-z] characters allowed, otherwise error
        if (!is_alpha(control_char)) {
            util::throw_error("Syntax error in ECMA regex: Invalid control sequence" + std::string("\\c"));
        }
        return make_token(TokenType::LITERAL, alphabet_rank(control_char));
    }

    uint32_t ECMALexer::get_backref_name_len(const uint32_t name_start_pos) const {
        bool found_closing_bracket = false;
        std::size_t name_length = 0;
        for (std::size_t pos = name_start_pos; pos < m_regex.length(); pos++) {
            const Z3Char current_name_char = m_regex[pos];
            if (current_name_char == '>') {
                found_closing_bracket = true;
                break;
            }
            if (!is_alnum(current_name_char) && current_name_char != '_' && current_name_char != '$') {
                util::throw_error("ECMA regex syntax error: Invalid character in back reference name");
            }
            name_length++;
        }

        if (!found_closing_bracket) {
            util::throw_error("ECMA regex syntax error: Unclosed back reference name at the end of regex");
        }
        if (name_length == 0) {
            util::throw_error("ECMA regex syntax error: Empty back reference name");
        }
        return name_length;
    }

    Token ECMALexer::get_named_backref_token() {
        // '\k<name>'
        // currently at '<' after '\k'
        if (m_position >= m_regex.length()) {
            util::throw_error("ECMA regex syntax error: Invalid named backreference at the end of regex");
        }

        const Z3Char open_bracket_char = m_regex[m_position];
        if (open_bracket_char != '<') {
            util::throw_error("ECMA regex syntax error: Missing '<' in named backreference");
        }

        m_position++;  // consume '<'
        const uint32_t name_start_pos = m_position;
        const uint32_t name_length = get_backref_name_len(name_start_pos);
        m_position += name_length + 1;  // consume name and '>'

        const zstring_view backref_name {&m_regex[name_start_pos], name_length};
        auto it = m_named_groups.find(backref_name);
        if (it == m_named_groups.end()) {
            util::throw_error("ECMA regex syntax error: Backreference to undefined named group");
        }
        return make_token(TokenType::BACKREFERENCE, it->second);
    }

    Token ECMALexer::octal_or_backref(const Z3Char first_digit) {
        uint64_t decimal_val = first_digit - '0';
        const uint32_t fallback_pos = m_position;  // save position right after the first digit

        // greedily read as much digits as possible
        while (m_position < m_regex.length()) {
            const Z3Char digit = m_regex[m_position];
            if (!is_digit(digit)) {
                break;
            }
            // Once the value exceeds the number of groups, it cannot be a backreference -- stop accumulating to
            // prevent overflow (which could wrap it back to a valid group number).
            if (decimal_val <= m_num_capture_groups) {
                decimal_val = decimal_val * 10 + (digit - '0');
            }
            m_position++;
        }

        // try to match it to a backreference
        if (decimal_val > 0 && decimal_val <= m_num_capture_groups) {
            return make_token(TokenType::BACKREFERENCE, static_cast<Z3Char>(decimal_val));
        }

        // cannot be backreference --> match the input to an octal escape sequence
        m_position = fallback_pos;  // fallback to after the first digit
        return get_octal_escape_sequence_token(false, first_digit);
    }

    Token ECMALexer::get_octal_escape_sequence_token(const bool from_char_class, const Z3Char first_digit) {
        // m_position is right after first_digit. m_lexeme_start_pos is at '\'
        uint32_t max_possible_octal_len = 3;

        if (!from_char_class && (first_digit == '8' || first_digit == '9')) {
            util::throw_error("ECMA regex syntax error: backreference to nonexistent subpattern");
        }

        if (first_digit > '3') {
            max_possible_octal_len = 2;
        }

        uint32_t real_octal_len = 1;  // already parsed the first digit
        while (real_octal_len < max_possible_octal_len && m_position < m_regex.length()) {
            const Z3Char digit = m_regex[m_position];
            if (!is_octal_digit(digit)) {
                break;
            }
            m_position++;
            real_octal_len++;
        }

        // Octal string starts at m_lexeme_start_pos + 1 (skipping '\')
        Z3Char octal_val = oct2char(zstring_view(&m_regex[m_lexeme_start_pos + 1], real_octal_len));
        return make_token(TokenType::LITERAL, octal_val);
    }

    Token ECMALexer::get_named_capture_group_token() {
        // called right after '(?<'
        uint32_t name_length = 0;
        const uint32_t group_name_start_pos = m_position;
        bool found_closing_bracket = false;

        while (m_position < m_regex.length()) {
            const Z3Char current_char = m_regex[m_position];
            m_position++;

            if (current_char == '>') {
                found_closing_bracket = true;
                break;
            }
            if (!is_alnum(current_char) && current_char != '_' && current_char != '$') {
                util::throw_error("ECMA regex syntax error: Invalid character in capture group name");
            }
            name_length++;
        }
        if (!found_closing_bracket) {
            util::throw_error("ECMA regex syntax error: Unclosed group capture name");
        }
        if (name_length == 0) {
            util::throw_error("ECMA regex syntax error: Empty group name");
        }
        // payload is just the name of the group, lexeme is the whole '(?<name>' thing
        return make_token(TokenType::GROUP_NAMED_START, zstring_view(&m_regex[group_name_start_pos], name_length));
    }

    uint32_t ECMALexer::validate_and_get_bound(uint64_t& bound_value) {
        uint32_t parsed_digits = 0;
        while (m_position < m_regex.length()) {
            const Z3Char current_digit = m_regex[m_position];
            if (!is_digit(current_digit)) {
                break;
            }
            // Saturate just above the supported maximum to prevent overflow (and collision with UNBOUNDED)
            if (bound_value <= MAX_QUANTIFIER_BOUND) {
                bound_value = std::min(bound_value * 10 + (current_digit - '0'), MAX_QUANTIFIER_BOUND + 1);
            }
            m_position++;
            parsed_digits++;
        }
        return parsed_digits;
    }

    Token ECMALexer::make_quantifier_token(uint64_t min, uint64_t max) {
        // Called only once the quantifier is known to be well-formed (otherwise '{' is a literal).
        if (min > max) {
            util::throw_error("ECMA regex syntax error: numbers out of order in {} quantifier");
        }
        if (min > MAX_QUANTIFIER_BOUND || (max != UNBOUNDED && max > MAX_QUANTIFIER_BOUND)) {
            util::throw_error("Unsupported: ECMA regex quantifier bound exceeds " +
                              std::to_string(MAX_QUANTIFIER_BOUND));
        }
        return make_token(TokenType::QUANTIFIER, QuantifierRange {min, max});
    }

    Token ECMALexer::get_braced_quant_token() {
        // already have '{' consumed -> check range of quantifier
        uint64_t lower_bound = 0;
        uint32_t bound_digits = validate_and_get_bound(lower_bound);

        if (bound_digits == 0 || m_position >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(TokenType::LITERAL, static_cast<Z3Char>('{'));
        }

        // case '{n}'
        if (m_regex[m_position] == '}') {
            m_position++;  // consume '}'
            if (m_position < m_regex.length() && m_regex[m_position] == '?') {
                // skip lazy quantifier
                m_position++;
            }
            return make_quantifier_token(lower_bound, lower_bound);
        }

        if (m_regex[m_position] != ',') {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(TokenType::LITERAL, static_cast<Z3Char>('{'));
        }

        m_position++;  // skip comma
        if (m_position >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(TokenType::LITERAL, static_cast<Z3Char>('{'));
        }

        // case '{n,}'
        if (m_regex[m_position] == '}') {
            m_position++;  // consume '}'
            if (m_position < m_regex.length() && m_regex[m_position] == '?') {
                // skip lazy quantifier
                m_position++;
            }
            return make_quantifier_token(lower_bound, UNBOUNDED);
        }

        uint64_t upper_bound = 0;
        bound_digits = validate_and_get_bound(upper_bound);

        if (bound_digits == 0 || m_position >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(TokenType::LITERAL, static_cast<Z3Char>('{'));
        }

        // '}' after number -> case {n,m}
        if (m_regex[m_position] == '}') {
            m_position++;  // consume '}'
            if (m_position < m_regex.length() && m_regex[m_position] == '?') {
                m_position++;
            }
            return make_quantifier_token(lower_bound, upper_bound);
        }

        // not a well-formed quantifier --> '{' is a literal
        m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
        return make_token(TokenType::LITERAL, static_cast<Z3Char>('{'));
    }

    Token ECMALexer::get_lookbehind_or_named_group_token() {
        // called right after '(?<'
        if (m_position >= m_regex.length()) {
            util::throw_error("ECMA regex syntax error: Unfinished sequence '(?<'");
        }

        const Z3Char fourth_char = m_regex[m_position];
        m_position++;  // consume the '=' or '!'

        if (fourth_char == '=') {
            return make_token(TokenType::LOOKBEHIND_POS_START);
        }
        if (fourth_char == '!') {
            return make_token(TokenType::LOOKBEHIND_NEG_START);
        }

        // not '!' or '=' --> has to be named capture group (?<name>)
        // we consumed the first letter of the name --> step back
        m_position--;
        return get_named_capture_group_token();
    }

    Token ECMALexer::get_special_group_or_lookaround_token() {
        // called right after '(?'
        if (m_position >= m_regex.length()) {
            util::throw_error("ECMA regex syntax error: Unfinished sequence '(?' at the end of regex");
        }

        const Z3Char third_char = m_regex[m_position];
        m_position++;
        switch (third_char) {
        case ':': return make_token(TokenType::GROUP_NONCAPTURE_START);
        case '=': return make_token(TokenType::LOOKAHEAD_POS_START);
        case '!': return make_token(TokenType::LOOKAHEAD_NEG_START);
        case '<': return get_lookbehind_or_named_group_token();
        default: util::throw_error("ECMA regex syntax error: Invalid group indentifier"); return {};
        }
    }

    Token ECMALexer::get_group_token() {
        // called right after '('
        if (m_position >= m_regex.length() || m_regex[m_position] != '?') {
            return make_token(TokenType::GROUP_START);
        }
        m_position++;  // consume '?'
        return get_special_group_or_lookaround_token();
    }

    Token ECMALexer::get_escape_sequence_token() {
        // called right after '\'
        if (m_position >= m_regex.length()) {
            util::throw_error("ECMA regex syntax error: Unfinished escape sequence at the end of regex");
        }

        const Z3Char second_char = m_regex[m_position];
        m_position++;
        switch (second_char) {
        case 'd':
        case 'D':
        case 'w':
        case 'W':
        case 's':
        case 'S': return make_token(TokenType::CHAR_CLASS_ESCAPE, second_char);
        case 'b':
        case 'B': return make_token(TokenType::ASSERTION, second_char);
        case 'x': return get_hex_escape_seq_token();
        case 'u': return get_unicode_escape_seq_token();
        case 'c': return get_control_escape_seq_token();
        case 'k': return get_named_backref_token();
        case 't': return make_token(TokenType::LITERAL, CH_HT);
        case 'n': return make_token(TokenType::LITERAL, CH_LF);
        case 'r': return make_token(TokenType::LITERAL, CH_CR);
        case 'f': return make_token(TokenType::LITERAL, CH_FF);
        case 'v': return make_token(TokenType::LITERAL, CH_VT);
        case '0':
            // backreference cannot start with 0 -> always octal escape, e.g. \01 is U+0001
            return get_octal_escape_sequence_token(false, second_char);
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
        case '8':
        case '9': return octal_or_backref(second_char);
        default: return make_token(TokenType::LITERAL, second_char);
        }
    }

    Token ECMALexer::get_token_standard() {
        const Z3Char current_char = m_regex[m_position];
        m_position++;
        switch (current_char) {
        case '*':
        case '+':
        case '?':
            // lazy quantifier -- not relevant for membership problem, just skip it
            if (m_position < m_regex.length() && m_regex[m_position] == '?') {
                m_position++;
            }
            return make_token(TokenType::QUANTIFIER, current_char);
        case '{': return get_braced_quant_token();
        case '.': return make_token(TokenType::DOT);
        case '|': return make_token(TokenType::ALTERNATION);
        case '^':
        case '$': return make_token(TokenType::ASSERTION, current_char);
        case '(': return get_group_token();
        case ')': return make_token(TokenType::GROUP_END);
        case '\\': return get_escape_sequence_token();
        case '[':
            m_in_char_class = true;
            m_first_in_char_class = true;
            return make_token(TokenType::CHAR_CLASS_START);
        default: return make_token(TokenType::LITERAL, current_char);
        }
    }

    Token ECMALexer::get_char_class_escape_sequence_token() {
        // called right after '\' inside character class
        if (m_position >= m_regex.length()) {
            util::throw_error("ECMA regex syntax error: Unfinished escape sequence at the end of regex");
        }

        const Z3Char second_char = m_regex[m_position];
        m_position++;
        switch (second_char) {
        case 'd':
        case 'D':
        case 'w':
        case 'W':
        case 's':
        case 'S': return make_token(TokenType::CHAR_CLASS_ESCAPE, second_char);
        case 'x': return get_hex_escape_seq_token();
        case 'u': return get_unicode_escape_seq_token();
        case 'c': return get_control_escape_seq_token();
        case 'b': return make_token(TokenType::LITERAL, BACKSPACE_LITERAL);
        case 't': return make_token(TokenType::LITERAL, CH_HT);
        case 'n': return make_token(TokenType::LITERAL, CH_LF);
        case 'r': return make_token(TokenType::LITERAL, CH_CR);
        case 'f': return make_token(TokenType::LITERAL, CH_FF);
        case 'v': return make_token(TokenType::LITERAL, CH_VT);
        case '0':
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7': return get_octal_escape_sequence_token(true, second_char);
        default:
            // digits 8 and 9 in escape are '8' and '9' literals as well in char class
            return make_token(TokenType::LITERAL, second_char);
        }
    }

    Token ECMALexer::get_token_char_class() {
        const Z3Char current_char = m_regex[m_position];
        m_position++;

        const bool is_first = m_first_in_char_class;
        m_first_in_char_class = false;

        switch (current_char) {
        case ']': m_in_char_class = false; return make_token(TokenType::CHAR_CLASS_END);
        case '-': return make_token(TokenType::CHAR_CLASS_RANGE);
        case '^':
            if (is_first) {
                return make_token(TokenType::CHAR_CLASS_NEGATION);
            }
            else {
                return make_token(TokenType::LITERAL, current_char);
            }
        case '\\': return get_char_class_escape_sequence_token();
        default: return make_token(TokenType::LITERAL, current_char);
        }
    }

    std::pair<bool, zstring_view> ECMALexer::is_capture_or_named_capture(uint32_t position) const {
        position++;
        if (position >= m_regex.length()) {
            return {false, {}};
        }
        if (m_regex[position] != '?') {
            return {true, {}};
        }
        position++;
        if (position >= m_regex.length() || m_regex[position] != '<') {
            return {false, {}};
        }

        const uint32_t name_start = position + 1;
        uint32_t name_len = 0;
        bool found_closing_bracket = false;
        while (++position < m_regex.length()) {
            const Z3Char current_char = m_regex[position];
            if (current_char == '>') {
                found_closing_bracket = true;
                break;
            }
            if (!is_alnum(current_char) && current_char != '_' && current_char != '$') {
                break;
            }
            name_len++;
        }
        if (name_len > 0 && found_closing_bracket) {
            return {true, zstring_view(&m_regex[name_start], name_len)};
        }
        return {false, {}};
    }

    void ECMALexer::perform_first_traverse() {
        uint32_t open_parens_count = 0;
        bool in_char_class = false;
        bool escaped = false;

        for (uint32_t pos = 0; pos < m_regex.length(); pos++) {
            switch (m_regex[pos]) {
            case '[':
                if (escaped) {
                    escaped = false;  // '\[' --> ignore that
                }
                else {
                    in_char_class = true;
                }
                break;
            case ']':
                if (escaped) {
                    escaped = false;  // '\]' --> ignore that
                }
                else if (in_char_class) {
                    in_char_class = false;
                }
                break;
            case '\\': escaped = !escaped; break;
            case '(':
                if (escaped) {
                    escaped = false;  // '\(' --> ignore that
                }
                else if (!in_char_class) {
                    open_parens_count++;
                    auto [is_capture, name] = is_capture_or_named_capture(pos);
                    if (is_capture) {
                        m_num_capture_groups++;
                        if (name.length() > 0) {
                            if (m_named_groups.contains(name)) {
                                util::throw_error("ECMA Regex error: Duplicate capture group name");
                            }
                            m_named_groups.insert(std::make_pair(name, m_num_capture_groups));
                        }
                    }
                }
                break;
            case ')':
                if (escaped) {
                    escaped = false;  // '\)' --> ignore that
                }
                else if (!in_char_class) {
                    // match not only capture groups but any group structure (lookarounds,...)
                    // lets us throw early errors
                    if (open_parens_count > 0) {
                        open_parens_count--;
                    }
                    else {
                        util::throw_error("Syntax error: Unmatched ')' in regular expression");
                    }
                }
                break;
            default: escaped = false; break;
            }
        }
    }

    // =============== ECMA REGEX PARSER ===============

    CharSet ECMAParser::word_chars() {
        CharSet chars = CharSet::range('0', '9');
        chars.add('A', 'Z');
        chars.add('_');
        chars.add('a', 'z');
        return chars;
    }

    CharSet ECMAParser::white_space_chars() {
        CharSet chars = CharSet::of(WHITE_SPACES);
        chars.add(CH_ENQUAD, CH_HAIRSP);
        chars.add(CharSet::of(LINE_TERMINATORS));
        return chars;
    }

    CharSet ECMAParser::class_escape_chars(const Z3Char escape) {
        switch (escape) {
        case 'd': return CharSet::range('0', '9');
        case 'D': return CharSet::range('0', '9').complement();
        case 's': return white_space_chars();
        case 'S': return white_space_chars().complement();
        case 'w': return word_chars();
        case 'W': return word_chars().complement();
        default: util::throw_error("Syntax error in ECMA regex: Unknown character class escape"); return {};
        }
    }

    CharSet ECMAParser::dot_chars() {
        return CharSet::of(LINE_TERMINATORS).complement();
    }

    NodeRef ECMAParser::parse() {
        NodeRef ast = parse_disjunction();
        consume(TokenType::END_OF_INPUT, "Expected end of input");
        return ast;
    }

    void ECMAParser::next() {
        m_current_token = m_lexer.get_next_token();
    }

    bool ECMAParser::match(const TokenType type) {
        if (m_current_token.type == type) {
            next();
            return true;
        }
        return false;
    }

    Token ECMAParser::consume(const TokenType type, const char* message) {
        if (m_current_token.type == type) {
            const Token t = m_current_token;
            next();
            return t;
        }
        util::throw_error("Syntax error: " + std::string(message));
        return {};
    }

    NodeRef ECMAParser::parse_disjunction() {
        NodeRef alt = parse_alternative();

        if (m_current_token.type != TokenType::ALTERNATION) {
            return alt;
        }

        Alternation disj;
        disj.alternatives.push_back(std::move(alt));
        while (match(TokenType::ALTERNATION)) {
            disj.alternatives.push_back(parse_alternative());
        }
        return make_node(std::move(disj));
    }

    NodeRef ECMAParser::parse_alternative() {
        Concatenation alt;
        while (m_current_token.type != TokenType::ALTERNATION && m_current_token.type != TokenType::GROUP_END &&
               m_current_token.type != TokenType::END_OF_INPUT) {
            alt.terms.push_back(parse_term());
        }
        return make_node(std::move(alt));
    }

    NodeRef ECMAParser::parse_term() {
        switch (m_current_token.type) {
        case TokenType::ASSERTION:
        case TokenType::LOOKAHEAD_POS_START:
        case TokenType::LOOKAHEAD_NEG_START:
        case TokenType::LOOKBEHIND_POS_START:
        case TokenType::LOOKBEHIND_NEG_START: return parse_assertion();
        case TokenType::LITERAL:
        case TokenType::DOT:
        case TokenType::BACKREFERENCE:
        case TokenType::CHAR_CLASS_ESCAPE:
        case TokenType::GROUP_START:
        case TokenType::GROUP_NAMED_START:
        case TokenType::GROUP_NONCAPTURE_START:
        case TokenType::CHAR_CLASS_START: return parse_maybe_quantifier(parse_atom());
        default: util::throw_error("Syntax error in ECMA regex: Unexpected token in term"); return {};
        }
    }

    NodeRef ECMAParser::parse_maybe_quantifier(NodeRef term) {
        if (m_current_token.type != TokenType::QUANTIFIER) {
            return term;
        }
        const Token t = m_current_token;
        next();

        // ES2020 RepeatMatcher resets the captures inside the quantified subpattern at the start of every iteration
        // (step 4) and rejects an iteration beyond the minimum that matched the empty string (step 2.b)
        Repetition quant {.child = std::move(term), .resets_captures = true, .rejects_empty_iterations = true};
        if (std::holds_alternative<QuantifierRange>(t.payload)) {
            const QuantifierRange range = std::get<QuantifierRange>(t.payload);
            quant.min = range.min;
            quant.max = range.max;
        }
        else {
            SASSERT(std::holds_alternative<Z3Char>(t.payload) && "QUANTIFIER has no range");
            switch (std::get<Z3Char>(t.payload)) {
            case '*':
                quant.min = 0;
                quant.max = UNBOUNDED;
                break;
            case '+':
                quant.min = 1;
                quant.max = UNBOUNDED;
                break;
            case '?':
                quant.min = 0;
                quant.max = 1;
                break;
            default: util::throw_error("Syntax error in ECMA regex: Unknown quantifier");
            }
        }
        return make_node(std::move(quant));
    }

    NodeRef ECMAParser::parse_assertion() {
        const Token t = m_current_token;
        switch (t.type) {
        case TokenType::ASSERTION:
            SASSERT(std::holds_alternative<Z3Char>(t.payload) && "ASSERTION has no specifier");
            next();
            switch (std::get<Z3Char>(t.payload)) {
            // Without the multiline flag (flags are not supported), ^ and $ match only at the start and at
            // the end of the whole string
            case '^': return make_node(Anchor::START_OF_TEXT);
            case '$': return make_node(Anchor::END_OF_TEXT);
            case 'b': return make_word_boundary(word_chars(), false);
            case 'B': return make_word_boundary(word_chars(), true);
            default: util::throw_error("Syntax error in ECMA regex: Unknown assertion"); return {};
            }
        case TokenType::LOOKAHEAD_POS_START:
        case TokenType::LOOKAHEAD_NEG_START:
        case TokenType::LOOKBEHIND_POS_START:
        case TokenType::LOOKBEHIND_NEG_START: {
            next();
            NodeRef subpattern = parse_disjunction();
            consume(TokenType::GROUP_END, "Expected ')' after lookaround assertion");
            const bool is_forward =
                (t.type == TokenType::LOOKAHEAD_POS_START || t.type == TokenType::LOOKAHEAD_NEG_START);
            const bool is_positive =
                (t.type == TokenType::LOOKAHEAD_POS_START || t.type == TokenType::LOOKBEHIND_POS_START);
            return make_node(Lookaround {std::move(subpattern),
                                         is_forward ? LookaroundDirection::FORWARD : LookaroundDirection::BACKWARD,
                                         is_positive});
        }
        default: util::throw_error("Syntax error in ECMA regex: Expected assertion"); return {};
        }
    }

    NodeRef ECMAParser::parse_atom() {
        const Token t = m_current_token;
        switch (t.type) {
        case TokenType::LITERAL:
            SASSERT(std::holds_alternative<Z3Char>(t.payload) && "LITERAL has no literal value");
            next();
            return make_node(CharSet::single(std::get<Z3Char>(t.payload)));
        case TokenType::DOT: next(); return make_node(dot_chars());
        case TokenType::BACKREFERENCE:
            SASSERT(std::holds_alternative<Z3Char>(t.payload) && "BACKREFERENCE payload must be Z3Char");
            next();
            // A backreference to a group without a capture matches the empty string
            // https://tc39.es/ecma262/2020/#sec-backreferencematcher -- "e. If `s` is undefined, return c(x)."
            return make_node(Backreference {std::get<Z3Char>(t.payload), true});
        case TokenType::CHAR_CLASS_ESCAPE:
            SASSERT(std::holds_alternative<Z3Char>(t.payload) && "CHAR_CLASS_ESCAPE has no class specifier");
            next();
            return make_node(class_escape_chars(std::get<Z3Char>(t.payload)));
        case TokenType::GROUP_START:
        case TokenType::GROUP_NAMED_START:
        case TokenType::GROUP_NONCAPTURE_START: return parse_group();
        case TokenType::CHAR_CLASS_START: return parse_character_class();
        default: util::throw_error("Syntax error in ECMA regex: Unexpected token in atom"); return {};
        }
    }

    NodeRef ECMAParser::parse_group() {
        const TokenType type = m_current_token.type;
        if (type != TokenType::GROUP_START && type != TokenType::GROUP_NAMED_START &&
            type != TokenType::GROUP_NONCAPTURE_START) {
            util::throw_error("Syntax error in ECMA regex: Expected group start");
        }
        SASSERT((type != TokenType::GROUP_NAMED_START ||
                 std::holds_alternative<zstring_view>(m_current_token.payload)) &&
                "GROUP_NAMED_START has no name");

        // Named groups are numbered together with the other capture groups
        GroupID gid = 0;
        if (type != TokenType::GROUP_NONCAPTURE_START) {
            gid = ++m_current_group_id;
        }

        next();
        NodeRef subpattern = parse_disjunction();
        consume(TokenType::GROUP_END, "Expected ')' after group");

        // Non-capturing groups have no meaning for the subpattern
        if (type == TokenType::GROUP_NONCAPTURE_START) {
            return subpattern;
        }
        return make_node(Capture {gid, std::move(subpattern)});
    }

    NodeRef ECMAParser::parse_character_class() {
        consume(TokenType::CHAR_CLASS_START, "Expected '['");
        const bool is_negated = match(TokenType::CHAR_CLASS_NEGATION);

        // empty char class [] --> no character; negated empty char class [^] --> any character
        CharSet chars;
        parse_class_ranges(chars);
        consume(TokenType::CHAR_CLASS_END, "Expected ']'");
        return make_node(is_negated ? chars.complement() : std::move(chars));
    }

    void ECMAParser::add_atom_to_class(CharSet& chars, const CharClassAtom atom) {
        if (atom.is_escape) {
            chars.add(class_escape_chars(atom.val));
        }
        else {
            chars.add(atom.val);
        }
    }

    void ECMAParser::add_range_to_class(CharSet& chars, const Z3Char from, const Z3Char to) {
        if (from > to) {
            util::throw_error("ECMA Regex error: Character range out of order");
        }
        chars.add(from, to);
    }

    void ECMAParser::parse_class_ranges(CharSet& chars) {
        if (m_current_token.type == TokenType::LITERAL || m_current_token.type == TokenType::CHAR_CLASS_ESCAPE ||
            m_current_token.type == TokenType::CHAR_CLASS_RANGE) {
            const CharClassAtom first_atom = parse_class_atom();
            parse_class_ranges_tail(chars, first_atom);
        }
    }

    void ECMAParser::parse_class_ranges_tail(CharSet& chars, const CharClassAtom prev_atom) {
        switch (m_current_token.type) {
        case TokenType::CHAR_CLASS_RANGE:
            next();  // skip '-'
            parse_dash_tail(chars, prev_atom);
            parse_class_ranges(chars);
            break;
        case TokenType::LITERAL:
        case TokenType::CHAR_CLASS_ESCAPE: {
            add_atom_to_class(chars, prev_atom);
            const CharClassAtom next_atom = parse_class_atom_no_dash();
            parse_class_ranges_tail(chars, next_atom);
            break;
        }
        default:  // epsilon
            add_atom_to_class(chars, prev_atom);
            break;
        }
    }

    void ECMAParser::parse_dash_tail(CharSet& chars, const CharClassAtom atom_before_dash) {
        switch (m_current_token.type) {
        case TokenType::CHAR_CLASS_ESCAPE: {
            util::throw_error("ECMA Regex error: Character class as a bound of range");
            break;
        }
        case TokenType::CHAR_CLASS_RANGE:
            if (atom_before_dash.is_escape) {
                util::throw_error("ECMA Regex error: Character class as a bound of range");
            }
            add_range_to_class(chars, atom_before_dash.val, '-');
            next();
            break;
        case TokenType::LITERAL: {
            if (atom_before_dash.is_escape) {
                util::throw_error("ECMA Regex Error: Character class as a bound of range");
            }
            SASSERT(std::holds_alternative<Z3Char>(m_current_token.payload) && "LITERAL has no literal value");
            const Z3Char from = atom_before_dash.val;
            const Z3Char to = std::get<Z3Char>(m_current_token.payload);
            add_range_to_class(chars, from, to);
            next();
            break;
        }
        default:  // epsilon
            add_atom_to_class(chars, atom_before_dash);
            chars.add('-');
            break;
        }
    }

    CharClassAtom ECMAParser::parse_class_atom() {
        switch (m_current_token.type) {
        case TokenType::LITERAL:
        case TokenType::CHAR_CLASS_ESCAPE: return parse_class_atom_no_dash();
        case TokenType::CHAR_CLASS_RANGE: next(); return {false, static_cast<Z3Char>('-')};
        default: util::throw_error("Syntax error in ECMA regex: Expected class atom"); return {};
        }
    }

    CharClassAtom ECMAParser::parse_class_atom_no_dash() {
        const Token current_token = m_current_token;
        next();
        switch (current_token.type) {
        case TokenType::LITERAL:
            SASSERT(std::holds_alternative<Z3Char>(current_token.payload));
            return {false, std::get<Z3Char>(current_token.payload)};
        case TokenType::CHAR_CLASS_ESCAPE:
            SASSERT(std::holds_alternative<Z3Char>(current_token.payload));
            return {true, std::get<Z3Char>(current_token.payload)};
        default: util::throw_error("Syntax error in ECMA regex: Expected literal or escape sequence"); return {};
        }
    }
}  // namespace smt::noodler::extended_regex::ecma
