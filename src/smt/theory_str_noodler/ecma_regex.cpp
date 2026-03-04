#include "ecma_regex.h"

#include "util/z3_exception.h"
#include "util/zstring_view.h"

#include <cctype>
#include <cstdint>
#include <limits>

namespace smt::noodler::ecma {

    // ======================= UTILS =======================
    constexpr uint32_t HEX_SEQUENCE_LEN = 3;
    constexpr uint32_t UNICODE_ESCAPE_SEQUENCE_LEN = 4;
    constexpr uint32_t CONTROL_SEQUENCE_LEN = 1;
    constexpr uint32_t BACKSLASH_OFFSET = 1;
    constexpr uint32_t GROUP_NAME_START_OFFSET = 3;
    constexpr uint32_t NAMED_BACKREF_MINIMAL_LEN = 4;
    constexpr uint32_t CLOSING_ANGLE_BRACKET_OFFSET = 1;
    constexpr uint32_t UNICODE_ESCAPE_OFFSET = 2;
    constexpr uint32_t UNICODE_LEXEME_LENGTH = 6;
    constexpr uint32_t CONTROL_CHAR_OFFSET = 2;
    constexpr uint32_t CONTROL_ESCAPE_SEQ_LEXEME_LEN = 3;
    constexpr uint32_t OPEN_ANGLED_BRACKET_OFFSET = 2;
    constexpr uint32_t BACKREF_NAME_OFFSET = 2;
    constexpr uint32_t NAMED_BACKREF_LEN_NO_NAME = 4;

    bool ecma_lexer::is_digit(const uint32_t digit) {
        return digit >= '0' && digit <= '9';
    }

    bool ecma_lexer::is_alpha(const uint32_t digit) {
        return (digit >= 'A' && digit <= 'Z') || (digit >= 'a' && digit <= 'z');
    }

    bool ecma_lexer::is_alnum(const uint32_t digit) {
        return is_alpha(digit) || is_digit(digit);
    }

    bool ecma_lexer::is_hex_digit(const uint32_t digit) {
        return is_digit(digit) || (digit >= 'A' && digit <= 'F') || (digit >= 'a' && digit <= 'f');
    }

    bool ecma_lexer::is_octal_digit(const uint32_t digit) {
        return digit >= '0' && digit <= '7';
    }

    bool ecma_lexer::is_upper(const uint32_t digit) {
        return digit >= 'A' && digit <= 'Z';
    }

    uint32_t ecma_lexer::alphabet_rank(const uint32_t digit) {
        if (is_upper(digit)) {
            return digit - 'A' + 1;
        }
        return digit - 'a' + 1;
    }

    uint32_t ecma_lexer::hex2dec(zstring_view number) {
        uint32_t res = 0;
        for (uint32_t pos = 0; pos < number.length(); pos++) {
            const uint32_t hex_digit = number[pos];
            if (hex_digit >= '0' && hex_digit <= '9') {
                res = res * 16 + (hex_digit - '0');
            } else if (hex_digit >= 'A' && hex_digit <= 'F') {
                res = res * 16 + (hex_digit - 'A' + 10);
            } else {
                res = res * 16 + (hex_digit - 'a' + 10);
            }
        }
        return res;
    }

    uint32_t ecma_lexer::oct2dec(zstring_view number) {
        uint32_t res = 0;
        for (uint32_t pos = 0; pos < number.length(); pos++) {
            const uint32_t digit = number[pos];
            if (is_octal_digit(digit)) {
                res = res * 8 + (digit - '0');
            }
        }
        return res;
    }

    token ecma_lexer::get_hex_escape_seq_token() const {
        // hexadecimal escape sequence in format \xHH
        if (m_position + HEX_SEQUENCE_LEN >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Unfinished hexadecimal escape sequence at the end of regex");
        }

        const uint32_t first_hex_digit = m_regex[m_position + 2];
        const uint32_t second_hex_digit = m_regex[m_position + 3];

        if (!is_hex_digit(first_hex_digit) || !is_hex_digit(second_hex_digit)) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Invalid hexadecimal escape sequence at " +
                                    std::to_string(m_position + 2) + " in regex");
        }

        return {token_type::LITERAL, hex2dec(zstring_view(&m_regex[m_position + 2], 2)),
                zstring_view(&m_regex[m_position], m_position)};
    }

    token ecma_lexer::get_unicode_escape_seq_token() const {
        // unicode escape sequence in format \uHHHH
        if (m_position + UNICODE_ESCAPE_OFFSET + UNICODE_ESCAPE_SEQUENCE_LEN >= m_regex.length()) {
            throw default_exception("Lexical Error: Unfinished unicode escape sequence at the end of regex");
        }

        const uint32_t first_unicode_digit_pos = m_position + UNICODE_ESCAPE_OFFSET;
        for (uint32_t i = 0; i < UNICODE_ESCAPE_SEQUENCE_LEN; i++) {
            const uint32_t current_char = m_regex[first_unicode_digit_pos + i];
            if (!is_hex_digit(static_cast<unsigned char>(current_char))) {
                throw default_exception("Lexical Error: Invalid unicode escape sequence");
            }
        }

        return {token_type::LITERAL,
                hex2dec(zstring_view(&m_regex[m_position + UNICODE_ESCAPE_OFFSET], UNICODE_ESCAPE_SEQUENCE_LEN)),
                zstring_view(&m_regex[m_position], UNICODE_LEXEME_LENGTH)};
    }

    token ecma_lexer::get_control_escape_seq_token() const {
        if (m_position + CONTROL_SEQUENCE_LEN >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Unfinished control escape sequence at the end of regex");
        }

        const uint32_t control_char = m_regex[m_position + CONTROL_CHAR_OFFSET];

        // [A-Za-z] characters allowed,
        if (!is_alpha(control_char)) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Invalid control escape sequence at position " +
                                    std::to_string(m_position + CONTROL_CHAR_OFFSET));
        }

        return {token_type::LITERAL, alphabet_rank(control_char),
                zstring_view(&m_regex[m_position], CONTROL_ESCAPE_SEQ_LEXEME_LEN)};
    }

    uint32_t ecma_lexer::get_backref_name_len(const uint32_t name_start_pos) {
        bool found_closing_bracket = false;
        uint32_t name_length = 0;
        for (uint32_t pos = name_start_pos; pos < m_regex.length(); pos++) {
            const uint32_t current_name_char = m_regex[pos];
            if (current_name_char == '>') {
                found_closing_bracket = true;
                break;
            }
            if (!is_alnum(current_name_char) && current_name_char != '_' && current_name_char != '$') {
                // TODO: implement own exceptions later
                throw default_exception("Lexical Error: Invalid character in back reference name at position " +
                                        std::to_string(pos + 1) + " in regex");
            }
            name_length++;
        }

        if (!found_closing_bracket) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Unclosed back reference name at the end of regex");
        }
        if (name_length == 0) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Empty back reference name at position " +
                                    std::to_string(name_start_pos + 1) + " in regex");
        }
        return name_length;
    }

    token ecma_lexer::get_named_backref_token() {
        // '\k<name>' ---> tokenLength = 3 + len(name) + 1, where name is nonempty string
        // ---> at least 5 chars in total, further checks done when resolving name
        // currently at '\' ---> 4 more at least to go
        if (m_position + NAMED_BACKREF_MINIMAL_LEN >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Invalid named backreference at the end of regex");
        }

        const uint32_t open_bracket_char = m_regex[m_position + OPEN_ANGLED_BRACKET_OFFSET];
        if (open_bracket_char != '<') {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Missing open angle bracket in named back reference at position " +
                                    std::to_string(m_position + OPEN_ANGLED_BRACKET_OFFSET) + " in regex");
        }

        const uint32_t name_start_pos = m_position + BACKREF_NAME_OFFSET;
        uint32_t name_length = get_backref_name_len(name_start_pos);

        return {token_type::BACKREFERENCE, zstring_view(&m_regex[m_position + BACKREF_NAME_OFFSET], name_length),
                zstring_view(&m_regex[m_position], NAMED_BACKREF_LEN_NO_NAME + name_length)};
    }

    token ecma_lexer::octal_or_backref() {
        // TODO: dodelat
        uint32_t num_of_digits = 1;
        uint32_t current_pos = m_position + 2;
        while (current_pos < m_regex.length() && is_digit(m_regex[current_pos])) {
            num_of_digits++;
            current_pos++;
        }
        return {token_type::BACKREFERENCE, {}, {}};
    }

    token ecma_lexer::get_octal_escape_sequence_token() {
        uint32_t max_possible_octal_len = 3;
        // i.e. \123, m_position currently at '\'
        const uint32_t first_digit = m_regex[m_position + 1];
        // no need to check, we got here through cases '1' -- '7'
        if (first_digit > '3') {
            max_possible_octal_len = 2;
        }

        uint32_t real_octal_len = 0;
        uint32_t decimal_value = 0;
        for (uint32_t pos = 1; pos <= max_possible_octal_len; pos++) {
            if (m_position + pos >= m_regex.length()) {
                break;
            }
            const uint32_t digit = m_regex[m_position + pos];
            if (!is_octal_digit(digit)) {
                break;
            }
            decimal_value = decimal_value * 8 + (digit - '0');
            real_octal_len++;
        }

        return {token_type::LITERAL, oct2dec(zstring_view(&m_regex[m_position + BACKSLASH_OFFSET], real_octal_len)),
                zstring_view(&m_regex[m_position], BACKSLASH_OFFSET + real_octal_len)};
    }

    token ecma_lexer::get_named_capture_group_token(const uint32_t group_name_start_pos) const {
        uint32_t name_length = 0;
        uint32_t current_pos = group_name_start_pos;
        bool found_closing_bracket = false;

        while (current_pos < m_regex.length()) {
            const uint32_t current_char = m_regex[current_pos];
            if (current_char == '>') {
                found_closing_bracket = true;
                break;
            }
            // TODO: there can be unicode blob in the group name, implement it
            if (!is_alnum(current_char) && current_char != '_' && current_char != '$') {
                // TODO: implement own exceptions later
                throw default_exception("Lexical error: Invalid character in capture group name at position " +
                                        std::to_string(current_pos + 1) + " in regex");
            }
            name_length++;
            current_pos++;
        }
        if (!found_closing_bracket) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical error: Unclosed group capture name at position " +
                                    std::to_string(current_pos + 1) + " in regex");
        }
        // payload is just the name of the group, lexeme is the whole '(?<name>' thing
        return {
            token_type::GROUP_NAMED_START, zstring_view(&m_regex[group_name_start_pos], name_length),
            zstring_view(&m_regex[m_position], GROUP_NAME_START_OFFSET + name_length + CLOSING_ANGLE_BRACKET_OFFSET)};
    }

    bool ecma_lexer::validate_and_get_bound(uint32_t& bound, uint32_t& current_pos) const {
        uint32_t current_digit;
        uint32_t parsed_digits = 0;
        while (true) {
            // Regex is smth like "abc{123" -> valid, just not quantifier
            if (m_position + current_pos >= m_regex.length()) {
                return false;
            }
            current_digit = m_regex[m_position + current_pos];
            if (current_digit < '0' || current_digit > '9') {
                break;
            }
            bound = bound * 10 + static_cast<uint32_t>(current_digit - '0');
            current_pos++;
            parsed_digits++;
        }
        return (parsed_digits > 0);
    }

    token ecma_lexer::get_braced_quant_token() {
        // if the quantifier is not well-formed, we assume the '{' is a literal and return the position back to it
        uint32_t fallback_pos = m_position;

        // already have '{' from parent function -> check range of quantifier
        // lower bound
        uint32_t lower_bound = 0;
        uint32_t current_pos = 1;
        if (!validate_and_get_bound(lower_bound, current_pos)) {
            m_position = fallback_pos;
            return {token_type::LITERAL, static_cast<uint32_t>('{'), zstring_view(&m_regex[m_position], 1)};
        }

        if (m_position + current_pos >= m_regex.length()) {
            return {token_type::LITERAL, static_cast<uint32_t>('{'), zstring_view(&m_regex[m_position], 1)};
        }

        // after lower bound, there is either ',' or '}', otherwise not quantifier
        uint32_t current_char = m_regex[m_position + current_pos];

        // case {n}
        if (current_char == '}') {
            return {token_type::QUANTIFIER, quantifier_range(lower_bound, lower_bound),
                    zstring_view(&m_regex[m_position], 3)};
        }

        if (current_char != ',') {
            return {token_type::LITERAL, static_cast<uint32_t>('{'), zstring_view(&m_regex[m_position], 1)};
        }
        // skip comma
        current_pos++;
        if (m_position + current_pos >= m_regex.length()) {
            return {token_type::LITERAL, static_cast<uint32_t>('{'), zstring_view(&m_regex[m_position], 1)};
        }

        // case '{n,}'
        current_char = m_regex[m_position + current_pos];
        if (current_char == '}') {
            return {token_type::QUANTIFIER, quantifier_range(lower_bound, std::numeric_limits<uint32_t>::max()),
                    zstring_view(&m_regex[m_position], 4)};
        }

        // upper bound of the quantifier
        uint32_t upper_bound = 0;
        if (!validate_and_get_bound(upper_bound, current_pos)) {
            m_position = fallback_pos;
            return {token_type::LITERAL, static_cast<uint32_t>('{'), zstring_view(&m_regex[m_position], 1)};
        }

        if (m_position + current_pos >= m_regex.length()) {
            return {token_type::LITERAL, static_cast<uint32_t>('{'), zstring_view(&m_regex[m_position], 1)};
        }

        // '}' after number -> case {n,m}
        current_char = m_regex[m_position + current_pos];
        if (current_char == '}') {
            return {token_type::QUANTIFIER, quantifier_range(lower_bound, upper_bound),
                    zstring_view(&m_regex[m_position], m_token_len)};
        }

        m_position = fallback_pos;
        return {token_type::LITERAL, static_cast<uint32_t>('{'), zstring_view(&m_regex[m_position], m_token_len)};
    }

    token ecma_lexer::get_lookbehind_or_named_group_token() {
        if (m_position + 3 >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical error: Unfinished sequence '(?<' at position" +
                                    std::to_string(m_position + 3) + " in regex");
        }
        const uint32_t fourth_char = m_regex[m_position + 3];

        switch (fourth_char) {
            case '=':
                return {token_type::LOOKBEHIND_POS_START, {}, zstring_view(&m_regex[m_position], 4)};
            case '!':
                return {token_type::LOOKAHEAD_POS_START, {}, zstring_view(&m_regex[m_position], 4)};
            default:
                return get_named_capture_group_token(m_position + 3);
        }
    }

    token ecma_lexer::get_special_group_or_lookaround_token() {
        if (m_position + 2 >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical error: Unfinished sequence '(?' at the end of regex");
        }
        const uint32_t third_char = m_regex[m_position + 2];

        switch (third_char) {
            case ':':
                return {token_type::GROUP_NONCAPTURE_START, {}, zstring_view(&m_regex[m_position], 3)};
            case '=':
                return {token_type::LOOKAHEAD_POS_START, {}, zstring_view(&m_regex[m_position], 3)};
            case '!':
                return {token_type::LOOKAHEAD_NEG_START, {}, zstring_view(&m_regex[m_position], 3)};
            case '<':
                return get_lookbehind_or_named_group_token();
            default:
                // TODO: implement own exceptions later
                throw default_exception("Lexical error: Invalid group indentifier at position" +
                                        std::to_string(m_position + 2) + " in regex");
        }
    }

    token ecma_lexer::get_group_token() {
        // Lexically it is correct, return the token and let the parser throw a syntax error
        if (m_position + 1 >= m_regex.length()) {
            return {token_type::GROUP_START, {}, zstring_view(&m_regex[m_position], 1)};
        }

        const uint32_t second_char = m_regex[m_position + 1];
        if (second_char != '?') {
            return {token_type::GROUP_START, {}, zstring_view(&m_regex[m_position], 1)};
        }

        return get_special_group_or_lookaround_token();
    }

    token ecma_lexer::get_escape_sequence_token() {
        if (m_position + 1 >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical error: Unfinished escape sequence at the end of regex");
        }

        const uint32_t second_char = m_regex[m_position + 1];
        switch (second_char) {
            case 'd':
            case 'D':
            case 'w':
            case 'W':
            case 's':
            case 'S':
                return {token_type::CHAR_CLASS_ESCAPE, second_char, zstring_view(&m_regex[m_position], 2)};
            case 'b':
            case 'B':
                return {token_type::ASSERTION, second_char, zstring_view(&m_regex[m_position], 2)};
            case 'x':
                return get_hex_escape_seq_token();
            case 'u':
                return get_unicode_escape_seq_token();
            case 'c':
                return get_control_escape_seq_token();
            case 'k':
                return validate_named_back_reference();
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
                return octal_or_backref();
            default:
                return {token_type::LITERAL, {}, {}};
        }
    }

    token ecma_lexer::get_token_standard() {
        const uint32_t current_char = m_regex[m_position];
        switch (current_char) {
            case '*':
            case '+':
            case '?':
                return {token_type::QUANTIFIER, {}, zstring_view(&m_regex[m_position], 1)};
            case '{':
                return get_braced_quant_token();
            case '.':
                return {token_type::DOT, {}, zstring_view(&m_regex[m_position], 1)};
            case '|':
                return {token_type::ALTERNATION, {}, zstring_view(&m_regex[m_position], 1)};
            case '^':
            case '$':
                return {token_type::ASSERTION, current_char, zstring_view(&m_regex[m_position], 1)};
            case '(':
                return get_group_token();
            case ')':
                return {token_type::GROUP_END, {}, zstring_view(&m_regex[m_position], 1)};
            case '\\':
                return get_escape_sequence_token();
            case '[': {
                m_in_char_class = true;
                return {token_type::CHAR_CLASS_START, {}, {}};
            }
            default:
                return {token_type::LITERAL, current_char, zstring_view(&m_regex[m_position], 1)};
        }
    }

    token ecma_lexer::get_char_class_escape_sequence_token() {
        if (m_position + 1 >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical error: Unfinished escape sequence at the end of regex");
        }

        const uint32_t second_char = m_regex[m_position + 1];
        m_token_len = 2;

        switch (second_char) {
            case 'd':
            case 'D':
            case 'w':
            case 'W':
            case 's':
            case 'S':
                return {token_type::CHAR_CLASS_ESCAPE, {}, {}};
            case 'x':
                return get_hex_escape_seq_token();
            case 'u':
                return get_unicode_escape_seq_token();
            case 'c':
                return get_control_escape_seq_token();
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
                return get_octal_escape_sequence_token();
            default:
                return {token_type::LITERAL, {}, {}};
        }
    }

    token ecma_lexer::get_token_char_class() {
        const uint32_t current_char = m_regex[m_position];
        switch (current_char) {
            case ']':
                m_in_char_class = false;
                return {token_type::CHAR_CLASS_END, {}, {}};
            case '-':
                return {token_type::CHAR_CLASS_RANGE, {}, {}};
            case '^':
                return {token_type::CHAR_CLASS_NEGATION, {}, {}};
            case '\\':
                return get_char_class_escape_sequence_token();
            default:
                return {token_type::LITERAL, {}, {}};
        }
    }

    uint32_t ecma_lexer::octal_to_dec(zstring_view octal_text, const uint32_t octal_len) {
        uint32_t res = 0;
        for (uint32_t i = 0; i < octal_len; i++) {
            const uint32_t octal_digit = octal_text[i] - '0';
            res = res * 8 + octal_digit;
        }
        return res;
    }

    token ecma_lexer::get_next_token() {
        if (m_first_traverse) {
            perform_first_traverse();
            m_first_traverse = false;
        }

        if (m_position >= m_regex.length()) {
            return {token_type::END_OF_INPUT, {}, {}};
        }
        m_lexeme_start_pos = m_position;

        if (m_in_char_class) {
            return get_token_char_class();
        } else {
            return get_token_standard();
        }
    }

    void ecma_lexer::perform_first_traverse() {
        uint32_t open_parens_count = 0;
        bool in_char_class = false;
        bool escaped = false;

        for (uint32_t pos = 0; pos < m_regex.length(); pos++) {
            switch (m_regex[pos]) {
                case '[':
                    if (escaped) {
                        escaped = false;  // '\[' --> ignore that
                    } else {
                        in_char_class = true;
                    }
                    break;
                case ']':
                    if (escaped) {
                        escaped = false;  // '\]' --> ignore that
                    } else if (in_char_class) {
                        in_char_class = false;
                    }
                    break;
                case '\\':
                    // more backslashes in a row --> toggle escaping
                    escaped = !escaped;
                    break;
                case '(':
                    if (escaped) {
                        escaped = false;  // '\(' --> ignore that
                    } else if (!in_char_class) {
                        open_parens_count++;

                        if (is_capture_or_named_capture(pos)) {
                            m_num_capture_groups++;
                        }
                    }
                    break;
                case ')':
                    if (escaped) {
                        escaped = false;  // '\)' --> ignore that
                    } else if (!in_char_class) {
                        // match not only capture groups but any group structure (lookarounds,...)
                        if (open_parens_count > 0) {
                            open_parens_count--;
                        } else {
                            throw default_exception("Syntax error: Unmatched ')' in regular expression");
                        }
                    }
                    break;
                default:
                    escaped = false;
                    break;
            }
        }
    }

    // =============== ECMA REGEX PARSER ===============

    void ecma_parser::next() {
        m_current_token = m_lexer.get_next_token();
    }

    bool ecma_parser::match(const token_type type) {
        if (m_current_token.type == type) {
            next();
            return true;
        }
        return false;
    }

    void ecma_parser::consume(const token_type type, const char* message) {
        if (m_current_token.type == type) {
            next();
            return;
        }
        throw default_exception("Syntax error: " + std::string(message));
    }

    regex_constraint_graph ecma_parser::parse() {
        parse_disjunction();
        consume(token_type::END_OF_INPUT, "Expected end of input");
        std::cout << "\033[32m Ecma regex parsing successful! \033[0m" << std::endl;
        return {};
    }

    void ecma_parser::parse_disjunction() {
        parse_alternative();
        while (match(token_type::ALTERNATION)) {
            parse_alternative();
        }
    }

    void ecma_parser::parse_alternative() {
        while (m_current_token.type != token_type::ALTERNATION && m_current_token.type != token_type::GROUP_END &&
               m_current_token.type != token_type::END_OF_INPUT) {
            parse_term();
        }
    }

    void ecma_parser::parse_term() {
        switch (m_current_token.type) {
            case token_type::ASSERTION:
            case token_type::LOOKAHEAD_POS_START:
            case token_type::LOOKAHEAD_NEG_START:
            case token_type::LOOKBEHIND_POS_START:
            case token_type::LOOKBEHIND_NEG_START:
                parse_assertion();
                break;
            default:
                parse_atom();
                match(token_type::QUANTIFIER);
                break;
        }
    }

    void ecma_parser::parse_assertion() {
        switch (m_current_token.type) {
            case token_type::ASSERTION:
                next();
                break;
            case token_type::LOOKAHEAD_POS_START:
            case token_type::LOOKAHEAD_NEG_START:
            case token_type::LOOKBEHIND_POS_START:
            case token_type::LOOKBEHIND_NEG_START:
                next();
                parse_disjunction();
                consume(token_type::GROUP_END, "Expected ')' after lookahead/lookbehind");
                break;
            default:
                break;
        }
    }

    void ecma_parser::parse_atom() {
        switch (m_current_token.type) {
            case token_type::LITERAL:
            case token_type::DOT:
            case token_type::CHAR_CLASS_ESCAPE:
            case token_type::BACKREFERENCE:
                next();
                break;
            case token_type::CHAR_CLASS_START:
                parse_character_class();
                break;
            case token_type::GROUP_START:
            case token_type::GROUP_NONCAPTURE_START:
            case token_type::GROUP_NAMED_START:
                next();
                parse_disjunction();
                consume(token_type::GROUP_END, "Expected ')' after group");
                break;
            default:
                // TODO: implement own exceptions later
                throw default_exception("Unexpected token in atom");
        }
    }

    void ecma_parser::parse_character_class() {
        consume(token_type::CHAR_CLASS_START, "Expected '['");
        match(token_type::CHAR_CLASS_NEGATION);

        while (m_current_token.type != token_type::CHAR_CLASS_END && m_current_token.type != token_type::END_OF_INPUT) {
            next();
        }
        consume(token_type::CHAR_CLASS_END, "Expected ']'");
    }
}  // namespace smt::noodler::ecma