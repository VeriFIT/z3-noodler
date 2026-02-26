#include "ecma_regex.h"

#include "util/z3_exception.h"
#include "util/zstring_view.h"

#include <cctype>

namespace smt::noodler::ecma {

    // ======================= UTILS =======================
    constexpr uint32_t HEX_SEQUENCE_LEN = 3;
    constexpr uint32_t UNICODE_ESCAPE_SEQUENCE_LEN = 4;
    constexpr uint32_t CONTROL_SEQUENCE_LEN = 1;
    constexpr uint32_t BACKSLASH_OFFSET = 1;
    constexpr uint32_t NAMED_BACKREF_START_OFFSET = 3;
    constexpr uint32_t NAMED_BACKREF_MINIMAL_LEN = 4;
    constexpr uint32_t CLOSING_ANGLE_BRACKET_OFFSET = 1;

    sequence_validator::sequence_validator(const zstring_view regex, const uint32_t position)
        : m_regex(regex),
          m_position(position) { }

    bool sequence_validator::is_octal(uint32_t digit) const {
        return digit >= '0' && digit <= '7';
    }

    void sequence_validator::validate_hex_escape_sequence(uint32_t& token_len) const {
        if (m_position + HEX_SEQUENCE_LEN >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Unfinished hexadecimal escape sequence at the end of regex");
        }

        const uint32_t first_hex_digit = m_regex[m_position + 2];
        const uint32_t second_hex_digit = m_regex[m_position + 3];

        // TODO: Implement custom isxdigit for 4 byte characters
        if (!std::isxdigit(static_cast<unsigned char>(first_hex_digit)) ||
            !std::isxdigit(static_cast<unsigned char>(second_hex_digit))) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Invalid hexadecimal escape sequence at position " +
                                    std::to_string(m_position + 2) + " in regex");
        }
        token_len = 4;
    }

    void sequence_validator::validate_unicode_escape_sequence(uint32_t& token_len) const {
        // unicode escape sequence in format \uHHHH
        if (m_position + UNICODE_ESCAPE_SEQUENCE_LEN >= m_regex.length()) {
            throw default_exception("Lexical Error: Unfinished unicode escape sequence at the end of regex");
        }

        const uint32_t first_unicode_digit_pos = m_position + 2;
        for (uint32_t i = 0; i < UNICODE_ESCAPE_SEQUENCE_LEN; i++) {
            const uint32_t current_char = m_regex[first_unicode_digit_pos + i];
            if (!std::isxdigit(static_cast<unsigned char>(current_char))) {
                throw default_exception("Lexical Error: Invalid unicode escape sequence");
            }
        }
        token_len = 6;
    }

    void sequence_validator::validate_control_escape_sequence(uint32_t& token_len) const {
        if (m_position + CONTROL_SEQUENCE_LEN >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Unfinished control escape sequence at the end of regex");
        }

        const uint32_t control_char = m_regex[m_position + 2];

        // Only [A-Z] characters allowed
        // TODO: implement 4-byte isupper
        if (!std::isupper(static_cast<unsigned char>(control_char))) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Invalid control escape sequence at position " +
                                    std::to_string(m_position + 2));
        }

        token_len = 3;
    }

    void sequence_validator::validate_named_back_reference(uint32_t& token_len) const {
        // '\k<name>' ---> tokenLength = 3 + len(name) + 1, where name is nonempty string
        // ---> at least 5 chars in total, further checks done when resolving name
        // currently at '\' ---> 4 more at least to go
        if (m_position + NAMED_BACKREF_MINIMAL_LEN >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Invalid named backreference at the end of regex");
        }

        const uint32_t open_bracket_char = m_regex[m_position + 2];
        if (open_bracket_char != '<') {
            // TODO: implement own exceptions later
            throw default_exception("Lexical Error: Missing open angle bracket in named back reference at position " +
                                    std::to_string(m_position + 3) + " in regex");
        }

        const uint32_t name_start_pos = m_position + 3;
        uint32_t name_length = 0;
        bool found_closing_bracket = false;

        // Go through the back reference name char by char and count the length of it
        for (uint32_t current_pos = name_start_pos; current_pos < m_regex.length(); current_pos++) {
            const uint32_t current_name_char = m_regex[current_pos];
            if (current_name_char == '>') {
                found_closing_bracket = true;
                break;
            }
            // TODO: Implement custom isalnum for 4-byte characters
            if (!std::isalnum(static_cast<unsigned char>(current_name_char)) && current_name_char != '_' &&
                current_name_char != '$') {
                // TODO: implement own exceptions later
                throw default_exception("Lexical Error: Invalid character in back reference name at position " +
                                        std::to_string(current_pos + 1) + " in regex");
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
        token_len = NAMED_BACKREF_START_OFFSET + name_length + CLOSING_ANGLE_BRACKET_OFFSET;
    }

    void sequence_validator::validate_back_reference(uint32_t& token_len) const {
        uint32_t num_of_digits = 1;
        uint32_t current_pos = m_position + 2;
        while (current_pos < m_regex.length() && std::isdigit(static_cast<unsigned char>(m_regex[current_pos]))) {
            num_of_digits++;
            current_pos++;
        }
        token_len = num_of_digits + BACKSLASH_OFFSET;
    }

    void sequence_validator::validate_octal_escape_sequence(uint32_t& token_len) const {
        // An octal number can be one, two or three digits long
        if (m_position + 2 >= m_regex.length()) {
            return;
        }

        const uint32_t second_digit = m_regex[m_position + 2];
        if (!is_octal(second_digit)) {
            return;
        }
        token_len = 3;

        // Octal sequences in ECMAScript regexes are valid up to '\377'.
        // A regex '\402' matches literal '\40' in octal and then '2' in decimal.
        const uint32_t first_digit = m_regex[m_position + 1];
        if (first_digit > '3') {
            return;
        }

        if (m_position + 3 >= m_regex.length()) {
            return;
        }
        const uint32_t third_digit = m_regex[m_position + 3];
        if (!is_octal(third_digit)) {
            return;
        }
        token_len = 4;
    }

    // ================== ECMA REGEX LEXER ==================
    uint32_t ecma_lexer::get_backref_name_length(const uint32_t group_name_start_pos) const {
        uint32_t name_length = 0;
        uint32_t current_pos = group_name_start_pos;
        bool found_closing_bracket = false;

        while (current_pos < m_regex.length()) {
            const uint32_t current_char = m_regex[current_pos];
            if (current_char == '>') {
                found_closing_bracket = true;
                break;
            }
            if (!std::isalnum(static_cast<unsigned char>(current_char)) && current_char != '_' && current_char != '$') {
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
        return name_length;
    }

    bool ecma_lexer::braces_are_quantifier() {
        uint32_t fallback_pos = m_position;
    }

    token_type ecma_lexer::parse_fourth_char_in_capture_group() {
        token_type type;
        const uint32_t fourth_char = m_regex[m_position + 3];

        switch (fourth_char) {
            case '=':
                type = token_type::LOOKBEHIND_POS_START;
                m_token_len = 4;
                break;
            case '!':
                type = token_type::LOOKBEHIND_NEG_START;
                m_token_len = 4;
                break;
            default:
                type = token_type::GROUP_NAMED_START;
                m_token_len = 3 + get_backref_name_length(m_position + 3) + CLOSING_ANGLE_BRACKET_OFFSET;
                break;
        }
        return type;
    }

    token_type ecma_lexer::parse_third_char_in_capture_group() {
        token_type type;
        const uint32_t third_char = m_regex[m_position + 2];

        switch (third_char) {
            case ':':
                type = token_type::GROUP_NONCAPTURE_START;
                m_token_len = 3;
                break;
            case '=':
                type = token_type::LOOKAHEAD_POS_START;
                m_token_len = 3;
                break;
            case '!':
                type = token_type::LOOKAHEAD_NEG_START;
                m_token_len = 3;
                break;
            case '<':
                if (m_position + 3 >= m_regex.length()) {
                    // TODO: implement own exceptions later
                    throw default_exception("Lexical error: Unfinished sequence '(?<' at position" +
                                            std::to_string(m_position + 3) + " in regex");
                }
                type = parse_fourth_char_in_capture_group();
                break;
            default:
                // TODO: implement own exceptions later
                throw default_exception("Lexical error: Invalid group indentifier at position" +
                                        std::to_string(m_position + 2) + " in regex");
        }
        return type;
    }

    token_type ecma_lexer::get_group_token() {
        // Lexically it is correct, return the token and let the parser throw a syntax error
        if (m_position + 1 >= m_regex.length()) {
            return token_type::GROUP_START;
        }

        const uint32_t second_char = m_regex[m_position + 1];
        if (second_char != '?') {
            return token_type::GROUP_START;
        }

        if (m_position + 2 >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical error: Unfinished sequence '(?' at the end of regex");
        }
        return parse_third_char_in_capture_group();
    }

    token_type ecma_lexer::get_escape_sequence_token() {
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
                return token_type::CHAR_CLASS_ESCAPE;
            case 'b':
            case 'B':
                return token_type::ASSERTION;
            case 'x':
                sequence_validator(m_regex, m_position).validate_hex_escape_sequence(m_token_len);
                return token_type::LITERAL;
            case 'u':
                sequence_validator(m_regex, m_position).validate_unicode_escape_sequence(m_token_len);
                return token_type::LITERAL;
            case 'c':
                sequence_validator(m_regex, m_position).validate_control_escape_sequence(m_token_len);
                return token_type::LITERAL;
            case 'k':
                sequence_validator(m_regex, m_position).validate_named_back_reference(m_token_len);
                return token_type::BACKREFERENCE;
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
                sequence_validator(m_regex, m_position).validate_back_reference(m_token_len);
                return token_type::BACKREFERENCE;
            default:
                return token_type::LITERAL;
        }
    }

    token_type ecma_lexer::get_standard_token_type() {
        const uint32_t current_char = m_regex[m_position];
        switch (current_char) {
            case '*':
            case '+':
            case '?':
                return token_type::QUANTIFIER;
            case '{':
                if (braces_are_quantifier()) {
                    return token_type::QUANTIFIER;
                }
            case '.':
                return token_type::DOT;
            case '|':
                return token_type::ALTERNATION;
            case '^':
            case '$':
                return token_type::ASSERTION;
            case '(':
                return get_group_token();
            case ')':
                return token_type::GROUP_END;
            case '\\':
                return get_escape_sequence_token();
            case '[': {
                m_in_char_class = true;
                return token_type::CHAR_CLASS_START;
            }
            default:
                return token_type::LITERAL;
        }
    }

    token_type ecma_lexer::get_char_class_escape_sequence_token() {
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
                return token_type::CHAR_CLASS_ESCAPE;
            case 'x':
                sequence_validator(m_regex, m_position).validate_hex_escape_sequence(m_token_len);
                return token_type::LITERAL;
            case 'u':
                sequence_validator(m_regex, m_position).validate_unicode_escape_sequence(m_token_len);
                return token_type::LITERAL;
            case 'c':
                sequence_validator(m_regex, m_position).validate_control_escape_sequence(m_token_len);
                return token_type::LITERAL;
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
                sequence_validator(m_regex, m_position).validate_octal_escape_sequence(m_token_len);
                return token_type::LITERAL;
            default:
                return token_type::LITERAL;
        }
    }

    token_type ecma_lexer::get_token_type_from_char_class() {
        const uint32_t current_char = m_regex[m_position];
        switch (current_char) {
            case ']':
                m_in_char_class = false;
                return token_type::CHAR_CLASS_END;
            case '-':
                return token_type::CHAR_CLASS_RANGE;
            case '^':
                return token_type::CHAR_CLASS_NEGATION;
            case '\\':
                return get_char_class_escape_sequence_token();
            default:
                return token_type::LITERAL;
        }
    }

    token ecma_lexer::get_next_token() {
        if (m_position >= m_regex.length()) {
            return {token_type::END_OF_INPUT, {}, zstring_view(nullptr, 0)};
        }

        const uint32_t* token_start = &m_regex[m_position];

        token_type type;

        if (m_in_char_class) {
            type = get_token_type_from_char_class();
        } else {
            type = get_standard_token_type();
        }

        m_position += m_token_len;
        return {type, {}, zstring_view(token_start, m_token_len)};
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