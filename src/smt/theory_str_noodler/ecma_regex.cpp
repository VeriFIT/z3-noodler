#include "ecma_regex.h"

#include "util/z3_exception.h"
#include "util/zstring_view.h"

#include <cctype>
#include <cstdint>
#include <limits>

namespace smt::noodler::ecma {

    // ======================= UTILS =======================
    constexpr uint32_t HEX_SEQUENCE_LEN = 2;
    constexpr uint32_t UNICODE_ESCAPE_SEQUENCE_LEN = 4;
    constexpr uint32_t BACKSPACE_LITERAL = 8;

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

    token ecma_lexer::make_token(token_type type, token_payload payload) {
        uint32_t len = m_position - m_lexeme_start_pos;
        return {type, payload, zstring_view(&m_regex[m_lexeme_start_pos], len)};
    }

    token ecma_lexer::get_hex_escape_seq_token() {
        // hexadecimal escape sequence in format \xHH
        // currently m_position is right after '\x' -- hence the 1
        if (m_position + 1 >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\x'
            return make_token(token_type::LITERAL, static_cast<uint32_t>('x'));
        }

        const uint32_t first_hex_digit = m_regex[m_position];
        const uint32_t second_hex_digit = m_regex[m_position + 1];

        // if the hex number is not well-formed, then '\x' is a literal 'x' and the rest is parsed separately
        if (!is_hex_digit(first_hex_digit) || !is_hex_digit(second_hex_digit)) {
            m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\x'
            return make_token(token_type::LITERAL, static_cast<uint32_t>('x'));
        }

        // get decimal value of hex digits after '\x'
        uint32_t hex_val = hex2dec(zstring_view(&m_regex[m_lexeme_start_pos + 2], HEX_SEQUENCE_LEN));
        m_position += 2;  // consume both hex digits
        return make_token(token_type::LITERAL, hex_val);
    }

    token ecma_lexer::get_unicode_escape_seq_token() {
        // TODO: zstring contructor parser unicode escape sequences for us, remove this???
        // unicode escape sequence in format \uHHHH
        // currently m_position is on the first hex digit right after '\u' -- hence the 3
        if (m_position + 3 >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\u'
            return make_token(token_type::LITERAL, static_cast<uint32_t>('u'));
        }

        for (uint32_t i = 0; i < UNICODE_ESCAPE_SEQUENCE_LEN; i++) {
            const uint32_t current_char = m_regex[m_position + i];
            if (!is_hex_digit(current_char)) {
                m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\u'
                return make_token(token_type::LITERAL, static_cast<uint32_t>('u'));
            }
        }

        // TODO: implement own exceptions
        throw default_exception(
            "How did we get here? The zstring constructor should have parsed the unicode sequence for us");

        // code to be executed if we actually parsed it:
        // uint32_t hex_val = hex2dec(zstring_view(&m_regex[m_lexeme_start_pos + 2], UNICODE_ESCAPE_SEQUENCE_LEN));
        // m_position += UNICODE_ESCAPE_SEQUENCE_LEN;
        // return make_token(token_type::LITERAL, hex_val);
    }

    token ecma_lexer::get_control_escape_seq_token() {
        // control escape sequence in format \cC, where C is a control character
        // Currently m_position is right after '\c'
        if (m_position >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 1;  // rollback -- skip '\'
            return make_token(token_type::LITERAL, static_cast<uint32_t>('\\'));
        }

        const uint32_t control_char = m_regex[m_position];
        m_position++;  // consume the control character

        // [A-Za-z] characters allowed, otherwise error
        // TODO: based on rule CharacterEscape --> c ControlLetter, where ControlLetter --> [A-Za-z]
        // https://tc39.es/ecma262/2020/#prod-CharacterEscape
        // regex engines usually consume '\' and leave rest as literals, which does not follow the standard
        if (!is_alpha(control_char)) {
            throw default_exception("Syntax error in ECMA regex: invalid control sequence" + std::string("\\c") +
                                    std::to_string(m_regex[m_position]));
        }
        return make_token(token_type::LITERAL, alphabet_rank(control_char));
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
            // TODO: the name of the group is described in RegExpIdentifierName nonterminal in the standard, finish this
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
        // '\k<name>'
        // currently at '<' after '\k'
        if (m_position >= m_regex.length()) {
            throw default_exception("Lexical Error: Invalid named backreference at the end of regex");
        }

        const uint32_t open_bracket_char = m_regex[m_position];
        if (open_bracket_char != '<') {
            throw default_exception("Lexical Error: Missing open angle bracket in named back reference at position " +
                                    std::to_string(m_position - 1) + " in regex");
        }

        m_position++;  // consume '<'
        const uint32_t name_start_pos = m_position;
        uint32_t name_length = get_backref_name_len(name_start_pos);

        m_position += name_length + 1;  // consume name and '>'

        return make_token(token_type::BACKREFERENCE, zstring_view(&m_regex[name_start_pos], name_length));
    }

    token ecma_lexer::octal_or_backref(uint32_t first_digit) {
        uint32_t decimal_val = first_digit - '0';
        uint32_t fallback_pos = m_position;  // save position right after the first digit

        // greedily read as much digits as possible
        while (m_position < m_regex.length()) {
            const uint32_t digit = m_regex[m_position];
            if (!is_digit(digit)) {
                break;
            }
            decimal_val = decimal_val * 10 + (digit - '0');
            m_position++;
        }

        // try to match it to a backreference
        if (decimal_val > 0 && decimal_val <= m_num_capture_groups) {
            return make_token(token_type::BACKREFERENCE, decimal_val);
        }

        // cannot be backreference --> match the input to an octal escape sequence
        m_position = fallback_pos;  // fallback to after the first digit
        return get_octal_escape_sequence_token(false, first_digit);
    }

    token ecma_lexer::get_octal_escape_sequence_token(const bool from_char_class, const uint32_t first_digit) {
        // m_position is right after first_digit. m_lexeme_start_pos is at '\'
        uint32_t max_possible_octal_len = 3;

        if (!from_char_class && (first_digit == '8' || first_digit == '9')) {
            // TODO: based on https://tc39.es/ecma262/2020/#sec-decimalescape, I think this should be an error.
            // however, engine in node.js 20 interprets this as '8' or '9' (ascii 56/57) characters.
            throw default_exception("Lexical error: backreference to nonexistent subpattern");
        }

        if (first_digit > '3') {
            max_possible_octal_len = 2;
        }

        uint32_t real_octal_len = 1;  // already parsed the first digit
        while (real_octal_len < max_possible_octal_len && m_position < m_regex.length()) {
            const uint32_t digit = m_regex[m_position];
            if (!is_octal_digit(digit)) {
                break;
            }
            m_position++;
            real_octal_len++;
        }

        // Octal string starts at m_lexeme_start_pos + 1 (skipping '\')
        uint32_t octal_val = oct2dec(zstring_view(&m_regex[m_lexeme_start_pos + 1], real_octal_len));
        return make_token(token_type::LITERAL, octal_val);
    }

    token ecma_lexer::get_named_capture_group_token() {
        // called right after '(?<'
        uint32_t name_length = 0;
        uint32_t group_name_start_pos = m_position;
        bool found_closing_bracket = false;

        while (m_position < m_regex.length()) {
            const uint32_t current_char = m_regex[m_position];
            m_position++;

            if (current_char == '>') {
                found_closing_bracket = true;
                break;
            }
            // TODO: there can be unicode blob in the group name, implement it
            if (!is_alnum(current_char) && current_char != '_' && current_char != '$') {
                // TODO: implement own exceptions later
                throw default_exception("Lexical error: Invalid character in capture group name at position " +
                                        std::to_string(m_position - 1) + " in regex");
            }
            name_length++;
        }
        if (!found_closing_bracket) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical error: Unclosed group capture name at position " +
                                    std::to_string(m_position - 1) + " in regex");
        }
        // payload is just the name of the group, lexeme is the whole '(?<name>' thing
        return make_token(token_type::GROUP_NAMED_START, zstring_view(&m_regex[group_name_start_pos], name_length));
    }

    uint32_t ecma_lexer::validate_and_get_bound(uint32_t& bound) const {
        // read digits one by one, save the decimal value of bound
        uint32_t parsed_digits = 0;
        while (m_position < m_regex.length()) {
            uint32_t current_digit = m_regex[m_position];
            if (!is_digit(current_digit)) {
                break;
            }
            bound = bound * 10 + static_cast<uint32_t>(current_digit - '0');
            parsed_digits++;
        }
        return parsed_digits;
    }

    token ecma_lexer::get_braced_quant_token() {
        // already have '{' consumed -> check range of quantifier
        uint32_t lower_bound = 0;

        uint32_t bound_digits = validate_and_get_bound(lower_bound);
        m_position += bound_digits;  // consume the bound digits

        if (bound_digits == 0 || m_position >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(token_type::LITERAL, static_cast<uint32_t>('{'));
        }

        // case '{n}'
        if (m_regex[m_position] == '}') {
            m_position++;  // consume '}'
            return make_token(token_type::QUANTIFIER, quantifier_range {lower_bound, lower_bound});
        }

        if (m_regex[m_position] != ',') {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(token_type::LITERAL, static_cast<uint32_t>('{'));
        }

        m_position++;  // skip comma
        if (m_position >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(token_type::LITERAL, static_cast<uint32_t>('{'));
        }

        // case '{n,}'
        if (m_regex[m_position] == '}') {
            m_position++;  // consume '}'
            return make_token(token_type::QUANTIFIER,
                              quantifier_range {lower_bound, std::numeric_limits<uint32_t>::max()});
        }

        uint32_t upper_bound = 0;
        bound_digits = validate_and_get_bound(upper_bound);
        m_position += bound_digits;

        if (bound_digits == 0 || m_position >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(token_type::LITERAL, static_cast<uint32_t>('{'));
        }

        // '}' after number -> case {n,m}
        if (m_regex[m_position] == '}') {
            m_position++;  // consume '}'
            return make_token(token_type::QUANTIFIER, quantifier_range {lower_bound, upper_bound});
        }

        // not a well-formed quantifier --> '{' is a literal
        m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
        return make_token(token_type::LITERAL, static_cast<uint32_t>('{'));
    }

    token ecma_lexer::get_lookbehind_or_named_group_token() {
        // called right after '(?<'
        if (m_position >= m_regex.length()) {
            throw default_exception("Lexical error: Unfinished sequence '(?<' at position" +
                                    std::to_string(m_position) + " in regex");
        }

        const uint32_t fourth_char = m_regex[m_position];
        m_position++;  // consume the '=' or '!'

        if (fourth_char == '=') {
            return make_token(token_type::LOOKBEHIND_POS_START);
        }
        if (fourth_char == '!') {
            return make_token(token_type::LOOKBEHIND_NEG_START);
        }

        // not '!' or '=' --> has to be named capture group (?<name>)
        // we consumed the first letter of the name --> step back
        m_position--;
        return get_named_capture_group_token();
    }

    token ecma_lexer::get_special_group_or_lookaround_token() {
        // called right after '(?'
        if (m_position >= m_regex.length()) {
            throw default_exception("Lexical error: Unfinished sequence '(?' at the end of regex");
        }

        const uint32_t third_char = m_regex[m_position];
        m_position++;

        switch (third_char) {
            case ':':
                return make_token(token_type::GROUP_NONCAPTURE_START);
            case '=':
                return make_token(token_type::LOOKAHEAD_POS_START);
            case '!':
                return make_token(token_type::LOOKAHEAD_NEG_START);
            case '<':
                return get_lookbehind_or_named_group_token();
            default:
                throw default_exception("Lexical error: Invalid group indentifier at position" +
                                        std::to_string(m_position - 1) + " in regex");
        }
    }

    token ecma_lexer::get_group_token() {
        // called right after '('
        if (m_position >= m_regex.length() || m_regex[m_position] != '?') {
            return make_token(token_type::GROUP_START);
        }

        m_position++;  // consume '?'
        return get_special_group_or_lookaround_token();
    }

    token ecma_lexer::get_escape_sequence_token() {
        // called right after '\'
        if (m_position >= m_regex.length()) {
            throw default_exception("Lexical error: Unfinished escape sequence at the end of regex");
        }

        const uint32_t second_char = m_regex[m_position];
        m_position++;
        switch (second_char) {
            case 'd':
            case 'D':
            case 'w':
            case 'W':
            case 's':
            case 'S':
                return make_token(token_type::CHAR_CLASS_ESCAPE, second_char);
            case 'b':
            case 'B':
                return make_token(token_type::ASSERTION, second_char);
            case 'x':
                return get_hex_escape_seq_token();
            case 'u':
                return get_unicode_escape_seq_token();
            case 'c':
                return get_control_escape_seq_token();
            case 'k':
                return get_named_backref_token();
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
                return octal_or_backref(second_char);
            default:
                return make_token(token_type::LITERAL, second_char);
        }
    }

    token ecma_lexer::get_token_standard() {
        const uint32_t current_char = m_regex[m_position];
        m_position++;
        switch (current_char) {
            case '*':
            case '+':
            case '?':
                return make_token(token_type::QUANTIFIER, current_char);
            case '{':
                return get_braced_quant_token();
            case '.':
                return make_token(token_type::DOT);
            case '|':
                return make_token(token_type::ALTERNATION);
            case '^':
            case '$':
                return make_token(token_type::ASSERTION, current_char);
            case '(':
                return get_group_token();
            case ')':
                return make_token(token_type::GROUP_END);
            case '\\':
                return get_escape_sequence_token();
            case '[':
                m_in_char_class = true;
                return make_token(token_type::CHAR_CLASS_START);
            default:
                return make_token(token_type::LITERAL, current_char);
        }
    }

    token ecma_lexer::get_char_class_escape_sequence_token() {
        // called right after '\' inside character class
        if (m_position >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("Lexical error: Unfinished escape sequence at the end of regex");
        }

        const uint32_t second_char = m_regex[m_position];
        m_position++;
        switch (second_char) {
            case 'd':
            case 'D':
            case 'w':
            case 'W':
            case 's':
            case 'S':
                return make_token(token_type::CHAR_CLASS_ESCAPE, second_char);
            case 'x':
                return get_hex_escape_seq_token();
            case 'u':
                return get_unicode_escape_seq_token();
            case 'c':
                return get_control_escape_seq_token();
            case 'b':
                return make_token(token_type::LITERAL, BACKSPACE_LITERAL);
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
                return get_octal_escape_sequence_token(true, second_char);
            default:
                // digits 8 and 9 in escape are '8' and '9' literals as well in char class
                return make_token(token_type::LITERAL, second_char);
        }
    }

    token ecma_lexer::get_token_char_class() {
        const uint32_t current_char = m_regex[m_position];
        m_position++;
        switch (current_char) {
            case ']':
                m_in_char_class = false;
                return make_token(token_type::CHAR_CLASS_END, current_char);
            case '-':
                return make_token(token_type::CHAR_CLASS_RANGE, current_char);
            case '^':
                return make_token(token_type::CHAR_CLASS_NEGATION, current_char);
            case '\\':
                return get_char_class_escape_sequence_token();
            default:
                return make_token(token_type::LITERAL, current_char);
        }
    }

    bool ecma_lexer::is_capture_or_named_capture(uint32_t position) {
        position++;
        if (position >= m_regex.length()) {
            return false;
        }
        if (m_regex[position] != '?') {
            return true;
        }
        position++;
        if (position >= m_regex.length() || m_regex[position] != '<') {
            return false;
        }

        uint32_t name_len = 0;
        bool found_closing_bracket = false;
        while (++position < m_regex.length()) {
            const uint32_t current_char = m_regex[position];
            if (current_char == '>') {
                found_closing_bracket = true;
                break;
            }
            // TODO: implement unicode blob
            if (!is_alnum(current_char) && current_char != '_' && current_char != '$') {
                break;
            }
        }
        return (name_len > 0) && (found_closing_bracket);
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
                        // lets us throw early errors
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

    token ecma_lexer::get_next_token() {
        if (m_first_traverse) {
            perform_first_traverse();
            m_first_traverse = false;
        }

        if (m_position >= m_regex.length()) {
            return {token_type::END_OF_INPUT, {}, zstring_view(nullptr, 0)};
        }

        m_lexeme_start_pos = m_position;

        if (m_in_char_class) {
            return get_token_char_class();
        } else {
            return get_token_standard();
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