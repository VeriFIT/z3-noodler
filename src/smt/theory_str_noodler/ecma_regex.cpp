#include "ecma_regex.h"

#include "util/z3_exception.h"
#include "util/zstring_view.h"

#include <cctype>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <limits>
#include <ostream>
#include <string>

namespace smt::noodler::ecma {

    // ======================= UTILS =======================
    constexpr uint32_t HEX_SEQUENCE_LEN = 2;
    constexpr uint32_t UNICODE_ESCAPE_SEQUENCE_LEN = 4;
    constexpr uint32_t BACKSPACE_LITERAL = 8;

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
        }
        return get_token_standard();
    }

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

    token ecma_lexer::make_token(const token_type type, const token_payload payload) {
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
            throw default_exception("Syntax error in ECMA regex: Invalid control sequence" + std::string("\\c"));
        }

        const uint32_t control_char = m_regex[m_position];
        m_position++;  // consume the control character

        // [A-Za-z] characters allowed, otherwise error
        // TODO: based on rule CharacterEscape --> c ControlLetter, where ControlLetter --> [A-Za-z]
        // https://tc39.es/ecma262/2020/#prod-CharacterEscape
        // regex engines usually consume '\' and leave rest as literals, which does not follow the standard
        if (!is_alpha(control_char)) {
            throw default_exception("Syntax error in ECMA regex: Invalid control sequence" + std::string("\\c"));
        }
        return make_token(token_type::LITERAL, alphabet_rank(control_char));
    }

    uint32_t ecma_lexer::get_backref_name_len(const uint32_t name_start_pos) const {
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
                throw default_exception("ECMA regex syntax error: Invalid character in back reference name");
            }
            name_length++;
        }

        if (!found_closing_bracket) {
            // TODO: implement own exceptions later
            throw default_exception("ECMA regex syntax error: Unclosed back reference name at the end of regex");
        }
        if (name_length == 0) {
            // TODO: implement own exceptions later
            throw default_exception("ECMA regex syntax error: Empty back reference name");
        }
        return name_length;
    }

    token ecma_lexer::get_named_backref_token() {
        // '\k<name>'
        // currently at '<' after '\k'
        if (m_position >= m_regex.length()) {
            throw default_exception("ECMA regex syntax error: Invalid named backreference at the end of regex");
        }

        const uint32_t open_bracket_char = m_regex[m_position];
        if (open_bracket_char != '<') {
            throw default_exception("ECMA regex syntax error: Missing '<' in named backreference");
        }

        m_position++;  // consume '<'
        const uint32_t name_start_pos = m_position;
        const uint32_t name_length = get_backref_name_len(name_start_pos);
        m_position += name_length + 1; // consume name and '>'
        return make_token(token_type::BACKREFERENCE, zstring_view(&m_regex[name_start_pos], name_length));
    }

    token ecma_lexer::octal_or_backref(uint32_t first_digit) {
        uint32_t decimal_val = first_digit - '0';
        const uint32_t fallback_pos = m_position; // save position right after the first digit

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
            throw default_exception("ECMA regex syntax error: backreference to nonexistent subpattern");
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
        const uint32_t group_name_start_pos = m_position;
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
                throw default_exception("ECMA regex syntax error: Invalid character in capture group name");
            }
            name_length++;
        }
        if (!found_closing_bracket) {
            // TODO: implement own exceptions later
            throw default_exception("ECMA regex syntax error: Unclosed group capture name");
        }
        if (name_length == 0) {
            throw default_exception("ECMA regex syntax error: Empty group name");
        }
        // payload is just the name of the group, lexeme is the whole '(?<name>' thing
        return make_token(token_type::GROUP_NAMED_START, zstring_view(&m_regex[group_name_start_pos], name_length));
    }

    uint32_t ecma_lexer::validate_and_get_bound(uint32_t& bound) {
        // read digits one by one, save the decimal value of bound
        uint32_t parsed_digits = 0;
        while (m_position < m_regex.length()) {
            const uint32_t current_digit = m_regex[m_position];
            if (!is_digit(current_digit)) {
                break;
            }
            bound = bound * 10 + static_cast<uint32_t>(current_digit - '0');
            m_position++;
            parsed_digits++;
        }
        return parsed_digits;
    }

    token ecma_lexer::get_braced_quant_token() {
        // already have '{' consumed -> check range of quantifier
        uint32_t lower_bound = 0;

        uint32_t bound_digits = validate_and_get_bound(lower_bound);

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
            throw default_exception("ECMA regex syntax error: Unfinished sequence '(?<'");
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
            throw default_exception("ECMA regex syntax error: Unfinished sequence '(?' at the end of regex");
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
                throw default_exception("ECMA regex syntax error: Invalid group indentifier");
        }
    }

    token ecma_lexer::get_group_token() {
        // called right after '('
        if (m_position >= m_regex.length() || m_regex[m_position] != '?') {
            return make_token(token_type::GROUP_START);
        }
        m_position++; // consume '?'
        return get_special_group_or_lookaround_token();
    }

    token ecma_lexer::get_escape_sequence_token() {
        // called right after '\'
        if (m_position >= m_regex.length()) {
            throw default_exception("ECMA regex syntax error: Unfinished escape sequence at the end of regex");
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
            case '0':
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
                m_first_in_char_class = true;
                return make_token(token_type::CHAR_CLASS_START);
            default:
                return make_token(token_type::LITERAL, current_char);
        }
    }

    token ecma_lexer::get_char_class_escape_sequence_token() {
        // called right after '\' inside character class
        if (m_position >= m_regex.length()) {
            // TODO: implement own exceptions later
            throw default_exception("ECMA regex syntax error: Unfinished escape sequence at the end of regex");
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

        const bool is_first = m_first_in_char_class;
        m_first_in_char_class = false;

        switch (current_char) {
            case ']':
                m_in_char_class = false;
                return make_token(token_type::CHAR_CLASS_END);
            case '-':
                return make_token(token_type::CHAR_CLASS_RANGE);
            case '^':
                if (is_first) {
                    return make_token(token_type::CHAR_CLASS_NEGATION);
                } else {
                    return make_token(token_type::LITERAL, current_char);
                }
            case '\\':
                return get_char_class_escape_sequence_token();
            default:
                return make_token(token_type::LITERAL, current_char);
        }
    }

    bool ecma_lexer::is_capture_or_named_capture(uint32_t position) const {
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
            name_len++;
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

    // ================== ECMA REGEX AST ==================
    uint32_t ast_node_disjunction::print_dot(std::ostream& out, uint32_t& node_count) const {
        const int id = ++node_count;
        out << "  node" << id << " [label=\"DISJUNCTION\"];\n";
        for (const ast_node_ref& alt : m_alternatives) {
            const int child_id = alt->print_dot(out, node_count);
            out << "  node" << id << " -> node" << child_id << ";\n";
        }
        return id;
    }

    void ast_node_disjunction::add_alternative(ast_node_ref alt) {
        m_alternatives.push_back(std::move(alt));
    }

    uint32_t ast_node_alternative::print_dot(std::ostream& out, uint32_t& node_count) const {
        const int id = ++node_count;
        out << "  node" << id << " [label=\"ALTERNATIVE\"];\n";
        for (const ast_node_ref& term : m_terms) {
            const int child_id = term->print_dot(out, node_count);
            out << "  node" << id << " -> node" << child_id << ";\n";
        }
        return id;
    }

    void ast_node_alternative::add_term(ast_node_ref term) {
        m_terms.push_back(std::move(term));
    }

    uint32_t ast_node_assertion::print_dot(std::ostream& out, uint32_t& node_count) const {
        const int id = ++node_count;
        std::string label = "ASSERTION (";
        if (m_child) {
            switch (m_assert_type) {
                case token_type::LOOKAHEAD_POS_START:
                    label += "?=";
                    break;
                case token_type::LOOKAHEAD_NEG_START:
                    label += "?!";
                    break;
                case token_type::LOOKBEHIND_POS_START:
                    label += "?<=";
                    break;
                case token_type::LOOKBEHIND_NEG_START:
                    label += "?<!";
                    break;
                default:
                    break;
            }
            label += ")";
            out << "  node" << id << " [label=\"" << label << "\"];\n";
            const int child_id = m_child->print_dot(out, node_count);
            out << "  node" << id << " -> node" << child_id << ";\n";
        } else {
            label += std::string(1, static_cast<char>(m_payload)) + ")";
            out << "  node" << id << " [label=\"" << label << "\"];\n";
        }
        return id;
    }

    void ast_node_assertion::set_type(const token_type type) {
        m_assert_type = type;
    }

    void ast_node_assertion::set_payload(const uint32_t payload) {
        m_payload = payload;
    }

    void ast_node_assertion::set_expr(ast_node_ref expr) {
        m_child = std::move(expr);
    }

    uint32_t ast_node_quantifier::print_dot(std::ostream& out, uint32_t& node_count) const {
        const int id = ++node_count;
        out << "  node" << id << " [label=\"QUANTIFIER {" << m_range.min << ",";
        if (m_range.max == std::numeric_limits<uint32_t>::max()) {
            out << "inf";
        } else {
            out << m_range.max;
        }
        out << "}\"];\n";
        const int child_id = m_child->print_dot(out, node_count);
        out << "  node" << id << " -> node" << child_id << ";\n";
        return id;
    }

    void ast_node_quantifier::set(const token& t, ast_node_ref term) {
        if (std::holds_alternative<quantifier_range>(t.payload)) {
            m_range = std::get<quantifier_range>(t.payload);
        } else if (std::holds_alternative<uint32_t>(t.payload)) {
            uint32_t ch = std::get<uint32_t>(t.payload);
            if (ch == '*') {
                m_range = {0, std::numeric_limits<uint32_t>::max()};
            } else if (ch == '+') {
                m_range = {1, std::numeric_limits<uint32_t>::max()};
            } else if (ch == '?') {
                m_range = {0, 1};
            }
        }
        m_child = std::move(term);
    }

    uint32_t ast_node_literal::print_dot(std::ostream& out, uint32_t& node_count) const {
        const int id = ++node_count;
        out << "  node" << id << " [label=\"LITERAL ('" << static_cast<char>(m_char) << "')\"];\n";
        return id;
    }

    void ast_node_literal::set_char(const uint32_t ch) {
        m_char = ch;
    }

    uint32_t ast_node_dot::print_dot(std::ostream& out, uint32_t& node_count) const {
        const int id = ++node_count;
        out << "  node" << id << " [label=\"DOT\"];\n";
        return id;
    }

    uint32_t ast_node_backreference::print_dot(std::ostream& out, uint32_t& node_count) const {
        const int id = ++node_count;
        out << "  node" << id << " [label=\"BACKREF\"];\n";
        return id;
    }

    uint32_t ast_node_group::print_dot(std::ostream& out, uint32_t& node_count) const {
        const int id = ++node_count;
        std::string label = "GROUP";
        if (m_type == group_type::NAMED) {
            label += " (?<";
            for (uint32_t i = 0; i < m_name.length(); i++) {
                label += static_cast<char>(m_name[i]);
            }
        } else if (m_type == group_type::NONCAPTURE) {
            label += " (?:)";
        }

        out << "  node" << id << " [label=\"" << label << "\"];\n";
        const int child_id = m_child->print_dot(out, node_count);
        out << "  node" << id << " -> node" << child_id << ";\n";
        return id;
    }

    void ast_node_group::set_type(const group_type type) {
        m_type = type;
    }

    void ast_node_group::set_name(const zstring_view name) {
        m_name = name;
    }

    void ast_node_group::set_expr(ast_node_ref expr) {
        m_child = std::move(expr);
    }

    uint32_t ast_node_character_class::print_dot(std::ostream& out, uint32_t& node_count) const {
        const int id = ++node_count;
        std::string label = "CLASS [";
        if (m_is_negated) {
            label += "^";
        }

        for (const auto& [kind, lower, upper] : m_elements) {
            if (kind == element_type::SINGLE) {
                label += static_cast<char>(lower);
            } else if (kind == element_type::ESCAPE) {
                label += "\\";
                label += static_cast<char>(lower);
            } else if (kind == element_type::RANGE) {
                label += static_cast<char>(lower);
                label += "-";
                label += static_cast<char>(upper);
            }
        }
        label += "]";

        out << "  node" << id << " [label=\"" << label << "\"];\n";
        return id;
    }

    void ast_node_character_class::add_element(const char_class_element elem) {
        m_elements.push_back(elem);
    }

    void ast_node_character_class::set_negation(const bool neg) {
        m_is_negated = neg;
    }

    // =============== ECMA REGEX PARSER ===============

    ast_node_ref ecma_parser::parse() {
        ast_node_ref ast = parse_disjunction();
        consume(token_type::END_OF_INPUT, "Expected end of input");

        namespace fs = std::filesystem;
        fs::path project_root = fs::path(__FILE__).parent_path().parent_path().parent_path().parent_path();
        fs::path dot_file = project_root / "output.dot";
        std::ofstream out(dot_file);
        if (out.is_open()) {
            uint32_t node_count = 0;
            out << "digraph G {\n";
            ast->print_dot(out, node_count);
            out << "}" << std::endl;
            out.close();
        }

        std::cout << "\033[32m Ecma regex parsing successful! \033[0m" << std::endl;
        return ast;
    }

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

    token ecma_parser::consume(const token_type type, const char* message) {
        if (m_current_token.type == type) {
            const token t = m_current_token;
            next();
            return t;
        }
        throw default_exception("Syntax error: " + std::string(message));
    }

    ast_node_ref ecma_parser::parse_disjunction() {
        // Disjunction -> Alternative Disjunction2
        // Disjunction2 -> ALTERNATION Alternative Disjunction2 | epsilon
        ast_node_ref alt = parse_alternative();

        // little optimalization -- only one alternative --> no disjunction node
        if (m_current_token.type != token_type::ALTERNATION) {
            return alt;
        }

        auto disj = std::make_shared<ast_node_disjunction>();
        disj->add_alternative(std::move(alt));
        while (match(token_type::ALTERNATION)) {
            disj->add_alternative(parse_alternative());
        }
        return disj;
    }

    ast_node_ref ecma_parser::parse_alternative() {
        auto alt = std::make_shared<ast_node_alternative>();
        while (m_current_token.type != token_type::ALTERNATION && m_current_token.type != token_type::GROUP_END &&
               m_current_token.type != token_type::END_OF_INPUT) {
            alt->add_term(parse_term());
        }
        return alt;
    }

    ast_node_ref ecma_parser::parse_term() {
        switch (m_current_token.type) {
            case token_type::ASSERTION:
            case token_type::LOOKAHEAD_POS_START:
            case token_type::LOOKAHEAD_NEG_START:
            case token_type::LOOKBEHIND_POS_START:
            case token_type::LOOKBEHIND_NEG_START:
                return parse_assertion();
            case token_type::LITERAL:
            case token_type::DOT:
            case token_type::BACKREFERENCE:
            case token_type::CHAR_CLASS_ESCAPE:
            case token_type::GROUP_START:
            case token_type::GROUP_NAMED_START:
            case token_type::GROUP_NONCAPTURE_START:
            case token_type::CHAR_CLASS_START:
                return parse_maybe_quantifier(parse_atom());
            default:
                throw default_exception("Syntax error in ECMA regex: Unexpected token in term");
        }
    }

    ast_node_ref ecma_parser::parse_maybe_quantifier(ast_node_ref term) {
        // MaybeQuantifier -> QUANTIFIER | epsilon
        if (m_current_token.type == token_type::QUANTIFIER) {
            const token t = m_current_token;
            next();

            auto quant = std::make_shared<ast_node_quantifier>();
            quant->set(t, std::move(term));
            return quant;
        }
        return term;
    }

    ast_node_ref ecma_parser::parse_assertion() {
        const token t = m_current_token;
        auto node = std::make_shared<ast_node_assertion>();
        node->set_type(t.type);

        switch (m_current_token.type) {
            case token_type::ASSERTION:
                if (std::holds_alternative<uint32_t>(t.payload)) {
                    node->set_payload(std::get<uint32_t>(t.payload));
                }
                next();
                return node;
            case token_type::LOOKAHEAD_POS_START:
            case token_type::LOOKAHEAD_NEG_START:
            case token_type::LOOKBEHIND_POS_START:
            case token_type::LOOKBEHIND_NEG_START:
                next();
                node->set_expr(parse_disjunction());
                consume(token_type::GROUP_END, "Expected ')' after lookaround assertion");
                return node;
            default:
                throw default_exception("Syntax error in ECMA regex: Expected assertion");
        }
    }

    ast_node_ref ecma_parser::parse_atom() {
        const token t = m_current_token;
        switch (m_current_token.type) {
            case token_type::LITERAL: {
                auto node = std::make_shared<ast_node_literal>();
                if (std::holds_alternative<uint32_t>(t.payload)) {
                    node->set_char(std::get<uint32_t>(t.payload));
                }
                next();
                return node;
            }
            case token_type::DOT:
                next();
                return std::make_shared<ast_node_dot>();
            case token_type::BACKREFERENCE: {
                auto node = std::make_shared<ast_node_backreference>();
                // Překopírovat payload... (ve tvé implementaci bys řešil string vs index)
                next();
                return node;
            }
            case token_type::CHAR_CLASS_ESCAPE: {
                auto node = std::make_shared<ast_node_character_class>();
                if (std::holds_alternative<uint32_t>(t.payload)) {
                    const char_class_element elem{.kind = element_type::ESCAPE,
                                                  .lower = std::get<uint32_t>(t.payload)};
                    node->add_element(elem);
                }
                next();
                return node;
            }
            case token_type::GROUP_START:
            case token_type::GROUP_NAMED_START:
            case token_type::GROUP_NONCAPTURE_START:
                return parse_group();
            case token_type::CHAR_CLASS_START:
                return parse_character_class();
            default:
                throw default_exception("Syntax error in ECMA regex: Unexpected token in atom");
        }
    }

    ast_node_ref ecma_parser::parse_group() {
        const token t = m_current_token;
        auto node = std::make_shared<ast_node_group>();

        switch (m_current_token.type) {
            case token_type::GROUP_START:
                node->set_type(group_type::NORMAL);
                next();
                break;
            case token_type::GROUP_NAMED_START:
                node->set_type(group_type::NAMED);
                if (std::holds_alternative<zstring_view>(t.payload)) {
                    node->set_name(std::get<zstring_view>(t.payload));
                } else {
                    throw default_exception("Internal error: GROUP_NAMED_START has no name");
                }
                next();
                break;
            case token_type::GROUP_NONCAPTURE_START:
                node->set_type(group_type::NONCAPTURE);
                next();
                break;
            default:
                throw default_exception("Syntax error in ECMA regex: Expected group start");
        }
        node->set_expr(parse_disjunction());
        consume(token_type::GROUP_END, "Expected ')' after group");
        return node;
    }

    ast_node_ref ecma_parser::parse_character_class() {
        consume(token_type::CHAR_CLASS_START, "Expected '['");

        auto node = std::make_shared<ast_node_character_class>();
        node->set_negation(match(token_type::CHAR_CLASS_NEGATION));

        parse_class_ranges(node);
        consume(token_type::CHAR_CLASS_END, "Expected ']'");
        return node;
    }

    void ecma_parser::add_atom_to_class(const std::shared_ptr<ast_node_character_class>& parent,
                                        const class_atom atom) const {
        if (atom.is_escape) {
            parent->add_element({.kind = element_type::ESCAPE, .lower = atom.val});
        } else {
            parent->add_element({.kind = element_type::SINGLE, .lower = atom.val});
        }
    }

    void ecma_parser::parse_class_ranges(const std::shared_ptr<ast_node_character_class>& parent) {
        if (m_current_token.type == token_type::LITERAL || m_current_token.type == token_type::CHAR_CLASS_ESCAPE ||
            m_current_token.type == token_type::CHAR_CLASS_RANGE) {
            parse_class_ranges_tail(parent, parse_class_atom());
        }
    }

    void ecma_parser::parse_class_ranges_tail(const std::shared_ptr<ast_node_character_class>& parent,
                                              const class_atom prev_atom) {
        switch (m_current_token.type) {
            case token_type::CHAR_CLASS_RANGE:
                next();
                parse_dash_tail(parent, prev_atom);
                break;
            case token_type::LITERAL:
            case token_type::CHAR_CLASS_ESCAPE: {
                add_atom_to_class(parent, prev_atom);
                const class_atom next_atom = parse_class_atom_no_dash();
                parse_class_ranges_tail(parent, next_atom);
            }
            break;
            default: // epsilon
                add_atom_to_class(parent, prev_atom);
                break;
        }
    }

    void ecma_parser::parse_dash_tail(const std::shared_ptr<ast_node_character_class>& parent,
                                      const class_atom prev_atom) {
        switch (m_current_token.type) {
            case token_type::LITERAL:
            case token_type::CHAR_CLASS_ESCAPE:
                // TODO: based on prev_atom, we decide whether this is an error or not
                break;
            case token_type::CHAR_CLASS_RANGE: {
                // TODO: two dashes in a row, read standard and implement
                break;
            }
            default: // epsilon
                // '-' at the end of character class, its a literal
                add_atom_to_class(parent, prev_atom);
                parent->add_element({element_type::SINGLE, static_cast<uint32_t>('-'), 0});
                break;
        }
    }

    class_atom ecma_parser::parse_class_atom() {
        switch (m_current_token.type) {
            case token_type::LITERAL:
            case token_type::CHAR_CLASS_ESCAPE:
                return parse_class_atom_no_dash();
            case token_type::CHAR_CLASS_RANGE:
                next();
                return {false, static_cast<uint32_t>('-')};
            default:
                throw default_exception("Syntax error in ECMA regex: Expected class atom");
        }
    }

    class_atom ecma_parser::parse_class_atom_no_dash() {
        const token t = m_current_token;
        switch (m_current_token.type) {
            case token_type::LITERAL:
                next();
                return {false, std::get<uint32_t>(t.payload)};
            case token_type::CHAR_CLASS_ESCAPE:
                next();
                return {true, std::get<uint32_t>(t.payload)};
            default:
                throw default_exception("Syntax error in ECMA regex: Expected literal or escape sequence");
        }
    }
}  // namespace smt::noodler::ecma