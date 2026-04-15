#include "ecma_regex.h"

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "util.h"
#include "util/debug.h"
#include "util/zstring_view.h"

#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <limits>
#include <ostream>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

namespace smt::noodler::ecma {
    // ======================= UTILS =======================
    constexpr uint32_t HEX_SEQUENCE_LEN = 2;
    constexpr uint32_t UNICODE_ESCAPE_SEQUENCE_LEN = 4;
    constexpr uint32_t BACKSPACE_LITERAL = 8;
    constexpr uint32_t UNBOUNDED = std::numeric_limits<uint32_t>::max();
    constexpr bool debug_mode = false;

    zstring view_to_zstring(const zstring_view view) {
        zstring res;
        for (uint32_t i = 0; i < view.length(); ++i) {
            res += view[i];
        }
        return res;
    }

    GraphFragment chain_fragments(RegexConstraintGraph& graph, const GraphFragment& first,
                                  const GraphFragment& second) {
        for (const EdgeId id : first.edges_pointing_to_vout) {
            graph.edges[id].target = second.v_in;
        }
        return GraphFragment {first.v_in, second.v_out, second.edges_pointing_to_vout};
    }

    GraphFragment alternate_fragments(RegexConstraintGraph& graph, const GraphFragment& first,
                                      const GraphFragment& second) {
        std::vector<EdgeId> new_vin_outgoing;
        for (const EdgeId id : graph.vertices[first.v_in].outgoing_edges) {
            new_vin_outgoing.push_back(id);
        }
        for (const EdgeId id : graph.vertices[second.v_in].outgoing_edges) {
            new_vin_outgoing.push_back(id);
        }

        graph.vertices[first.v_in].outgoing_edges.clear();
        graph.vertices[second.v_in].outgoing_edges.clear();

        const VertexId new_vin = graph.create_vertex(new_vin_outgoing);
        const VertexId new_vout = graph.create_vertex();

        std::vector<EdgeId> new_vout_incoming;
        for (const EdgeId id : first.edges_pointing_to_vout) {
            graph.edges[id].target = new_vout;
            new_vout_incoming.push_back(id);
        }
        for (const EdgeId id : second.edges_pointing_to_vout) {
            graph.edges[id].target = new_vout;
            new_vout_incoming.push_back(id);
        }

        return GraphFragment {new_vin, new_vout, new_vout_incoming};
    }

    // =============== REGEX CONSTRAINT GRAPH ==============

    void RegexConstraintGraph::add_vertex(RCGVertex vtx) {
        vertices.push_back(std::move(vtx));
    }

    VertexId RegexConstraintGraph::create_vertex() {
        VertexId new_id = vertices.size();
        vertices.emplace_back(new_id, std::vector<EdgeId> {});
        return new_id;
    }

    VertexId RegexConstraintGraph::create_vertex(std::vector<EdgeId> edge_list) {
        VertexId new_id = vertices.size();
        vertices.emplace_back(new_id, std::move(edge_list));
        return new_id;
    }

    void RegexConstraintGraph::add_edge(RCGEdge child) {
        edges.push_back(std::move(child));
    }

    EdgeId RegexConstraintGraph::create_edge() {
        EdgeId new_id = edges.size();
        edges.emplace_back(new_id, UNKNOWN_VERTEX, BackrefEdge {0u});
        return new_id;
    }

    EdgeId RegexConstraintGraph::create_edge(VertexId target_vertex, RCGEdgePayload payload) {
        EdgeId new_id = edges.size();
        edges.emplace_back(new_id, target_vertex, std::move(payload));
        return new_id;
    }

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

    bool ECMALexer::is_digit(const uint32_t digit) {
        return digit >= '0' && digit <= '9';
    }

    bool ECMALexer::is_alpha(const uint32_t digit) {
        return (digit >= 'A' && digit <= 'Z') || (digit >= 'a' && digit <= 'z');
    }

    bool ECMALexer::is_alnum(const uint32_t digit) {
        return is_alpha(digit) || is_digit(digit);
    }

    bool ECMALexer::is_hex_digit(const uint32_t digit) {
        return is_digit(digit) || (digit >= 'A' && digit <= 'F') || (digit >= 'a' && digit <= 'f');
    }

    bool ECMALexer::is_octal_digit(const uint32_t digit) {
        return digit >= '0' && digit <= '7';
    }

    bool ECMALexer::is_upper(const uint32_t digit) {
        return digit >= 'A' && digit <= 'Z';
    }

    uint32_t ECMALexer::alphabet_rank(const uint32_t digit) {
        if (is_upper(digit)) {
            return digit - 'A' + 1;
        }
        return digit - 'a' + 1;
    }

    uint32_t ECMALexer::hex2dec(const zstring_view number) {
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

    uint32_t ECMALexer::oct2dec(const zstring_view number) {
        uint32_t res = 0;
        for (uint32_t pos = 0; pos < number.length(); pos++) {
            const uint32_t digit = number[pos];
            if (is_octal_digit(digit)) {
                res = res * 8 + (digit - '0');
            }
        }
        return res;
    }

    Token ECMALexer::make_token(const TokenType type, const token_payload& payload) const {
        const uint32_t len = m_position - m_lexeme_start_pos;
        return {type, payload, zstring_view(&m_regex[m_lexeme_start_pos], len)};
    }

    Token ECMALexer::get_hex_escape_seq_token() {
        // hexadecimal escape sequence in format \xHH
        // currently m_position is right after '\x' -- hence the 1
        if (m_position + 1 >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\x'
            return make_token(TokenType::LITERAL, static_cast<uint32_t>('x'));
        }

        const uint32_t first_hex_digit = m_regex[m_position];
        const uint32_t second_hex_digit = m_regex[m_position + 1];

        // if the hex number is not well-formed, then '\x' is a literal 'x' and the rest is parsed separately
        if (!is_hex_digit(first_hex_digit) || !is_hex_digit(second_hex_digit)) {
            m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\x'
            return make_token(TokenType::LITERAL, static_cast<uint32_t>('x'));
        }

        // get decimal value of hex digits after '\x'
        uint32_t hex_val = hex2dec(zstring_view(&m_regex[m_lexeme_start_pos + 2], HEX_SEQUENCE_LEN));
        m_position += 2;  // consume both hex digits
        return make_token(TokenType::LITERAL, hex_val);
    }

    Token ECMALexer::get_unicode_escape_seq_token() {
        // unicode escape sequence in format \uHHHH
        // currently m_position is on the first hex digit right after '\u' -- hence the 3
        if (m_position + 3 >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\u'
            return make_token(TokenType::LITERAL, static_cast<uint32_t>('u'));
        }

        for (uint32_t i = 0; i < UNICODE_ESCAPE_SEQUENCE_LEN; i++) {
            const uint32_t current_char = m_regex[m_position + i];
            if (!is_hex_digit(current_char)) {
                m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\u'
                return make_token(TokenType::LITERAL, static_cast<uint32_t>('u'));
            }
        }

        util::throw_error(
            "How did we get here? The zstring constructor should have parsed the unicode sequence for us");
        // return dummy token, because compilation errors with return type (execution wont get here)
        return {};

        // code to be executed if we actually parsed it:
        // uint32_t hex_val = hex2dec(zstring_view(&m_regex[m_lexeme_start_pos + 2], UNICODE_ESCAPE_SEQUENCE_LEN));
        // m_position += UNICODE_ESCAPE_SEQUENCE_LEN;
        // return make_token(token_type::LITERAL, hex_val);
    }

    Token ECMALexer::get_control_escape_seq_token() {
        // control escape sequence in format \cC, where C is a control character
        // Currently m_position is right after '\c'
        if (m_position >= m_regex.length()) {
            util::throw_error("Syntax error in ECMA regex: Invalid control sequence" + std::string("\\c"));
        }

        const uint32_t control_char = m_regex[m_position];
        m_position++;  // consume the control character

        // [A-Za-z] characters allowed, otherwise error
        // based on rule CharacterEscape --> c ControlLetter, where ControlLetter --> [A-Za-z]
        // https://tc39.es/ecma262/2020/#prod-CharacterEscape
        // regex engines usually consume '\' and leave rest as literals, which does not follow the standard
        if (!is_alpha(control_char)) {
            util::throw_error("Syntax error in ECMA regex: Invalid control sequence" + std::string("\\c"));
        }
        return make_token(TokenType::LITERAL, alphabet_rank(control_char));
    }

    uint32_t ECMALexer::get_backref_name_len(const uint32_t name_start_pos) const {
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

        const uint32_t open_bracket_char = m_regex[m_position];
        if (open_bracket_char != '<') {
            util::throw_error("ECMA regex syntax error: Missing '<' in named backreference");
        }

        m_position++;  // consume '<'
        const uint32_t name_start_pos = m_position;
        const uint32_t name_length = get_backref_name_len(name_start_pos);
        m_position += name_length + 1;  // consume name and '>'

        zstring_view backref_name {&m_regex[name_start_pos], name_length};
        auto it = m_named_groups.find(backref_name);
        if (it == m_named_groups.end()) {
            util::throw_error("ECMA regex syntax error: Backreference to undefined named group");
        }
        return make_token(TokenType::BACKREFERENCE, it->second);
    }

    Token ECMALexer::octal_or_backref(const uint32_t first_digit) {
        uint32_t decimal_val = first_digit - '0';
        const uint32_t fallback_pos = m_position;  // save position right after the first digit

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
            return make_token(TokenType::BACKREFERENCE, decimal_val);
        }

        // cannot be backreference --> match the input to an octal escape sequence
        m_position = fallback_pos;  // fallback to after the first digit
        return get_octal_escape_sequence_token(false, first_digit);
    }

    Token ECMALexer::get_octal_escape_sequence_token(const bool from_char_class, const uint32_t first_digit) {
        // m_position is right after first_digit. m_lexeme_start_pos is at '\'
        uint32_t max_possible_octal_len = 3;

        if (!from_char_class && (first_digit == '8' || first_digit == '9')) {
            // based on https://tc39.es/ecma262/2020/#sec-decimalescape, this is an error
            util::throw_error("ECMA regex syntax error: backreference to nonexistent subpattern");
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
        return make_token(TokenType::LITERAL, octal_val);
    }

    Token ECMALexer::get_named_capture_group_token() {
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

    uint32_t ECMALexer::validate_and_get_bound(uint32_t& bound) {
        // TODO: the value of bound can be pretty big (bigger than what fits into 32 bits) --> take care of that
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

    Token ECMALexer::get_braced_quant_token() {
        // already have '{' consumed -> check range of quantifier
        uint32_t lower_bound = 0;

        uint32_t bound_digits = validate_and_get_bound(lower_bound);

        if (bound_digits == 0 || m_position >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(TokenType::LITERAL, static_cast<uint32_t>('{'));
        }

        // case '{n}'
        if (m_regex[m_position] == '}') {
            m_position++;  // consume '}'
            return make_token(TokenType::QUANTIFIER, QuantifierRange {lower_bound, lower_bound});
        }

        if (m_regex[m_position] != ',') {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(TokenType::LITERAL, static_cast<uint32_t>('{'));
        }

        m_position++;  // skip comma
        if (m_position >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(TokenType::LITERAL, static_cast<uint32_t>('{'));
        }

        // case '{n,}'
        if (m_regex[m_position] == '}') {
            m_position++;  // consume '}'
            return make_token(TokenType::QUANTIFIER, QuantifierRange {lower_bound, UNBOUNDED});
        }

        uint32_t upper_bound = 0;
        bound_digits = validate_and_get_bound(upper_bound);

        if (bound_digits == 0 || m_position >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
            return make_token(TokenType::LITERAL, static_cast<uint32_t>('{'));
        }

        // '}' after number -> case {n,m}
        if (m_regex[m_position] == '}') {
            m_position++;  // consume '}'
            return make_token(TokenType::QUANTIFIER, QuantifierRange {lower_bound, upper_bound});
        }

        // not a well-formed quantifier --> '{' is a literal
        m_position = m_lexeme_start_pos + 1;  // rollback to skip only '{'
        return make_token(TokenType::LITERAL, static_cast<uint32_t>('{'));
    }

    Token ECMALexer::get_lookbehind_or_named_group_token() {
        // called right after '(?<'
        if (m_position >= m_regex.length()) {
            util::throw_error("ECMA regex syntax error: Unfinished sequence '(?<'");
        }

        const uint32_t fourth_char = m_regex[m_position];
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

        const uint32_t third_char = m_regex[m_position];
        m_position++;
        switch (third_char) {
            case ':':
                return make_token(TokenType::GROUP_NONCAPTURE_START);
            case '=':
                return make_token(TokenType::LOOKAHEAD_POS_START);
            case '!':
                return make_token(TokenType::LOOKAHEAD_NEG_START);
            case '<':
                return get_lookbehind_or_named_group_token();
            default:
                util::throw_error("ECMA regex syntax error: Invalid group indentifier");
                // return dummy token, because compilation errors with return type (execution wont get here)
                return {};
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

        const uint32_t second_char = m_regex[m_position];
        m_position++;
        switch (second_char) {
            case 'd':
            case 'D':
            case 'w':
            case 'W':
            case 's':
            case 'S':
                return make_token(TokenType::CHAR_CLASS_ESCAPE, second_char);
            case 'b':
            case 'B':
                return make_token(TokenType::ASSERTION, second_char);
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
                return make_token(TokenType::LITERAL, second_char);
        }
    }

    Token ECMALexer::get_token_standard() {
        const uint32_t current_char = m_regex[m_position];
        m_position++;
        switch (current_char) {
            case '*':
            case '+':
            case '?':
                return make_token(TokenType::QUANTIFIER, current_char);
            case '{':
                return get_braced_quant_token();
            case '.':
                return make_token(TokenType::DOT);
            case '|':
                return make_token(TokenType::ALTERNATION);
            case '^':
            case '$':
                return make_token(TokenType::ASSERTION, current_char);
            case '(':
                return get_group_token();
            case ')':
                return make_token(TokenType::GROUP_END);
            case '\\':
                return get_escape_sequence_token();
            case '[':
                m_in_char_class = true;
                m_first_in_char_class = true;
                return make_token(TokenType::CHAR_CLASS_START);
            default:
                return make_token(TokenType::LITERAL, current_char);
        }
    }

    Token ECMALexer::get_char_class_escape_sequence_token() {
        // called right after '\' inside character class
        if (m_position >= m_regex.length()) {
            util::throw_error("ECMA regex syntax error: Unfinished escape sequence at the end of regex");
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
                return make_token(TokenType::CHAR_CLASS_ESCAPE, second_char);
            case 'x':
                return get_hex_escape_seq_token();
            case 'u':
                return get_unicode_escape_seq_token();
            case 'c':
                return get_control_escape_seq_token();
            case 'b':
                return make_token(TokenType::LITERAL, BACKSPACE_LITERAL);
            case '0':
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
                return make_token(TokenType::LITERAL, second_char);
        }
    }

    Token ECMALexer::get_token_char_class() {
        const uint32_t current_char = m_regex[m_position];
        m_position++;

        const bool is_first = m_first_in_char_class;
        m_first_in_char_class = false;

        switch (current_char) {
            case ']':
                m_in_char_class = false;
                return make_token(TokenType::CHAR_CLASS_END);
            case '-':
                return make_token(TokenType::CHAR_CLASS_RANGE);
            case '^':
                if (is_first) {
                    return make_token(TokenType::CHAR_CLASS_NEGATION);
                } else {
                    return make_token(TokenType::LITERAL, current_char);
                }
            case '\\':
                return get_char_class_escape_sequence_token();
            default:
                return make_token(TokenType::LITERAL, current_char);
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

        uint32_t name_start = position + 1;
        uint32_t name_len = 0;
        bool found_closing_bracket = false;
        while (++position < m_regex.length()) {
            const uint32_t current_char = m_regex[position];
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
                        auto [is_capture, name] = is_capture_or_named_capture(pos);
                        if (is_capture) {
                            m_num_capture_groups++;
                            // named capture group --> add it to the map,
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
                    } else if (!in_char_class) {
                        // match not only capture groups but any group structure (lookarounds,...)
                        // lets us throw early errors
                        if (open_parens_count > 0) {
                            open_parens_count--;
                        } else {
                            util::throw_error("Syntax error: Unmatched ')' in regular expression");
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
    uint32_t ASTNodeDisjunction::print_dot(std::ostream& out, uint32_t& node_count) const {
        const uint32_t id = ++node_count;
        out << "  node" << id << " [label=\"DISJUNCTION\"];\n";
        for (const ASTNodeRef& alt : m_alternatives) {
            const uint32_t child_id = alt->print_dot(out, node_count);
            out << "  node" << id << " -> node" << child_id << ";\n";
        }
        return id;
    }

    zstring ASTNodeDisjunction::serialize() const {
        zstring res("(DISJ");
        for (const auto& alt : m_alternatives) {
            res += zstring(" ");
            res += alt->serialize();
        }
        res += zstring(")");
        return res;
    }

    void ASTNodeDisjunction::add_alternative(ASTNodeRef alt) {
        m_alternatives.push_back(std::move(alt));
    }

    RegexComponent ASTNodeDisjunction::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s,
                                                    ast_manager& m) const {
        // Disjunction is commutative --> we can merge ALL the regular segments into one
        // and nonregular segments are kept in the same order
        std::vector<app_ref> regular_alternatives;
        std::vector<GraphFragment> nonregular_alternatives;

        // First pass --> sort regular and nonregular segments
        for (const ASTNodeRef& alternative : m_alternatives) {
            RegexComponent current_term = alternative->get_subgraph(graph, util_s, m);
            if (std::holds_alternative<app_ref>(current_term)) {
                regular_alternatives.push_back(std::get<app_ref>(current_term));
                continue;
            }
            nonregular_alternatives.push_back(std::get<GraphFragment>(current_term));
        }

        // No need to construct a graph if all segments were regular
        if (!regular_alternatives.empty() && nonregular_alternatives.empty()) {
            app_ref final_regular_segment = regular_alternatives[0];
            for (std::size_t i = 1; i < regular_alternatives.size(); i++) {
                final_regular_segment = util_s.re.mk_union(final_regular_segment, regular_alternatives[i]);
            }
            return final_regular_segment;
        }

        GraphFragment result_fragment = nonregular_alternatives[0];
        for (std::size_t i = 1; i < nonregular_alternatives.size(); i++) {
            result_fragment = alternate_fragments(graph, result_fragment, nonregular_alternatives[i]);
        }

        // If there was at least one regular segment, merge them and add corresponding edge
        if (!regular_alternatives.empty()) {
            app_ref merged_regular = regular_alternatives[0];
            for (std::size_t i = 1; i < regular_alternatives.size(); i++) {
                merged_regular = app_ref(util_s.re.mk_union(merged_regular, regular_alternatives[i]), m);
            }

            // Create fragment for the merged regular segment
            VertexId reg_vout = graph.create_vertex();
            EdgeId reg_eid = graph.create_edge(reg_vout, RCGEdgePayload {MatchEdge {merged_regular}});
            VertexId reg_vin = graph.create_vertex(std::vector<EdgeId> {reg_eid});
            GraphFragment reg_fragment {reg_vin, reg_vout, {reg_eid}};

            result_fragment = alternate_fragments(graph, result_fragment, reg_fragment);
        }

        return result_fragment;
    }

    uint32_t ASTNodeAlternative::print_dot(std::ostream& out, uint32_t& node_count) const {
        const uint32_t id = ++node_count;
        out << "  node" << id << " [label=\"ALTERNATIVE\"];\n";
        for (const ASTNodeRef& term : m_terms) {
            const uint32_t child_id = term->print_dot(out, node_count);
            out << "  node" << id << " -> node" << child_id << ";\n";
        }
        return id;
    }

    zstring ASTNodeAlternative::serialize() const {
        zstring res("(SEQ");
        for (const auto& term : m_terms) {
            res += zstring(" ");
            res += term->serialize();
        }
        res += zstring(")");
        return res;
    }

    void ASTNodeAlternative::add_term(ASTNodeRef term) {
        m_terms.push_back(std::move(term));
    }

    RegexComponent ASTNodeAlternative::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s,
                                                    ast_manager& m) const {
        // Two passes through the terms that should be concatenated:
        // Pass 1. If there are adjacent regular components, merge them with mk_concat.
        std::vector<RegexComponent> simplified_terms;
        for (const ASTNodeRef& term : m_terms) {
            RegexComponent current_term = term->get_subgraph(graph, util_s, m);

            // No components yet to merge --> just add it (first iteration)
            if (simplified_terms.empty()) {
                simplified_terms.push_back(current_term);
                continue;
            }

            RegexComponent& most_recent_term = simplified_terms.back();
            // Both current and most recently added component are regular --> merge them and rewrite in-situ
            if (std::holds_alternative<app_ref>(most_recent_term) && std::holds_alternative<app_ref>(current_term)) {
                app_ref last_regular = std::get<app_ref>(most_recent_term);
                app_ref current_regular = std::get<app_ref>(current_term);
                most_recent_term = app_ref(util_s.re.mk_concat(last_regular, current_regular), m);
            } else {
                // Either of them not regular --> cannot merge, just add it
                simplified_terms.push_back(current_term);
            }
        }

        // Single regular term left --> no graph building needed
        if (simplified_terms.size() == 1 && std::holds_alternative<app_ref>(simplified_terms[0])) {
            return simplified_terms[0];
        }

        // Helper lambda for converting regular components into trivial graph fragments
        auto to_fragment = [&](RegexComponent& component) -> GraphFragment {
            if (std::holds_alternative<app_ref>(component)) {
                const VertexId v_in = graph.create_vertex();
                const VertexId v_out = graph.create_vertex();
                EdgeId eid = graph.create_edge(v_out, RCGEdgePayload {MatchEdge {std::get<app_ref>(component)}});
                graph.vertices[v_in].outgoing_edges.push_back(eid);
                return GraphFragment {v_in, v_out, {eid}};
            }
            return std::get<GraphFragment>(component);
        };

        // Pass 2. At least one component not regular --> chain the components into a graph
        GraphFragment result = to_fragment(simplified_terms[0]);
        for (std::size_t i = 1; i < simplified_terms.size(); i++) {
            GraphFragment current = to_fragment(simplified_terms[i]);
            result = chain_fragments(graph, result, current);
        }
        return result;
    }

    uint32_t ASTNodeAssertion::print_dot(std::ostream& out, uint32_t& node_count) const {
        const uint32_t id = ++node_count;
        std::string label = "ASSERTION (";
        if (m_subpattern) {
            switch (m_assert_type) {
                case TokenType::LOOKAHEAD_POS_START:
                    label += "?=";
                    break;
                case TokenType::LOOKAHEAD_NEG_START:
                    label += "?!";
                    break;
                case TokenType::LOOKBEHIND_POS_START:
                    label += "?<=";
                    break;
                case TokenType::LOOKBEHIND_NEG_START:
                    label += "?<!";
                    break;
                default:
                    break;
            }
            label += ")";
            out << "  node" << id << " [label=\"" << label << "\"];\n";
            const uint32_t child_id = m_subpattern->print_dot(out, node_count);
            out << "  node" << id << " -> node" << child_id << ";\n";
        } else {
            label += std::string(1, static_cast<char>(m_payload)) + ")";
            out << "  node" << id << " [label=\"" << label << "\"];\n";
        }
        return id;
    }

    zstring ASTNodeAssertion::serialize() const {
        if (m_subpattern) {
            zstring label;
            switch (m_assert_type) {
                case TokenType::LOOKAHEAD_POS_START:
                    label = zstring("?=");
                    break;
                case TokenType::LOOKAHEAD_NEG_START:
                    label = zstring("?!");
                    break;
                case TokenType::LOOKBEHIND_POS_START:
                    label = zstring("?<=");
                    break;
                case TokenType::LOOKBEHIND_NEG_START:
                    label = zstring("?<!");
                    break;
                default:
                    label = zstring("??");
                    break;
            }
            return zstring("(ASSERT ") + label + zstring(" ") + m_subpattern->serialize() + zstring(")");
        }
        return zstring("(ASSERT '") + zstring(m_payload) + zstring("')");
    }

    void ASTNodeAssertion::set_type(const TokenType type) {
        m_assert_type = type;
    }

    void ASTNodeAssertion::set_payload(const uint32_t payload) {
        m_payload = payload;
    }

    void ASTNodeAssertion::set_expr(ASTNodeRef expr) {
        m_subpattern = std::move(expr);
    }

    RegexComponent ASTNodeAssertion::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const {
        // Anchors --
        if (m_assert_type == TokenType::ASSERTION) {
            if (m_payload == '^' || m_payload == '$') {
                VertexId v_in = graph.create_vertex();
                VertexId v_out = graph.create_vertex();
                EdgeId eid = graph.create_edge(v_out, RCGEdgePayload {AssertionEdge {Anchor {m_payload}}});
                graph.vertices[v_in].outgoing_edges.push_back(eid);
                return GraphFragment {v_in, v_out, {eid}};
            }
            return make_word_boundary_fragment(graph, util_s, m, m_payload == 'b');
        }

        // The subpattern cannot contain backreferences
        RegexComponent inner_regex = m_subpattern->get_subgraph(graph, util_s, m);
        if (!std::holds_alternative<app_ref>(inner_regex)) {
            // TODO: nested lookarounds not supported (yet). Only backreferences inside lookaround should be unsupported
            util::throw_error("Unsupported: non-regular content inside lookaround");
        }

        const bool is_forward =
            (m_assert_type == TokenType::LOOKAHEAD_POS_START || m_assert_type == TokenType::LOOKAHEAD_NEG_START);
        const bool is_positive =
            (m_assert_type == TokenType::LOOKAHEAD_POS_START || m_assert_type == TokenType::LOOKBEHIND_POS_START);

        return make_assertion_fragment(graph, m, std::get<app_ref>(inner_regex),
                                       is_forward ? AssertionDirection::FORWARD : AssertionDirection::BACKWARD,
                                       is_positive);
    }

    GraphFragment ASTNodeAssertion::make_assertion_fragment(RegexConstraintGraph& graph, ast_manager& m,
                                                            app_ref assert_regex, AssertionDirection dir,
                                                            bool is_positive) {
        VertexId v_in = graph.create_vertex();
        VertexId v_out = graph.create_vertex();
        EdgeId eid = graph.create_edge(
            v_out, RCGEdgePayload {AssertionEdge {Lookaround {std::move(assert_regex), dir, is_positive}}});
        graph.vertices[v_in].outgoing_edges.push_back(eid);
        return GraphFragment {v_in, v_out, {eid}};
    }

    GraphFragment ASTNodeAssertion::make_word_boundary_fragment(RegexConstraintGraph& graph, seq_util& util_s,
                                                                ast_manager& m, bool is_word_boundary) {
        app_ref word_characters = make_word_char_re(util_s, m);  // [A-Za-z0-9_]

        // Branch 1: the word boundary is either after a whitespace and before a character --> (?<=\w)RE(?!\w)
        GraphFragment b1_lookbehind =
            make_assertion_fragment(graph, m, word_characters, AssertionDirection::BACKWARD, true);
        GraphFragment b1_lookahead =
            make_assertion_fragment(graph, m, word_characters, AssertionDirection::FORWARD, !is_word_boundary);

        // Branch 2: the word boundary is either after a character and before a whitespace --> (?<!\w)RE(?=\w)
        GraphFragment b2_lookbehind =
            make_assertion_fragment(graph, m, word_characters, AssertionDirection::BACKWARD, false);
        GraphFragment b2_lookahead =
            make_assertion_fragment(graph, m, word_characters, AssertionDirection::FORWARD, is_word_boundary);

        GraphFragment branch1 = chain_fragments(graph, b1_lookbehind, b1_lookahead);
        GraphFragment branch2 = chain_fragments(graph, b2_lookbehind, b2_lookahead);
        return alternate_fragments(graph, branch1, branch2);
    }

    app_ref ASTNodeAssertion::make_word_char_re(seq_util& util_s, ast_manager& m) {
        app* upper = util_s.re.mk_range(util_s.str.mk_string("A"), util_s.str.mk_string("Z"));
        app* lower = util_s.re.mk_range(util_s.str.mk_string("a"), util_s.str.mk_string("z"));
        app* digits = util_s.re.mk_range(util_s.str.mk_string("0"), util_s.str.mk_string("9"));
        app* underscore = util_s.re.mk_to_re(util_s.str.mk_string("_"));
        return {util_s.re.mk_union(upper, util_s.re.mk_union(lower, util_s.re.mk_union(digits, underscore))), m};
    }

    uint32_t ASTNodeQuantifier::print_dot(std::ostream& out, uint32_t& node_count) const {
        const uint32_t id = ++node_count;
        out << "  node" << id << " [label=\"QUANTIFIER {" << m_range.min << ",";
        if (m_range.max == UNBOUNDED) {
            out << "inf";
        } else {
            out << m_range.max;
        }
        out << "}\"];\n";
        const uint32_t child_id = m_child->print_dot(out, node_count);
        out << "  node" << id << " -> node" << child_id << ";\n";
        return id;
    }

    zstring ASTNodeQuantifier::serialize() const {
        zstring max_str = (m_range.max == UNBOUNDED) ? zstring("inf") : zstring(std::to_string(m_range.max));
        zstring min_str = zstring(std::to_string(m_range.min));

        return zstring("(QUANT {") + min_str + zstring(",") + max_str + zstring("} ") + m_child->serialize() +
               zstring(")");
    }

    void ASTNodeQuantifier::set(const Token& t, ASTNodeRef term) {
        if (std::holds_alternative<QuantifierRange>(t.payload)) {
            m_range = std::get<QuantifierRange>(t.payload);
        } else if (std::holds_alternative<uint32_t>(t.payload)) {
            const uint32_t ch = std::get<uint32_t>(t.payload);
            if (ch == '*') {
                m_range = {0, UNBOUNDED};
            } else if (ch == '+') {
                m_range = {1, UNBOUNDED};
            } else if (ch == '?') {
                m_range = {0, 1};
            }
        }
        m_child = std::move(term);
    }

    RegexComponent ASTNodeQuantifier::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s,
                                                   ast_manager& m) const {
        RegexComponent child_subgraph = m_child->get_subgraph(graph, util_s, m);
        // Backreferences or lookarounds under kleene star/plus --> unsupported yet, leads to dynamic number of string variables
        // Possible solution: fixed unrolling (not supported yet)
        if (std::holds_alternative<GraphFragment>(child_subgraph)) {
            if (m_range.max == UNBOUNDED) {
                util::throw_error("Unsupported regex structure: Non-regular constructs under kleene star/kleene plus");
            }

            // {n, m} quantified non-regular segments currently unsupported
            // TODO: possible solution: concatenate the graph fragment m times and from nth to mth copy, create epsilon-MatchEdge out
            util::throw_error("Unsupported regex structure: Non-regular constructs under {n,m} quantifier");
        }

        // Quantified regular sub-regex
        SASSERT(std::holds_alternative<app_ref>(child_subgraph));
        app_ref child_expr = std::get<app_ref>(child_subgraph);
        app* quant = nullptr;
        if (m_range.max == UNBOUNDED) {
            if (m_range.min == 0) {
                quant = util_s.re.mk_star(child_expr);
            } else if (m_range.min == 1) {
                quant = util_s.re.mk_plus(child_expr);
            } else {
                quant = util_s.re.mk_loop(child_expr, m_range.min);
            }
        } else {
            quant = util_s.re.mk_loop(child_expr, m_range.min, m_range.max);
        }
        SASSERT(quant != nullptr);
        return app_ref(quant, m);
    }

    uint32_t ASTNodeLiteral::print_dot(std::ostream& out, uint32_t& node_count) const {
        const uint32_t id = ++node_count;
        out << "  node" << id << " [label=\"LITERAL ('" << static_cast<char>(m_char) << "')\"];\n";
        return id;
    }

    zstring ASTNodeLiteral::serialize() const {
        return zstring("(LIT '") + zstring(m_char) + zstring("')");
    }

    void ASTNodeLiteral::set_char(const uint32_t ch) {
        m_char = ch;
    }

    RegexComponent ASTNodeLiteral::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const {
        SASSERT(m_char < std::numeric_limits<uint32_t>::max());
        app* str_unit = util_s.str.mk_string(m_char);
        return app_ref(util_s.re.mk_to_re(str_unit), m);
    }

    uint32_t ASTNodeDot::print_dot(std::ostream& out, uint32_t& node_count) const {
        const uint32_t id = ++node_count;
        out << "  node" << id << " [label=\"DOT\"];\n";
        return id;
    }

    zstring ASTNodeDot::serialize() const {
        return zstring("(DOT)");
    }

    RegexComponent ASTNodeDot::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const {
        return app_ref(util_s.re.mk_full_seq(nullptr), m);
    }

    uint32_t ASTNodeBackref::print_dot(std::ostream& out, uint32_t& node_count) const {
        const uint32_t id = ++node_count;
        out << "  node" << id << " [label=\"BACKREF\"];\n";
        return id;
    }

    zstring ASTNodeBackref::serialize() const {
        return zstring("(BACKREF ") + std::to_string(m_backref_id) + zstring(")");
    }

    void ASTNodeBackref::set_ref(uint32_t backref_number) {
        m_backref_id = backref_number;
    }

    RegexComponent ASTNodeBackref::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const {
        const VertexId vin = graph.create_vertex();
        const VertexId vout = graph.create_vertex();
        const EdgeId backref_eid = graph.create_edge(vout, {BackrefEdge {m_backref_id}});
        graph.vertices[vin].outgoing_edges.push_back(backref_eid);
        return GraphFragment {vin, vout, {backref_eid}};
    }

    uint32_t ASTNodeGroup::print_dot(std::ostream& out, uint32_t& node_count) const {
        const uint32_t id = ++node_count;
        std::string label = "GROUP";
        if (m_type == GroupType::NONCAPTURE) {
            label += " (?:)";
        } else {
            label += " #" + std::to_string(m_gid);
        }

        out << "  node" << id << " [label=\"" << label << "\"];\n";
        const uint32_t child_id = m_child->print_dot(out, node_count);
        out << "  node" << id << " -> node" << child_id << ";\n";
        return id;
    }

    zstring ASTNodeGroup::serialize() const {
        zstring label;
        if (m_type == GroupType::NONCAPTURE) {
            label = zstring("GROUP-NONCAP");
        } else {
            label = zstring("GROUP #") + std::to_string(m_gid);
        }
        return zstring("(") + label + zstring(" ") + m_child->serialize() + zstring(")");
    }

    void ASTNodeGroup::set_type(const GroupType type) {
        m_type = type;
    }

    void ASTNodeGroup::set_expr(ASTNodeRef expr) {
        m_child = std::move(expr);
    }

    void ASTNodeGroup::set_id(const uint32_t gid) {
        m_gid = gid;
    }

    RegexComponent ASTNodeGroup::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const {
        RegexComponent subregex = m_child->get_subgraph(graph, util_s, m);
        if (m_type == GroupType::NONCAPTURE) {
            return subregex;
        }

        // Capture groups contain very important information for the solver --> even if the subregex is regular,
        // we cannot greedily merge it with anything (possible backreferences later in the regex)
        // Therefore, we normalize the regular subregex and then work with it uniformly
        GraphFragment fragment;
        if (std::holds_alternative<app_ref>(subregex)) {
            const VertexId vin = graph.create_vertex();
            const VertexId vout = graph.create_vertex();
            const EdgeId eid = graph.create_edge(vout, RCGEdgePayload {MatchEdge {std::get<app_ref>(subregex)}});
            graph.vertices[vin].outgoing_edges.push_back(eid);
            fragment = GraphFragment {vin, vout, {eid}};
        } else {
            fragment = std::get<GraphFragment>(subregex);
        }

        // Instead of creating separate vertices for the capture groups, we tag all the edges that are going out
        // of v_in of the subregex with the capture group index.
        // If there are nested capture groups, e.g., ((a)), the edges from v_in are tagged with two capture group starts.
        for (const EdgeId eid : graph.vertices[fragment.v_in].outgoing_edges) {
            graph.group_starts[eid].push_back(m_gid);
        }

        // The same optimalization for capture group ends
        for (const EdgeId eid : fragment.edges_pointing_to_vout) {
            graph.group_ends[eid].push_back(m_gid);
        }

        return fragment;
    }

    uint32_t ASTNodeCharClass::print_dot(std::ostream& out, uint32_t& node_count) const {
        const uint32_t id = ++node_count;
        std::string label = "CLASS [";
        if (m_is_negated) {
            label += "^";
        }

        for (const auto& [kind, lower, upper] : m_elements) {
            if (kind == ElementType::SINGLE) {
                label += static_cast<char>(lower);
            } else if (kind == ElementType::ESCAPE) {
                label += "\\";
                label += static_cast<char>(lower);
            } else {
                SASSERT(kind == ElementType::RANGE);
                label += static_cast<char>(lower);
                label += "-";
                label += static_cast<char>(upper);
            }
        }
        label += "]";

        out << "  node" << id << " [label=\"" << label << "\"];\n";
        return id;
    }

    zstring ASTNodeCharClass::serialize() const {
        zstring res("(CLASS");
        if (m_is_negated) {
            res += zstring(" ^");
        }
        for (const auto& [kind, lower, upper] : m_elements) {
            if (kind == ElementType::SINGLE) {
                res += zstring(" (LIT '") + zstring(lower) + zstring("')");
            } else if (kind == ElementType::ESCAPE) {
                res += zstring(" (CHAR_CLASS '") + zstring(lower) + zstring("')");
            } else {
                SASSERT(kind == ElementType::RANGE);
                res += zstring(" (RANGE '") + zstring(lower) + zstring("' '") + zstring(upper) + zstring("')");
            }
        }
        res += zstring(")");
        return res;
    }

    void ASTNodeCharClass::add_element(const CharClassElement elem) {
        if (elem.kind == ElementType::RANGE && elem.lower > elem.upper) {
            util::throw_error("ECMA Regex error: Character range out of order");
        }
        m_elements.push_back(elem);
    }

    void ASTNodeCharClass::set_negation(const bool neg) {
        m_is_negated = neg;
    }

    RegexComponent ASTNodeCharClass::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const {
        SASSERT(!m_elements.empty());
        app_ref_vector class_elements(m);

        for (const CharClassElement& elem : m_elements) {
            if (elem.kind == ElementType::SINGLE) {
                // Convert character to internal z3 seq (string) representation, then to regex and add to vector
                app* unit_str = util_s.str.mk_string(elem.lower);
                class_elements.push_back(util_s.re.mk_to_re(unit_str));
            } else if (elem.kind == ElementType::RANGE) {
                app* lower = util_s.str.mk_string(elem.lower);
                app* upper = util_s.str.mk_string(elem.upper);
                class_elements.push_back(util_s.re.mk_range(lower, upper));
            } else {  // CHAR_CLASS
                switch (elem.lower) {
                    case 'd':
                    case 'D': {
                        app* lower = util_s.str.mk_string("0");
                        app* upper = util_s.str.mk_string("9");
                        app* re_digit = util_s.re.mk_range(lower, upper);
                        if (elem.lower == 'D') {
                            re_digit = util_s.re.mk_complement(re_digit);
                        }
                        class_elements.push_back(re_digit);
                        break;
                    }
                    case 's':
                    case 'S': {
                        // HT, VT, FF, SP, NBSP, ZWNBSP, US, LF, CR, LS, PS
                        std::array<uint32_t, 11> whitespaces {0x0009, 0x000B, 0x000C, 0x0020, 0x00A0, 0xFEFF,
                                                              0x001F, 0x000A, 0x000D, 0x2028, 0x2029};
                        app* re_whitespace = util_s.re.mk_to_re(util_s.str.mk_string(whitespaces[0]));
                        for (std::size_t i = 1; i < whitespaces.size(); i++) {
                            app* whitespace_str = util_s.re.mk_to_re(util_s.str.mk_string(whitespaces[i]));
                            re_whitespace = util_s.re.mk_union(re_whitespace, whitespace_str);
                        }
                        if (elem.lower == 'S') {
                            re_whitespace = util_s.re.mk_complement(re_whitespace);
                        }
                        class_elements.push_back(re_whitespace);
                        break;
                    }
                    case 'w':
                    case 'W': {
                        // [A-Za-z0-9_]
                        app* lowercase = util_s.re.mk_range(util_s.str.mk_string("a"), util_s.str.mk_string("z"));
                        app* uppercase = util_s.re.mk_range(util_s.str.mk_string("A"), util_s.str.mk_string("Z"));
                        app* digits = util_s.re.mk_range(util_s.str.mk_string("0"), util_s.str.mk_string("9"));
                        app* underscore = util_s.re.mk_to_re(util_s.str.mk_string("_"));
                        app* re_word = util_s.re.mk_union(util_s.re.mk_union(lowercase, uppercase),
                                                          util_s.re.mk_union(digits, underscore));
                        if (elem.lower == 'W') {
                            re_word = util_s.re.mk_complement(re_word);
                        }
                        class_elements.push_back(re_word);
                        break;
                    }
                }
            }
        }

        // Unite all the ranges and literals
        app_ref current_class_re(class_elements.get(0), m);
        for (std::size_t i = 1; i < class_elements.size(); ++i) {
            current_class_re = util_s.re.mk_union(current_class_re, class_elements.get(i));
        }
        // Negated class --> set difference of all chars and the character class
        if (m_is_negated) {
            // Set diff didnt work well --> intersection with complement
            current_class_re =
                util_s.re.mk_inter(util_s.re.mk_full_seq(nullptr), util_s.re.mk_complement(current_class_re));
        }

        return current_class_re;
    }

    // =============== ECMA REGEX PARSER ===============

    ASTNodeRef ECMAParser::parse() {
        ASTNodeRef ast = parse_disjunction();
        consume(TokenType::END_OF_INPUT, "Expected end of input");

        if (debug_mode) {
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
        }

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

        // return dummy token, because compilation errors with return type (execution wont get here)
        return {};
    }

    ASTNodeRef ECMAParser::parse_disjunction() {
        // Disjunction -> Alternative Disjunction2
        // Disjunction2 -> ALTERNATION Alternative Disjunction2 | epsilon
        ASTNodeRef alt = parse_alternative();

        // little optimalization: only one alternative --> no disjunction node
        if (m_current_token.type != TokenType::ALTERNATION) {
            return alt;
        }

        auto disj = std::make_unique<ASTNodeDisjunction>();
        disj->add_alternative(std::move(alt));
        while (match(TokenType::ALTERNATION)) {
            disj->add_alternative(parse_alternative());
        }
        return disj;
    }

    ASTNodeRef ECMAParser::parse_alternative() {
        auto alt = std::make_unique<ASTNodeAlternative>();
        while (m_current_token.type != TokenType::ALTERNATION && m_current_token.type != TokenType::GROUP_END &&
               m_current_token.type != TokenType::END_OF_INPUT) {
            alt->add_term(parse_term());
        }
        return alt;
    }

    ASTNodeRef ECMAParser::parse_term() {
        switch (m_current_token.type) {
            case TokenType::ASSERTION:
            case TokenType::LOOKAHEAD_POS_START:
            case TokenType::LOOKAHEAD_NEG_START:
            case TokenType::LOOKBEHIND_POS_START:
            case TokenType::LOOKBEHIND_NEG_START:
                return parse_assertion();
            case TokenType::LITERAL:
            case TokenType::DOT:
            case TokenType::BACKREFERENCE:
            case TokenType::CHAR_CLASS_ESCAPE:
            case TokenType::GROUP_START:
            case TokenType::GROUP_NAMED_START:
            case TokenType::GROUP_NONCAPTURE_START:
            case TokenType::CHAR_CLASS_START:
                return parse_maybe_quantifier(parse_atom());
            default:
                util::throw_error("Syntax error in ECMA regex: Unexpected token in term");

                // return dummy node because compilation errors with return type (execution wont get here)
                return {};
        }
    }

    ASTNodeRef ECMAParser::parse_maybe_quantifier(ASTNodeRef term) {
        // MaybeQuantifier -> QUANTIFIER | epsilon
        if (m_current_token.type == TokenType::QUANTIFIER) {
            const Token t = m_current_token;
            next();

            auto quant = std::make_unique<ASTNodeQuantifier>();
            quant->set(t, std::move(term));
            return quant;
        }
        return term;
    }

    ASTNodeRef ECMAParser::parse_assertion() {
        const Token t = m_current_token;
        auto node = std::make_unique<ASTNodeAssertion>();
        node->set_type(t.type);

        switch (m_current_token.type) {
            case TokenType::ASSERTION:
                SASSERT(std::holds_alternative<uint32_t>(t.payload) && "ASSERTION has no specifier");
                node->set_payload(std::get<uint32_t>(t.payload));
                next();
                return node;
            case TokenType::LOOKAHEAD_POS_START:
            case TokenType::LOOKAHEAD_NEG_START:
            case TokenType::LOOKBEHIND_POS_START:
            case TokenType::LOOKBEHIND_NEG_START:
                next();
                node->set_expr(parse_disjunction());
                consume(TokenType::GROUP_END, "Expected ')' after lookaround assertion");
                return node;
            default:
                util::throw_error("Syntax error in ECMA regex: Expected assertion");
                // return dummy node, because compilation errors with return type
                return {};
        }
    }

    ASTNodeRef ECMAParser::parse_atom() {
        const Token t = m_current_token;
        switch (m_current_token.type) {
            case TokenType::LITERAL: {
                auto literal = std::make_unique<ASTNodeLiteral>();
                // no uint32_t (character) payload --> incorrect lexer implementation
                SASSERT(std::holds_alternative<uint32_t>(t.payload) && "LITERAL has no literal value");
                literal->set_char(std::get<uint32_t>(t.payload));
                next();
                return literal;
            }
            case TokenType::DOT:
                next();
                return std::make_unique<ASTNodeDot>();
            case TokenType::BACKREFERENCE: {
                auto backref = std::make_unique<ASTNodeBackref>();
                // Lexer already transforms named backreferences into indexed-based ones
                SASSERT(std::holds_alternative<uint32_t>(t.payload) && "BACKREFERENCE payload must be uint32_t");
                backref->set_ref(std::get<uint32_t>(t.payload));
                next();
                return backref;
            }
            case TokenType::CHAR_CLASS_ESCAPE: {
                auto char_class = std::make_unique<ASTNodeCharClass>();
                // char class without uint32_t (char class specifier 'w', 'd', etc.) --> incorrect lexer implementation
                SASSERT(std::holds_alternative<uint32_t>(t.payload) && "CHAR_CLASS_ESCAPE has no class specifier");
                const CharClassElement elem {.kind = ElementType::ESCAPE, .lower = std::get<uint32_t>(t.payload)};
                char_class->add_element(elem);
                next();
                return char_class;
            }
            case TokenType::GROUP_START:
            case TokenType::GROUP_NAMED_START:
            case TokenType::GROUP_NONCAPTURE_START:
                return parse_group();
            case TokenType::CHAR_CLASS_START:
                return parse_character_class();
            default:
                util::throw_error("Syntax error in ECMA regex: Unexpected token in atom");
                // return dummy node, because compilation errors with return type (execution wont get here)
                return {};
        }
    }

    ASTNodeRef ECMAParser::parse_group() {
        const Token t = m_current_token;
        auto group = std::make_unique<ASTNodeGroup>();

        switch (m_current_token.type) {
            case TokenType::GROUP_START:
                group->set_type(GroupType::NORMAL);
                break;
            case TokenType::GROUP_NAMED_START:
                group->set_type(GroupType::NAMED);
                SASSERT(std::holds_alternative<zstring_view>(t.payload) && "GROUP_NAMED_START has no name");
                break;
            case TokenType::GROUP_NONCAPTURE_START:
                group->set_type(GroupType::NONCAPTURE);
                break;
            default:
                util::throw_error("Syntax error in ECMA regex: Expected group start");
        }

        if (m_current_token.type != TokenType::GROUP_NONCAPTURE_START) {
            m_current_group_id++;
            group->set_id(m_current_group_id);
        }

        next();
        group->set_expr(parse_disjunction());
        consume(TokenType::GROUP_END, "Expected ')' after group");
        return group;
    }

    ASTNodeRef ECMAParser::parse_character_class() {
        // CharacterClass -> CHAR_CLASS_START MaybeNegation ClassRanges CHAR_CLASS_END
        consume(TokenType::CHAR_CLASS_START, "Expected '['");

        auto char_class = std::make_unique<ASTNodeCharClass>();
        char_class->set_negation(match(TokenType::CHAR_CLASS_NEGATION));

        parse_class_ranges(char_class);
        consume(TokenType::CHAR_CLASS_END, "Expected ']'");
        return char_class;
    }

    void ECMAParser::add_atom_to_class(const ASTNodeCharClassRef& char_class_parent, const CharClassAtom atom) {
        if (atom.is_escape) {
            char_class_parent->add_element({.kind = ElementType::ESCAPE, .lower = atom.val});
        } else {
            char_class_parent->add_element({.kind = ElementType::SINGLE, .lower = atom.val});
        }
    }

    void ECMAParser::parse_class_ranges(const ASTNodeCharClassRef& char_class_parent) {
        // ClassRanges -> ClassAtom ClassRangesTail
        //             -> epsilon
        if (m_current_token.type == TokenType::LITERAL || m_current_token.type == TokenType::CHAR_CLASS_ESCAPE ||
            m_current_token.type == TokenType::CHAR_CLASS_RANGE) {
            const CharClassAtom first_atom = parse_class_atom();
            parse_class_ranges_tail(char_class_parent, first_atom);
        }
    }

    void ECMAParser::parse_class_ranges_tail(const ASTNodeCharClassRef& char_class_parent,
                                             const CharClassAtom prev_atom) {
        // ClassRangesTail -> CHAR_CLASS_RANGE DashTail
        //                 -> ClassAtomNoDash ClassRangesTail
        //                 -> epsilon
        switch (m_current_token.type) {
            case TokenType::CHAR_CLASS_RANGE:
                next();  // skip '-'
                parse_dash_tail(char_class_parent, prev_atom);
                parse_class_ranges(char_class_parent);
                break;
            case TokenType::LITERAL:
            case TokenType::CHAR_CLASS_ESCAPE: {
                add_atom_to_class(char_class_parent, prev_atom);
                const CharClassAtom next_atom = parse_class_atom_no_dash();
                parse_class_ranges_tail(char_class_parent, next_atom);
                break;
            }
            default:  // epsilon
                add_atom_to_class(char_class_parent, prev_atom);
                break;
        }
    }

    void ECMAParser::parse_dash_tail(const ASTNodeCharClassRef& char_class, const CharClassAtom atom_before_dash) {
        // DashTail -> ClassAtom ClassRanges
        //          -> epsilon
        // https://tc39.es/ecma262/2020/#sec-runtime-semantics-characterrange-abstract-operation
        // https://tc39.es/ecma262/2020/#sec-nonemptyclassrangesnodash
        // when parsing range in the character class, both class atoms have to be single characters
        // when either of them is e.g., a character class themselves (like '\w', etc.), the standard says it should be an error
        // the only valid range is in form LITERAL RANGE LITERAL
        switch (m_current_token.type) {
            case TokenType::CHAR_CLASS_ESCAPE: {
                // no matter what the atom before dash was, this is an error
                util::throw_error("ECMA Regex error: Character class as a bound of range");
                break;  // leaving 'break;' because of compilation errors
            }
            case TokenType::CHAR_CLASS_RANGE:
                // second dash in a row --> just hardcode it as a '-' literal
                char_class->add_element({.kind = ElementType::RANGE, .lower = atom_before_dash.val, .upper = '-'});
                next();
                break;
            case TokenType::LITERAL: {
                // no uint32_t should never happen here -- if so, lexer implementation is incorrect
                if (atom_before_dash.is_escape) {
                    util::throw_error("ECMA Regex Error: Character class as a bound of range");
                }
                SASSERT(std::holds_alternative<uint32_t>(m_current_token.payload) && "LITERAL has no literal value");
                const uint32_t from = atom_before_dash.val;
                const uint32_t to = std::get<uint32_t>(m_current_token.payload);
                char_class->add_element({.kind = ElementType::RANGE, .lower = from, .upper = to});
                next();
                break;
            }
            default:  // epsilon
                // the '-' that got us here is at the end of char class --> its a literal
                add_atom_to_class(char_class, atom_before_dash);
                char_class->add_element({ElementType::SINGLE, static_cast<uint32_t>('-'), 0});
                break;
        }
    }

    CharClassAtom ECMAParser::parse_class_atom() {
        // ClassAtom -> ClassAtomNoDash
        //           -> CHAR_CLASS_RANGE
        switch (m_current_token.type) {
            case TokenType::LITERAL:
            case TokenType::CHAR_CLASS_ESCAPE:
                return parse_class_atom_no_dash();
            case TokenType::CHAR_CLASS_RANGE:
                next();
                return {false, static_cast<uint32_t>('-')};
            default:
                util::throw_error("Syntax error in ECMA regex: Expected class atom");
                // return dummy node, because compilation errors with return type (execution wont get here)
                return {};
        }
    }

    CharClassAtom ECMAParser::parse_class_atom_no_dash() {
        // ClassAtomNoDash -> LITERAL | CHAR_CLASS_ESCAPE
        const Token current_token = m_current_token;
        next();
        switch (current_token.type) {
            case TokenType::LITERAL:
                SASSERT(std::holds_alternative<uint32_t>(current_token.payload));
                return {false, std::get<uint32_t>(current_token.payload)};
            case TokenType::CHAR_CLASS_ESCAPE:
                SASSERT(std::holds_alternative<uint32_t>(current_token.payload));
                return {true, std::get<uint32_t>(current_token.payload)};
            default:
                util::throw_error("Syntax error in ECMA regex: Expected literal or escape sequence");
                // return dummy node, because compilation errors with return type (execution wont get here)
                return {};
        }
    }

    // ============= ECMA REGEX HANDLER =============

    RegexConstraintGraph RegexConstraintBuilder::build_rcg() {
        const ASTNodeRef root = m_parser.parse();
        const RegexComponent comp = root->get_subgraph(m_graph, m_util_s, m_manager);

        
        if (std::holds_alternative<app_ref>(comp)) {
            const VertexId v_in = m_graph.create_vertex();
            const VertexId v_out = m_graph.create_vertex();
            const EdgeId eid = m_graph.create_edge(v_out, RCGEdgePayload {MatchEdge {std::get<app_ref>(comp)}});
            m_graph.vertices[v_in].outgoing_edges.push_back(eid);
            m_graph.start_vertex = v_in;
            m_graph.end_vertex = v_out;
        } else {
            const GraphFragment frag = std::get<GraphFragment>(comp);
            m_graph.start_vertex = frag.v_in;
            m_graph.end_vertex = frag.v_out;
        }
        return m_graph;
    }

    expr_ref RegexConstraintBuilder::generate_constraints(app* target_string) {
        SASSERT(m_graph.start_vertex != UNKNOWN_VERTEX);

        m_unique_paths.reset();
        rcg_dfs_visit(m_graph.start_vertex, target_string);

        if (m_unique_paths.empty()) {
            return {m_manager.mk_false(), m_manager};
        }

        if (m_unique_paths.size() == 1) {
            SASSERT(is_expr(m_unique_paths.get(0)));
            return {m_unique_paths.get(0), m_manager};
        }

        return {m_manager.mk_or(m_unique_paths), m_manager};
    }

    app* RegexConstraintBuilder::mk_fresh_string_var() const {
        return m_manager.mk_fresh_const("ecma_re", m_str_sort);
    }

    expr_ref RegexConstraintBuilder::concat_vars(const expr_ref_vector& vars, const std::size_t start_idx) const {
        if (start_idx >= vars.size()) {
            return {m_util_s.str.mk_empty(m_str_sort), m_manager};
        }
        if (vars.size() - start_idx == 1) {
            return {vars[start_idx], m_manager};
        }

        expr_ref_vector apps_to_concat {m_manager};
        for (std::size_t i = start_idx; i < vars.size(); i++) {
            apps_to_concat.push_back(vars[i]);
        }
        expr* concat = m_util_s.str.mk_concat(apps_to_concat, m_str_sort);
        return {concat, m_manager};
    }

    void RegexConstraintBuilder::rcg_dfs_visit(const VertexId current_vertex, app* target_string) {
        // End of graph reached
        if (current_vertex == m_graph.end_vertex) {
            expr_ref_vector final_constraints(m_manager);

            // Copy all the path constraints gathered along the path
            for (expr* c : m_current_path_constraints) {
                final_constraints.push_back(c);
            }

            // Evaluate all postponed lookaheads
            for (const auto& la : m_active_lookaheads) {
                expr_ref suffix = concat_vars(m_current_path_vars, la.start_index);
                expr_ref condition(m_manager);

                if (la.is_end_anchor) {
                    // If the lookahead was '$' anchor, then all the variables after it should be empty string (nothing is behind '$')
                    condition = app_ref(m_manager.mk_eq(suffix, m_util_s.str.mk_empty(m_str_sort)), m_manager);
                } else {
                    // Normal lookahead -- variables x_k...x_l (after the lookahead) \in RE concat Sigma*
                    app_ref sigma_star = {m_util_s.re.mk_full_seq(nullptr), m_manager};
                    app_ref la_regex = {m_util_s.re.mk_concat(la.regex, sigma_star), m_manager};
                    condition = {m_util_s.re.mk_in_re(suffix, la_regex), m_manager};
                    // Negative lookahead -- just negate the RE in it
                    if (!la.is_positive) {
                        condition = app_ref(m_manager.mk_not(condition), m_manager);
                    }
                }
                final_constraints.push_back(condition);
            }

            // All the gathered string variables make the final string
            const expr_ref path_string = concat_vars(m_current_path_vars);
            final_constraints.push_back(app_ref(m_manager.mk_eq(target_string, path_string), m_manager));

            // Every constraint on the path has to be SAT if the path should be SAT
            expr_ref_vector and_args {m_manager};
            for (expr* c : final_constraints) {
                and_args.push_back(c);
            }
            m_unique_paths.push_back(m_manager.mk_and(and_args.size(), and_args.data()));

            return;
        }

        // Recursive DFS step
        for (EdgeId eid : m_graph.vertices[current_vertex].outgoing_edges) {
            const RCGEdge& edge = m_graph.edges[eid];

            // For current edge, make a new string variable and save thestate
            app_ref edge_var(mk_fresh_string_var(), m_manager);
            m_current_path_vars.push_back(edge_var);


            // Capture groups -- mark the new ones as active
            std::vector<uint32_t> newly_started_groups;
            if (m_graph.group_starts.contains(eid)) {
                for (uint32_t gid : m_graph.group_starts.at(eid)) {
                    m_active_groups.push_back(gid);
                    newly_started_groups.push_back(gid);
                    if (!m_group_vars.contains(gid)) {
                        m_group_vars.insert({gid, expr_ref_vector(m_manager)});
                    }
                }
            }

            // The fresh variable for this edge is added to all the capture groups on the path
            for (uint32_t gid : m_active_groups) {
                m_group_vars.at(gid).push_back(edge_var);
            }

            // Helper lambda to keep the constraint addition a oneliner.
            // Also, when the recursion returns here and leaves the current edge, we can clear all the constraints we created.
            size_t constraints_pushed = 0;
            auto push_constraint = [&](const app_ref& c) {
                m_current_path_constraints.push_back(c);
                constraints_pushed++;
            };

            // Constraint generation based on the type of edge
            bool la_pushed = false;
            if (std::holds_alternative<MatchEdge>(edge.payload)) {
                // Match edge -- make a regular constraint x_i \in RE
                app_ref regex = std::get<MatchEdge>(edge.payload).regex;
                push_constraint(app_ref(m_util_s.re.mk_in_re(edge_var, regex), m_manager));
            } else if (std::holds_alternative<AssertionEdge>(edge.payload)) {
                const AssertionEdge& assertion = std::get<AssertionEdge>(edge.payload);
                push_constraint(app_ref(m_manager.mk_eq(edge_var, m_util_s.str.mk_empty(m_str_sort)), m_manager));

                if (std::holds_alternative<Anchor>(assertion.payload)) {
                    const uint32_t anchor = std::get<Anchor>(assertion.payload);
                    if (anchor == '^') {
                        // All the string variables up to this point must be empty --> x_1...x_k = epsilon
                        expr_ref prefix = concat_vars(m_current_path_vars);
                        push_constraint(app_ref(m_manager.mk_eq(prefix, m_util_s.str.mk_empty(nullptr)), m_manager));
                    } else if (anchor == '$') {
                        // The '$' anchor is postponed and then handled separately as a lookahead
                        // All the string variables following '$' must be equal to epsilon --> generate in when end of graph is reached
                        // The dummy_re will not be used at all
                        const app_ref dummy_re(m_manager.mk_false(), m_manager);
                        m_active_lookaheads.push_back({dummy_re, true, m_current_path_vars.size() - 1, true});
                        la_pushed = true;
                    }
                } else if (std::holds_alternative<Lookaround>(assertion.payload)) {
                    const Lookaround& la = std::get<Lookaround>(assertion.payload);
                    if (la.direction == AssertionDirection::FORWARD) {
                        // Lookahead --> postpone and generate constraints when end of graph is reached (same as '$' anchor)
                        m_active_lookaheads.push_back({la.regex, la.is_positive, m_current_path_vars.size() - 1});
                        la_pushed = true;
                    } else {
                        // Lookbehind --> the concatenation of preceding variables should fulfill RE in lookbehind
                        // x_1...x_k \in L(RE)
                        expr_ref prefix = concat_vars(m_current_path_vars);
                        app_ref sigma_star = {m_util_s.re.mk_full_seq(nullptr), m_manager};
                        app_ref lb_regex = {m_util_s.re.mk_concat(sigma_star, la.regex), m_manager};
                        app_ref condition = {m_util_s.re.mk_in_re(prefix, lb_regex), m_manager};
                        if (!la.is_positive) {
                            condition = app_ref(m_manager.mk_not(condition), m_manager);
                        }
                        push_constraint(condition);
                    }
                }
            } else if (std::holds_alternative<BackrefEdge>(edge.payload)) {
                const uint32_t ref_id = std::get<BackrefEdge>(edge.payload).backref_id;
                if (m_group_vars.contains(ref_id)) {
                    expr_ref captured_string = concat_vars(m_group_vars.at(ref_id));
                    push_constraint(app_ref(m_manager.mk_eq(edge_var, captured_string), m_manager));
                } else {
                    // Forward reference matches an empty string in ECMAScript standard.
                    // https://tc39.es/ecma262/2020/#sec-backreference-matcher
                    push_constraint(app_ref(m_manager.mk_eq(edge_var, m_util_s.str.mk_empty(m_str_sort)), m_manager));
                }
            }

            // Capture group ends --> if a capture group ends on this edge, remove it from active groups.
            // Save the state for later cleanup after DFS step.
            std::vector<uint32_t> newly_ended_groups;
            if (m_graph.group_ends.contains(eid)) {
                for (uint32_t gid : m_graph.group_ends.at(eid)) {
                    auto it = std::ranges::find(m_active_groups, gid);
                    if (it != m_active_groups.end()) {
                        m_active_groups.erase(it);
                        newly_ended_groups.push_back(gid);
                    }
                }
            }

            rcg_dfs_visit(edge.target, target_string);

            // State cleanup
            // 1. Make all the ended groups active again
            for (uint32_t gid : newly_ended_groups) {
                m_active_groups.push_back(gid);
            }

            // 2. Remove the fresh string variable from all active groups
            for (uint32_t gid : m_active_groups) {
                m_group_vars.at(gid).pop_back();
            }

            // 3. Make all the started groups non-active
            for (uint32_t gid : newly_started_groups) {
                std::erase(m_active_groups, gid);
            }

            // 4. If the edge was lookaround, remove it
            if (la_pushed) {
                m_active_lookaheads.pop_back();
            }

            // 5. Remove all the created constraints for this edge
            for (size_t i = 0; i < constraints_pushed; i++) {
                m_current_path_constraints.pop_back();
            }

            // 6. Delete the variable created for this edge
            m_current_path_vars.pop_back();
        }
    }

    bool GraphFragment::is_initialized() const {
        return v_in == std::numeric_limits<VertexId>::max() && v_out == std::numeric_limits<VertexId>::max();
    }
}  // namespace smt::noodler::ecma
