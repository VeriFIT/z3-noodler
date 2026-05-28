#include "ecma_regex.h"

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "util.h"
#include "util/debug.h"
#include "util/zstring_view.h"

#include <algorithm>
#include <cassert>
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
    constexpr Z3Char BACKSPACE_LITERAL = 8;
    constexpr uint64_t UNBOUNDED = std::numeric_limits<uint64_t>::max();
    constexpr bool debug_mode = false;

    constexpr Z3Char CH_HT = 0x0009;      // Horizontal Tab
    constexpr Z3Char CH_VT = 0x000B;      // Vertical Tab
    constexpr Z3Char CH_FF = 0x000C;      // Form Feed
    constexpr Z3Char CH_SP = 0x0020;      // Space
    constexpr Z3Char CH_NBSP = 0x00A0;    // Non-Breaking Space
    constexpr Z3Char CH_ZWNBSP = 0xFEFF;  // Zero Width Non-Breaking Space (BOM)
    constexpr Z3Char CH_US = 0x001F;      // Unit Separator
    constexpr Z3Char CH_LF = 0x000A;      // Line Feed
    constexpr Z3Char CH_CR = 0x000D;      // Carriage Return
    constexpr Z3Char CH_LS = 0x2028;      // Line Separator
    constexpr Z3Char CH_PS = 0x2029;      // Paragraph Separator

    zstring sanitize_ecma_regex_input(const zstring& raw_input) {
        std::ostringstream sanitized;

        auto is_continuation = [&](uint32_t idx) -> bool {
            bool is_raw_byte = raw_input[idx] <= 0xFF;
            bool is_continuation_byte = (raw_input[idx] & 0xC0) == 0x80;  // top two bits must be 10xxxxxx
            return idx < raw_input.length() && is_raw_byte && is_continuation_byte;
        };

        // Unicode replacement character -- used when invalid byte is encountered
        auto insert_unicode_replacement = [&]() {
            sanitized << "\\u{fffd}";
        };

        uint32_t i = 0;
        while (i < raw_input.length()) {
            Z3Char raw_char = raw_input[i];

            // If the character value is > 0xFF, the zstring constructor already parsed it into a valid Unicode code
            // point --> skip this. Originally, the character was in form \uXXXX or similar.
            if (raw_char > 0xFF) {
                sanitized << "\\u{" << std::hex << raw_char << std::dec << "}";
                i++;
                continue;
            }

            if (raw_char < 0x80) {
                // 0xxxxxxx (1 byte)
                sanitized << static_cast<char>(raw_char);
                i++;
            } else if ((raw_char & 0xE0) == 0xC0) {
                // 110xxxxx 10xxxxxx (2 bytes)
                if (!is_continuation(i + 1)) {
                    insert_unicode_replacement();
                    i++;
                    continue;
                }
                Z3Char code_point = ((raw_char & 0x1F) << 6) | (raw_input[i + 1] & 0x3F);
                if (code_point < 0x80) {
                    insert_unicode_replacement();
                    i += 2;
                    continue;
                }
                sanitized << "\\u{" << std::hex << code_point << std::dec << "}";
                i += 2;
            } else if ((raw_char & 0xF0) == 0xE0) {
                // 1110xxxx 10xxxxxx 10xxxxxx (3 bytes)
                if (!is_continuation(i + 1) || !is_continuation(i + 2)) {
                    insert_unicode_replacement();
                    i++;
                    continue;
                }
                Z3Char code_point =
                    ((raw_char & 0x0F) << 12) | ((raw_input[i + 1] & 0x3F) << 6) | (raw_input[i + 2] & 0x3F);
                if (code_point < 0x800 || (code_point >= 0xD800 && code_point <= 0xDFFF)) {
                    insert_unicode_replacement();
                    i += 3;
                    continue;
                }
                sanitized << "\\u{" << std::hex << code_point << std::dec << "}";
                i += 3;
            } else if ((raw_char & 0xF8) == 0xF0) {
                // 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx (4 bytes)
                if (!is_continuation(i + 1) || !is_continuation(i + 2) || !is_continuation(i + 3)) {
                    insert_unicode_replacement();
                    i++;
                    continue;
                }
                Z3Char code_point = ((raw_char & 0x07) << 18) | ((raw_input[i + 1] & 0x3F) << 12) |
                                    ((raw_input[i + 2] & 0x3F) << 6) | (raw_input[i + 3] & 0x3F);
                if (code_point < 0x10000 || code_point > 0x10FFFF) {
                    insert_unicode_replacement();
                    i += 4;
                    continue;
                }
                sanitized << "\\u{" << std::hex << code_point << std::dec << "}";
                i += 4;
            } else {
                insert_unicode_replacement();
                i++;
            }
        }
        return zstring(sanitized.str().c_str());
    }

    GraphFragment chain_fragments(RegexConstraintGraph& graph, const GraphFragment& first,
                                  const GraphFragment& second) {
        for (const EdgeID id : first.edges_pointing_to_vout) {
            graph.edges[id].target = second.v_in;
        }
        return GraphFragment {first.v_in, second.v_out, second.edges_pointing_to_vout};
    }

    GraphFragment alternate_fragments(RegexConstraintGraph& graph, const GraphFragment& first,
                                      const GraphFragment& second) {
        std::vector<EdgeID> new_vin_outgoing;
        for (const EdgeID id : graph.vertices[first.v_in].outgoing_edges) {
            new_vin_outgoing.push_back(id);
        }
        for (const EdgeID id : graph.vertices[second.v_in].outgoing_edges) {
            new_vin_outgoing.push_back(id);
        }

        graph.vertices[first.v_in].outgoing_edges.clear();
        graph.vertices[second.v_in].outgoing_edges.clear();

        const VertexID new_vin = graph.create_vertex(new_vin_outgoing);
        const VertexID new_vout = graph.create_vertex();

        std::vector<EdgeID> new_vout_incoming;
        for (const EdgeID id : first.edges_pointing_to_vout) {
            graph.edges[id].target = new_vout;
            new_vout_incoming.push_back(id);
        }
        for (const EdgeID id : second.edges_pointing_to_vout) {
            graph.edges[id].target = new_vout;
            new_vout_incoming.push_back(id);
        }

        return GraphFragment {new_vin, new_vout, new_vout_incoming};
    }

    GraphFragment make_epsilon_fragment(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) {
        const VertexID v_in = graph.create_vertex();
        const VertexID v_out = graph.create_vertex();
        app_ref eps(util_s.re.mk_epsilon(util_s.mk_string_sort()), m);
        const EdgeID eid = graph.create_edge(v_out, RCGEdgePayload {MatchEdge {eps}});
        graph.vertices[v_in].outgoing_edges.push_back(eid);
        return GraphFragment {v_in, v_out, {eid}};
    }

    // =============== REGEX CONSTRAINT GRAPH ==============

    void RegexConstraintGraph::add_vertex(RCGVertex vtx) {
        vertices.push_back(std::move(vtx));
    }

    VertexID RegexConstraintGraph::create_vertex() {
        VertexID new_id = vertices.size();
        vertices.emplace_back(new_id, std::vector<EdgeID> {});
        return new_id;
    }

    VertexID RegexConstraintGraph::create_vertex(std::vector<EdgeID> edge_list) {
        VertexID new_id = vertices.size();
        vertices.emplace_back(new_id, std::move(edge_list));
        return new_id;
    }

    void RegexConstraintGraph::add_edge(RCGEdge child) {
        edges.push_back(std::move(child));
    }

    EdgeID RegexConstraintGraph::create_edge() {
        EdgeID new_id = edges.size();
        edges.emplace_back(new_id, UNKNOWN_VERTEX, BackrefEdge {0u});
        return new_id;
    }

    EdgeID RegexConstraintGraph::create_edge(VertexID target_vertex, RCGEdgePayload payload) {
        EdgeID new_id = edges.size();
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
            } else if (hex_digit >= 'A' && hex_digit <= 'F') {
                res = res * 16 + (hex_digit - 'A' + 10);
            } else {
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
        // unicode escape sequence in format \uHHHH
        // currently m_position is on the first hex digit right after '\u' -- hence the 3
        if (m_position + 3 >= m_regex.length()) {
            m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\u'
            return make_token(TokenType::LITERAL, static_cast<Z3Char>('u'));
        }

        for (uint32_t i = 0; i < UNICODE_ESCAPE_SEQUENCE_LEN; i++) {
            const Z3Char current_char = m_regex[m_position + i];
            if (!is_hex_digit(current_char)) {
                m_position = m_lexeme_start_pos + 2;  // rollback to skip just '\u'
                return make_token(TokenType::LITERAL, static_cast<Z3Char>('u'));
            }
        }

        util::throw_error(
            "How did we get here? The zstring constructor should have parsed the unicode sequence for us");
        // return dummy token, because compilation errors with return type (execution wont get here)
        return {};
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
        Z3Char decimal_val = first_digit - '0';
        const uint32_t fallback_pos = m_position;  // save position right after the first digit

        // greedily read as much digits as possible
        while (m_position < m_regex.length()) {
            const Z3Char digit = m_regex[m_position];
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
            bound_value = bound_value * 10 + static_cast<uint64_t>(current_digit - '0');
            m_position++;
            parsed_digits++;
        }
        return parsed_digits;
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
            if (m_regex[m_position] == '?') {
                // skip lazy quantifier
                m_position++;
            }
            return make_token(TokenType::QUANTIFIER, QuantifierRange {lower_bound, lower_bound});
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
            if (m_regex[m_position] == '?') {
                // skip lazy quantifier
                m_position++;
            }
            return make_token(TokenType::QUANTIFIER, QuantifierRange {lower_bound, UNBOUNDED});
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
            if (m_regex[m_position] == '?') {
                m_position++;
            }
            return make_token(TokenType::QUANTIFIER, QuantifierRange {lower_bound, upper_bound});
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

        const Z3Char second_char = m_regex[m_position];
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
            case 't':
                return make_token(TokenType::LITERAL, CH_HT);
            case 'n':
                return make_token(TokenType::LITERAL, CH_LF);
            case 'r':
                return make_token(TokenType::LITERAL, CH_CR);
            case 'f':
                return make_token(TokenType::LITERAL, CH_FF);
            case 'v':
                return make_token(TokenType::LITERAL, CH_VT);
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
        const Z3Char current_char = m_regex[m_position];
        m_position++;
        switch (current_char) {
            case '*':
            case '+':
            case '?':
                // lazy quantifier -- not relevant for membership problem, just skip it
                if (m_regex[m_position] == '?') {
                    m_position++;
                }
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

        const Z3Char second_char = m_regex[m_position];
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
            case 't':
                return make_token(TokenType::LITERAL, CH_HT);
            case 'n':
                return make_token(TokenType::LITERAL, CH_LF);
            case 'r':
                return make_token(TokenType::LITERAL, CH_CR);
            case 'f':
                return make_token(TokenType::LITERAL, CH_FF);
            case 'v':
                return make_token(TokenType::LITERAL, CH_VT);
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
        const Z3Char current_char = m_regex[m_position];
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
    uint64_t ASTNodeDisjunction::print_dot(std::ostream& out, uint64_t& node_count) const {
        const uint64_t id = ++node_count;
        out << "  node" << id << " [label=\"DISJUNCTION\"];\n";
        for (const ASTNodeRef& alt : m_alternatives) {
            const uint64_t child_id = alt->print_dot(out, node_count);
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
        std::vector<app_ref> regular_alternatives;
        std::vector<GraphFragment> nonregular_alternatives;

        // First pass -- sort regular and nonregular alternatives
        for (const ASTNodeRef& alternative : m_alternatives) {
            RegexComponent current_term = alternative->get_subgraph(graph, util_s, m);
            if (std::holds_alternative<app_ref>(current_term)) {
                regular_alternatives.push_back(std::get<app_ref>(current_term));
                continue;
            }
            nonregular_alternatives.push_back(std::get<GraphFragment>(current_term));
        }

        // All alternatives regular -- create a single regular fragment
        if (!regular_alternatives.empty() && nonregular_alternatives.empty()) {
            app_ref final_regular_segment = regular_alternatives[0];
            for (std::size_t i = 1; i < regular_alternatives.size(); i++) {
                final_regular_segment = util_s.re.mk_union(final_regular_segment, regular_alternatives[i]);
            }
            return final_regular_segment;
        }

        // Since alternation is commutative, unite all nonregular fragments first
        GraphFragment result_fragment = nonregular_alternatives[0];
        for (std::size_t i = 1; i < nonregular_alternatives.size(); i++) {
            result_fragment = alternate_fragments(graph, result_fragment, nonregular_alternatives[i]);
        }

        if (!regular_alternatives.empty()) {
            // Then, merge all regular alternatives into one regular fragment
            app_ref merged_regular = regular_alternatives[0];
            for (std::size_t i = 1; i < regular_alternatives.size(); i++) {
                merged_regular = {util_s.re.mk_union(merged_regular, regular_alternatives[i]), m};
            }

            // Lastly, unite the created regular fragment with all the non-regular ones
            VertexID reg_vout = graph.create_vertex();
            EdgeID reg_eid = graph.create_edge(reg_vout, RCGEdgePayload {MatchEdge {merged_regular}});
            VertexID reg_vin = graph.create_vertex(std::vector<EdgeID> {reg_eid});
            GraphFragment reg_fragment {reg_vin, reg_vout, {reg_eid}};

            result_fragment = alternate_fragments(graph, result_fragment, reg_fragment);
        }

        return result_fragment;
    }

    void ASTNodeDisjunction::strip_captures() {
        for (const ASTNodeRef& alternative : m_alternatives) {
            alternative->strip_captures();
        }
    }

    void ASTNodeDisjunction::collect_backrefs(std::unordered_set<GroupID>& refs) const {
        for (const ASTNodeRef& alternative : m_alternatives) {
            alternative->collect_backrefs(refs);
        }
    }

    void ASTNodeDisjunction::strip_unreferenced_captures(const std::unordered_set<GroupID>& referenced) {
        for (const ASTNodeRef& alternative : m_alternatives) {
            alternative->strip_unreferenced_captures(referenced);
        }
    }

    ASTNodeRef ASTNodeDisjunction::clone() const {
        auto cloned = std::make_unique<ASTNodeDisjunction>();
        for (const auto& alt : m_alternatives) {
            cloned->add_alternative(alt->clone());
        }
        return cloned;
    }

    uint64_t ASTNodeAlternative::print_dot(std::ostream& out, uint64_t& node_count) const {
        const uint64_t id = ++node_count;
        out << "  node" << id << " [label=\"ALTERNATIVE\"];\n";
        for (const ASTNodeRef& term : m_terms) {
            const uint64_t child_id = term->print_dot(out, node_count);
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
        if (m_terms.empty()) {
            return app_ref(util_s.re.mk_epsilon(util_s.mk_string_sort()), m);
        }

        // First pass: merge adjacent literals into one string
        std::vector<RegexComponent> components;
        zstring literal_buf;
        auto flush_literals = [&]() {
            if (!literal_buf.empty()) {
                components.emplace_back(app_ref(util_s.re.mk_to_re(util_s.str.mk_string(literal_buf)), m));
                literal_buf = zstring();
            }
        };

        for (const ASTNodeRef& term : m_terms) {
            const auto* lit = dynamic_cast<const ASTNodeLiteral*>(term.get());
            if (lit != nullptr) {
                literal_buf += lit->get_char();
            } else {
                flush_literals();
                components.emplace_back(term->get_subgraph(graph, util_s, m));
            }
        }
        flush_literals();

        if (components.size() == 1) {
            return components[0];
        }

        // Second pass: merge adjacent regular components into one regex
        std::vector<RegexComponent> simplified;
        for (RegexComponent& comp : components) {
            if (!simplified.empty() && std::holds_alternative<app_ref>(simplified.back()) &&
                std::holds_alternative<app_ref>(comp)) {
                simplified.back() =
                    app_ref(util_s.re.mk_concat(std::get<app_ref>(simplified.back()), std::get<app_ref>(comp)), m);
            } else {
                simplified.emplace_back(std::move(comp));
            }
        }

        if (simplified.size() == 1) {
            return simplified[0];
        }

        // Helper lambda for fragment creation
        auto to_fragment = [&](RegexComponent& component) -> GraphFragment {
            if (std::holds_alternative<app_ref>(component)) {
                const VertexID v_in = graph.create_vertex();
                const VertexID v_out = graph.create_vertex();
                EdgeID eid = graph.create_edge(v_out, RCGEdgePayload {MatchEdge {std::get<app_ref>(component)}});
                graph.vertices[v_in].outgoing_edges.push_back(eid);
                return GraphFragment {v_in, v_out, {eid}};
            }
            return std::get<GraphFragment>(component);
        };

        // Chain all the regular and non-regular fragments together in order
        GraphFragment result = to_fragment(simplified[0]);
        for (std::size_t i = 1; i < simplified.size(); i++) {
            result = chain_fragments(graph, result, to_fragment(simplified[i]));
        }
        return result;
    }

    void ASTNodeAlternative::strip_captures() {
        for (const ASTNodeRef& term : m_terms) {
            term->strip_captures();
        }
    }

    void ASTNodeAlternative::collect_backrefs(std::unordered_set<GroupID>& refs) const {
        for (const ASTNodeRef& term : m_terms) {
            term->collect_backrefs(refs);
        }
    }

    void ASTNodeAlternative::strip_unreferenced_captures(const std::unordered_set<GroupID>& referenced) {
        for (const ASTNodeRef& term : m_terms) {
            term->strip_unreferenced_captures(referenced);
        }
    }

    ASTNodeRef ASTNodeAlternative::clone() const {
        auto cloned = std::make_unique<ASTNodeAlternative>();
        for (const auto& term : m_terms) {
            cloned->add_term(term->clone());
        }
        return cloned;
    }

    uint64_t ASTNodeAssertion::print_dot(std::ostream& out, uint64_t& node_count) const {
        const uint64_t id = ++node_count;
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
            const uint64_t child_id = m_subpattern->print_dot(out, node_count);
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

    void ASTNodeAssertion::set_payload(const Z3Char payload) {
        m_payload = payload;
    }

    void ASTNodeAssertion::set_expr(ASTNodeRef expr) {
        m_subpattern = std::move(expr);
    }

    RegexComponent ASTNodeAssertion::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const {
        // Anchors -- directly create AssertionEdge with the anchor as the payload
        if (m_assert_type == TokenType::ASSERTION) {
            if (m_payload == '^' || m_payload == '$') {
                VertexID v_in = graph.create_vertex();
                VertexID v_out = graph.create_vertex();
                EdgeID eid = graph.create_edge(v_out, RCGEdgePayload {AssertionEdge {Anchor {m_payload}}});
                graph.vertices[v_in].outgoing_edges.push_back(eid);
                return GraphFragment {v_in, v_out, {eid}};
            }
            return make_word_boundary_fragment(graph, util_s, m, m_payload == 'b');
        }

        const RegexComponent inner_regex = m_subpattern->get_subgraph(graph, util_s, m);

        const bool is_forward =
            (m_assert_type == TokenType::LOOKAHEAD_POS_START || m_assert_type == TokenType::LOOKAHEAD_NEG_START);
        const bool is_positive =
            (m_assert_type == TokenType::LOOKAHEAD_POS_START || m_assert_type == TokenType::LOOKBEHIND_POS_START);
        const LookaroundDirection dir = is_forward ? LookaroundDirection::FORWARD : LookaroundDirection::BACKWARD;

        // Lookarounds with regular content --> create AssertionEdge with regex as payload
        if (std::holds_alternative<app_ref>(inner_regex)) {
            return make_assertion_fragment(graph, m, std::get<app_ref>(inner_regex), dir, is_positive);
        }

        // Non-regular lookarounds with non-regular inner content are not supported, since they would require universal
        // quantification. Lookarounds with regular content can be expressed as a negation of regular language -->
        // supported.
        if (!is_positive) {
            util::throw_error("Unsupported: negative lookaround with non-regular inner content "
                              "(would require universal quantifiers)");
        }

        GraphFragment inner_frag = std::get<GraphFragment>(inner_regex);

        // A non-regular lookaround needs to be wrapped on the open side with Sigma*,
        // otherwise it becomes a strict exact match up to the boundary.
        VertexID s_in = graph.create_vertex();
        VertexID s_out = graph.create_vertex();
        EdgeID s_eid =
            graph.create_edge(s_out, RCGEdgePayload {MatchEdge {app_ref(util_s.re.mk_full_seq(nullptr), m)}});
        graph.vertices[s_in].outgoing_edges.push_back(s_eid);
        GraphFragment sigma_frag {s_in, s_out, {s_eid}};

        // Chain Sigma* on the correct side of the inner fragment, depending on the lookaround direction
        // Lookaheads --> Pattern concat Sigma*
        // Lookbehinds --> Sigma* concat pattern
        if (dir == LookaroundDirection::FORWARD) {
            inner_frag = chain_fragments(graph, inner_frag, sigma_frag);
        } else {
            inner_frag = chain_fragments(graph, sigma_frag, inner_frag);
        }

        // Wrap the resulting fragment into an AssertionEdge
        VertexID v_in = graph.create_vertex();
        VertexID v_out = graph.create_vertex();
        EdgeID eid =
            graph.create_edge(v_out, RCGEdgePayload {AssertionEdge {Lookaround {std::move(inner_frag), dir, true}}});
        graph.vertices[v_in].outgoing_edges.push_back(eid);
        return GraphFragment {v_in, v_out, {eid}};
    }

    void ASTNodeAssertion::strip_captures() {
        if (m_assert_type == TokenType::ASSERTION) {
            // anchors have no capture groups to strip
            return;
        }
        m_subpattern->strip_captures();
    }

    void ASTNodeAssertion::collect_backrefs(std::unordered_set<GroupID>& refs) const {
        if (m_subpattern != nullptr) {
            m_subpattern->collect_backrefs(refs);
        }
    }

    void ASTNodeAssertion::strip_unreferenced_captures(const std::unordered_set<GroupID>& referenced) {
        if (m_subpattern != nullptr) {
            m_subpattern->strip_unreferenced_captures(referenced);
        }
    }

    ASTNodeRef ASTNodeAssertion::clone() const {
        auto cloned = std::make_unique<ASTNodeAssertion>();
        cloned->m_assert_type = m_assert_type;
        cloned->m_payload = m_payload;
        if (m_subpattern) {
            cloned->m_subpattern = m_subpattern->clone();
        }
        return cloned;
    }

    GraphFragment ASTNodeAssertion::make_assertion_fragment(RegexConstraintGraph& graph, ast_manager& m,
                                                            app_ref assert_regex, const LookaroundDirection dir,
                                                            const bool is_positive) {
        const VertexID v_in = graph.create_vertex();
        const VertexID v_out = graph.create_vertex();
        EdgeID eid = graph.create_edge(
            v_out, RCGEdgePayload {AssertionEdge {Lookaround {std::move(assert_regex), dir, is_positive}}});
        graph.vertices[v_in].outgoing_edges.push_back(eid);
        return GraphFragment {v_in, v_out, {eid}};
    }

    GraphFragment ASTNodeAssertion::make_word_boundary_fragment(RegexConstraintGraph& graph, seq_util& util_s,
                                                                ast_manager& m, const bool is_word_boundary) {
        //  A word boundary matches at a position where one side is a word char (\w) and the other is not. This is
        //  modelled as two branches in alternation:
        //    branch1: lookbehind(\w) AND lookahead(\W) -- or the reverse for '\B'
        //    branch2: lookbehind(\W) AND lookahead(\w) -- or the reverse for '\B'
        //  Each branch is built as a chain of two assertion fragments.
        const app_ref word_characters = {util_s.re.mk_word_char(), m};

        const GraphFragment b1_lookbehind =
            make_assertion_fragment(graph, m, word_characters, LookaroundDirection::BACKWARD, true);
        const GraphFragment b1_lookahead =
            make_assertion_fragment(graph, m, word_characters, LookaroundDirection::FORWARD, !is_word_boundary);

        const GraphFragment b2_lookbehind =
            make_assertion_fragment(graph, m, word_characters, LookaroundDirection::BACKWARD, false);
        const GraphFragment b2_lookahead =
            make_assertion_fragment(graph, m, word_characters, LookaroundDirection::FORWARD, is_word_boundary);

        const GraphFragment branch1 = chain_fragments(graph, b1_lookbehind, b1_lookahead);
        const GraphFragment branch2 = chain_fragments(graph, b2_lookbehind, b2_lookahead);
        return alternate_fragments(graph, branch1, branch2);
    }

    uint64_t ASTNodeQuantifier::print_dot(std::ostream& out, uint64_t& node_count) const {
        const uint64_t id = ++node_count;
        out << "  node" << id << " [label=\"QUANTIFIER {" << m_range.min << ",";
        if (m_range.max == UNBOUNDED) {
            out << "inf";
        } else {
            out << m_range.max;
        }
        out << "}\"];\n";
        const uint64_t child_id = m_child->print_dot(out, node_count);
        out << "  node" << id << " -> node" << child_id << ";\n";
        return id;
    }

    zstring ASTNodeQuantifier::serialize() const {
        const zstring max_str = (m_range.max == UNBOUNDED) ? zstring("inf") : zstring(std::to_string(m_range.max));
        const zstring min_str = zstring(std::to_string(m_range.min));

        return zstring("(QUANT {") + min_str + zstring(",") + max_str + zstring("} ") + m_child->serialize() +
               zstring(")");
    }

    void ASTNodeQuantifier::set(const Token& t, ASTNodeRef term) {
        if (std::holds_alternative<QuantifierRange>(t.payload)) {
            m_range = std::get<QuantifierRange>(t.payload);
        } else if (std::holds_alternative<Z3Char>(t.payload)) {
            const Z3Char ch = std::get<Z3Char>(t.payload);
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

    void ASTNodeQuantifier::strip_captures() {
        m_child->strip_captures();
    }

    ASTNodeRef ASTNodeQuantifier::clone() const {
        auto cloned = std::make_unique<ASTNodeQuantifier>();
        cloned->m_range = m_range;
        cloned->m_child = m_child->clone();
        return cloned;
    }

    ASTNodeRef ASTNodeQuantifier::unroll() const {
        auto disj = std::make_unique<ASTNodeDisjunction>();

        if (m_range.min == 0) {
            disj->add_alternative(std::make_unique<ASTNodeAlternative>());
        }

        // Create chains with (min, min+1, ..., max) subtrees and alternate them all.
        const uint64_t start = std::max<uint64_t>(1, m_range.min);
        for (uint64_t k = start; k <= m_range.max; ++k) {
            auto alt = std::make_unique<ASTNodeAlternative>();
            for (uint64_t i = 0; i < k; ++i) {
                alt->add_term(m_child->clone());
            }
            disj->add_alternative(std::move(alt));
        }

        return disj;
    }

    RegexComponent ASTNodeQuantifier::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s,
                                                   ast_manager& m) const {
        const RegexComponent child_subgraph = m_child->get_subgraph(graph, util_s, m);

        if (std::holds_alternative<GraphFragment>(child_subgraph)) {
            // Nonregular fragments under unbounded quantifiers -- unsupported.
            if (m_range.max == UNBOUNDED) {
                util::throw_error("Unsupported regex structure: Non-regular constructs under kleene star/kleene plus");
            }
            // Nonregular fragments under bounded quantifier -- statically unroll the AST and convert to graph fragment.
            return unroll()->get_subgraph(graph, util_s, m);
        }

        // Regular subregex --> directly create the corresponding regular expression
        SASSERT(std::holds_alternative<app_ref>(child_subgraph));
        const app_ref child_expr = std::get<app_ref>(child_subgraph);
        app* quant = nullptr;

        if (m_range.max == UNBOUNDED) {
            if (m_range.min == 0) {
                quant = util_s.re.mk_star(child_expr);
            } else if (m_range.min == 1) {
                quant = util_s.re.mk_plus(child_expr);
            } else {
                // Concatenation `min` times followed by kleene star
                quant = child_expr;
                for (uint64_t i = 1; i < m_range.min; i++) {
                    quant = util_s.re.mk_concat(quant, child_expr);
                }
                quant = util_s.re.mk_concat(quant, util_s.re.mk_star(child_expr));
            }
        } else {
            // For some reason, using mk_loop and mk_power directly leads to unsoudness of the solver, although the
            // semantics should be the same as concatenation.
            // if (m_range.min == m_range.max) {
            //     quant = util_s.re.mk_power(child_expr, m_range.min);
            // } else {
            //     quant = util_s.re.mk_loop(child_expr, m_range.min, m_range.max);
            // }
            if (m_range.min == m_range.max) {
                if (m_range.min == 0) {
                    quant = util_s.re.mk_epsilon(util_s.mk_string_sort());
                } else {
                    // A concrete number of concatenations
                    quant = child_expr;
                    for (uint64_t i = 1; i < m_range.min; i++) {
                        quant = util_s.re.mk_concat(quant, child_expr);
                    }
                }
            } else {
                // Range [min, max]:
                // Obligatory part -- at least `min` times
                app* at_least_min = util_s.re.mk_epsilon(util_s.mk_string_sort());
                if (m_range.min > 0) {
                    at_least_min = child_expr;
                    for (uint64_t i = 1; i < m_range.min; i++) {
                        at_least_min = util_s.re.mk_concat(at_least_min, child_expr);
                    }
                }

                // Optional pattern -- union with epsilon
                app* eps = util_s.re.mk_epsilon(util_s.mk_string_sort());
                app* re_optional = util_s.re.mk_union(eps, child_expr);

                // Chain the optional pattern `max` - `min` times
                app* up_to_max = re_optional;
                for (uint64_t i = 1; i < (m_range.max - m_range.min); i++) {
                    up_to_max = util_s.re.mk_concat(up_to_max, re_optional);
                }

                quant = util_s.re.mk_concat(at_least_min, up_to_max);
            }
        }

        SASSERT(quant != nullptr);
        return app_ref(quant, m);
    }

    void ASTNodeQuantifier::collect_backrefs(std::unordered_set<GroupID>& refs) const {
        m_child->collect_backrefs(refs);
    }

    void ASTNodeQuantifier::strip_unreferenced_captures(const std::unordered_set<GroupID>& referenced) {
        m_child->strip_unreferenced_captures(referenced);
    }

    uint64_t ASTNodeLiteral::print_dot(std::ostream& out, uint64_t& node_count) const {
        const uint64_t id = ++node_count;
        out << "  node" << id << " [label=\"LITERAL ('" << static_cast<char>(m_char) << "')\"];\n";
        return id;
    }

    zstring ASTNodeLiteral::serialize() const {
        return zstring("(LIT '") + zstring(m_char) + zstring("')");
    }

    void ASTNodeLiteral::set_char(const Z3Char ch) {
        m_char = ch;
    }

    Z3Char ASTNodeLiteral::get_char() const {
        return m_char;
    }

    RegexComponent ASTNodeLiteral::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const {
        // Always return mk.to_re(mk_string(char))
        SASSERT(m_char < std::numeric_limits<Z3Char>::max());
        app* str_unit = util_s.str.mk_string(m_char);
        return app_ref(util_s.re.mk_to_re(str_unit), m);
    }

    ASTNodeRef ASTNodeLiteral::clone() const {
        return std::make_unique<ASTNodeLiteral>(*this);
    }

    uint64_t ASTNodeDot::print_dot(std::ostream& out, uint64_t& node_count) const {
        const uint64_t id = ++node_count;
        out << "  node" << id << " [label=\"DOT\"];\n";
        return id;
    }

    zstring ASTNodeDot::serialize() const {
        return zstring("(DOT)");
    }

    RegexComponent ASTNodeDot::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const {
        return app_ref(util_s.re.mk_full_char(nullptr), m);
    }

    ASTNodeRef ASTNodeDot::clone() const {
        return std::make_unique<ASTNodeDot>(*this);
    }

    uint64_t ASTNodeBackref::print_dot(std::ostream& out, uint64_t& node_count) const {
        const uint64_t id = ++node_count;
        out << "  node" << id << " [label=\"BACKREF\"];\n";
        return id;
    }

    zstring ASTNodeBackref::serialize() const {
        return zstring("(BACKREF ") + std::to_string(m_backref_id) + zstring(")");
    }

    void ASTNodeBackref::set_ref(const GroupID backref_number) {
        m_backref_id = backref_number;
    }

    RegexComponent ASTNodeBackref::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const {
        const VertexID vin = graph.create_vertex();
        const VertexID vout = graph.create_vertex();
        const EdgeID backref_eid = graph.create_edge(vout, {BackrefEdge {m_backref_id}});
        graph.vertices[vin].outgoing_edges.push_back(backref_eid);
        return GraphFragment {vin, vout, {backref_eid}};
    }

    ASTNodeRef ASTNodeBackref::clone() const {
        return std::make_unique<ASTNodeBackref>(*this);
    }

    void ASTNodeBackref::collect_backrefs(std::unordered_set<GroupID>& refs) const {
        refs.insert(m_backref_id);
    }

    uint64_t ASTNodeGroup::print_dot(std::ostream& out, uint64_t& node_count) const {
        const uint64_t id = ++node_count;
        std::string label = "GROUP";
        if (m_type == GroupType::NONCAPTURE) {
            label += " (?:)";
        } else {
            label += " #" + std::to_string(m_gid);
        }

        out << "  node" << id << " [label=\"" << label << "\"];\n";
        const uint64_t child_id = m_child->print_dot(out, node_count);
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

    void ASTNodeGroup::set_id(const GroupID gid) {
        m_gid = gid;
    }

    RegexComponent ASTNodeGroup::get_subgraph(RegexConstraintGraph& graph, seq_util& util_s, ast_manager& m) const {
        RegexComponent subregex = m_child->get_subgraph(graph, util_s, m);
        // Noncapturing groups --> no semantic meaning for the subregex
        if (m_type == GroupType::NONCAPTURE) {
            return subregex;
        }

        GraphFragment fragment;
        if (std::holds_alternative<app_ref>(subregex)) {
            // Regular subregex in group -- create a MatchEdge and create a fragment
            const VertexID vin = graph.create_vertex();
            const VertexID vout = graph.create_vertex();
            const EdgeID eid = graph.create_edge(vout, RCGEdgePayload {MatchEdge {std::get<app_ref>(subregex)}});
            graph.vertices[vin].outgoing_edges.push_back(eid);
            fragment = GraphFragment {vin, vout, {eid}};
        } else {
            // Nonregular subregex in group -- take the fragment
            fragment = std::get<GraphFragment>(subregex);
        }

        // Mark all the outgoing edges from the v_in of the fragment as group starts
        for (const EdgeID eid : graph.vertices[fragment.v_in].outgoing_edges) {
            graph.group_starts[eid].push_back(m_gid);
        }

        // Mark all the incoming edges to the fragments' v_out as group ends
        for (const EdgeID eid : fragment.edges_pointing_to_vout) {
            graph.group_ends[eid].push_back(m_gid);
        }

        return fragment;
    }

    void ASTNodeGroup::strip_captures() {
        if (m_type == GroupType::CAPTURE) {
            m_type = GroupType::NONCAPTURE;
        }
        m_child->strip_captures();
    }

    void ASTNodeGroup::collect_backrefs(std::unordered_set<GroupID>& refs) const {
        m_child->collect_backrefs(refs);
    }

    void ASTNodeGroup::strip_unreferenced_captures(const std::unordered_set<GroupID>& referenced) {
        if (m_type == GroupType::CAPTURE && !referenced.contains(m_gid)) {
            m_type = GroupType::NONCAPTURE;
        }
        m_child->strip_unreferenced_captures(referenced);
    }

    ASTNodeRef ASTNodeGroup::clone() const {
        auto cloned = std::make_unique<ASTNodeGroup>();
        cloned->m_type = m_type;
        cloned->m_gid = m_gid;
        cloned->m_child = m_child->clone();
        return cloned;
    }

    uint64_t ASTNodeCharClass::print_dot(std::ostream& out, uint64_t& node_count) const {
        const uint64_t id = ++node_count;
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
                // Single character -- make str.to_re(char)
                app* unit_str = util_s.str.mk_string(elem.lower);
                class_elements.push_back(util_s.re.mk_to_re(unit_str));
            } else if (elem.kind == ElementType::RANGE) {
                // Same character -- just make a single string
                if (elem.lower == elem.upper) {
                    app* unit_str = util_s.str.mk_string(elem.lower);
                    class_elements.push_back(util_s.re.mk_to_re(unit_str));
                    continue;
                }
                // Range of characters -- make re.range(char1, char2)
                app* lower = util_s.str.mk_string(elem.lower);
                app* upper = util_s.str.mk_string(elem.upper);
                class_elements.push_back(util_s.re.mk_range(lower, upper));
            } else {
                // Character class
                switch (elem.lower) {
                    case 'd':
                    case 'D': {
                        // Digit character class -- re.range(0, 9)
                        app* lower = util_s.str.mk_string("0");
                        app* upper = util_s.str.mk_string("9");
                        app* re_digit = util_s.re.mk_range(lower, upper);
                        // Nondigit character class -- Sigma* - re.range(0, 9)
                        if (elem.lower == 'D') {
                            re_digit =
                                util_s.re.mk_inter(util_s.re.mk_full_char(nullptr), util_s.re.mk_complement(re_digit));
                        }
                        class_elements.push_back(re_digit);
                        break;
                    }
                    case 's':
                    case 'S': {
                        constexpr std::array<Z3Char, 11> whitespaces {CH_HT, CH_VT, CH_FF, CH_SP, CH_NBSP, CH_ZWNBSP,
                                                                      CH_US, CH_LF, CH_CR, CH_LS, CH_PS};
                        // Unite all the whitespaces
                        app* re_whitespace = util_s.re.mk_to_re(util_s.str.mk_string(whitespaces[0]));
                        for (std::size_t i = 1; i < whitespaces.size(); i++) {
                            app* whitespace_str = util_s.re.mk_to_re(util_s.str.mk_string(whitespaces[i]));
                            re_whitespace = util_s.re.mk_union(re_whitespace, whitespace_str);
                        }
                        // Non-whitespace class -- Sigma* - \s
                        if (elem.lower == 'S') {
                            re_whitespace = util_s.re.mk_inter(util_s.re.mk_full_char(nullptr),
                                                               util_s.re.mk_complement(re_whitespace));
                        }
                        class_elements.push_back(re_whitespace);
                        break;
                    }
                    case 'w':
                    case 'W': {
                        // Word/nonword character classes
                        app* re_word = util_s.re.mk_word_char();
                        // Sigma* - \w
                        if (elem.lower == 'W') {
                            re_word =
                                util_s.re.mk_inter(util_s.re.mk_full_char(nullptr), util_s.re.mk_complement(re_word));
                        }
                        class_elements.push_back(re_word);
                        break;
                    }
                }
            }
        }

        app_ref current_class_re(class_elements.get(0), m);
        for (std::size_t i = 1; i < class_elements.size(); ++i) {
            // Unite all the class elements we got in previous steps
            current_class_re = util_s.re.mk_union(current_class_re, class_elements.get(i));
        }
        if (m_is_negated) {
            // Negated character class -- Sigma* - class_re
            current_class_re =
                util_s.re.mk_inter(util_s.re.mk_full_char(nullptr), util_s.re.mk_complement(current_class_re));
        }

        return current_class_re;
    }

    ASTNodeRef ASTNodeCharClass::clone() const {
        return std::make_unique<ASTNodeCharClass>(*this);
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
                uint64_t node_count = 0;
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
        return {};
    }

    ASTNodeRef ECMAParser::parse_disjunction() {
        ASTNodeRef alt = parse_alternative();

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
                return {};
        }
    }

    ASTNodeRef ECMAParser::parse_maybe_quantifier(ASTNodeRef term) {
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
                SASSERT(std::holds_alternative<Z3Char>(t.payload) && "ASSERTION has no specifier");
                node->set_payload(std::get<Z3Char>(t.payload));
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
                return {};
        }
    }

    ASTNodeRef ECMAParser::parse_atom() {
        const Token t = m_current_token;
        switch (m_current_token.type) {
            case TokenType::LITERAL: {
                auto literal = std::make_unique<ASTNodeLiteral>();
                SASSERT(std::holds_alternative<Z3Char>(t.payload) && "LITERAL has no literal value");
                literal->set_char(std::get<Z3Char>(t.payload));
                next();
                return literal;
            }
            case TokenType::DOT:
                next();
                return std::make_unique<ASTNodeDot>();
            case TokenType::BACKREFERENCE: {
                auto backref = std::make_unique<ASTNodeBackref>();
                SASSERT(std::holds_alternative<Z3Char>(t.payload) && "BACKREFERENCE payload must be Z3Char");
                backref->set_ref(std::get<Z3Char>(t.payload));
                next();
                return backref;
            }
            case TokenType::CHAR_CLASS_ESCAPE: {
                auto char_class = std::make_unique<ASTNodeCharClass>();
                SASSERT(std::holds_alternative<Z3Char>(t.payload) && "CHAR_CLASS_ESCAPE has no class specifier");
                const CharClassElement elem {.kind = ElementType::ESCAPE, .lower = std::get<Z3Char>(t.payload)};
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
                return {};
        }
    }

    ASTNodeRef ECMAParser::parse_group() {
        const Token t = m_current_token;
        auto group = std::make_unique<ASTNodeGroup>();

        switch (m_current_token.type) {
            case TokenType::GROUP_START:
                group->set_type(GroupType::CAPTURE);
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
        if (m_current_token.type == TokenType::LITERAL || m_current_token.type == TokenType::CHAR_CLASS_ESCAPE ||
            m_current_token.type == TokenType::CHAR_CLASS_RANGE) {
            const CharClassAtom first_atom = parse_class_atom();
            parse_class_ranges_tail(char_class_parent, first_atom);
        }
    }

    void ECMAParser::parse_class_ranges_tail(const ASTNodeCharClassRef& char_class_parent,
                                             const CharClassAtom prev_atom) {
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
        switch (m_current_token.type) {
            case TokenType::CHAR_CLASS_ESCAPE: {
                util::throw_error("ECMA Regex error: Character class as a bound of range");
                break;
            }
            case TokenType::CHAR_CLASS_RANGE:
                char_class->add_element({.kind = ElementType::RANGE, .lower = atom_before_dash.val, .upper = '-'});
                next();
                break;
            case TokenType::LITERAL: {
                if (atom_before_dash.is_escape) {
                    util::throw_error("ECMA Regex Error: Character class as a bound of range");
                }
                SASSERT(std::holds_alternative<Z3Char>(m_current_token.payload) && "LITERAL has no literal value");
                const Z3Char from = atom_before_dash.val;
                const Z3Char to = std::get<Z3Char>(m_current_token.payload);
                char_class->add_element({.kind = ElementType::RANGE, .lower = from, .upper = to});
                next();
                break;
            }
            default:  // epsilon
                add_atom_to_class(char_class, atom_before_dash);
                char_class->add_element({ElementType::SINGLE, static_cast<Z3Char>('-'), 0});
                break;
        }
    }

    CharClassAtom ECMAParser::parse_class_atom() {
        switch (m_current_token.type) {
            case TokenType::LITERAL:
            case TokenType::CHAR_CLASS_ESCAPE:
                return parse_class_atom_no_dash();
            case TokenType::CHAR_CLASS_RANGE:
                next();
                return {false, static_cast<Z3Char>('-')};
            default:
                util::throw_error("Syntax error in ECMA regex: Expected class atom");
                return {};
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
            default:
                util::throw_error("Syntax error in ECMA regex: Expected literal or escape sequence");
                return {};
        }
    }

    // ============= DFS CONTEXT =============

    void DFSContext::set_target(app* target) {
        m_target_string = target;
    }

    app* DFSContext::get_target() const {
        return m_target_string;
    }

    void DFSContext::set_end_vertex(VertexID v) {
        m_end_vertex = v;
    }

    VertexID DFSContext::get_end_vertex() const {
        return m_end_vertex;
    }

    void DFSContext::set_base_prefix(const expr_ref& p) {
        m_base_prefix = p;
    }

    expr_ref DFSContext::get_base_prefix() const {
        return m_base_prefix;
    }

    bool DFSContext::has_group(GroupID gid) const {
        return m_group_vars.contains(gid);
    }

    const std::vector<ActiveLookahead>& DFSContext::get_active_lookaheads() const {
        return m_active_lookaheads;
    }

    expr_ref_vector& DFSContext::get_unique_paths() {
        return m_unique_paths;
    }

    app_ref DFSContext::mk_fresh_string_var() const {
        return {m_manager.mk_fresh_const("ecma_re", m_str_sort), m_manager};
    }

    app_ref DFSContext::create_edge_var() {
        app_ref edge_var = mk_fresh_string_var();
        m_current_path_vars.push_back(edge_var);
        return edge_var;
    }

    void DFSContext::push_edge_var_to_groups(const app_ref& edge_var) {
        for (GroupID gid : m_active_groups) {
            m_group_vars.at(gid).push_back(edge_var);
        }
    }

    void DFSContext::add_path_constraint(const app_ref& constraint) {
        m_current_path_constraints.push_back(constraint);
    }

    void DFSContext::start_groups(const std::vector<GroupID>& gids) {
        for (GroupID gid : gids) {
            m_active_groups.push_back(gid);
            if (m_group_vars.contains(gid)) {
                m_group_vars.at(gid).reset();
            } else {
                m_group_vars.insert({gid, expr_ref_vector(m_manager)});
            }
        }
    }

    void DFSContext::end_groups(const std::vector<GroupID>& gids) {
        for (GroupID gid : gids) {
            auto it = std::ranges::find(m_active_groups, gid);
            if (it != m_active_groups.end()) {
                m_active_groups.erase(it);
            }
        }
    }

    void DFSContext::push_lookahead(const std::variant<app_ref, GraphFragment>& subregex, bool is_positive) {
        m_active_lookaheads.push_back({subregex, is_positive, m_current_path_vars.size() - 1});
    }

    void DFSContext::commit_current_path(const expr_ref_vector& additional_constraints) {
        expr_ref_vector final_constraints(m_manager);

        for (expr* c : m_current_path_constraints) {
            final_constraints.push_back(c);
        }
        for (expr* c : additional_constraints) {
            final_constraints.push_back(c);
        }

        expr_ref path_string = concat_vars();
        final_constraints.push_back(m_manager.mk_eq(m_target_string, path_string));
        expr_ref_vector conjunction(m_manager);
        for (expr* c : final_constraints) {
            conjunction.push_back(c);
        }
        m_unique_paths.push_back(m_manager.mk_and(conjunction));
    }

    expr_ref DFSContext::concat_expr_vector(const expr_ref_vector& vars, const uint32_t start_idx,
                                            const uint32_t end_idx) const {
        const uint32_t actual_end = std::min(end_idx, vars.size());
        expr* empty_str = m_util_s.str.mk_empty(m_str_sort);

        if (start_idx >= actual_end) {
            return {empty_str, m_manager};
        }

        expr_ref_vector apps_to_concat {m_manager};
        for (uint32_t i = start_idx; i < actual_end; i++) {
            if (vars.get(i) != empty_str) {
                apps_to_concat.push_back(vars.get(i));
            }
        }

        if (apps_to_concat.empty()) {
            return {empty_str, m_manager};
        }
        if (apps_to_concat.size() == 1) {
            return {apps_to_concat.get(0), m_manager};
        }

        expr* concat = m_util_s.str.mk_concat(apps_to_concat, m_str_sort);
        return {concat, m_manager};
    }

    expr_ref DFSContext::concat_vars(const uint32_t start_idx, const uint32_t end_idx) const {
        return concat_expr_vector(m_current_path_vars, start_idx, end_idx);
    }

    expr_ref DFSContext::concat_group_vars(GroupID gid) const {
        const auto& vars = m_group_vars.at(gid);
        return concat_expr_vector(vars, 0, vars.size());
    }

    expr_ref DFSContext::get_global_prefix() const {
        expr_ref local_prefix = concat_vars();
        expr* empty_str = m_util_s.str.mk_empty(m_str_sort);

        if (m_base_prefix.get() == empty_str) {
            return local_prefix;
        }
        if (local_prefix.get() == empty_str) {
            return m_base_prefix;
        }

        return expr_ref(m_util_s.str.mk_concat(m_base_prefix, local_prefix), m_manager);
    }

    DFSStateSnapshot DFSContext::save_snapshot() const {
        DFSStateSnapshot s;
        s.num_path_vars = m_current_path_vars.size();
        s.num_path_constraints = m_current_path_constraints.size();
        s.num_active_lookaheads = m_active_lookaheads.size();
        s.active_groups = m_active_groups;

        // Deep copy the group variables to the snapshot
        for (const auto& [group_id, vars] : m_group_vars) {
            auto copy = std::make_unique<expr_ref_vector>(m_manager);
            for (unsigned i = 0; i < vars.size(); i++) {
                copy->push_back(vars[i]);
            }
            s.group_vars.insert({group_id, std::move(copy)});
        }
        return s;
    }

    void DFSContext::restore_snapshot(const DFSStateSnapshot& s) {
        m_current_path_vars.resize(s.num_path_vars);
        m_current_path_constraints.resize(s.num_path_constraints);

        // Safely truncating active lookaheads using pop_back avoids the need for a default constructor
        // which std::variant<app_ref, GraphFragment> natively prevents from existing.
        while (m_active_lookaheads.size() > s.num_active_lookaheads) {
            m_active_lookaheads.pop_back();
        }

        m_active_groups = s.active_groups;

        // Clear existing expr_ref_vectors to remove items appended in the discarded path branch.
        // It's perfectly safe to do so because the expressions themselves are preserved
        // by the deep copies stored in the Snapshot object up until this point.
        m_group_vars.clear();
        for (const auto& kv : s.group_vars) {
            GroupID gid = kv.first;
            const auto& vec_ptr = kv.second;
            expr_ref_vector vec(m_manager);
            for (unsigned i = 0; i < vec_ptr->size(); ++i) {
                vec.push_back(vec_ptr->get(i));
            }
            m_group_vars.insert({gid, std::move(vec)});
        }
    }

    OuterSearchState DFSContext::suspend_for_inner_search() {
        OuterSearchState state;
        state.unique_paths = std::make_unique<expr_ref_vector>(m_manager);
        state.current_path_vars = std::make_unique<expr_ref_vector>(m_manager);
        state.current_path_constraints = std::make_unique<expr_ref_vector>(m_manager);
        state.active_groups = std::move(m_active_groups);
        state.active_lookaheads = std::move(m_active_lookaheads);
        state.end_vertex = m_end_vertex;
        state.target_string = m_target_string;

        // Safe shallow copies via Z3 ref vectors
        for (unsigned i = 0; i < m_unique_paths.size(); ++i) {
            state.unique_paths->push_back(m_unique_paths.get(i));
        }
        for (unsigned i = 0; i < m_current_path_vars.size(); ++i) {
            state.current_path_vars->push_back(m_current_path_vars.get(i));
        }
        for (unsigned i = 0; i < m_current_path_constraints.size(); ++i) {
            state.current_path_constraints->push_back(m_current_path_constraints.get(i));
        }

        for (const auto& kv : m_group_vars) {
            state.existing_group_ids.push_back(kv.first);
        }

        m_unique_paths.reset();
        m_current_path_vars.reset();
        m_current_path_constraints.reset();
        m_active_groups.clear();
        m_active_lookaheads.clear();

        return state;
    }

    void DFSContext::resume_from_inner_search(OuterSearchState& state) {
        for (auto it = m_group_vars.begin(); it != m_group_vars.end();) {
            if (std::ranges::find(state.existing_group_ids, it->first) != state.existing_group_ids.end()) {
                ++it;
            } else {
                it = m_group_vars.erase(it);
            }
        }

        m_unique_paths.reset();
        for (unsigned i = 0; i < state.unique_paths->size(); ++i) {
            m_unique_paths.push_back(state.unique_paths->get(i));
        }
        m_current_path_vars.reset();
        for (unsigned i = 0; i < state.current_path_vars->size(); ++i) {
            m_current_path_vars.push_back(state.current_path_vars->get(i));
        }
        m_current_path_constraints.reset();
        for (unsigned i = 0; i < state.current_path_constraints->size(); ++i) {
            m_current_path_constraints.push_back(state.current_path_constraints->get(i));
        }

        m_active_groups = std::move(state.active_groups);
        m_active_lookaheads = std::move(state.active_lookaheads);
        m_end_vertex = state.end_vertex;
        m_target_string = state.target_string;
    }

    // ============= REGEX CONSTRAINT BUILDER =============

    RegexConstraintGraph RegexConstraintBuilder::build_rcg() {
        const ASTNodeRef root = m_parser.parse();
        // Get the subgraph from AST

        std::unordered_set<GroupID> referenced_groups;
        root->collect_backrefs(referenced_groups);
        root->strip_unreferenced_captures(referenced_groups);

        const RegexComponent comp = root->get_subgraph(m_graph, m_util_s, m_manager);

        VertexID inner_start = UNKNOWN_VERTEX;
        VertexID inner_end = UNKNOWN_VERTEX;

        if (std::holds_alternative<app_ref>(comp)) {
            // If the entire regex is regular, create a match edge and wrap it in two vertices
            inner_start = m_graph.create_vertex();
            inner_end = m_graph.create_vertex();
            const EdgeID eid = m_graph.create_edge(inner_end, RCGEdgePayload {MatchEdge {std::get<app_ref>(comp)}});
            m_graph.vertices[inner_start].outgoing_edges.push_back(eid);
        } else {
            const GraphFragment frag = std::get<GraphFragment>(comp);
            inner_start = frag.v_in;
            inner_end = frag.v_out;
        }

        if (m_params.m_ecma_engine_semantics) {
            // Wrap the entire regex in Sigma* to mimic the regex engine matching semantics --> the solution is any
            // substring
            const app_ref sigma_star(m_util_s.re.mk_full_seq(nullptr), m_manager);

            m_graph.start_vertex = m_graph.create_vertex();
            const EdgeID prefix_eid = m_graph.create_edge(inner_start, RCGEdgePayload {MatchEdge {sigma_star}});
            m_graph.vertices[m_graph.start_vertex].outgoing_edges.push_back(prefix_eid);

            m_graph.end_vertex = m_graph.create_vertex();
            const EdgeID suffix_eid = m_graph.create_edge(m_graph.end_vertex, RCGEdgePayload {MatchEdge {sigma_star}});
            m_graph.vertices[inner_end].outgoing_edges.push_back(suffix_eid);
        } else {
            // No engine matching semantics --> the whole string must match the regex
            m_graph.start_vertex = inner_start;
            m_graph.end_vertex = inner_end;
        }

        return m_graph;
    }

    expr_ref RegexConstraintBuilder::generate_constraints(app* target_string) {
        // Just a little sanity check that the graph is (at least somehow) constructed
        SASSERT(m_graph.start_vertex != UNKNOWN_VERTEX);

        // Store the global target string in the context for access in nested DFS calls when evaluating anchors and
        // lookaheads
        m_global_target_string = target_string;

        // Initialize the base DFS context and start the traversal
        DFSContext ctx {m_manager, m_util_s};
        ctx.set_target(target_string);
        ctx.set_base_prefix(expr_ref(m_util_s.str.mk_empty(m_str_sort), m_manager));
        ctx.set_end_vertex(m_graph.end_vertex);
        rcg_dfs_visit(m_graph.start_vertex, ctx);

        // OR all the paths that were generated along the graph traversal
        expr_ref_vector& unique_paths = ctx.get_unique_paths();
        if (unique_paths.empty()) {
            return {m_manager.mk_false(), m_manager};
        }
        if (unique_paths.size() == 1) {
            SASSERT(is_expr(unique_paths.get(0)));
            return {unique_paths.get(0), m_manager};
        }
        return {m_manager.mk_or(unique_paths), m_manager};
    }

    expr_ref RegexConstraintBuilder::run_inner_rcg_dfs(const GraphFragment& fragment, app* target_string,
                                                       DFSContext& ctx) {
        // Suspend the outer DFS context and save the state before proceeding with the inner DFS run
        auto suspended_state = ctx.suspend_for_inner_search();

        ctx.set_end_vertex(fragment.v_out);
        ctx.set_target(target_string);

        // Run the DFS
        rcg_dfs_visit(fragment.v_in, ctx);

        // Disjunct all the paths from the subgraph and add it to the current path constraints
        expr_ref inner_result(m_manager);
        auto& unique_paths = ctx.get_unique_paths();
        if (unique_paths.empty()) {
            inner_result = {m_manager.mk_false(), m_manager};
        } else if (unique_paths.size() == 1) {
            inner_result = {unique_paths.get(0), m_manager};
        } else {
            inner_result = {m_manager.mk_or(unique_paths), m_manager};
        }

        ctx.resume_from_inner_search(suspended_state);
        return inner_result;
    }

    void RegexConstraintBuilder::handle_lookaround_constraints(DFSContext& ctx, const AssertionEdge& assertion,
                                                               const expr_ref& global_prefix) {
        const auto& lookaround = std::get<Lookaround>(assertion.payload);

        if (lookaround.direction == LookaroundDirection::FORWARD) {
            // Lookaheads are postponed and evaluated at the end of each path in the graph because they depend on the
            // suffix of the matched string starting from current position.
            ctx.push_lookahead(lookaround.subregex, lookaround.is_positive);
        } else {
            // Lookbehinds are evaluated immediately since they depend on the prefix of the matched string up until the
            // current position Lookbehinds with regular subregexes are handled via automata operations
            if (std::holds_alternative<app_ref>(lookaround.subregex)) {
                // Create x = global_prefix (p1p2p3...)
                const app_ref lb_var(ctx.mk_fresh_string_var(), m_manager);
                ctx.add_path_constraint({m_manager.mk_eq(lb_var, global_prefix), m_manager});

                // The global prefix should end with a string that matches the lookbehind subregex, therefore generate
                // global_prefix \in (Sigma* concat lb.subregex)
                const app_ref& lb_regex_base = std::get<app_ref>(lookaround.subregex);
                const app_ref sigma_star = {m_util_s.re.mk_full_seq(nullptr), m_manager};
                app_ref lb_regex = {m_util_s.re.mk_concat(sigma_star, lb_regex_base), m_manager};
                if (!lookaround.is_positive) {
                    // negative regular lookbehind --> just complement the final lokbehind subregex
                    lb_regex = m_util_s.re.mk_complement(lb_regex);
                }
                const app_ref condition = {m_util_s.re.mk_in_re(lb_var, lb_regex), m_manager};
                ctx.add_path_constraint(condition);
            } else {
                // Non-regular lookbehind --> need to run a nested DFS to evaluate the inner graph fragment and generate
                // the corresponding constraints.
                if (!lookaround.is_positive) {
                    // Negative lookbehind with non-regular subregex leads to universal quantification
                    util::throw_error("Unsupported: negative lookbehind with non-regular subregex");
                }

                // Introduce a fresh variable x_lb for the subregex in lookbehind
                const GraphFragment& subregex_fragment = std::get<GraphFragment>(lookaround.subregex);
                const app_ref subregex_lb_var(ctx.mk_fresh_string_var(), m_manager);
                ctx.add_path_constraint({m_manager.mk_eq(global_prefix, subregex_lb_var), m_manager});

                // The lookbehind evaluates the subregex against the entire prefix --> the procedure starts from the
                // beginning of matched string, therefore the prefix is "".
                expr_ref old_base = ctx.get_base_prefix();
                ctx.set_base_prefix(expr_ref(m_util_s.str.mk_empty(m_str_sort), m_manager));

                // The subregex lookbehind is evaluated in a separate run of DFS on the subgraph.
                // We hand over x_lb which is the new global target for the inner DFS
                // run. The constraints for x_lb are generated in the same way.
                const expr_ref inner_result = run_inner_rcg_dfs(subregex_fragment, subregex_lb_var, ctx);

                // Restore the original base prefix for the outer DFS run and add the generated constraints for the
                // lookbehind.
                ctx.set_base_prefix(old_base);
                ctx.add_path_constraint({to_app(inner_result.get()), m_manager});
            }
        }
    }

    void RegexConstraintBuilder::generate_lookahead_constraints(DFSContext& ctx, expr_ref_vector& final_constraints) {
        for (const ActiveLookahead& la : ctx.get_active_lookaheads()) {
            expr_ref suffix = ctx.concat_vars(la.start_index);

            if (std::holds_alternative<app_ref>(la.subregex)) {
                app_ref la_var(ctx.mk_fresh_string_var(), m_manager);
                final_constraints.push_back(m_manager.mk_eq(la_var, suffix));
                const app_ref& la_regex_base = std::get<app_ref>(la.subregex);
                const app_ref sigma_star = {m_util_s.re.mk_full_seq(nullptr), m_manager};
                app_ref la_regex = {m_util_s.re.mk_concat(la_regex_base, sigma_star), m_manager};
                if (!la.is_positive) {
                    la_regex = m_util_s.re.mk_complement(la_regex);
                }
                const app_ref condition = {m_util_s.re.mk_in_re(la_var, la_regex), m_manager};
                final_constraints.push_back(condition);
            } else {
                SASSERT(std::holds_alternative<GraphFragment>(la.subregex));
                if (!la.is_positive) {
                    util::throw_error("Unsupported: negative lookaround with non-regular inner content "
                                      "(would require universal quantifiers)");
                }

                const GraphFragment& inner_frag = std::get<GraphFragment>(la.subregex);
                app_ref subregex_la_var(ctx.mk_fresh_string_var(), m_manager);
                final_constraints.push_back(m_manager.mk_eq(suffix, subregex_la_var));

                // The nested graph must inherently know its specific global position relative to the target string
                expr_ref old_base = ctx.get_base_prefix();
                expr_ref local_prefix_to_la = ctx.concat_vars(0, la.start_index);
                ctx.set_base_prefix(expr_ref(m_util_s.str.mk_concat(old_base, local_prefix_to_la), m_manager));

                expr_ref inner_result = run_inner_rcg_dfs(inner_frag, subregex_la_var, ctx);

                ctx.set_base_prefix(old_base);
                final_constraints.push_back(inner_result);
            }
        }
    }

    void RegexConstraintBuilder::generate_edge_constraints(DFSContext& ctx, const RCGEdge& edge,
                                                           const app_ref& edge_var) {
        // Get all the string variables preceding the currently processed edge.
        // This is important for lookaround and anchor evaluation, since they are dependent on the absolute position in
        // the text.
        expr_ref global_prefix = ctx.get_global_prefix();

        // The edge contains regular payload --> generate str.in_re(edge_var, payload)
        if (std::holds_alternative<MatchEdge>(edge.payload)) {
            const app_ref regex = std::get<MatchEdge>(edge.payload).regex;
            ctx.add_path_constraint({m_util_s.re.mk_in_re(edge_var, regex), m_manager});
        }
        // Assertion (or zero-width assertion) --> no text is consumed, therefore edge_var = ""
        else if (std::holds_alternative<AssertionEdge>(edge.payload)) {
            const AssertionEdge& assertion = std::get<AssertionEdge>(edge.payload);
            ctx.add_path_constraint({m_manager.mk_eq(edge_var, m_util_s.str.mk_empty(m_str_sort)), m_manager});
            if (std::holds_alternative<Anchor>(assertion.payload)) {
                const Z3Char anchor = std::get<Anchor>(assertion.payload);
                // '^' anchor means 'nothing is matched before this position' --> global prefix must be empty
                if (anchor == '^') {
                    ctx.add_path_constraint(
                        {m_manager.mk_eq(global_prefix, m_util_s.str.mk_empty(m_str_sort)), m_manager});
                }
                // '$' anchor means 'nothing is matched after this position' --> global prefix must be equal to the
                // entire target string
                else if (anchor == '$') {
                    ctx.add_path_constraint(
                        {m_manager.mk_eq(global_prefix, app_ref(m_global_target_string, m_manager)), m_manager});
                } else {
                    util::throw_error("Internal error: RegexConstraintBuilder::generate_edge_constraints: anchor != "
                                      "'$' && anchor != '^'");
                }
            } else if (std::holds_alternative<Lookaround>(assertion.payload)) {
                handle_lookaround_constraints(ctx, assertion, global_prefix);
            } else {
                util::throw_error("Internal error: RegexConstraintBuilder::generate_edge_constraints: Assertion is "
                                  "neither Anchor nor Lookaround");
            }
        }
        // Backreference --> edge_var must be equal to the concatenation of all variables in the referenced group on the
        // current path. If the referenced group is not active, it is a forward reference -- matches empty string.
        // https://tc39.es/ecma262/2020/#sec-backreferencematcher -- "e. If `s` is undefined, return c(x)."
        else if (std::holds_alternative<BackrefEdge>(edge.payload)) {
            const GroupID ref_id = std::get<BackrefEdge>(edge.payload).backref_id;
            if (ctx.has_group(ref_id)) {
                // Backreference -- concatenate all the variables accumulated in the capture group during the current
                // path.
                expr_ref captured_string = ctx.concat_group_vars(ref_id);
                ctx.add_path_constraint({m_manager.mk_eq(edge_var, captured_string), m_manager});
            } else {
                // Forward reference
                ctx.add_path_constraint({m_manager.mk_eq(edge_var, m_util_s.str.mk_empty(m_str_sort)), m_manager});
            }
        } else {
            util::throw_error("Internal error: RegexConstraintBuilder::generate_edge_constraints: edge payload is "
                              "neither BackrefEdge, AssertionEdge nor MatchEdge");
        }
    }

    void RegexConstraintBuilder::rcg_dfs_visit(const VertexID current_vertex, DFSContext& ctx) {
        // End of (sub)graph reached --> evaluate postponed lookaheads and commit current path
        if (current_vertex == ctx.get_end_vertex()) {
            expr_ref_vector final_constraints(m_manager);
            generate_lookahead_constraints(ctx, final_constraints);
            ctx.commit_current_path(final_constraints);
            return;
        }

        for (EdgeID eid : m_graph.vertices[current_vertex].outgoing_edges) {
            // Before continuing, save a snapshot of the previous edge in case of alternation
            const RCGEdge& edge = m_graph.edges[eid];
            DFSStateSnapshot snapshot = ctx.save_snapshot();

            // Mark all groups that begin on this edge as active
            if (m_graph.group_starts.contains(eid)) {
                ctx.start_groups(m_graph.group_starts.at(eid));
            }

            // Create a fresh variable (and add it to all the active capture groups) and generate constraints for the
            // current edge
            app_ref edge_var = ctx.create_edge_var();
            ctx.push_edge_var_to_groups(edge_var);
            generate_edge_constraints(ctx, edge, edge_var);

            // Mark all groups that end on this edge as inactive
            if (m_graph.group_ends.contains(eid)) {
                ctx.end_groups(m_graph.group_ends.at(eid));
            }

            // Continue DFS on the next edge, rollback to the snapshot after exploring the branch
            rcg_dfs_visit(edge.target, ctx);
            ctx.restore_snapshot(snapshot);
        }
    }

    bool GraphFragment::is_initialized() const {
        return v_in == std::numeric_limits<VertexID>::max() && v_out == std::numeric_limits<VertexID>::max();
    }
}  // namespace smt::noodler::ecma