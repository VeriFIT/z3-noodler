#include "re2_regex.h"

#include "smt/theory_str_noodler/util.h"

#include "util/debug.h"
#include "util/zstring.h"

#include <algorithm>
#include <optional>
#include <string>

namespace smt::noodler::extended_regex::re2 {
    // ======================= UTILS =======================

    // RE2 rejects counted repetitions with a larger count, also if it is the product of the counts of nested ones
    constexpr uint64_t MAX_REPEAT_COUNT = 1000;
    // Larger numbers in counted repetitions are not read as numbers by RE2, so '{' is then a literal
    constexpr uint64_t MAX_REPEAT_NUMBER = 100'000'000;
    constexpr Z3Char MAX_UNICODE_CODE_POINT = 0x10FFFF;

    // ================= RE2 REGEX LEXER ===================

    bool RE2Lexer::is_digit(const Z3Char ch) {
        return ch >= '0' && ch <= '9';
    }

    bool RE2Lexer::is_octal_digit(const Z3Char ch) {
        return ch >= '0' && ch <= '7';
    }

    bool RE2Lexer::is_alnum(const Z3Char ch) {
        return is_digit(ch) || (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z');
    }

    int RE2Lexer::hex_value(const Z3Char ch) {
        if (is_digit(ch)) {
            return static_cast<int>(ch - '0');
        }
        if (ch >= 'a' && ch <= 'f') {
            return static_cast<int>(ch - 'a' + 10);
        }
        if (ch >= 'A' && ch <= 'F') {
            return static_cast<int>(ch - 'A' + 10);
        }
        return -1;
    }

    Token RE2Lexer::get_next_token() {
        m_lexeme_start_pos = m_position;
        if (m_in_quote) {
            return get_quoted_token();
        }
        if (m_position >= m_regex.length()) {
            return make_token(TokenType::END_OF_INPUT);
        }
        return m_in_char_class ? get_token_char_class() : get_token_standard();
    }

    Token RE2Lexer::make_token(const TokenType type, const TokenPayload& payload) const {
        return {type, payload, zstring_view(m_regex.data() + m_lexeme_start_pos, m_position - m_lexeme_start_pos)};
    }

    void RE2Lexer::throw_syntax_error(const std::string& message) const {
        const zstring_view lexeme(m_regex.data() + m_lexeme_start_pos, m_position - m_lexeme_start_pos);
        util::throw_error("RE2 regex syntax error: " + message + ": " + lexeme.to_zstring().encode());
    }

    Token RE2Lexer::get_token_standard() {
        const Z3Char ch = m_regex[m_position];
        m_position++;
        switch (ch) {
        case '|': return make_token(TokenType::ALTERNATION);
        case '(': return get_group_token();
        case ')': return make_token(TokenType::GROUP_END);
        case '^':
        case '$': return make_token(TokenType::ASSERTION, ch);
        case '.': return make_token(TokenType::DOT);
        case '[':
            m_in_char_class = true;
            m_class_position = ClassPosition::START;
            return make_token(TokenType::CHAR_CLASS_START);
        case '*':
        case '+':
        case '?': return get_quantifier_token(ch);
        case '{': return get_braced_quantifier_token();
        case '\\': return get_escape_sequence_token();
        default: return make_token(TokenType::LITERAL, ch);
        }
    }

    Token RE2Lexer::get_quantifier_token(const Z3Char op) {
        QuantifierRange range {0, UNBOUNDED};
        if (op == '+') {
            range.min = 1;
        }
        else if (op == '?') {
            range.max = 1;
        }
        // A lazy quantifier matches the same strings as the greedy one
        if (m_position < m_regex.length() && m_regex[m_position] == '?') {
            m_position++;
        }
        return make_token(TokenType::QUANTIFIER, range);
    }

    bool RE2Lexer::parse_integer(std::size_t& pos, uint64_t& value) const {
        if (pos >= m_regex.length() || !is_digit(m_regex[pos])) {
            return false;
        }
        // Leading zeros are not allowed
        if (pos + 1 < m_regex.length() && m_regex[pos] == '0' && is_digit(m_regex[pos + 1])) {
            return false;
        }
        value = 0;
        while (pos < m_regex.length() && is_digit(m_regex[pos])) {
            if (value >= MAX_REPEAT_NUMBER) {
                return false;
            }
            value = value * 10 + (m_regex[pos] - '0');
            pos++;
        }
        return true;
    }

    Token RE2Lexer::get_braced_quantifier_token() {
        // {n}, {n,} or {n,m}, a '{' that does not start one of them is a literal
        std::size_t pos = m_position;
        uint64_t min = 0;
        uint64_t max = 0;
        if (!parse_integer(pos, min) || pos >= m_regex.length()) {
            return make_token(TokenType::LITERAL, static_cast<Z3Char>('{'));
        }
        if (m_regex[pos] == ',') {
            pos++;
            if (pos >= m_regex.length()) {
                return make_token(TokenType::LITERAL, static_cast<Z3Char>('{'));
            }
            if (m_regex[pos] == '}') {
                max = UNBOUNDED;
            }
            else if (!parse_integer(pos, max)) {
                return make_token(TokenType::LITERAL, static_cast<Z3Char>('{'));
            }
        }
        else {
            max = min;
        }
        if (pos >= m_regex.length() || m_regex[pos] != '}') {
            return make_token(TokenType::LITERAL, static_cast<Z3Char>('{'));
        }
        m_position = pos + 1;
        // A lazy quantifier matches the same strings as the greedy one
        if (m_position < m_regex.length() && m_regex[m_position] == '?') {
            m_position++;
        }
        return make_token(TokenType::QUANTIFIER, QuantifierRange {min, max});
    }

    Token RE2Lexer::get_group_token() {
        if (m_position >= m_regex.length() || m_regex[m_position] != '?') {
            return make_token(TokenType::GROUP_START);
        }
        m_position++;  // '?'

        // The number of characters after "(?"
        const std::size_t rest = m_regex.length() - m_position;
        // Lookarounds are not supported by RE2
        if ((rest > 1 && (m_regex[m_position] == '=' || m_regex[m_position] == '!')) ||
            (rest > 2 && m_regex[m_position] == '<' &&
             (m_regex[m_position + 1] == '=' || m_regex[m_position + 1] == '!'))) {
            m_position += (m_regex[m_position] == '<') ? 2 : 1;
            throw_syntax_error("invalid perl operator");
            return {};
        }
        // Named capture groups (?P<name>re) and (?<name>re)
        if (rest > 2 && m_regex[m_position] == 'P' && m_regex[m_position + 1] == '<') {
            return get_named_group_token(m_position + 2);
        }
        if (rest > 1 && m_regex[m_position] == '<') {
            return get_named_group_token(m_position + 1);
        }
        return get_flags_token();
    }

    Token RE2Lexer::get_named_group_token(const std::size_t name_start) {
        std::size_t name_end = name_start;
        while (name_end < m_regex.length() && m_regex[name_end] != '>') {
            name_end++;
        }
        if (name_end >= m_regex.length()) {
            m_position = m_regex.length();
            throw_syntax_error("invalid named capture group");
            return {};
        }

        m_position = name_end + 1;
        const zstring_view name(m_regex.data() + name_start, name_end - name_start);
        if (name.length() == 0) {
            throw_syntax_error("invalid named capture group");
        }
        for (std::size_t i = 0; i < name.length(); i++) {
            // RE2 accepts also Unicode letters, marks, digits and connector punctuation in the names
            if (name[i] >= 0x80) {
                util::throw_error("Unsupported: non-ASCII name of an RE2 capture group " + name.to_zstring().encode());
            }
            if (!is_alnum(name[i]) && name[i] != '_') {
                throw_syntax_error("invalid named capture group");
            }
        }
        return make_token(TokenType::GROUP_NAMED_START, name);
    }

    Token RE2Lexer::get_flags_token() {
        // (?flags) or (?flags:re), the flags before '-' are set, the flags after it are cleared, e.g., (?i-s)
        FlagChanges changes;
        bool is_negated = false;
        bool saw_flag = false;
        while (m_position < m_regex.length()) {
            const Z3Char ch = m_regex[m_position];
            m_position++;
            uint8_t flag = 0;
            switch (ch) {
            case 'i': flag = CASE_INSENSITIVE; break;
            case 'm': flag = MULTI_LINE; break;
            case 's': flag = DOT_NL; break;
            case 'U': flag = UNGREEDY; break;
            case '-':
                if (is_negated) {
                    throw_syntax_error("invalid perl operator");
                }
                is_negated = true;
                // Negating nothing is an error: (?-) and (?-:re)
                saw_flag = false;
                continue;
            case ':':
            case ')':
                if (is_negated && !saw_flag) {
                    throw_syntax_error("invalid perl operator");
                }
                return make_token(ch == ':' ? TokenType::GROUP_NONCAPTURE_START : TokenType::FLAGS, changes);
            default: throw_syntax_error("invalid perl operator"); return {};
            }
            saw_flag = true;
            if (is_negated) {
                changes.set &= ~flag;
                changes.cleared |= flag;
            }
            else {
                changes.set |= flag;
                changes.cleared &= ~flag;
            }
        }
        throw_syntax_error("invalid perl operator");
        return {};
    }

    Token RE2Lexer::get_escape_sequence_token() {
        if (m_position >= m_regex.length()) {
            throw_syntax_error("trailing \\");
            return {};
        }
        const Z3Char ch = m_regex[m_position];
        m_position++;
        switch (ch) {
        case 'b':
        case 'B':
        case 'A':
        case 'z': return make_token(TokenType::ASSERTION, ch);
        case 'd':
        case 'D':
        case 's':
        case 'S':
        case 'w':
        case 'W': return make_token(TokenType::CHAR_CLASS_ESCAPE, ch);
        case 'Q':
            // \Q...\E: the text up to \E (or to the end of the regex) is literal
            m_in_quote = true;
            return get_next_token();
        case 'C': util::throw_error("Unsupported: \\C (any byte) in RE2 regex"); return {};
        case 'p':
        case 'P': util::throw_error("Unsupported: Unicode character classes (\\p, \\P) in RE2 regex"); return {};
        default: return make_token(TokenType::LITERAL, parse_escaped_char(ch));
        }
    }

    Token RE2Lexer::get_quoted_token() {
        if (m_position + 1 < m_regex.length() && m_regex[m_position] == '\\' && m_regex[m_position + 1] == 'E') {
            m_position += 2;
            m_in_quote = false;
            return get_next_token();
        }
        if (m_position >= m_regex.length()) {
            m_in_quote = false;
            return make_token(TokenType::END_OF_INPUT);
        }
        const Z3Char ch = m_regex[m_position];
        m_position++;
        return make_token(TokenType::LITERAL, ch);
    }

    Z3Char RE2Lexer::parse_escaped_char(const Z3Char escaped) {
        switch (escaped) {
        // Octal escapes, a single non-zero digit is a backreference, which is not supported
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
            if (m_position >= m_regex.length() || !is_octal_digit(m_regex[m_position])) {
                throw_syntax_error("invalid escape sequence");
            }
            [[fallthrough]];
        case '0': {
            // Up to two more octal digits
            Z3Char code = escaped - '0';
            for (int i = 0; i < 2 && m_position < m_regex.length() && is_octal_digit(m_regex[m_position]); i++) {
                code = code * 8 + (m_regex[m_position] - '0');
                m_position++;
            }
            return code;
        }
        case 'x': return parse_hex_escape();
        case 'n': return '\n';
        case 'r': return '\r';
        case 't': return '\t';
        case 'a': return '\a';
        case 'f': return '\f';
        case 'v': return '\v';
        default:
            // Escaped characters other than ASCII letters and digits are themselves (including \_)
            if (escaped < 0x80 && !is_alnum(escaped)) {
                return escaped;
            }
            throw_syntax_error("invalid escape sequence");
            return 0;
        }
    }

    Z3Char RE2Lexer::parse_hex_escape() {
        if (m_position >= m_regex.length()) {
            throw_syntax_error("invalid escape sequence");
        }
        Z3Char ch = m_regex[m_position];
        m_position++;

        // \x{10FFFF}: any number of hexadecimal digits in braces, at least one
        if (ch == '{') {
            uint64_t code = 0;
            unsigned num_digits = 0;
            while (true) {
                if (m_position >= m_regex.length()) {
                    throw_syntax_error("invalid escape sequence");
                }
                ch = m_regex[m_position];
                m_position++;
                if (ch == '}') {
                    break;
                }
                const int value = hex_value(ch);
                if (value < 0) {
                    throw_syntax_error("invalid escape sequence");
                }
                code = code * 16 + value;
                if (code > MAX_UNICODE_CODE_POINT) {
                    throw_syntax_error("invalid escape sequence");
                }
                num_digits++;
            }
            if (num_digits == 0) {
                throw_syntax_error("invalid escape sequence");
            }
            return static_cast<Z3Char>(code);
        }

        // \x7F: exactly two hexadecimal digits
        if (m_position >= m_regex.length()) {
            throw_syntax_error("invalid escape sequence");
        }
        const int high = hex_value(ch);
        const int low = hex_value(m_regex[m_position]);
        m_position++;
        if (high < 0 || low < 0) {
            throw_syntax_error("invalid escape sequence");
        }
        return static_cast<Z3Char>(high * 16 + low);
    }

    Token RE2Lexer::get_token_char_class() {
        const Z3Char ch = m_regex[m_position];
        ClassPosition position = m_class_position;
        if (position == ClassPosition::START) {
            position = ClassPosition::FIRST;
            m_class_position = ClassPosition::FIRST;
            if (ch == '^') {
                m_position++;
                return make_token(TokenType::CHAR_CLASS_NEGATION);
            }
        }

        // ']' closes the class, except as its first element, where it is a literal
        if (ch == ']' && position != ClassPosition::FIRST) {
            m_position++;
            m_in_char_class = false;
            return make_token(TokenType::CHAR_CLASS_END);
        }

        // '-' after a single character makes a range, unless it is followed by ']', then it is a literal
        if (position == ClassPosition::AFTER_LOWER && ch == '-' && m_position + 1 < m_regex.length() &&
            m_regex[m_position + 1] != ']') {
            m_position++;
            m_class_position = ClassPosition::UPPER;
            return make_token(TokenType::CHAR_CLASS_RANGE);
        }

        // "[:name:]" at the start of an element is a POSIX class, if there is no ":]", '[' is a literal
        if (position != ClassPosition::UPPER && ch == '[' && m_position + 1 < m_regex.length() &&
            m_regex[m_position + 1] == ':') {
            for (std::size_t end = m_position + 2; end + 1 < m_regex.length(); end++) {
                if (m_regex[end] == ':' && m_regex[end + 1] == ']') {
                    const zstring_view name(m_regex.data() + m_position + 2, end - m_position - 2);
                    m_position = end + 2;
                    m_class_position = ClassPosition::ELEMENT;
                    return make_token(TokenType::POSIX_CLASS, name);
                }
            }
        }

        Token token {};
        if (ch == '\\') {
            m_position++;
            token = get_char_class_escape_sequence_token();
        }
        else {
            m_position++;
            token = make_token(TokenType::LITERAL, ch);
        }
        // A single character can be the lower bound of a range, unless it is already the upper bound of one
        const bool can_be_lower = token.type == TokenType::LITERAL && position != ClassPosition::UPPER;
        m_class_position = can_be_lower ? ClassPosition::AFTER_LOWER : ClassPosition::ELEMENT;
        return token;
    }

    Token RE2Lexer::get_char_class_escape_sequence_token() {
        if (m_position >= m_regex.length()) {
            throw_syntax_error("trailing \\");
            return {};
        }
        const Z3Char ch = m_regex[m_position];
        m_position++;
        switch (ch) {
        case 'd':
        case 'D':
        case 's':
        case 'S':
        case 'w':
        case 'W': return make_token(TokenType::CHAR_CLASS_ESCAPE, ch);
        case 'p':
        case 'P': util::throw_error("Unsupported: Unicode character classes (\\p, \\P) in RE2 regex"); return {};
        default: return make_token(TokenType::LITERAL, parse_escaped_char(ch));
        }
    }

    // =============== RE2 REGEX PARSER ===============

    CharSet RE2Parser::word_chars() {
        CharSet chars = CharSet::range('0', '9');
        chars.add('A', 'Z');
        chars.add('_');
        chars.add('a', 'z');
        return chars;
    }

    CharSet RE2Parser::space_chars() {
        CharSet chars = CharSet::range('\t', '\n');
        chars.add('\f', '\r');
        chars.add(' ');
        return chars;
    }

    CharSet RE2Parser::perl_class_chars(const Z3Char escape) {
        switch (escape) {
        case 'd': return CharSet::range('0', '9');
        case 'D': return CharSet::range('0', '9').complement();
        case 's': return space_chars();
        case 'S': return space_chars().complement();
        case 'w': return word_chars();
        case 'W': return word_chars().complement();
        default: util::throw_error("RE2 regex syntax error: unknown Perl character class"); return {};
        }
    }

    std::optional<CharSet> RE2Parser::ascii_class_chars(const std::string& name) {
        CharSet chars;
        if (name == "alnum") {
            chars.add('0', '9');
            chars.add('A', 'Z');
            chars.add('a', 'z');
        }
        else if (name == "alpha") {
            chars.add('A', 'Z');
            chars.add('a', 'z');
        }
        else if (name == "ascii") {
            chars.add(0x00, 0x7F);
        }
        else if (name == "blank") {
            chars.add('\t');
            chars.add(' ');
        }
        else if (name == "cntrl") {
            chars.add(0x00, 0x1F);
            chars.add(0x7F);
        }
        else if (name == "digit") {
            chars.add('0', '9');
        }
        else if (name == "graph") {
            chars.add('!', '~');
        }
        else if (name == "lower") {
            chars.add('a', 'z');
        }
        else if (name == "print") {
            chars.add(' ', '~');
        }
        else if (name == "punct") {
            chars.add('!', '/');
            chars.add(':', '@');
            chars.add('[', '`');
            chars.add('{', '~');
        }
        else if (name == "space") {
            chars.add('\t', '\r');
            chars.add(' ');
        }
        else if (name == "upper") {
            chars.add('A', 'Z');
        }
        else if (name == "word") {
            chars = word_chars();
        }
        else if (name == "xdigit") {
            chars.add('0', '9');
            chars.add('A', 'F');
            chars.add('a', 'f');
        }
        else {
            return std::nullopt;
        }
        return chars;
    }

    uint64_t RE2Parser::remaining_repeat_count(const Node& node, uint64_t remaining) {
        if (const auto* repetition = std::get_if<Repetition>(&node.content)) {
            const uint64_t count = (repetition->max == UNBOUNDED) ? repetition->min : repetition->max;
            if (count > 0) {
                remaining /= count;
            }
        }
        uint64_t result = remaining;
        for_each_child(node, [&](const NodeRef& child) {
            result = std::min(result, remaining_repeat_count(*child, remaining));
        });
        return result;
    }

    NodeRef RE2Parser::parse() {
        NodeRef ast = parse_disjunction();
        if (m_current_token.type == TokenType::GROUP_END) {
            throw_syntax_error("unexpected )");
        }
        SASSERT(m_current_token.type == TokenType::END_OF_INPUT);

        // Counted repetitions must not repeat more than MAX_REPEAT_COUNT times, also when they are nested
        if (remaining_repeat_count(*ast, MAX_REPEAT_COUNT) == 0) {
            util::throw_error("RE2 regex syntax error: invalid repetition size (nested repetitions repeat more than " +
                              std::to_string(MAX_REPEAT_COUNT) + " times)");
        }
        return ast;
    }

    void RE2Parser::next() {
        m_current_token = m_lexer.get_next_token();
    }

    bool RE2Parser::match(const TokenType type) {
        if (m_current_token.type == type) {
            next();
            return true;
        }
        return false;
    }

    void RE2Parser::throw_syntax_error(const std::string& message) const {
        util::throw_error("RE2 regex syntax error: " + message + ": " + m_current_token.lexeme.to_zstring().encode());
    }

    void RE2Parser::apply_flags(const FlagChanges changes) {
        if (changes.set & CASE_INSENSITIVE) {
            util::throw_error("Unsupported: case-insensitive RE2 regex (flag i)");
        }
        m_flags = (m_flags | changes.set) & ~changes.cleared;
    }

    NodeRef RE2Parser::parse_disjunction() {
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

    NodeRef RE2Parser::parse_alternative() {
        Concatenation alt;
        while (m_current_token.type != TokenType::ALTERNATION && m_current_token.type != TokenType::GROUP_END &&
               m_current_token.type != TokenType::END_OF_INPUT) {
            // The flags of (?flags) hold until the end of the enclosing group, also in the following alternatives
            if (m_current_token.type == TokenType::FLAGS) {
                apply_flags(std::get<FlagChanges>(m_current_token.payload));
                next();
                continue;
            }
            alt.terms.push_back(parse_term());
        }
        return make_node(std::move(alt));
    }

    NodeRef RE2Parser::parse_term() {
        switch (m_current_token.type) {
        // RE2 allows repeating also the empty-width assertions
        case TokenType::ASSERTION: return parse_maybe_quantifier(parse_assertion());
        case TokenType::LITERAL:
        case TokenType::DOT:
        case TokenType::CHAR_CLASS_ESCAPE:
        case TokenType::CHAR_CLASS_START:
        case TokenType::GROUP_START:
        case TokenType::GROUP_NAMED_START:
        case TokenType::GROUP_NONCAPTURE_START: return parse_maybe_quantifier(parse_atom());
        case TokenType::QUANTIFIER: throw_syntax_error("no argument for repetition operator"); return {};
        default: throw_syntax_error("unexpected token"); return {};
        }
    }

    NodeRef RE2Parser::parse_maybe_quantifier(NodeRef term) {
        if (m_current_token.type != TokenType::QUANTIFIER) {
            return term;
        }
        const QuantifierRange range = std::get<QuantifierRange>(m_current_token.payload);
        if (range.min > MAX_REPEAT_COUNT ||
            (range.max != UNBOUNDED && (range.max > MAX_REPEAT_COUNT || range.max < range.min))) {
            throw_syntax_error("invalid repetition size");
        }
        next();

        // Repetitions cannot be repeated, e.g., a** is invalid
        if (m_current_token.type == TokenType::QUANTIFIER) {
            throw_syntax_error("bad repetition operator");
        }
        return make_node(Repetition {.child = std::move(term), .min = range.min, .max = range.max});
    }

    NodeRef RE2Parser::parse_assertion() {
        SASSERT(std::holds_alternative<Z3Char>(m_current_token.payload) && "ASSERTION has no specifier");
        const Z3Char assertion = std::get<Z3Char>(m_current_token.payload);
        const bool is_multi_line = m_flags & MULTI_LINE;
        next();
        switch (assertion) {
        // Without the flag m, ^ and $ match only at the start and at the end of the text ($ is \z, not \Z), with it,
        // also at the start and at the end of lines
        case '^': return is_multi_line ? make_line_start(CharSet::single('\n')) : make_node(Anchor::START_OF_TEXT);
        case '$': return is_multi_line ? make_line_end(CharSet::single('\n')) : make_node(Anchor::END_OF_TEXT);
        case 'A': return make_node(Anchor::START_OF_TEXT);
        case 'z': return make_node(Anchor::END_OF_TEXT);
        case 'b': return make_word_boundary(word_chars(), false);
        case 'B': return make_word_boundary(word_chars(), true);
        default: util::throw_error("RE2 regex syntax error: unknown assertion"); return {};
        }
    }

    NodeRef RE2Parser::parse_atom() {
        const Token t = m_current_token;
        switch (t.type) {
        case TokenType::LITERAL:
            SASSERT(std::holds_alternative<Z3Char>(t.payload) && "LITERAL has no literal value");
            next();
            return make_node(CharSet::single(std::get<Z3Char>(t.payload)));
        case TokenType::DOT: {
            // Without the flag s, '.' matches any character except \n
            const bool matches_nl = m_flags & DOT_NL;
            next();
            return make_node(matches_nl ? CharSet::all() : CharSet::single('\n').complement());
        }
        case TokenType::CHAR_CLASS_ESCAPE:
            SASSERT(std::holds_alternative<Z3Char>(t.payload) && "CHAR_CLASS_ESCAPE has no class specifier");
            next();
            return make_node(perl_class_chars(std::get<Z3Char>(t.payload)));
        case TokenType::GROUP_START:
        case TokenType::GROUP_NAMED_START:
        case TokenType::GROUP_NONCAPTURE_START: return parse_group();
        case TokenType::CHAR_CLASS_START: return parse_character_class();
        default: throw_syntax_error("unexpected token"); return {};
        }
    }

    NodeRef RE2Parser::parse_group() {
        const TokenType type = m_current_token.type;
        // The flags changed inside the group hold only until its end
        const uint8_t outer_flags = m_flags;
        GroupID gid = 0;
        if (type == TokenType::GROUP_NONCAPTURE_START) {
            apply_flags(std::get<FlagChanges>(m_current_token.payload));
        }
        else {
            gid = ++m_current_group_id;
        }

        next();
        NodeRef subpattern = parse_disjunction();
        if (m_current_token.type != TokenType::GROUP_END) {
            throw_syntax_error("missing )");
        }
        next();
        m_flags = outer_flags;

        // Non-capturing groups have no meaning for the subpattern
        if (type == TokenType::GROUP_NONCAPTURE_START) {
            return subpattern;
        }
        return make_node(Capture {gid, std::move(subpattern)});
    }

    NodeRef RE2Parser::parse_character_class() {
        next();  // '['
        const bool is_negated = match(TokenType::CHAR_CLASS_NEGATION);

        CharSet chars;
        while (m_current_token.type != TokenType::CHAR_CLASS_END) {
            const Token t = m_current_token;
            switch (t.type) {
            case TokenType::END_OF_INPUT: throw_syntax_error("missing ]"); return {};
            case TokenType::CHAR_CLASS_ESCAPE:
                chars.add(perl_class_chars(std::get<Z3Char>(t.payload)));
                next();
                break;
            case TokenType::POSIX_CLASS: {
                // [:^name:] is the negation of [:name:]
                std::string name = std::get<zstring_view>(t.payload).to_zstring().encode();
                const bool is_negated_class = !name.empty() && name[0] == '^';
                const std::optional<CharSet> class_chars = ascii_class_chars(is_negated_class ? name.substr(1) : name);
                if (!class_chars) {
                    throw_syntax_error("invalid character class range");
                }
                chars.add(is_negated_class ? class_chars->complement() : *class_chars);
                next();
                break;
            }
            case TokenType::LITERAL: {
                const Z3Char lower = std::get<Z3Char>(t.payload);
                next();
                if (!match(TokenType::CHAR_CLASS_RANGE)) {
                    chars.add(lower);
                    break;
                }
                if (m_current_token.type != TokenType::LITERAL || std::get<Z3Char>(m_current_token.payload) < lower) {
                    throw_syntax_error("invalid character class range");
                }
                chars.add(lower, std::get<Z3Char>(m_current_token.payload));
                next();
                break;
            }
            default: throw_syntax_error("invalid character class"); return {};
            }
        }
        next();  // ']'

        // Negated classes match also \n in RE2
        return make_node(is_negated ? chars.complement() : std::move(chars));
    }
}  // namespace smt::noodler::extended_regex::re2
