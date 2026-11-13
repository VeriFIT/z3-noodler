#include "pcre2.h"

#include "smt/theory_str_noodler/util.h"

#include "util/debug.h"
#include "util/zstring.h"

#include <algorithm>
#include <array>
#include <optional>
#include <string>
#include <string_view>

namespace smt::noodler::extended_regex::pcre2 {
    // ======================= UTILS =======================

    // The largest number of repetitions in a quantifier
    constexpr uint64_t MAX_REPEAT_COUNT = 65'535;
    // The largest number of a capture group
    constexpr uint64_t MAX_GROUP_NUMBER = 65'535;
    // Numbers in the pattern are read only up to this value, larger ones are too big for every use
    constexpr uint64_t MAX_NUMBER = 100'000'000;
    // The largest length of the name of a capture group
    constexpr std::size_t MAX_NAME_LENGTH = 128;
    constexpr Z3Char MAX_UNICODE_CODE_POINT = 0x10FFFF;
    constexpr Z3Char FIRST_SURROGATE = 0xD800;
    constexpr Z3Char LAST_SURROGATE = 0xDFFF;

    // The start-of-pattern options that do not change which strings match.
    // They are the defaults (UTF, LF, BSR_UNICODE), settings of the matching engine and CASELESS_RESTRICT, which has
    // no effect without caseless matching.
    constexpr std::array<std::string_view, 8> IGNORED_START_OPTIONS = {"UTF)",          "LF)",
                                                                       "BSR_UNICODE)",  "NO_AUTO_POSSESS)",
                                                                       "NO_START_OPT)", "NO_DOTSTAR_ANCHOR)",
                                                                       "NO_JIT)",       "CASELESS_RESTRICT)"};
    // The start-of-pattern options with a number, e.g., (*LIMIT_MATCH=1000), they limit only the resources of matching
    constexpr std::array<std::string_view, 4> IGNORED_START_LIMITS = {
        "LIMIT_HEAP=", "LIMIT_MATCH=", "LIMIT_DEPTH=", "LIMIT_RECURSION="};
    constexpr std::array<std::string_view, 10> UNSUPPORTED_START_OPTIONS = {
        "UCP)", "NOTEMPTY)",    "NOTEMPTY_ATSTART)", "CR)", "CRLF)", "ANYCRLF)", "ANY)",
        "NUL)", "BSR_ANYCRLF)", "TURKISH_CASING)"};
    // The backtracking control verbs, (*:NAME) is (*MARK:NAME)
    constexpr std::array<std::string_view, 9> VERBS = {"",     "ACCEPT", "COMMIT", "F",   "FAIL",
                                                       "MARK", "PRUNE",  "SKIP",   "THEN"};
    // The alphabetic names of lookarounds, atomic groups, script runs and scan substring assertions
    constexpr std::array<std::string_view, 19> ALPHA_ASSERTIONS = {"pla",
                                                                   "plb",
                                                                   "nla",
                                                                   "nlb",
                                                                   "positive_lookahead",
                                                                   "positive_lookbehind",
                                                                   "negative_lookahead",
                                                                   "negative_lookbehind",
                                                                   "atomic",
                                                                   "sr",
                                                                   "asr",
                                                                   "script_run",
                                                                   "atomic_script_run",
                                                                   "napla",
                                                                   "naplb",
                                                                   "non_atomic_positive_lookahead",
                                                                   "non_atomic_positive_lookbehind",
                                                                   "scs",
                                                                   "scan_substring"};

    void throw_unsupported(const std::string& feature) {
        util::throw_error("Unsupported: " + feature + " in PCRE2 regex");
    }

    // ================= PCRE2 REGEX LEXER =================

    bool PCRE2Lexer::is_digit(const Z3Char ch) {
        return ch >= '0' && ch <= '9';
    }

    bool PCRE2Lexer::is_octal_digit(const Z3Char ch) {
        return ch >= '0' && ch <= '7';
    }

    bool PCRE2Lexer::is_upper(const Z3Char ch) {
        return ch >= 'A' && ch <= 'Z';
    }

    bool PCRE2Lexer::is_lower(const Z3Char ch) {
        return ch >= 'a' && ch <= 'z';
    }

    bool PCRE2Lexer::is_alnum(const Z3Char ch) {
        return is_digit(ch) || is_upper(ch) || is_lower(ch);
    }

    int PCRE2Lexer::hex_value(const Z3Char ch) {
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

    void PCRE2Lexer::set_num_capture_groups(const GroupID num_capture_groups) {
        m_num_capture_groups = num_capture_groups;
    }

    Token PCRE2Lexer::get_next_token() {
        m_lexeme_start_pos = m_position;
        if (m_in_quote) {
            return get_quoted_token();
        }
        if (m_position >= m_regex.length()) {
            return make_token(TokenType::END_OF_INPUT);
        }
        return m_in_char_class ? get_token_char_class() : get_token_standard();
    }

    Token PCRE2Lexer::make_token(const TokenType type, const TokenPayload& payload) const {
        return {type, payload, zstring_view(m_regex.data() + m_lexeme_start_pos, m_position - m_lexeme_start_pos)};
    }

    void PCRE2Lexer::throw_syntax_error(const std::string& message) const {
        const zstring_view lexeme(m_regex.data() + m_lexeme_start_pos, m_position - m_lexeme_start_pos);
        util::throw_error("PCRE2 regex syntax error: " + message + ": " + lexeme.to_zstring().encode());
    }

    bool PCRE2Lexer::starts_with(const std::size_t pos, const std::string_view text) const {
        if (pos > m_regex.length() || m_regex.length() - pos < text.size()) {
            return false;
        }
        for (std::size_t i = 0; i < text.size(); i++) {
            if (m_regex[pos + i] != static_cast<Z3Char>(text[i])) {
                return false;
            }
        }
        return true;
    }

    void PCRE2Lexer::skip_blanks(std::size_t& pos) const {
        while (pos < m_regex.length() && (m_regex[pos] == ' ' || m_regex[pos] == '\t')) {
            pos++;
        }
    }

    bool PCRE2Lexer::parse_integer(std::size_t& pos, uint64_t& value) const {
        if (pos >= m_regex.length() || !is_digit(m_regex[pos])) {
            return false;
        }
        value = 0;
        while (pos < m_regex.length() && is_digit(m_regex[pos])) {
            // A value above MAX_NUMBER stays above it, so the value cannot overflow
            if (value <= MAX_NUMBER) {
                value = value * 10 + (m_regex[pos] - '0');
            }
            pos++;
        }
        return true;
    }

    Token PCRE2Lexer::get_token_standard() {
        const Z3Char ch = m_regex[m_position];
        m_position++;
        switch (ch) {
        case '|': return make_token(TokenType::ALTERNATION);
        case '(': return get_group_token();
        case ')': return make_token(TokenType::GROUP_END);
        case '^':
        case '$': return make_token(TokenType::ASSERTION, ch);
        case '.': return make_token(TokenType::DOT);
        case '[': {
            // "[[:<:]]" and "[[:>:]]" are the start and the end of a word
            if (starts_with(m_position, "[:<:]]") || starts_with(m_position, "[:>:]]")) {
                m_position += 6;
                throw_unsupported("POSIX word boundaries [[:<:]] and [[:>:]]");
            }
            // The syntax of POSIX classes is not allowed outside a character class, e.g., [:alpha:]
            std::size_t posix_end = 0;
            if (find_posix_class_end(m_position - 1, posix_end)) {
                const bool is_named_class = m_regex[m_position] == ':';
                m_position = posix_end + 2;
                throw_syntax_error(is_named_class ? "POSIX named classes are supported only within a class"
                                                  : "POSIX collating elements are not supported");
            }
            m_in_char_class = true;
            m_class_position = ClassPosition::START;
            return make_token(TokenType::CHAR_CLASS_START);
        }
        case '*':
        case '+':
        case '?': return get_quantifier_token(ch);
        case '{': return get_braced_quantifier_token();
        case '\\': return get_escape_sequence_token();
        default: return make_token(TokenType::LITERAL, ch);
        }
    }

    QuantifierMode PCRE2Lexer::read_quantifier_mode() {
        if (m_position < m_regex.length() && m_regex[m_position] == '?') {
            m_position++;
            return QuantifierMode::LAZY;
        }
        if (m_position < m_regex.length() && m_regex[m_position] == '+') {
            m_position++;
            return QuantifierMode::POSSESSIVE;
        }
        return QuantifierMode::GREEDY;
    }

    Token PCRE2Lexer::get_quantifier_token(const Z3Char op) {
        QuantifierRange range {0, UNBOUNDED};
        if (op == '+') {
            range.min = 1;
        }
        else if (op == '?') {
            range.max = 1;
        }
        return make_token(TokenType::QUANTIFIER, Quantifier {range, read_quantifier_mode()});
    }

    bool PCRE2Lexer::parse_quantifier_range(std::size_t& pos, QuantifierRange& range) const {
        std::size_t end = pos;
        uint64_t min = 0;
        uint64_t max = 0;
        skip_blanks(end);
        const bool has_min = parse_integer(end, min);
        skip_blanks(end);
        if (end < m_regex.length() && m_regex[end] == ',') {
            end++;
            skip_blanks(end);
            const bool has_max = parse_integer(end, max);
            skip_blanks(end);
            // {,} is not a quantifier
            if (!has_min && !has_max) {
                return false;
            }
            if (!has_max) {
                max = UNBOUNDED;
            }
        }
        else if (has_min) {
            max = min;
        }
        else {
            return false;
        }
        if (end >= m_regex.length() || m_regex[end] != '}') {
            return false;
        }
        pos = end + 1;
        range = {min, max};
        return true;
    }

    Token PCRE2Lexer::get_braced_quantifier_token() {
        std::size_t pos = m_position;
        QuantifierRange range {};
        if (!parse_quantifier_range(pos, range)) {
            return make_token(TokenType::LITERAL, static_cast<Z3Char>('{'));
        }
        m_position = pos;
        if (range.min > MAX_REPEAT_COUNT || (range.max != UNBOUNDED && range.max > MAX_REPEAT_COUNT)) {
            throw_syntax_error("number too big in {} quantifier");
        }
        if (range.max < range.min) {
            throw_syntax_error("numbers out of order in {} quantifier");
        }
        return make_token(TokenType::QUANTIFIER, Quantifier {range, read_quantifier_mode()});
    }

    Token PCRE2Lexer::get_group_token() {
        if (m_position < m_regex.length() && m_regex[m_position] == '*') {
            return get_verb_token();
        }
        if (m_position >= m_regex.length() || m_regex[m_position] != '?') {
            return make_token(TokenType::GROUP_START);
        }
        m_position++;  // '?'

        // The two characters after "(?", 0 behind the end of the pattern
        const Z3Char ch = (m_position < m_regex.length()) ? m_regex[m_position] : 0;
        const Z3Char next_ch = (m_position + 1 < m_regex.length()) ? m_regex[m_position + 1] : 0;
        switch (ch) {
        case '#':
            m_position++;
            skip_comment();
            return get_next_token();
        case '>': m_position++; return make_token(TokenType::ATOMIC_GROUP_START);
        case '=':
        case '!':
            m_position++;
            return make_token(TokenType::LOOKAROUND_START, LookaroundKind {LookaroundDirection::FORWARD, ch == '='});
        case '<':
            if (next_ch == '=' || next_ch == '!') {
                m_position += 2;
                return make_token(TokenType::LOOKAROUND_START,
                                  LookaroundKind {LookaroundDirection::BACKWARD, next_ch == '='});
            }
            if (next_ch == '*') {
                m_position += 2;
                throw_unsupported("non-atomic lookarounds");
            }
            return get_named_group_token(m_position + 1, '>');
        case '\'': return get_named_group_token(m_position + 1, '\'');
        case 'P':
            if (next_ch == '<') {
                return get_named_group_token(m_position + 2, '>');
            }
            m_position = std::min<std::size_t>(m_position + 2, m_regex.length());
            if (next_ch == '=') {
                throw_unsupported("backreferences");
            }
            if (next_ch == '>') {
                throw_unsupported("recursion and subroutine calls");
            }
            throw_syntax_error("unrecognized character after (?P");
            return {};
        case '*':
            m_position++;
            throw_unsupported("non-atomic lookarounds");
            return {};
        case '|':
            m_position++;
            throw_unsupported("branch reset groups (?|...)");
            return {};
        case '(':
            m_position++;
            throw_unsupported("conditional groups");
            return {};
        case 'C':
            m_position++;
            throw_unsupported("callouts");
            return {};
        case '[':
            m_position++;
            throw_unsupported("extended character classes (?[...])");
            return {};
        case 'R':
        case '&':
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
            m_position++;
            throw_unsupported("recursion and subroutine calls");
            return {};
        case '+':
        case '-':
            // (?+1) and (?-1) are relative subroutine calls, (?-i) clears a flag
            if (is_digit(next_ch)) {
                m_position += 2;
                throw_unsupported("recursion and subroutine calls");
            }
            break;
        default: break;
        }
        return get_flags_token();
    }

    zstring_view PCRE2Lexer::read_name(const std::size_t name_start, const Z3Char terminator) {
        std::size_t name_end = name_start;
        while (name_end < m_regex.length() && (is_alnum(m_regex[name_end]) || m_regex[name_end] == '_')) {
            name_end++;
        }
        // The lexeme of the errors includes the character after the name
        m_position = std::min<std::size_t>(name_end + 1, m_regex.length());

        // PCRE2 accepts also Unicode letters and decimal digits in the names
        if (name_end < m_regex.length() && m_regex[name_end] >= 0x80) {
            throw_unsupported("non-ASCII names of capture groups");
        }
        if (name_end == name_start) {
            throw_syntax_error("subpattern name expected");
        }
        if (is_digit(m_regex[name_start])) {
            throw_syntax_error("subpattern name must start with a non-digit");
        }
        if (name_end >= m_regex.length() || m_regex[name_end] != terminator) {
            throw_syntax_error("syntax error in subpattern name (missing terminator?)");
        }
        if (name_end - name_start > MAX_NAME_LENGTH) {
            throw_syntax_error("subpattern name is too long (maximum 128 code units)");
        }
        return zstring_view(m_regex.data() + name_start, name_end - name_start);
    }

    Token PCRE2Lexer::get_named_group_token(const std::size_t name_start, const Z3Char terminator) {
        const zstring_view name = read_name(name_start, terminator);
        return make_token(TokenType::GROUP_NAMED_START, name);
    }

    Token PCRE2Lexer::get_flags_token() {
        // (?flags) or (?flags:re), the flags before '-' are set, the flags after it are cleared, e.g., (?i-s)
        FlagChanges changes;
        bool is_negated = false;

        // (?^flags) clears the flags i, m, n, r, s and x and sets the given flags
        const bool is_reset = m_position < m_regex.length() && m_regex[m_position] == '^';
        if (is_reset) {
            m_position++;
            changes.cleared = CASE_INSENSITIVE | MULTI_LINE | NO_AUTO_CAPTURE | CASELESS_RESTRICT | DOT_ALL | EXTENDED |
                              EXTENDED_MORE;
        }

        while (m_position < m_regex.length()) {
            const Z3Char ch = m_regex[m_position];
            m_position++;
            const Z3Char next_ch = (m_position < m_regex.length()) ? m_regex[m_position] : 0;
            uint16_t flag = 0;
            switch (ch) {
            case 'i': flag = CASE_INSENSITIVE; break;
            case 'm': flag = MULTI_LINE; break;
            case 'n': flag = NO_AUTO_CAPTURE; break;
            case 's': flag = DOT_ALL; break;
            case 'J': flag = DUP_NAMES; break;
            case 'U': flag = UNGREEDY; break;
            case 'r': flag = CASELESS_RESTRICT; break;
            case 'x':
                flag = EXTENDED;
                if (next_ch == 'x') {
                    m_position++;
                    flag |= EXTENDED_MORE;
                }
                // Clearing x or xx clears both of them
                if (is_negated) {
                    flag = EXTENDED | EXTENDED_MORE;
                }
                break;
            case 'a':
                // a, aD, aS, aW, aP or aT
                flag = ASCII_RESTRICT;
                if (next_ch == 'D' || next_ch == 'S' || next_ch == 'W' || next_ch == 'P' || next_ch == 'T') {
                    m_position++;
                }
                break;
            case '-':
                if (is_negated || is_reset) {
                    throw_syntax_error("invalid hyphen in option setting");
                }
                is_negated = true;
                continue;
            case ':': return make_token(TokenType::GROUP_NONCAPTURE_START, changes);
            case ')': return make_token(TokenType::FLAGS, changes);
            default: throw_syntax_error("unrecognized character after (? or (?-"); return {};
            }
            if (is_negated) {
                changes.set &= ~flag;
                changes.cleared |= flag;
            }
            else {
                changes.set |= flag;
                changes.cleared &= ~flag;
            }
        }
        throw_syntax_error("missing closing parenthesis");
        return {};
    }

    void PCRE2Lexer::skip_comment() {
        // The comment ends at the first ')', which cannot be escaped
        while (m_position < m_regex.length() && m_regex[m_position] != ')') {
            m_position++;
        }
        if (m_position >= m_regex.length()) {
            throw_syntax_error("missing ) after (?# comment");
        }
        m_position++;  // ')'
    }

    Token PCRE2Lexer::get_verb_token() {
        const std::size_t name_start = m_position + 1;  // behind "(*"

        // The options are recognized only at the very start of the pattern, one after another
        if (m_lexeme_start_pos == m_start_options_end) {
            std::size_t option_end = 0;
            for (const std::string_view option : IGNORED_START_OPTIONS) {
                if (starts_with(name_start, option)) {
                    option_end = name_start + option.size();
                }
            }
            for (const std::string_view limit : IGNORED_START_LIMITS) {
                std::size_t pos = name_start + limit.size();
                uint64_t value = 0;
                if (starts_with(name_start, limit) && parse_integer(pos, value) && starts_with(pos, ")")) {
                    option_end = pos + 1;
                }
            }
            if (option_end != 0) {
                m_position = option_end;
                m_start_options_end = option_end;
                return get_next_token();
            }
            for (const std::string_view option : UNSUPPORTED_START_OPTIONS) {
                if (starts_with(name_start, option)) {
                    m_position = name_start + option.size();
                    throw_unsupported("start-of-pattern option (*" + std::string(option));
                }
            }
        }

        const Z3Char first = (name_start < m_regex.length()) ? m_regex[name_start] : 0;
        // The name of (*NAME) with upper case letters is a backtracking control verb, also the empty name of (*:NAME)
        if (is_upper(first) || first == ':') {
            std::size_t name_end = name_start;
            while (name_end < m_regex.length() && is_upper(m_regex[name_end])) {
                name_end++;
            }
            m_position = name_end;
            for (const std::string_view verb : VERBS) {
                if (name_end - name_start == verb.size() && starts_with(name_start, verb)) {
                    throw_unsupported("backtracking control verbs");
                }
            }
            throw_syntax_error("(*VERB) not recognized or malformed");
        }
        // The name of (*name: with lower case letters is the alphabetic name of a lookaround or of a special group
        if (is_lower(first)) {
            std::size_t name_end = name_start;
            while (name_end < m_regex.length() && (is_lower(m_regex[name_end]) || m_regex[name_end] == '_')) {
                name_end++;
            }
            m_position = name_end;
            for (const std::string_view assertion : ALPHA_ASSERTIONS) {
                if (name_end - name_start == assertion.size() && starts_with(name_start, assertion)) {
                    throw_unsupported("(*" + std::string(assertion) + ":...)");
                }
            }
            throw_syntax_error("(*alpha_assertion) not recognized");
        }

        // "(*" that is not followed by a letter or ':' is the start of a capture group followed by the quantifier '*'
        return make_token(TokenType::GROUP_START);
    }

    Token PCRE2Lexer::get_escape_sequence_token() {
        if (m_position >= m_regex.length()) {
            throw_syntax_error("\\ at end of pattern");
            return {};
        }
        const Z3Char ch = m_regex[m_position];
        m_position++;
        switch (ch) {
        case 'A':
        case 'b':
        case 'B':
        case 'G':
        case 'z':
        case 'Z': return make_token(TokenType::ASSERTION, ch);
        case 'd':
        case 'D':
        case 'h':
        case 'H':
        case 's':
        case 'S':
        case 'v':
        case 'V':
        case 'w':
        case 'W': return make_token(TokenType::CHAR_CLASS_ESCAPE, ch);
        case 'N': {
            if (m_position >= m_regex.length() || m_regex[m_position] != '{') {
                return make_token(TokenType::CHAR_CLASS_ESCAPE, ch);
            }
            // \N{U+h...} is a character, \N{n,m} is \N with a quantifier
            std::size_t pos = m_position + 1;
            skip_blanks(pos);
            if (starts_with(pos, "U+")) {
                return make_token(TokenType::LITERAL, parse_unicode_name_escape());
            }
            QuantifierRange range {};
            if (parse_quantifier_range(pos, range)) {
                return make_token(TokenType::CHAR_CLASS_ESCAPE, ch);
            }
            m_position++;  // '{'
            throw_syntax_error("PCRE2 does not support \\F, \\L, \\l, \\N{name}, \\U, or \\u");
            return {};
        }
        case 'R': return make_token(TokenType::NEWLINE_SEQUENCE);
        case 'Q':
            // \Q...\E: the text up to \E (or to the end of the regex) is literal
            m_in_quote = true;
            return get_next_token();
        case 'E':
            // \E that does not end quoted text is ignored
            return get_next_token();
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
        case '8':
        case '9': return get_backreference_token(ch);
        case 'g':
        case 'k': throw_unsupported("backreferences and subroutine calls (\\g, \\k)"); return {};
        case 'p':
        case 'P': throw_unsupported("Unicode properties (\\p, \\P)"); return {};
        case 'X': throw_unsupported("extended grapheme clusters (\\X)"); return {};
        case 'C': throw_unsupported("\\C (a single code unit)"); return {};
        case 'K': throw_unsupported("\\K"); return {};
        default: return make_token(TokenType::LITERAL, parse_escaped_char(ch, false));
        }
    }

    Token PCRE2Lexer::get_backreference_token(const Z3Char first_digit) {
        std::size_t pos = m_position - 1;
        uint64_t number = 0;
        parse_integer(pos, number);
        if (number < 10 || first_digit >= '8' || number <= m_num_capture_groups) {
            m_position = pos;
            if (number > MAX_GROUP_NUMBER) {
                throw_syntax_error("number is too big");
            }
            return make_token(TokenType::BACKREFERENCE, BackrefTarget {.kind = BackrefTarget::Kind::NUMBER,
                                                                       .number = static_cast<int64_t>(number),
                                                                       .name = {}});
        }
        return make_token(TokenType::LITERAL, parse_octal_escape(first_digit));
    }

    Token PCRE2Lexer::get_quoted_token() {
        if (starts_with(m_position, "\\E")) {
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
        return m_in_char_class ? make_class_literal_token(ch) : make_token(TokenType::LITERAL, ch);
    }

    Z3Char PCRE2Lexer::parse_escaped_char(const Z3Char escaped, const bool in_char_class) {
        switch (escaped) {
        case 'a': return '\a';
        case 'e': return 0x1B;
        case 'f': return '\f';
        case 'n': return '\n';
        case 'r': return '\r';
        case 't': return '\t';
        case 'c': return parse_control_escape();
        case 'x': return parse_hex_escape();
        case 'o':
            if (m_position >= m_regex.length() || m_regex[m_position] != '{') {
                throw_syntax_error("missing opening brace after \\o");
            }
            m_position++;  // '{'
            skip_blanks(m_position);
            return parse_braced_code_point(8);
        case '0': return parse_octal_escape(escaped);
        case 'F':
        case 'l':
        case 'L':
        case 'u':
        case 'U': throw_syntax_error("PCRE2 does not support \\F, \\L, \\l, \\N{name}, \\U, or \\u"); return 0;
        default: break;
        }

        if (in_char_class) {
            switch (escaped) {
            case 'b': return '\b';
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7': return parse_octal_escape(escaped);
            case '8':
            case '9':
            case 'g':
            case 'k': return escaped;
            default: break;
            }
        }

        // Only ASCII letters and digits have a special meaning after '\', other characters are themselves
        if (escaped >= 0x80 || !is_alnum(escaped)) {
            return escaped;
        }
        throw_syntax_error("unrecognized character follows \\");
        return 0;
    }

    Z3Char PCRE2Lexer::parse_hex_escape() {
        if (m_position < m_regex.length() && m_regex[m_position] == '{') {
            m_position++;  // '{'
            skip_blanks(m_position);
            return parse_braced_code_point(16);
        }

        Z3Char code = 0;
        unsigned num_digits = 0;
        while (num_digits < 2 && m_position < m_regex.length() && hex_value(m_regex[m_position]) >= 0) {
            code = code * 16 + hex_value(m_regex[m_position]);
            m_position++;
            num_digits++;
        }
        if (num_digits == 0) {
            throw_syntax_error("digits missing after \\x or in \\x{} or \\o{} or \\N{U+}");
        }
        return code;
    }

    Z3Char PCRE2Lexer::parse_octal_escape(const Z3Char first_digit) {
        Z3Char code = first_digit - '0';
        for (int i = 0; i < 2 && m_position < m_regex.length() && is_octal_digit(m_regex[m_position]); i++) {
            code = code * 8 + (m_regex[m_position] - '0');
            m_position++;
        }
        return code;
    }

    Z3Char PCRE2Lexer::parse_control_escape() {
        if (m_position >= m_regex.length()) {
            throw_syntax_error("\\c at end of pattern");
        }
        Z3Char ch = m_regex[m_position];
        m_position++;
        if (ch < 32 || ch > 126) {
            throw_syntax_error("\\c must be followed by a printable ASCII character");
        }
        // The character is converted to upper case and its bit 6 is inverted, e.g., \cA and \ca are the character 1
        if (is_lower(ch)) {
            ch -= 'a' - 'A';
        }
        return ch ^ 0x40;
    }

    Z3Char PCRE2Lexer::parse_unicode_name_escape() {
        m_position++;  // '{'
        skip_blanks(m_position);
        if (!starts_with(m_position, "U+")) {
            throw_syntax_error("PCRE2 does not support \\F, \\L, \\l, \\N{name}, \\U, or \\u");
        }
        m_position += 2;  // "U+"
        return parse_braced_code_point(16);
    }

    Z3Char PCRE2Lexer::parse_braced_code_point(const unsigned base) {
        uint64_t code = 0;
        unsigned num_digits = 0;
        while (m_position < m_regex.length()) {
            const int value = hex_value(m_regex[m_position]);
            if (value < 0 || static_cast<unsigned>(value) >= base) {
                break;
            }
            // A code point above the maximum stays above it, so the value cannot overflow
            if (code <= MAX_UNICODE_CODE_POINT) {
                code = code * base + value;
            }
            m_position++;
            num_digits++;
        }
        skip_blanks(m_position);

        if (m_position >= m_regex.length() || m_regex[m_position] != '}') {
            m_position = std::min<std::size_t>(m_position + 1, m_regex.length());
            throw_syntax_error(base == 16 ? "non-hex character in \\x{} (closing brace missing?)"
                                          : "non-octal character in \\o{} (closing brace missing?)");
        }
        m_position++;  // '}'
        if (num_digits == 0) {
            throw_syntax_error("digits missing after \\x or in \\x{} or \\o{} or \\N{U+}");
        }
        if (code > MAX_UNICODE_CODE_POINT) {
            throw_syntax_error("character code point value in \\x{} or \\o{} is too large");
        }
        if (code >= FIRST_SURROGATE && code <= LAST_SURROGATE) {
            throw_syntax_error("disallowed Unicode code point (>= 0xd800 && <= 0xdfff)");
        }
        return static_cast<Z3Char>(code);
    }

    bool PCRE2Lexer::find_posix_class_end(const std::size_t bracket_pos, std::size_t& end) const {
        if (bracket_pos + 1 >= m_regex.length()) {
            return false;
        }
        const Z3Char terminator = m_regex[bracket_pos + 1];
        if (terminator != ':' && terminator != '.' && terminator != '=') {
            return false;
        }
        for (std::size_t pos = bracket_pos + 2; pos + 1 < m_regex.length(); pos++) {
            const Z3Char ch = m_regex[pos];
            const Z3Char next_ch = m_regex[pos + 1];
            if (ch == '\\' && (next_ch == ']' || next_ch == '\\')) {
                pos++;
            }
            else if ((ch == '[' && next_ch == terminator) || ch == ']') {
                return false;
            }
            else if (ch == terminator && next_ch == ']') {
                end = pos;
                return true;
            }
        }
        return false;
    }

    Token PCRE2Lexer::make_class_literal_token(const Z3Char ch) {
        m_class_position =
            (m_class_position == ClassPosition::UPPER) ? ClassPosition::ELEMENT : ClassPosition::AFTER_LOWER;
        return make_token(TokenType::LITERAL, ch);
    }

    Token PCRE2Lexer::get_token_char_class() {
        const Z3Char ch = m_regex[m_position];
        const bool is_first = m_class_position == ClassPosition::START || m_class_position == ClassPosition::FIRST;

        if (m_class_position == ClassPosition::START && ch == '^') {
            m_position++;
            m_class_position = ClassPosition::FIRST;
            return make_token(TokenType::CHAR_CLASS_NEGATION);
        }

        // ']' closes the class, except as its first element, where it is a literal
        if (ch == ']' && !is_first) {
            m_position++;
            m_in_char_class = false;
            return make_token(TokenType::CHAR_CLASS_END);
        }

        if (ch == '-') {
            // '-' after a single character starts a range, the parser makes it a literal if ']' follows
            if (m_class_position == ClassPosition::AFTER_LOWER) {
                m_position++;
                m_class_position = ClassPosition::UPPER;
                return make_token(TokenType::CHAR_CLASS_RANGE);
            }
            // '-' after a class escape or a POSIX class is a literal only as the last character of the class
            if (m_class_position == ClassPosition::AFTER_CLASS_ESCAPE && m_position + 1 < m_regex.length() &&
                m_regex[m_position + 1] != ']') {
                m_position++;
                throw_syntax_error("invalid range in character class");
            }
        }

        // "[:name:]" is a POSIX class, '[' that does not start the syntax of a POSIX class is a literal
        std::size_t posix_end = 0;
        if (ch == '[' && find_posix_class_end(m_position, posix_end)) {
            const bool is_named_class = m_regex[m_position + 1] == ':';
            const zstring_view name(m_regex.data() + m_position + 2, posix_end - m_position - 2);
            m_position = posix_end + 2;
            if (!is_named_class) {
                throw_syntax_error("POSIX collating elements are not supported");
            }
            m_class_position = ClassPosition::AFTER_CLASS_ESCAPE;
            return make_token(TokenType::POSIX_CLASS, name);
        }

        m_position++;
        return (ch == '\\') ? get_char_class_escape_sequence_token() : make_class_literal_token(ch);
    }

    Token PCRE2Lexer::get_char_class_escape_sequence_token() {
        if (m_position >= m_regex.length()) {
            throw_syntax_error("\\ at end of pattern");
            return {};
        }
        const Z3Char ch = m_regex[m_position];
        m_position++;
        switch (ch) {
        case 'd':
        case 'D':
        case 'h':
        case 'H':
        case 's':
        case 'S':
        case 'v':
        case 'V':
        case 'w':
        case 'W':
            m_class_position = ClassPosition::AFTER_CLASS_ESCAPE;
            return make_token(TokenType::CHAR_CLASS_ESCAPE, ch);
        case 'Q':
            // The position in the class does not change, so "[\Q\E]" is not closed and "[\Q\E^a]" is negated
            m_in_quote = true;
            return get_next_token();
        case 'E': return get_next_token();
        case 'N':
            if (m_position >= m_regex.length() || m_regex[m_position] != '{') {
                throw_syntax_error("\\N is not supported in a class");
            }
            return make_class_literal_token(parse_unicode_name_escape());
        case 'A':
        case 'B':
        case 'C':
        case 'G':
        case 'K':
        case 'R':
        case 'X':
        case 'z':
        case 'Z': throw_syntax_error("escape sequence is invalid in character class"); return {};
        case 'p':
        case 'P': throw_unsupported("Unicode properties (\\p, \\P)"); return {};
        default: return make_class_literal_token(parse_escaped_char(ch, true));
        }
    }

    // =============== PCRE2 REGEX PARSER ===============

    CharSet PCRE2Parser::word_chars() {
        CharSet chars = CharSet::range('0', '9');
        chars.add('A', 'Z');
        chars.add('_');
        chars.add('a', 'z');
        return chars;
    }

    CharSet PCRE2Parser::space_chars() {
        CharSet chars = CharSet::range('\t', '\r');
        chars.add(' ');
        return chars;
    }

    CharSet PCRE2Parser::horizontal_space_chars() {
        CharSet chars = CharSet::single('\t');
        chars.add(' ');
        chars.add(0xA0);
        chars.add(0x1680);
        chars.add(0x180E);
        chars.add(0x2000, 0x200A);
        chars.add(0x202F);
        chars.add(0x205F);
        chars.add(0x3000);
        return chars;
    }

    CharSet PCRE2Parser::vertical_space_chars() {
        CharSet chars = CharSet::range('\n', '\r');
        chars.add(0x85);
        chars.add(0x2028, 0x2029);
        return chars;
    }

    CharSet PCRE2Parser::class_escape_chars(const Z3Char escape) {
        switch (escape) {
        case 'd': return CharSet::range('0', '9');
        case 'D': return CharSet::range('0', '9').complement();
        case 'h': return horizontal_space_chars();
        case 'H': return horizontal_space_chars().complement();
        case 's': return space_chars();
        case 'S': return space_chars().complement();
        case 'v': return vertical_space_chars();
        case 'V': return vertical_space_chars().complement();
        case 'w': return word_chars();
        case 'W': return word_chars().complement();
        // \N is any character except \n, also with the flag s
        case 'N': return CharSet::single('\n').complement();
        default: util::throw_error("PCRE2 regex syntax error: unknown character type"); return {};
        }
    }

    std::optional<CharSet> PCRE2Parser::posix_class_chars(const std::string& name) {
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
            chars = space_chars();
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

    NodeRef PCRE2Parser::make_newline_sequence() {
        Concatenation cr_lf;
        cr_lf.terms.push_back(make_node(CharSet::single('\r')));
        cr_lf.terms.push_back(make_node(CharSet::single('\n')));

        // \R is atomic: if \r\n matches, \r is never tried alone, so \r alone matches only if no \n follows
        Concatenation cr;
        cr.terms.push_back(make_node(CharSet::single('\r')));
        cr.terms.push_back(
            make_node(Lookaround {make_node(CharSet::single('\n')), LookaroundDirection::FORWARD, false}));

        // The vertical space characters except \r
        CharSet single_chars = CharSet::range('\n', '\f');
        single_chars.add(0x85);
        single_chars.add(0x2028, 0x2029);

        Alternation newline;
        newline.alternatives.push_back(make_node(std::move(cr_lf)));
        newline.alternatives.push_back(make_node(std::move(cr)));
        newline.alternatives.push_back(make_node(std::move(single_chars)));
        return make_node(std::move(newline));
    }

    NodeRef PCRE2Parser::make_circumflex(const bool is_multi_line) {
        if (!is_multi_line) {
            return make_node(Anchor::START_OF_TEXT);
        }

        // After a \n that is followed by some character, i.e., that does not end the text
        Concatenation after_newline;
        after_newline.terms.push_back(
            make_node(Lookaround {make_node(CharSet::single('\n')), LookaroundDirection::BACKWARD, true}));
        after_newline.terms.push_back(
            make_node(Lookaround {make_node(CharSet::all()), LookaroundDirection::FORWARD, true}));

        Alternation line_start;
        line_start.alternatives.push_back(make_node(Anchor::START_OF_TEXT));
        line_start.alternatives.push_back(make_node(std::move(after_newline)));
        return make_node(std::move(line_start));
    }

    NodeRef PCRE2Parser::make_dollar(const bool is_multi_line) {
        if (is_multi_line) {
            return make_line_end(CharSet::single('\n'));
        }

        // The end of the text or the position before a \n that ends the text, i.e., the position that is followed
        // neither by a character other than \n, nor by \n and one more character
        Concatenation newline_and_char;
        newline_and_char.terms.push_back(make_node(CharSet::single('\n')));
        newline_and_char.terms.push_back(make_node(CharSet::all()));

        Alternation more_text;
        more_text.alternatives.push_back(make_node(CharSet::single('\n').complement()));
        more_text.alternatives.push_back(make_node(std::move(newline_and_char)));
        return make_node(Lookaround {make_node(std::move(more_text)), LookaroundDirection::FORWARD, false});
    }

    NodeRef PCRE2Parser::parse() {
        NodeRef ast = parse_disjunction();
        if (m_current_token.type == TokenType::GROUP_END) {
            throw_syntax_error("unmatched closing parenthesis");
        }
        SASSERT(m_current_token.type == TokenType::END_OF_INPUT);
        return ast;
    }

    void PCRE2Parser::next() {
        m_current_token = m_lexer.get_next_token();
    }

    bool PCRE2Parser::match(const TokenType type) {
        if (m_current_token.type == type) {
            next();
            return true;
        }
        return false;
    }

    void PCRE2Parser::throw_syntax_error(const std::string& message) const {
        util::throw_error("PCRE2 regex syntax error: " + message + ": " + m_current_token.lexeme.to_zstring().encode());
    }

    void PCRE2Parser::apply_flags(const FlagChanges changes) {
        if (changes.set & CASE_INSENSITIVE) {
            throw_unsupported("case-insensitive matching (flag i)");
        }
        if (changes.set & (EXTENDED | EXTENDED_MORE)) {
            throw_unsupported("extended syntax (flags x and xx)");
        }
        m_flags = (m_flags | changes.set) & ~changes.cleared;
    }

    NodeRef PCRE2Parser::parse_disjunction() {
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

    NodeRef PCRE2Parser::parse_alternative() {
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

    NodeRef PCRE2Parser::parse_term() {
        switch (m_current_token.type) {
        // The simple assertions cannot be repeated, a quantifier after them is reported by the next call
        case TokenType::ASSERTION: return parse_assertion();
        case TokenType::LITERAL:
        case TokenType::DOT:
        case TokenType::CHAR_CLASS_ESCAPE:
        case TokenType::NEWLINE_SEQUENCE:
        case TokenType::BACKREFERENCE:
        case TokenType::CHAR_CLASS_START:
        case TokenType::GROUP_START:
        case TokenType::GROUP_NAMED_START:
        case TokenType::GROUP_NONCAPTURE_START:
        case TokenType::ATOMIC_GROUP_START:
        case TokenType::LOOKAROUND_START: return parse_maybe_quantifier(parse_atom());
        case TokenType::QUANTIFIER: throw_syntax_error("quantifier does not follow a repeatable item"); return {};
        default: throw_syntax_error("unexpected token"); return {};
        }
    }

    NodeRef PCRE2Parser::parse_maybe_quantifier(NodeRef term) {
        if (m_current_token.type != TokenType::QUANTIFIER) {
            return term;
        }
        const Quantifier quantifier = std::get<Quantifier>(m_current_token.payload);
        if (quantifier.mode == QuantifierMode::POSSESSIVE) {
            throw_unsupported("possessive quantifiers");
        }
        next();

        // A lazy quantifier matches the same strings as the greedy one.
        // Captures are kept between the iterations and an empty iteration does not fail (the defaults of Repetition).
        return make_node(
            Repetition {.child = std::move(term), .min = quantifier.range.min, .max = quantifier.range.max});
    }

    NodeRef PCRE2Parser::parse_assertion() {
        SASSERT(std::holds_alternative<Z3Char>(m_current_token.payload) && "ASSERTION has no specifier");
        const Z3Char assertion = std::get<Z3Char>(m_current_token.payload);
        const bool is_multi_line = m_flags & MULTI_LINE;
        next();
        switch (assertion) {
        case '^': return make_circumflex(is_multi_line);
        case '$': return make_dollar(is_multi_line);
        case 'A': return make_node(Anchor::START_OF_TEXT);
        // \Z is $ without the flag m
        case 'Z': return make_dollar(false);
        case 'z': return make_node(Anchor::END_OF_TEXT);
        case 'b': return make_word_boundary(word_chars(), false);
        case 'B': return make_word_boundary(word_chars(), true);
        case 'G': throw_unsupported("\\G"); return {};
        default: util::throw_error("PCRE2 regex syntax error: unknown assertion"); return {};
        }
    }

    NodeRef PCRE2Parser::parse_atom() {
        const Token t = m_current_token;
        switch (t.type) {
        case TokenType::LITERAL:
            SASSERT(std::holds_alternative<Z3Char>(t.payload) && "LITERAL has no literal value");
            next();
            return make_node(CharSet::single(std::get<Z3Char>(t.payload)));
        case TokenType::DOT: {
            // Without the flag s, '.' matches any character except \n
            const bool matches_newline = m_flags & DOT_ALL;
            next();
            return make_node(matches_newline ? CharSet::all() : CharSet::single('\n').complement());
        }
        case TokenType::CHAR_CLASS_ESCAPE:
            SASSERT(std::holds_alternative<Z3Char>(t.payload) && "CHAR_CLASS_ESCAPE has no class specifier");
            next();
            return make_node(class_escape_chars(std::get<Z3Char>(t.payload)));
        case TokenType::NEWLINE_SEQUENCE: next(); return make_newline_sequence();
        case TokenType::BACKREFERENCE: return parse_backreference();
        case TokenType::GROUP_START:
        case TokenType::GROUP_NAMED_START:
        case TokenType::GROUP_NONCAPTURE_START:
        case TokenType::ATOMIC_GROUP_START: return parse_group();
        case TokenType::LOOKAROUND_START: return parse_lookaround();
        case TokenType::CHAR_CLASS_START: return parse_character_class();
        default: throw_syntax_error("unexpected token"); return {};
        }
    }

    NodeRef PCRE2Parser::parse_group() {
        const Token start = m_current_token;
        // The flags changed inside the group hold only until its end
        const uint16_t outer_flags = m_flags;
        bool is_capturing = false;
        switch (start.type) {
        case TokenType::GROUP_NONCAPTURE_START: apply_flags(std::get<FlagChanges>(start.payload)); break;
        // With the flag n, plain parentheses do not capture
        case TokenType::GROUP_START: is_capturing = !(m_flags & NO_AUTO_CAPTURE); break;
        case TokenType::GROUP_NAMED_START: is_capturing = true; break;
        case TokenType::ATOMIC_GROUP_START: throw_unsupported("atomic groups"); return {};
        default: throw_syntax_error("unexpected token"); return {};
        }

        // Named groups are numbered together with the other capture groups
        GroupID gid = 0;
        if (is_capturing) {
            if (m_current_group_id >= MAX_GROUP_NUMBER) {
                throw_syntax_error("too many capturing groups (maximum 65535)");
            }
            gid = ++m_current_group_id;
            m_lexer.set_num_capture_groups(gid);
        }
        if (start.type == TokenType::GROUP_NAMED_START) {
            const zstring_view name = std::get<zstring_view>(start.payload);
            if (!m_named_groups.emplace(name, gid).second) {
                // The flag J allows capture groups with the same name
                if (m_flags & DUP_NAMES) {
                    throw_unsupported("capture groups with the same name (flag J)");
                }
                throw_syntax_error("two named subpatterns have the same name (PCRE2_DUPNAMES not set)");
            }
        }

        next();
        NodeRef subpattern = parse_disjunction();
        if (m_current_token.type != TokenType::GROUP_END) {
            throw_syntax_error("missing closing parenthesis");
        }
        next();
        m_flags = outer_flags;

        // Non-capturing groups have no meaning for the subpattern
        if (!is_capturing) {
            return subpattern;
        }
        return make_node(Capture {gid, std::move(subpattern)});
    }

    NodeRef PCRE2Parser::parse_lookaround() {
        throw_unsupported("lookarounds");
        return {};
    }

    NodeRef PCRE2Parser::parse_backreference() {
        throw_unsupported("backreferences");
        return {};
    }

    NodeRef PCRE2Parser::parse_character_class() {
        next();  // '['
        const bool is_negated = match(TokenType::CHAR_CLASS_NEGATION);

        CharSet chars;
        while (m_current_token.type != TokenType::CHAR_CLASS_END) {
            const Token t = m_current_token;
            switch (t.type) {
            case TokenType::END_OF_INPUT: throw_syntax_error("missing terminating ] for character class"); return {};
            case TokenType::CHAR_CLASS_ESCAPE:
                chars.add(class_escape_chars(std::get<Z3Char>(t.payload)));
                next();
                break;
            case TokenType::POSIX_CLASS: {
                // [:^name:] is the negation of [:name:]
                const std::string name = std::get<zstring_view>(t.payload).to_zstring().encode();
                const bool is_negated_class = !name.empty() && name[0] == '^';
                const std::optional<CharSet> class_chars = posix_class_chars(is_negated_class ? name.substr(1) : name);
                if (!class_chars) {
                    throw_syntax_error("unknown POSIX class name");
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
                // '-' before the closing ']' is a literal
                if (m_current_token.type == TokenType::CHAR_CLASS_END) {
                    chars.add(lower);
                    chars.add('-');
                    break;
                }
                if (m_current_token.type == TokenType::END_OF_INPUT) {
                    throw_syntax_error("missing terminating ] for character class");
                }
                // The upper bound of a range cannot be a class escape or a POSIX class
                if (m_current_token.type != TokenType::LITERAL) {
                    throw_syntax_error("invalid range in character class");
                }
                const Z3Char upper = std::get<Z3Char>(m_current_token.payload);
                if (upper < lower) {
                    throw_syntax_error("range out of order in character class");
                }
                chars.add(lower, upper);
                next();
                break;
            }
            default: throw_syntax_error("invalid character class"); return {};
            }
        }
        next();  // ']'

        // Negated classes match also \n
        return make_node(is_negated ? chars.complement() : std::move(chars));
    }
}  // namespace smt::noodler::extended_regex::pcre2
