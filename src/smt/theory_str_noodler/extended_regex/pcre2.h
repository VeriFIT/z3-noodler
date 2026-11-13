#pragma once

#include "regex_ast.h"

#include "util/zstring_view.h"

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <variant>

/**
 * Frontend of the PCRE2 regex flavor (https://www.pcre2.org/doc/pcre2pattern/): the lexer and the parser into the
 * common AST.
 *
 * The pattern is interpreted as by pcre2_compile() with the option PCRE2_UTF and without PCRE2_UCP, i.e., the
 * characters of the pattern are code points, but the character types (\d, \s, \w), the POSIX classes and the word
 * boundaries are ASCII only.
 * The newline convention is LF and \R matches any Unicode newline sequence (the defaults of PCRE2 builds).
 */
namespace smt::noodler::extended_regex::pcre2 {
    // ======================= TOKENS =======================

    /**
     * The types of the tokens of PCRE2 regexes.
     */
    enum class TokenType {
        ALTERNATION,             // |
        ASSERTION,               // ^, $, \A, \Z, \z, \b, \B, \G
        BACKREFERENCE,           // \1, \g1, \g{1}, \g-1, \g{-1}, \k<name>, \k'name', \k{name}, \g{name}, (?P=name)
        CHAR_CLASS_START,        // [
        CHAR_CLASS_END,          // ]
        CHAR_CLASS_NEGATION,     // '^' after '['
        CHAR_CLASS_RANGE,        // '-' between the bounds of a range inside '[]'
        CHAR_CLASS_ESCAPE,       // \d, \D, \h, \H, \s, \S, \v, \V, \w, \W, \N (\N outside '[]' only)
        POSIX_CLASS,             // [:alpha:], [:^alpha:] inside '[]'
        NEWLINE_SEQUENCE,        // \R
        DOT,                     // .
        END_OF_INPUT,            // EOF
        GROUP_START,             // (
        GROUP_NAMED_START,       // (?<name>, (?'name', (?P<name>
        GROUP_NONCAPTURE_START,  // (?:, (?flags:
        ATOMIC_GROUP_START,      // (?>, (*atomic:
        LOOKAROUND_START,        // (?=, (?!, (?<=, (?<!, (*pla:, (*positive_lookahead:, ...
        FLAGS,                   // (?flags)
        GROUP_END,               // )
        LITERAL,                 // a, \*, \x41, \x{41}, \101, \o{101}, \cA, characters of \Q...\E, ...
        QUANTIFIER,              // *, +, ?, {n}, {n,}, {n,m}, {,m}, possibly followed by ? (lazy) or + (possessive)
    };

    /**
     * Flags of PCRE2 regexes, changed by (?flags) and (?flags:re).
     */
    enum Flag : uint16_t {
        CASE_INSENSITIVE = 1,     // i
        MULTI_LINE = 2,           // m: ^ and $ match also at the start and at the end of lines
        NO_AUTO_CAPTURE = 4,      // n: plain parentheses do not capture, named groups still do
        DOT_ALL = 8,              // s: '.' matches also \n
        EXTENDED = 16,            // x: white space and #-comments outside character classes are ignored
        EXTENDED_MORE = 32,       // xx: like x, and also spaces and tabs inside character classes are ignored
        DUP_NAMES = 64,           // J: capture groups may have the same name
        UNGREEDY = 128,           // U: swaps the meaning of x* and x*?, x+ and x+?, ...
        CASELESS_RESTRICT = 256,  // r: caseless matching does not match ASCII and non-ASCII characters together
        ASCII_RESTRICT = 512,     // a, aD, aS, aW, aP, aT: character types and POSIX classes are ASCII under UCP
    };

    /**
     * Flags set and cleared by (?flags) or (?flags:re), e.g., (?i-s) sets i and clears s, (?^) clears imnsx.
     */
    struct FlagChanges {
        uint16_t set = 0;      // The flags set
        uint16_t cleared = 0;  // The flags cleared
    };

    /**
     * The numbers of repetitions allowed by a quantifier.
     */
    struct QuantifierRange {
        uint64_t min;  // The minimum number of repetitions
        uint64_t max;  // The maximum number of repetitions, UNBOUNDED if there is none
    };

    /**
     * Greedy (x*), lazy (x*?) or possessive (x*+) repetition.
     */
    enum class QuantifierMode {
        GREEDY,      // Repeats as many times as possible, can give up repetitions by backtracking
        LAZY,        // Repeats as few times as possible, can add repetitions by backtracking
        POSSESSIVE,  // Repeats as many times as possible, never gives up repetitions
    };

    /**
     * A quantifier, i.e., its range and its mode.
     */
    struct Quantifier {
        QuantifierRange range;  // The numbers of repetitions
        QuantifierMode mode;    // Greedy, lazy or possessive
    };

    /**
     * The capture group a backreference refers to, as written in the pattern.
     *
     * Relative numbers (\g-1, \g{+1}) and names are resolved to group IDs by PCRE2Parser.
     */
    struct BackrefTarget {
        /**
         * The ways a backreference refers to a capture group.
         */
        enum class Kind {
            NUMBER,    // \1, \g1, \g{1}
            RELATIVE,  // \g-1, \g{-1}, \g{+1}
            NAME,      // \k<name>, \k'name', \k{name}, \g{name}, (?P=name)
        };

        Kind kind;           // How the group is referred to
        int64_t number = 0;  // The number of the group for NUMBER, the offset from the current group for RELATIVE
        zstring_view name;   // The name of the group for NAME
    };

    /**
     * The direction and polarity of a lookaround, e.g., (?<! is a negative lookbehind.
     */
    struct LookaroundKind {
        LookaroundDirection direction;  // Lookahead (FORWARD) or lookbehind (BACKWARD)
        bool is_positive;               // True for a positive lookaround, false for a negative one
    };

    /**
     * The payload of a token: none, a literal/escape/assertion character, a quantifier, flag changes, a capture
     * group/POSIX class name, a backreference target or a lookaround kind.
     */
    using TokenPayload =
        std::variant<std::monostate, Z3Char, Quantifier, FlagChanges, zstring_view, BackrefTarget, LookaroundKind>;

    /**
     * A token of a PCRE2 regex.
     */
    struct Token {
        TokenType type;        // The type of the token
        TokenPayload payload;  // The data of the token, depends on its type
        zstring_view lexeme;   // The text of the token in the pattern
    };

    /**
     * @brief Throw the error that @p feature is not supported, e.g., "Unsupported: callouts in PCRE2 regex".
     */
    void throw_unsupported(const std::string& feature);

    // ================= PCRE2 REGEX LEXER =================

    /**
     * Tokenizes a PCRE2 regex string on demand.
     *
     * The lexer switches between standard tokenization, character-class tokenization and quoted text (\Q...\E), since
     * characters have different meanings in them.
     * Inside a character class, the lexer tracks the position in the current element of the class, which determines
     * whether ']' closes the class, whether '-' makes a range and whether "[:" starts a POSIX class.
     *
     * Comments (?#...) and the start-of-pattern options (*...) produce no tokens.
     *
     * The lexer reports invalid escape sequences, groups and flags; whether the tokens follow each other correctly is
     * checked by PCRE2Parser.
     */
    class PCRE2Lexer {
    public:
        /**
         * @brief Create a lexer of the pattern @p regex.
         */
        explicit PCRE2Lexer(const zstring_view regex)
            : m_regex(regex) { }

        /**
         * @brief Set the number of capture groups opened before the next token.
         *
         * The number decides whether \NN with two or more digits is a backreference or an octal escape.
         * It is known only to the parser, since the flag n turns plain parentheses into non-capturing groups.
         */
        void set_num_capture_groups(GroupID num_capture_groups);

        /**
         * @brief Read the next token of the pattern.
         *
         * @return Token The next token, END_OF_INPUT at the end of the pattern (also on every later call).
         */
        Token get_next_token();

    private:
        /**
         * The position of the lexer in the current element of a character class.
         */
        enum class ClassPosition {
            START,               // Right after '[', where '^' negates the class
            FIRST,               // At the first element, where ']' is a literal
            ELEMENT,             // At the start of an element
            AFTER_LOWER,         // After a single character, which can be the lower bound of a range
            UPPER,               // After '-' of a range, at its upper bound
            AFTER_CLASS_ESCAPE,  // After a class escape or a POSIX class, where '-' must be followed by ']'
        };

        /** The pattern. */
        zstring_view m_regex;

        /** The number of capture groups opened before the next token, see set_num_capture_groups(). */
        GroupID m_num_capture_groups = 0;

        /** The position of the next character to read. */
        std::size_t m_position = 0;

        /** The position of the first character of the token being read. */
        std::size_t m_lexeme_start_pos = 0;

        /** The end of the start-of-pattern options (*...) read so far, an option after it is not at the start. */
        std::size_t m_start_options_end = 0;

        /** True between '[' and the ']' closing the character class. */
        bool m_in_char_class = false;

        /** The position in the current element of the character class, if m_in_char_class is true. */
        ClassPosition m_class_position = ClassPosition::START;

        /** True inside quoted text \Q...\E. */
        bool m_in_quote = false;

        /**
         * @brief Make a token whose lexeme is the text from m_lexeme_start_pos to m_position.
         *
         * @param type    The type of the token.
         * @param payload The data of the token.
         */
        Token make_token(TokenType type, const TokenPayload& payload = {}) const;

        /**
         * @brief Throw a syntax error with @p message and the text of the token being read.
         */
        void throw_syntax_error(const std::string& message) const;

        /**
         * @brief Read a token outside character classes and quoted text.
         */
        Token get_token_standard();

        /**
         * @brief Read a token inside a character class.
         */
        Token get_token_char_class();

        /**
         * @brief Make the token of the single character @p ch inside a character class and update the position in the
         * class: the character can be the lower bound of a range, unless it is the upper bound of one.
         */
        Token make_class_literal_token(Z3Char ch);

        /**
         * @brief Check whether '[' at @p bracket_pos starts the syntax of a POSIX class, i.e., "[:", "[." or "[="
         * followed later by ":]", ".]" or "=]" with no ']' in between (check_posix_syntax() of PCRE2).
         *
         * @param bracket_pos The position of '['.
         * @param end         Set to the position of the terminating ":]", ".]" or "=]".
         * @return bool True if '[' starts the syntax of a POSIX class.
         */
        bool find_posix_class_end(std::size_t bracket_pos, std::size_t& end) const;

        /**
         * @brief Read a literal of quoted text \Q...\E, or move behind \E and read the token after it.
         */
        Token get_quoted_token();

        /**
         * @brief Read an escape sequence outside character classes, after '\'.
         */
        Token get_escape_sequence_token();

        /**
         * @brief Read an escape sequence inside a character class, after '\'.
         */
        Token get_char_class_escape_sequence_token();

        /**
         * @brief The character of the escape sequence whose first character after '\' is @p escaped (already read),
         * e.g., '\n' for 'n'.
         *
         * Reads the rest of the escape sequence, e.g., the digits of \x41.
         *
         * @param escaped       The first character after '\'.
         * @param in_char_class True inside a character class, where \b is a backspace, \1 to \7 start octal escapes
         *                      and \8, \9, \g and \k are the characters '8', '9', 'g' and 'k'.
         */
        Z3Char parse_escaped_char(Z3Char escaped, bool in_char_class);

        /**
         * @brief The character of \xh, \xhh (one or two hexadecimal digits) or \x{h...}, after "\x".
         */
        Z3Char parse_hex_escape();

        /**
         * @brief The character of the octal escape \d, \dd or \ddd (at most three octal digits).
         *
         * @param first_digit The first digit, already read.
         */
        Z3Char parse_octal_escape(Z3Char first_digit);

        /**
         * @brief The character of \cx, i.e., the control character of the printable ASCII character x, after "\c".
         */
        Z3Char parse_control_escape();

        /**
         * @brief The character of \N{U+h...}, i.e., the character with the given code point, after "\N".
         */
        Z3Char parse_unicode_name_escape();

        /**
         * @brief Read the digits of a code point in braces up to '}' and move behind it, e.g., "41}" of \x{41}.
         *
         * Spaces and tabs before '}' are skipped.
         * The code point must be a Unicode code point that is not a surrogate, as in the UTF modes of PCRE2.
         *
         * @param base The base of the digits, 8 or 16.
         */
        Z3Char parse_braced_code_point(unsigned base);

        /**
         * @brief Read \1, \2, ... after '\' outside a character class, which is a backreference or an octal escape.
         *
         * All the following digits are read as a decimal number.
         * If the number is less than 10, starts with 8 or 9, or is at most the number of capture groups opened so far,
         * the sequence is a backreference, otherwise it is an octal escape of at most three digits.
         *
         * @param first_digit The first digit, already read.
         */
        Token get_backreference_token(Z3Char first_digit);

        /**
         * @brief Read the token starting with '(' (already read), i.e., the start of a group or of a lookaround, or
         * flags.
         *
         * Comments (?#...) are skipped and the token after them is read.
         */
        Token get_group_token();

        /**
         * @brief Read the name of a capture group or of a named backreference and move behind its terminator.
         *
         * @param name_start The position of the first character of the name.
         * @param terminator The character after the name, e.g., '>' for (?<name>.
         * @return zstring_view The name, which is an ASCII identifier [A-Za-z_][A-Za-z0-9_]* of at most 128 characters.
         */
        zstring_view read_name(std::size_t name_start, Z3Char terminator);

        /**
         * @brief Read the start of a named capture group (?<name>, (?'name' or (?P<name>.
         *
         * @param name_start The position of the first character of the name.
         * @param terminator The character after the name, '>' or '\''.
         */
        Token get_named_group_token(std::size_t name_start, Z3Char terminator);

        /**
         * @brief Read the flags of (?flags) or (?flags:re) after "(?".
         */
        Token get_flags_token();

        /**
         * @brief Skip the comment (?#...) after "(?#".
         */
        void skip_comment();

        /**
         * @brief Read (*...) after '(': a start-of-pattern option, which produces no token, or an alphabetic name of a
         * lookaround or an atomic group, e.g., (*pla: or (*atomic:.
         *
         * "(*" that is not followed by a letter or ':' is the start of a capture group followed by the quantifier '*'.
         */
        Token get_verb_token();

        /**
         * @brief Check whether the pattern continues with the ASCII @p text at the position @p pos.
         */
        bool starts_with(std::size_t pos, std::string_view text) const;

        /**
         * @brief Read the quantifier *, + or ? and its mode.
         *
         * @param op The quantifier character, already read.
         */
        Token get_quantifier_token(Z3Char op);

        /**
         * @brief Read the quantifier {n}, {n,}, {n,m} or {,m} and its mode after '{'.
         *
         * A '{' that does not start one of them is a literal.
         */
        Token get_braced_quantifier_token();

        /**
         * @brief Read the numbers of {n}, {n,}, {n,m} or {,m} after '{' at @p pos and move @p pos behind '}'.
         *
         * Spaces and tabs are allowed around the numbers.
         *
         * @param pos   The position after '{', it is moved only if the text is a quantifier.
         * @param range The numbers of repetitions.
         * @return bool False if the text after '{' is not a quantifier.
         */
        bool parse_quantifier_range(std::size_t& pos, QuantifierRange& range) const;

        /**
         * @brief Read the '?' (lazy) or '+' (possessive) after a quantifier.
         *
         * @return QuantifierMode GREEDY if there is neither of them.
         */
        QuantifierMode read_quantifier_mode();

        /**
         * @brief Read a decimal number at @p pos into @p value and move @p pos behind it.
         *
         * A number that is too big to be a repetition count or a group number is read as a value larger than both.
         *
         * @return bool False if there is no digit at @p pos.
         */
        bool parse_integer(std::size_t& pos, uint64_t& value) const;

        /**
         * @brief Move @p pos behind the spaces and tabs at it, which are allowed inside braces.
         */
        void skip_blanks(std::size_t& pos) const;

        /**
         * @brief Check whether @p ch is a decimal digit.
         */
        static bool is_digit(Z3Char ch);

        /**
         * @brief Check whether @p ch is an octal digit.
         */
        static bool is_octal_digit(Z3Char ch);

        /**
         * @brief Check whether @p ch is an ASCII upper case letter.
         */
        static bool is_upper(Z3Char ch);

        /**
         * @brief Check whether @p ch is an ASCII lower case letter.
         */
        static bool is_lower(Z3Char ch);

        /**
         * @brief Check whether @p ch is an ASCII letter or a decimal digit.
         */
        static bool is_alnum(Z3Char ch);

        /**
         * @brief The value of the hexadecimal digit @p ch, or -1 if @p ch is no hexadecimal digit.
         */
        static int hex_value(Z3Char ch);
    };

    // =============== PCRE2 REGEX PARSER ===============

    /**
     * Recursive descent parser for PCRE2 regex syntax.
     * Consumes tokens from PCRE2Lexer and builds the common AST.
     * The grammar is:
     *   disjunction  -> alternative ('|' alternative)*
     *   alternative  -> (term | flags)*
     *   term         -> assertion | atom quantifier?
     *   atom         -> literal | dot | class_escape | newline_sequence | backref | group | lookaround | char_class
     *
     * The PCRE2 constructs are translated into the primitives of the common AST while parsing, i.e., literals, the
     * dot, character classes and class escapes into character sets, word boundaries and the anchors of lines into
     * lookarounds, and non-capturing groups into their subpatterns.
     * The flags hold until the end of the enclosing group (also in the following alternatives), the flags of
     * (?flags:re) only in re.
     *
     * PCRE2 matches by backtracking like Perl, so captures are kept from one iteration of a repetition to the next and
     * an iteration matching the empty string ends the repetition but does not fail.
     * A backreference to an unset capture group fails.
     *
     * Unsupported: case-insensitive matching (flag i), extended syntax (flags x, xx), capture groups with the same name
     * (flag J), Unicode properties (\p, \P, \X), \C, \K, \G, recursion and subroutine calls ((?R), (?1), (?&name),
     * \g<1>), conditional groups, callouts, backtracking control verbs, branch reset groups (?|...), non-atomic
     * lookarounds, script runs, extended character classes (?[...]), the POSIX word boundaries [[:<:]] and [[:>:]],
     * non-ASCII names of capture groups and the start-of-pattern options that change the semantics (e.g., (*UCP),
     * (*CR)).
     * The flags r and a are accepted, they have no effect without the flag i and without PCRE2_UCP.
     *
     * Not implemented yet: backreferences, lookarounds, atomic groups and possessive quantifiers.
     */
    class PCRE2Parser {
    public:
        /**
         * @brief Create a parser of the pattern @p regex and read its first token.
         */
        explicit PCRE2Parser(const zstring_view regex)
            : m_lexer(regex),
              m_current_token(m_lexer.get_next_token()) { }

        /**
         * @brief Parse the whole pattern into the common AST.
         *
         * Throws a syntax error for invalid patterns and an "Unsupported" error for unsupported constructs.
         *
         * @return NodeRef The root of the AST.
         */
        NodeRef parse();

    private:
        /** The lexer of the pattern. */
        PCRE2Lexer m_lexer;

        /** The token being parsed. */
        Token m_current_token;

        /** The ID of the last capture group opened, the groups are numbered from 1 by their opening parentheses. */
        GroupID m_current_group_id = 0;

        /** The flags holding at the current token, see Flag. */
        uint16_t m_flags = 0;

        /** The IDs of the named capture groups read so far. */
        std::unordered_map<zstring_view, GroupID> m_named_groups {};

        /**
         * @brief Move to the next token.
         */
        void next();

        /**
         * @brief Move to the next token if the current token has the type @p type.
         *
         * @return bool True if the current token has the type @p type.
         */
        bool match(TokenType type);

        /**
         * @brief Throw a syntax error with @p message and the text of the current token.
         */
        void throw_syntax_error(const std::string& message) const;

        /**
         * @brief Set and clear the flags in m_flags by @p changes.
         *
         * Throws an "Unsupported" error if an unsupported flag is set.
         */
        void apply_flags(FlagChanges changes);

        /**
         * @brief Parse alternatives separated by '|'.
         */
        NodeRef parse_disjunction();

        /**
         * @brief Parse the terms of an alternative up to '|', ')' or the end of the pattern, (?flags) on the way change
         * the flags.
         */
        NodeRef parse_alternative();

        /**
         * @brief Parse an assertion, or an atom with its quantifier if it has one.
         */
        NodeRef parse_term();

        /**
         * @brief Make a repetition of @p term if a quantifier follows, otherwise return @p term.
         */
        NodeRef parse_maybe_quantifier(NodeRef term);

        /**
         * @brief Translate the current assertion into anchors and lookarounds.
         */
        NodeRef parse_assertion();

        /**
         * @brief Parse a literal, the dot, a class escape, \R, a backreference, a group, a lookaround or a character
         * class.
         */
        NodeRef parse_atom();

        /**
         * @brief Parse a capture group, a named capture group, a non-capturing group (with its flags) or an atomic
         * group.
         */
        NodeRef parse_group();

        /**
         * @brief Parse a lookahead or a lookbehind.
         */
        NodeRef parse_lookaround();

        /**
         * @brief Resolve the current backreference to the ID of its capture group.
         */
        NodeRef parse_backreference();

        /**
         * @brief Parse a character class [...] into the set of its characters.
         */
        NodeRef parse_character_class();

        /**
         * @brief \w and the word characters of \b, i.e., [0-9A-Za-z_].
         */
        static CharSet word_chars();

        /**
         * @brief \s, i.e., [\t\n\v\f\r ].
         */
        static CharSet space_chars();

        /**
         * @brief \h, i.e., U+0009, U+0020, U+00A0, U+1680, U+180E, U+2000-U+200A, U+202F, U+205F and U+3000.
         */
        static CharSet horizontal_space_chars();

        /**
         * @brief \v, i.e., U+000A-U+000D, U+0085, U+2028 and U+2029.
         */
        static CharSet vertical_space_chars();

        /**
         * @brief The characters of the class escape \d, \D, \h, \H, \s, \S, \v, \V, \w, \W or \N given by its letter
         * @p escape.
         */
        static CharSet class_escape_chars(Z3Char escape);

        /**
         * @brief The characters of the POSIX class [:name:] with the given @p name, or nothing for an unknown name.
         */
        static std::optional<CharSet> posix_class_chars(const std::string& name);

        /**
         * @brief Make \R, which matches \r\n or a single vertical space character.
         *
         * \R is atomic, so \r does not match alone if \n follows: \r\n|\r(?!\n)|[\n\v\f\x85\x{2028}\x{2029}].
         */
        static NodeRef make_newline_sequence();

        /**
         * @brief Make ^, which matches at the start of the text, or with the flag m also after a \n that is not at the
         * end of the text: \A|(?<=\n)(?=[^]).
         */
        static NodeRef make_circumflex(bool is_multi_line);

        /**
         * @brief Make $ (and \Z if @p is_multi_line is false), which matches at the end of the text or before a \n at
         * the end of the text, (?![^\n]|\n[^]), or with the flag m also before any \n.
         */
        static NodeRef make_dollar(bool is_multi_line);
    };
}  // namespace smt::noodler::extended_regex::pcre2
