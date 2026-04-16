#!/bin/bash
# =============================================================================
# ECMAScript Regex Test Suite for Z3-Noodler
# =============================================================================
# Tests the re.from_ecma2020 SMT-LIB2 extension using the Noodler string
# solver.  Each test writes one .smt2 file, runs Z3 with a per-test timeout,
# and checks whether the solver output matches the expected status.
#
# Known unsupported features (no tests for these):
#   - Backreferences inside quantifier loops
#   - Lookarounds inside quantifier loops
#   - Nested lookarounds
#
# Usage:
#   bash run_ecma_tests.sh
#   Z3_BIN=/path/to/z3 bash run_ecma_tests.sh
# =============================================================================

# --- CONFIGURATION ---
Z3_BIN=${Z3_BIN:-"cmake-build-debug/z3"}
TEST_DIR="ecma_automated_tests"
TIMEOUT=30          # per-test wall-clock timeout (seconds)

# Clean and recreate the test output directory
rm -rf "$TEST_DIR"
mkdir -p "$TEST_DIR"

echo "Generating SMT-LIB2 tests into: $TEST_DIR"

# =============================================================================
# HELPER: write one .smt2 test file
#
# Usage: make_test <id_name> <sat|unsat> <ecma_regex> <extra_smt_assertions>
#
# Bash escaping conventions for the regex argument (double-quoted strings):
#   \\d   →  \d  in SMT  (digit shorthand)
#   \\w   →  \w  in SMT  (word shorthand)
#   \\s   →  \s  in SMT  (space shorthand)
#   \\b   →  \b  in SMT  (word boundary)
#   \\1   →  \1  in SMT  (backreference)
#   \\.   →  \.  in SMT  (escaped dot → literal '.')
# =============================================================================
make_test() {
    local name=$1
    local expected=$2
    local regex=$3
    local asserts=$4
    cat <<EOF > "$TEST_DIR/$name.smt2"
(set-logic QF_S)
(set-info :status $expected)
(declare-const w String)
(assert (str.in_re w (re.from_ecma2020 "$regex")))
$asserts
(check-sat)
EOF
}

# =============================================================================
# TEST CASES
# =============================================================================

# ---------------------------------------------------------------------------
# 1. Basic Literals
# ---------------------------------------------------------------------------
make_test "001_literal_sat"          "sat"   "abc"   "(assert (= (str.len w) 3))"
make_test "002_literal_unsat"        "unsat" "abc"   "(assert (= (str.len w) 4))"
# Escaped metacharacter '.' must be treated as a literal period, not wildcard
make_test "003_escaped_dot_sat"      "sat"   "a\\.b" "(assert (= w \"a.b\"))"
make_test "004_escaped_dot_unsat"    "unsat" "a\\.b" "(assert (= w \"axb\"))"
# Escaped backslash: \\ in the regex matches a single '\'
make_test "005_escaped_backslash_sat"   "sat"   "a\\\\b" "(assert (= w \"a\\b\"))"
make_test "006_escaped_backslash_unsat" "unsat" "a\\\\b" "(assert (= w \"ab\"))"

# ---------------------------------------------------------------------------
# 2. Dot Metacharacter  (matches any character except newline \n)
# ---------------------------------------------------------------------------
# Dot must consume exactly one character
make_test "007_dot_one_char_sat"     "sat"   "a.b"   \
    "(assert (= (str.len w) 3)) (assert (= w \"axb\"))"
make_test "008_dot_too_short_unsat"  "unsat" "a.b"   "(assert (= w \"ab\"))"
make_test "009_dot_too_long_unsat"   "unsat" "a.b"   "(assert (= w \"axyb\"))"
# Dot repeated with + covers arbitrary single-char sequences
make_test "010_dot_plus_sat"         "sat"   ".+"    "(assert (= (str.len w) 5))"
make_test "011_dot_plus_empty_unsat" "unsat" ".+"    "(assert (= w \"\"))"

# ---------------------------------------------------------------------------
# 3. Character Classes
# ---------------------------------------------------------------------------
make_test "012_charclass_sat"            "sat"   "[a-z]"          "(assert (= (str.len w) 1))"
make_test "013_charclass_unsat"          "unsat" "[a-z]"          "(assert (= w \"A\"))"
make_test "014_charclass_negated_sat"    "sat"   "[^a-z]"         "(assert (= w \"A\"))"
make_test "015_charclass_negated_unsat"  "unsat" "[^a-z]"         "(assert (= w \"m\"))"
# Multiple ranges in one class
make_test "016_charclass_multi_sat"      "sat"   "[a-zA-Z0-9_]+"  "(assert (= w \"Hello_World42\"))"
make_test "017_charclass_multi_unsat"    "unsat" "[a-zA-Z0-9_]+"  "(assert (= w \"hello world\"))"
# Class with a single explicit member list
make_test "018_charclass_explicit_sat"   "sat"   "[aeiou]+"       "(assert (= w \"aeiouaioeu\"))"
make_test "019_charclass_explicit_unsat" "unsat" "[aeiou]"        "(assert (= w \"b\"))"
# Complex negated class (original "monster" test — exercises the full parser)
make_test "020_monster_class_unsat"      "unsat" "[^\\]\\--/a-z^\\b--\\0-\\37\\cZ]" \
    "(assert (or (= w \"-\") (= w \"a\") (= w \"]\")))"

# ---------------------------------------------------------------------------
# 4. Shorthand Character Classes  \d \D \w \W \s \S
# ---------------------------------------------------------------------------
make_test "021_digit_sat"        "sat"   "\\d+"  "(assert (= w \"12345\"))"
make_test "022_digit_unsat"      "unsat" "\\d+"  "(assert (= w \"abc\"))"
make_test "023_nondigit_sat"     "sat"   "\\D"   "(assert (= w \"x\"))"
make_test "024_nondigit_unsat"   "unsat" "\\D"   "(assert (= w \"5\"))"
make_test "025_word_sat"         "sat"   "\\w+"  "(assert (= w \"hello_42\"))"
make_test "026_word_unsat"       "unsat" "\\w"   "(assert (= w \"!\"))"
make_test "027_nonword_sat"      "sat"   "\\W"   "(assert (= w \"@\"))"
make_test "028_nonword_unsat"    "unsat" "\\W"   "(assert (= w \"a\"))"
make_test "029_space_sat"        "sat"   "\\s"   "(assert (= w \" \"))"
make_test "030_space_unsat"      "unsat" "\\s"   "(assert (= w \"a\"))"
make_test "031_nonspace_sat"     "sat"   "\\S+"  "(assert (= w \"hello\"))"
make_test "032_nonspace_unsat"   "unsat" "\\S"   "(assert (= w \" \"))"
# Mixed shorthands in sequence: digit, space, word-char
make_test "033_mixed_shorthands_sat"   "sat"   "\\d\\s\\w" \
    "(assert (= w \"5 x\"))"
make_test "034_mixed_shorthands_unsat" "unsat" "\\d\\s\\w" \
    "(assert (= w \"5x \"))"   # wrong order: space and word-char swapped

# ---------------------------------------------------------------------------
# 5. Alternation
# ---------------------------------------------------------------------------
make_test "035_alternation_sat"          "sat"   "a|b|c"        "(assert (= w \"b\"))"
make_test "036_alternation_unsat"        "unsat" "a|b|c"        "(assert (= w \"d\"))"
make_test "037_alternation_words_sat"    "sat"   "cat|dog|bird" "(assert (= w \"bird\"))"
make_test "038_alternation_words_unsat"  "unsat" "cat|dog|bird" "(assert (= w \"fish\"))"
# Alternatives of different lengths — verifies parser doesn't confuse them
make_test "039_alternation_lengths_sat"  "sat"   "a|ab|abc"     "(assert (= w \"ab\"))"
# Empty left branch = empty-string alternative
make_test "040_alternation_empty_sat"    "sat"   "|a"           "(assert (= w \"\"))"
make_test "041_alternation_empty_unsat"  "unsat" "|a"           "(assert (= w \"b\"))"

# ---------------------------------------------------------------------------
# 6. Quantifiers (greedy)
# ---------------------------------------------------------------------------
make_test "042_star_empty_sat"     "sat"   "a*"     "(assert (= w \"\"))"
make_test "043_star_many_sat"      "sat"   "a*"     "(assert (= (str.len w) 7))"
make_test "044_plus_sat"           "sat"   "a+"     "(assert (= (str.len w) 5))"
make_test "045_plus_empty_unsat"   "unsat" "a+"     "(assert (= w \"\"))"
make_test "046_question_zero_sat"  "sat"   "ab?"    "(assert (= w \"a\"))"
make_test "047_question_one_sat"   "sat"   "ab?"    "(assert (= w \"ab\"))"
make_test "048_question_two_unsat" "unsat" "ab?"    "(assert (= w \"abb\"))"
make_test "049_exact_sat"          "sat"   "a{3}"   "(assert (= w \"aaa\"))"
make_test "050_exact_unsat"        "unsat" "a{3}"   "(assert (= w \"aa\"))"
make_test "051_range_sat"          "sat"   "a{2,4}" "(assert (= (str.len w) 3))"
make_test "052_range_unsat"        "unsat" "a{2,4}" "(assert (= (str.len w) 5))"
make_test "053_open_range_sat"     "sat"   "a{3,}"  "(assert (= (str.len w) 10))"
make_test "054_open_range_unsat"   "unsat" "a{3,}"  "(assert (= (str.len w) 2))"

# ---------------------------------------------------------------------------
# 7. Lazy Quantifiers
# In str.in_re (full-match) semantics, lazy and greedy describe the same
# language; these tests verify that lazy syntax is parsed without errors.
# ---------------------------------------------------------------------------
make_test "057_lazy_star_sat"      "sat"   "a*?b"     "(assert (= w \"aaab\"))"
make_test "058_lazy_plus_sat"      "sat"   "a+?b"     "(assert (= w \"ab\"))"
make_test "059_lazy_plus_unsat"    "unsat" "a+?b"     "(assert (= w \"b\"))"    # needs ≥1 'a'
make_test "060_lazy_range_sat"     "sat"   "a{2,4}?b" "(assert (= w \"aaab\"))"
make_test "061_lazy_range_unsat"   "unsat" "a{2,4}?b" "(assert (= w \"b\"))"   # fewer than 2 'a's
# Optional 'u' (British/American spelling) — lazy ?? vs greedy ?  same language
make_test "062_lazy_question_sat"  "sat"   "colou??r" "(assert (= w \"color\"))"
make_test "063_lazy_question2_sat" "sat"   "colou??r" "(assert (= w \"colour\"))"

# ---------------------------------------------------------------------------
# 8. Non-capturing Groups  (?:...)
# ---------------------------------------------------------------------------
make_test "064_noncap_sat"               "sat"   "(?:ab)+"         "(assert (= w \"ababab\"))"
make_test "065_noncap_unsat"             "unsat" "(?:ab)+"         "(assert (= w \"abba\"))"
make_test "066_noncap_alternation_sat"   "sat"   "(?:foo|bar)baz"  "(assert (= w \"barbaz\"))"
make_test "067_noncap_alternation_unsat" "unsat" "(?:foo|bar)baz"  "(assert (= w \"quxbaz\"))"
# Two levels of non-capturing nesting
make_test "068_nested_noncap_sat"        "sat"   "(?:a(?:b|c))+"   "(assert (= w \"abacab\"))"
make_test "069_nested_noncap_unsat"      "unsat" "(?:a(?:b|c))+"   "(assert (= w \"aa\"))"
# Non-capturing group with exact quantifier
make_test "070_noncap_exact_sat"         "sat"   "(?:ab){3}"       "(assert (= w \"ababab\"))"
make_test "071_noncap_exact_unsat"       "unsat" "(?:ab){3}"       "(assert (= w \"abab\"))"

# ---------------------------------------------------------------------------
# 9. Capture Groups and Backreferences
# Restriction: backreferences inside quantifier loops are NOT supported.
# ---------------------------------------------------------------------------
# Group 1 repeated immediately → doubled character
make_test "072_backref_char_sat"       "sat"   "([a-z])\\1"           "(assert (= (str.len w) 2))"
make_test "073_backref_char_unsat"     "unsat" "([a-z])\\1"           "(assert (= w \"ab\"))"
# Word repeated after a space
make_test "074_backref_word_sat"       "sat"   "(\\w+) \\1"           "(assert (= w \"hello hello\"))"
make_test "075_backref_word_unsat"     "unsat" "(\\w+) \\1"           "(assert (= w \"hello world\"))"
# Two independent groups, both backreferenced → XYXY pattern
make_test "076_two_backrefs_sat"       "sat"   "([a-c])([0-2])\\1\\2" "(assert (= w \"a1a1\"))"
make_test "077_two_backrefs_unsat"     "unsat" "([a-c])([0-2])\\1\\2" "(assert (= w \"a1b1\"))"
# Four-character palindrome: (X)(Y)\2\1 → abba-style
make_test "078_palindrome4_sat"        "sat"   "(.)(.)\\2\\1"          "(assert (= w \"abba\"))"
make_test "079_palindrome4_unsat"      "unsat" "(.)(.)\\2\\1"          "(assert (= w \"abcd\"))"
# Group 1 used as separator in a triple: word-digit-word where start == end
make_test "080_symmetric_key_sat"      "sat"   "([a-z]+)-\\d+-\\1"    \
    "(assert (= w \"abc-123-abc\"))"
make_test "081_symmetric_key_unsat"    "unsat" "([a-z]+)-\\d+-\\1"    \
    "(assert (= w \"abc-123-def\"))"

# ---------------------------------------------------------------------------
# 10. Named Capture Groups and Named Backreferences  (?<name>...)  \k<name>
# ---------------------------------------------------------------------------
# Named groups used for readability — date format YYYY-MM-DD
make_test "082_named_date_sat"    "sat"   "(?<year>\\d{4})-(?<month>\\d{2})-(?<day>\\d{2})" \
    "(assert (= w \"2024-01-15\"))"
make_test "083_named_date_unsat"  "unsat" "(?<year>\\d{4})-(?<month>\\d{2})-(?<day>\\d{2})" \
    "(assert (= w \"2024-1-15\"))"   # single-digit month fails \d{2}
# Named backreference: same lowercase letter at start and end
make_test "084_named_backref_sat"    "sat"   "(?<ch>[a-z])\\k<ch>"    \
    "(assert (= (str.len w) 2))"
make_test "085_named_backref_unsat"  "unsat" "(?<ch>[a-z])\\k<ch>"    \
    "(assert (= w \"ab\"))"
# Named group with literal between group and backreference
make_test "086_named_backref_mid_sat"   "sat"   "(?<letter>[a-z])x\\k<letter>" \
    "(assert (= w \"axa\"))"
make_test "087_named_backref_mid_unsat" "unsat" "(?<letter>[a-z])x\\k<letter>" \
    "(assert (= w \"axb\"))"

# ---------------------------------------------------------------------------
# 11. Anchors  ^ and $
# ---------------------------------------------------------------------------
# In str.in_re full-match semantics anchors are implicit, but must still parse
make_test "088_anchor_sat"   "sat"   "^abc\$" "(assert (= w \"abc\"))"
make_test "089_anchor_unsat" "unsat" "^abc\$" "(assert (= w \"xabcx\"))"
# Anchor-only patterns
make_test "090_anchor_empty_sat"   "sat"   "^\$"  "(assert (= w \"\"))"
make_test "091_anchor_empty_unsat" "unsat" "^\$"  "(assert (= (str.len w) 1))"

# ---------------------------------------------------------------------------
# 12. Word Boundaries  \b  \B
# ---------------------------------------------------------------------------
# \bword\b must match the exact string "word"
make_test "092_word_boundary_sat"        "sat"   "\\bword\\b"   "(assert (= w \"word\"))"
# 'a' and 'w' are both word characters — no boundary between them
make_test "093_word_boundary_unsat"      "unsat" "a\\bword"     "(assert (= w \"aword\"))"
# All-digit string forms a word token under \b
make_test "094_word_boundary_digits_sat" "sat"   "\\b\\d+\\b"   "(assert (= w \"42\"))"
# No word boundary inside a run of word characters
make_test "095_word_boundary_mid_unsat"  "unsat" "\\w\\b\\w"    \
    "(assert (= w \"ab\"))"  # 'a' and 'b' are both \w → no \b between them

# ---------------------------------------------------------------------------
# 13. Lookaheads  (nested lookarounds are NOT supported)
# ---------------------------------------------------------------------------
# Positive: consume 'a', assert 'b' follows, then consume 'b' → matches "ab"
make_test "096_pos_lookahead_sat"        "sat"   "a(?=b)b"       "(assert (= w \"ab\"))"
# Negative contradiction: consume 'a', assert 'b' does NOT follow,
# but the pattern then requires 'b' → always unsat
make_test "097_neg_lookahead_unsat"      "unsat" "a(?!b)b"       "(assert (= w \"ab\"))"
# Lookahead as a "peek-then-consume" guard on a suffix
make_test "098_pos_lookahead_unit_sat"   "sat"   "\\d+(?=px)"    "(assert (= w \"12px\"))"
make_test "099_pos_lookahead_unit_unsat" "unsat" "\\d+(?=px)"    "(assert (= w \"12em\"))"
# Negative lookahead: digits NOT immediately followed by "px"
# In full-match mode the whole string must be consumed, so w is just digits
make_test "100_neg_lookahead_sat"       "sat"   "\\d+(?!px)"    "(assert (= w \"42\"))"
make_test "101_neg_lookahead_unsat"     "unsat" "\\d+(?!px)"    "(assert (= w \"42px\"))"
# Lookahead used to enforce a non-trivial constraint on remaining input
make_test "102_lookahead_nonempty_sat"  "sat"   "(?=.{4,})\\w+" \
    "(assert (= (str.len w) 5))"   # at least 4 chars total, all word chars
make_test "103_lookahead_nonempty_unsat" "unsat" "(?=.{4,})\\w+" \
    "(assert (= w \"hi\"))"         # too short to pass the lookahead

# ---------------------------------------------------------------------------
# 14. Complex / Realistic Patterns
# ---------------------------------------------------------------------------

# -- Date: YYYY-MM-DD --
make_test "104_date_sat"   "sat"   "\\d{4}-\\d{2}-\\d{2}" "(assert (= w \"2024-01-15\"))"
make_test "105_date_unsat" "unsat" "\\d{4}-\\d{2}-\\d{2}" "(assert (= w \"2024-1-5\"))"

# -- Simplified IPv4 (syntax only, no range check on octet values) --
make_test "106_ipv4_sat"   "sat"   "\\d{1,3}\\.\\d{1,3}\\.\\d{1,3}\\.\\d{1,3}" \
    "(assert (= w \"192.168.1.1\"))"
make_test "107_ipv4_unsat" "unsat" "\\d{1,3}\\.\\d{1,3}\\.\\d{1,3}\\.\\d{1,3}" \
    "(assert (= w \"192.168.1\"))"   # only three octets

# -- Simplified email: local@domain.tld --
make_test "108_email_sat"   "sat"   "[a-z0-9]+@[a-z0-9]+\\.[a-z]{2,}" \
    "(assert (= w \"user@example.com\"))"
make_test "109_email_unsat" "unsat" "[a-z0-9]+@[a-z0-9]+\\.[a-z]{2,}" \
    "(assert (= w \"user@example\"))"   # missing TLD

# -- Hex colour code: #RRGGBB --
make_test "110_hex_color_sat"   "sat"   "#[0-9a-fA-F]{6}" "(assert (= w \"#ff00aa\"))"
make_test "111_hex_color_unsat" "unsat" "#[0-9a-fA-F]{6}" "(assert (= w \"#ff00\"))"

# -- C / JS identifier: starts with letter or _, followed by letters/digits/_ --
make_test "112_identifier_sat"   "sat"   "[a-zA-Z_][a-zA-Z0-9_]*" "(assert (= w \"_myVar123\"))"
make_test "113_identifier_unsat" "unsat" "[a-zA-Z_][a-zA-Z0-9_]*" "(assert (= w \"123abc\"))"

# -- URL prefix: http or https followed by :// and a non-whitespace host --
make_test "114_url_sat"   "sat"   "https?://\\S+" "(assert (= w \"https://example.com\"))"
make_test "115_url_unsat" "unsat" "https?://\\S+" "(assert (= w \"ftp://example.com\"))"

# -- Signed integer (optional leading +/-) --
make_test "116_signed_int_sat"   "sat"   "[+-]?\\d+" "(assert (= w \"-42\"))"
make_test "117_signed_int_unsat" "unsat" "[+-]?\\d+" "(assert (= w \"--42\"))"

# -- CSS-style dimension value: number followed by a unit --
make_test "118_css_dimension_sat"   "sat"   "\\d+(\\.\\d+)?(px|em|rem|%)" \
    "(assert (= w \"1.5rem\"))"
make_test "119_css_dimension_unsat" "unsat" "\\d+(\\.\\d+)?(px|em|rem|%)" \
    "(assert (= w \"1.5vh\"))"   # 'vh' not in the unit set

# -- Semantic version (major.minor.patch) --
make_test "120_semver_sat"   "sat"   "\\d+\\.\\d+\\.\\d+" "(assert (= w \"2.10.3\"))"
make_test "121_semver_unsat" "unsat" "\\d+\\.\\d+\\.\\d+" "(assert (= w \"2.10\"))"

# -- Repeating word-digit pair: (word digit){2,} --
make_test "122_repeat_pair_sat"   "sat"   "([a-z]+\\d)+" "(assert (= w \"abc1def2\"))"
make_test "123_repeat_pair_unsat" "unsat" "([a-z]+\\d)+" "(assert (= w \"abc\"))"

# -- Password-strength pattern: ≥8 chars, contains digit, letter, special --
# Implemented as: lookahead for digit, lookahead for letter, then ≥8 any-chars
make_test "124_password_sat"   "sat"   "(?=.*\\d)(?=.*[a-z]).{8,}" \
    "(assert (= w \"hello123\"))"
make_test "125_password_unsat" "unsat" "(?=.*\\d)(?=.*[a-z]).{8,}" \
    "(assert (= w \"hello123\")) (assert (= (str.len w) 5))"  # too short (len constraint overrides)

# =============================================================================
# TEST RUNNER
# =============================================================================
echo "Running ${TIMEOUT}s-timeout tests..."
echo "=================================================="

PASSED=0
FAILED=0
TIMED_OUT=0
TOTAL=0

for test_file in "$TEST_DIR"/*.smt2; do
    TOTAL=$((TOTAL + 1))

    # Extract expected result from the :status annotation
    EXPECTED=$(grep ":status" "$test_file" | awk '{print $3}' | tr -d ')')

    # Run Z3 with a hard wall-clock timeout
    OUTPUT=$(timeout "$TIMEOUT" "$Z3_BIN" smt.string_solver=noodler "$test_file" 2>&1)
    EXIT_CODE=$?

    # Determine outcome
    if [ "$EXIT_CODE" -eq 124 ]; then
        RESULT="timeout"
    elif echo "$OUTPUT" | grep -q "^unsat$"; then
        RESULT="unsat"
    elif echo "$OUTPUT" | grep -q "^sat$"; then
        RESULT="sat"
    else
        RESULT="unknown"
    fi

    NAME=$(basename "$test_file" .smt2)

    if [ "$RESULT" = "$EXPECTED" ]; then
        echo -e "[\033[32mPASS\033[0m] $NAME"
        PASSED=$((PASSED + 1))
    elif [ "$RESULT" = "timeout" ]; then
        echo -e "[\033[33mTIME\033[0m] $NAME  (limit: ${TIMEOUT}s)"
        TIMED_OUT=$((TIMED_OUT + 1))
    else
        echo -e "[\033[31mFAIL\033[0m] $NAME"
        printf  "       Expected : %s\n" "$EXPECTED"
        printf  "       Got      : %s\n" "$RESULT"
        if [ "$RESULT" = "unknown" ]; then
            echo "       Z3 output (first 5 lines):"
            echo "$OUTPUT" | head -5 | sed 's/^/         /'
        fi
        FAILED=$((FAILED + 1))
    fi
done

echo "=================================================="
printf "Results: %d passed  %d failed  %d timed out  (total: %d)\n" \
    "$PASSED" "$FAILED" "$TIMED_OUT" "$TOTAL"

[ "$PASSED" -eq "$TOTAL" ] && exit 0 || exit 1