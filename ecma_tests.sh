#!/bin/bash
# =============================================================================
# ECMAScript Regex Test Suite for Z3-Noodler
# Tests the re.from_ecma2020 SMT-LIB2 extension using the Noodler string solver.
#
# Known unsupported features:
#   - Backreferences inside quantifier loops
#   - Lookarounds inside quantifier loops
#   - Capture groups inside quantifier loops
# =============================================================================

Z3_BIN=${Z3_BIN:-"cmake-build-debug/z3"}
TEST_DIR="ecma_automated_tests"
TIMEOUT=30

rm -rf "$TEST_DIR"
mkdir -p "$TEST_DIR"

# Usage: make_test <id_name> <sat|unsat> <ecma_regex> <extra_smt_assertions>
make_test() {
    local name=$1 expected=$2 regex=$3 asserts=$4
    cat <<EOF > "$TEST_DIR/$name.smt2"
(set-logic QF_S)
(set-info :status $expected)
(declare-const w String)
(assert (str.in_re w (re.from_ecma2020 "$regex")))
$asserts
(check-sat)
EOF
}

# --- 1. Basic Literals ---
make_test "001_literal_sat"             "sat"   "abc"    "(assert (= (str.len w) 3))"
make_test "002_literal_unsat"           "unsat" "abc"    "(assert (= (str.len w) 4))"
make_test "003_escaped_dot_sat"         "sat"   "a\\.b"  "(assert (= w \"a.b\"))"
make_test "004_escaped_dot_unsat"       "unsat" "a\\.b"  "(assert (= w \"axb\"))"
make_test "005_escaped_backslash_sat"   "sat"   "a\\\\b" "(assert (= w \"a\\b\"))"
make_test "006_escaped_backslash_unsat" "unsat" "a\\\\b" "(assert (= w \"ab\"))"

# --- 2. Dot Metacharacter ---
make_test "007_dot_one_char_sat"     "sat"   "a.b" "(assert (= (str.len w) 3)) (assert (= w \"axb\"))"
make_test "008_dot_too_short_unsat"  "unsat" "a.b" "(assert (= w \"ab\"))"
make_test "009_dot_too_long_unsat"   "unsat" "a.b" "(assert (= w \"axyb\"))"
make_test "010_dot_plus_sat"         "sat"   ".+"  "(assert (= (str.len w) 5))"
make_test "011_dot_plus_empty_unsat" "unsat" ".+"  "(assert (= w \"\"))"

# --- 3. Character Classes ---
make_test "012_charclass_sat"            "sat"   "[a-z]"           "(assert (= (str.len w) 1))"
make_test "013_charclass_unsat"          "unsat" "[a-z]"           "(assert (= w \"A\"))"
make_test "014_charclass_negated_sat"    "sat"   "[^a-z]"          "(assert (= w \"A\"))"
make_test "015_charclass_negated_unsat"  "unsat" "[^a-z]"          "(assert (= w \"m\"))"
make_test "016_charclass_multi_sat"      "sat"   "[a-zA-Z0-9_]+"   "(assert (= w \"Hello_World42\"))"
make_test "017_charclass_multi_unsat"    "unsat" "[a-zA-Z0-9_]+"   "(assert (= w \"hello world\"))"
make_test "018_charclass_explicit_sat"   "sat"   "[aeiou]+"        "(assert (= w \"aeiouaioeu\"))"
make_test "019_charclass_explicit_unsat" "unsat" "[aeiou]"         "(assert (= w \"b\"))"
make_test "020_monster_class_unsat"      "unsat" "[^\\]\\--/a-z^\\b--\\0-\\37\\cZ]" "(assert (or (= w \"-\") (= w \"a\") (= w \"]\")))"

# --- 4. Shorthand Character Classes ---
make_test "021_digit_sat"              "sat"   "\\d+"      "(assert (= w \"12345\"))"
make_test "022_digit_unsat"            "unsat" "\\d+"      "(assert (= w \"abc\"))"
make_test "023_nondigit_sat"           "sat"   "\\D"       "(assert (= w \"x\"))"
make_test "024_nondigit_unsat"         "unsat" "\\D"       "(assert (= w \"5\"))"
make_test "025_word_sat"               "sat"   "\\w+"      "(assert (= w \"hello_42\"))"
make_test "026_word_unsat"             "unsat" "\\w"       "(assert (= w \"!\"))"
make_test "027_nonword_sat"            "sat"   "\\W"       "(assert (= w \"@\"))"
make_test "028_nonword_unsat"          "unsat" "\\W"       "(assert (= w \"a\"))"
make_test "029_space_sat"              "sat"   "\\s"       "(assert (= w \" \"))"
make_test "030_space_unsat"            "unsat" "\\s"       "(assert (= w \"a\"))"
make_test "031_nonspace_sat"           "sat"   "\\S+"      "(assert (= w \"hello\"))"
make_test "032_nonspace_unsat"         "unsat" "\\S"       "(assert (= w \" \"))"
make_test "033_mixed_shorthands_sat"   "sat"   "\\d\\s\\w" "(assert (= w \"5 x\"))"
make_test "034_mixed_shorthands_unsat" "unsat" "\\d\\s\\w" "(assert (= w \"5x \"))"

# --- 5. Alternation ---
make_test "035_alternation_sat"         "sat"   "a|b|c"        "(assert (= w \"b\"))"
make_test "036_alternation_unsat"       "unsat" "a|b|c"        "(assert (= w \"d\"))"
make_test "037_alternation_words_sat"   "sat"   "cat|dog|bird" "(assert (= w \"bird\"))"
make_test "038_alternation_words_unsat" "unsat" "cat|dog|bird" "(assert (= w \"fish\"))"
make_test "039_alternation_lengths_sat" "sat"   "a|ab|abc"     "(assert (= w \"ab\"))"
make_test "040_alternation_empty_sat"   "sat"   "|a"           "(assert (= w \"\"))"
make_test "041_alternation_empty_unsat" "unsat" "|a"           "(assert (= w \"b\"))"

# --- 6. Quantifiers ---
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

# --- 7. Lazy Quantifiers ---
make_test "055_lazy_star_sat"      "sat"   "a*?b"     "(assert (= w \"aaab\"))"
make_test "056_lazy_plus_sat"      "sat"   "a+?b"     "(assert (= w \"ab\"))"
make_test "057_lazy_plus_unsat"    "unsat" "a+?b"     "(assert (= w \"b\"))"
make_test "058_lazy_range_sat"     "sat"   "a{2,4}?b" "(assert (= w \"aaab\"))"
make_test "059_lazy_range_unsat"   "unsat" "a{2,4}?b" "(assert (= w \"b\"))"
make_test "060_lazy_question_sat"  "sat"   "colou??r" "(assert (= w \"color\"))"
make_test "061_lazy_question2_sat" "sat"   "colou??r" "(assert (= w \"colour\"))"

make_test "062_lazy_question_sat"  "sat"   "colou??r" "(assert (= w \"color\"))"
make_test "063_lazy_question2_sat" "sat"   "colou??r" "(assert (= w \"colour\"))"

# --- 8. Non-capturing Groups ---
make_test "064_noncap_sat"               "sat"   "(?:ab)+"        "(assert (= w \"ababab\"))"
make_test "065_noncap_unsat"             "unsat" "(?:ab)+"        "(assert (= w \"abba\"))"
make_test "066_noncap_alternation_sat"   "sat"   "(?:foo|bar)baz" "(assert (= w \"barbaz\"))"
make_test "067_noncap_alternation_unsat" "unsat" "(?:foo|bar)baz" "(assert (= w \"quxbaz\"))"
make_test "068_nested_noncap_sat"        "sat"   "(?:a(?:b|c))+"  "(assert (= w \"abacab\"))"
make_test "069_nested_noncap_unsat"      "unsat" "(?:a(?:b|c))+"  "(assert (= w \"aa\"))"
make_test "070_noncap_exact_sat"         "sat"   "(?:ab){3}"      "(assert (= w \"ababab\"))"
make_test "071_noncap_exact_unsat"       "unsat" "(?:ab){3}"      "(assert (= w \"abab\"))"

# --- 9. Capture Groups and Backreferences ---
make_test "072_backref_char_sat"    "sat"   "([a-z])\\1"           "(assert (= (str.len w) 2))"
make_test "073_backref_char_unsat"  "unsat" "([a-z])\\1"           "(assert (= w \"ab\"))"
make_test "074_backref_word_sat"    "sat"   "(\\w+) \\1"           "(assert (= w \"hello hello\"))"
make_test "075_backref_word_unsat"  "unsat" "(\\w+) \\1"           "(assert (= w \"hello world\"))"
make_test "076_two_backrefs_sat"    "sat"   "([a-c])([0-2])\\1\\2" "(assert (= w \"a1a1\"))"
make_test "077_two_backrefs_unsat"  "unsat" "([a-c])([0-2])\\1\\2" "(assert (= w \"a1b1\"))"
make_test "078_palindrome4_sat"     "sat"   "(.)(.)\\2\\1"         "(assert (= w \"abba\"))"
make_test "079_palindrome4_unsat"   "unsat" "(.)(.)\\2\\1"         "(assert (= w \"abcd\"))"
make_test "080_symmetric_key_sat"   "sat"   "([a-z]+)-\\d+-\\1"    "(assert (= w \"abc-123-abc\"))"
make_test "081_symmetric_key_unsat" "unsat" "([a-z]+)-\\d+-\\1"    "(assert (= w \"abc-123-def\"))"

# --- 10. Named Capture Groups ---
make_test "082_named_date_sat"          "sat"   "(?<year>\\d{4})-(?<month>\\d{2})-(?<day>\\d{2})" "(assert (= w \"2024-01-15\"))"
make_test "083_named_date_unsat"        "unsat" "(?<year>\\d{4})-(?<month>\\d{2})-(?<day>\\d{2})" "(assert (= w \"2024-1-15\"))"
make_test "084_named_backref_sat"       "sat"   "(?<ch>[a-z])\\k<ch>"          "(assert (= (str.len w) 2))"
make_test "085_named_backref_unsat"     "unsat" "(?<ch>[a-z])\\k<ch>"          "(assert (= w \"ab\"))"
make_test "086_named_backref_mid_sat"   "sat"   "(?<letter>[a-z])x\\k<letter>" "(assert (= w \"axa\"))"
make_test "087_named_backref_mid_unsat" "unsat" "(?<letter>[a-z])x\\k<letter>" "(assert (= w \"axb\"))"

# --- 11. Anchors ---
make_test "088_anchor_sat"         "sat"   "^abc\$" "(assert (= w \"abc\"))"
make_test "089_anchor_unsat"       "unsat" "^abc\$" "(assert (= w \"xabcx\"))"
make_test "090_anchor_empty_sat"   "sat"   "^\$"    "(assert (= w \"\"))"
make_test "091_anchor_empty_unsat" "unsat" "^\$"    "(assert (= (str.len w) 1))"

# --- 12. Word Boundaries ---
make_test "092_word_boundary_sat"        "sat"   "\\bword\\b" "(assert (= w \"word\"))"
make_test "093_word_boundary_unsat"      "unsat" "a\\bword"   "(assert (= w \"aword\"))"
make_test "094_word_boundary_digits_sat" "sat"   "\\b\\d+\\b" "(assert (= w \"42\"))"
make_test "095_word_boundary_mid_unsat"  "unsat" "\\w\\b\\w"  "(assert (= w \"ab\"))"

# --- 13. Lookaheads ---
make_test "096_pos_lookahead_sat"        "sat"   "a(?=b)b"      "(assert (= w \"ab\"))"
make_test "097_neg_lookahead_unsat"      "unsat" "a(?!b)b"      "(assert (= w \"ab\"))"
make_test "098_pos_lookahead_unit_sat"   "sat"   "\\d+(?=px)"   "(assert (= w \"12px\"))"
make_test "099_pos_lookahead_unit_unsat" "unsat" "\\d+(?=px)"   "(assert (= w \"12em\"))"
make_test "100_neg_lookahead_sat"        "sat"   "\\d+(?!px)"   "(assert (= w \"42\"))"
make_test "101_neg_lookahead_unsat"      "unsat" "\\d+(?!px)"   "(assert (= w \"42px\"))"
make_test "102_lookahead_nonempty_sat"   "sat"   "(?=.{4,})\\w+" "(assert (= (str.len w) 5))"
make_test "103_lookahead_nonempty_unsat" "unsat" "(?=.{4,})\\w+" "(assert (= w \"hi\"))"

# --- 14. Realistic Patterns ---
make_test "104_date_sat"            "sat"   "\\d{4}-\\d{2}-\\d{2}" "(assert (= w \"2024-01-15\"))"
make_test "105_date_unsat"          "unsat" "\\d{4}-\\d{2}-\\d{2}" "(assert (= w \"2024-1-5\"))"
make_test "106_ipv4_sat"            "sat"   "\\d{1,3}\\.\\d{1,3}\\.\\d{1,3}\\.\\d{1,3}" "(assert (= w \"192.168.1.1\"))"
make_test "107_ipv4_unsat"          "unsat" "\\d{1,3}\\.\\d{1,3}\\.\\d{1,3}\\.\\d{1,3}" "(assert (= w \"192.168.1\"))"
make_test "108_email_sat"           "sat"   "[a-z0-9]+@[a-z0-9]+\\.[a-z]{2,}" "(assert (= w \"user@example.com\"))"
make_test "109_email_unsat"         "unsat" "[a-z0-9]+@[a-z0-9]+\\.[a-z]{2,}" "(assert (= w \"user@example\"))"
make_test "110_hex_color_sat"       "sat"   "#[0-9a-fA-F]{6}" "(assert (= w \"#ff00aa\"))"
make_test "111_hex_color_unsat"     "unsat" "#[0-9a-fA-F]{6}" "(assert (= w \"#ff00\"))"
make_test "112_identifier_sat"      "sat"   "[a-zA-Z_][a-zA-Z0-9_]*" "(assert (= w \"_myVar123\"))"
make_test "113_identifier_unsat"    "unsat" "[a-zA-Z_][a-zA-Z0-9_]*" "(assert (= w \"123abc\"))"
make_test "114_url_sat"             "sat"   "https?://\\S+" "(assert (= w \"https://example.com\"))"
make_test "115_url_unsat"           "unsat" "https?://\\S+" "(assert (= w \"ftp://example.com\"))"
make_test "116_signed_int_sat"      "sat"   "[+-]?\\d+" "(assert (= w \"-42\"))"
make_test "117_signed_int_unsat"    "unsat" "[+-]?\\d+" "(assert (= w \"--42\"))"
make_test "118_css_dimension_sat"   "sat"   "\\d+(\\.\\d+)?(px|em|rem|%)" "(assert (= w \"1.5rem\"))"
make_test "119_css_dimension_unsat" "unsat" "\\d+(\\.\\d+)?(px|em|rem|%)" "(assert (= w \"1.5vh\"))"
make_test "120_semver_sat"          "sat"   "\\d+\\.\\d+\\.\\d+" "(assert (= w \"2.10.3\"))"
make_test "121_semver_unsat"        "unsat" "\\d+\\.\\d+\\.\\d+" "(assert (= w \"2.10\"))"
make_test "122_repeat_pair_sat"     "sat"   "(?:[a-z]+\\d)+" "(assert (= w \"abc1def2\"))"
make_test "123_repeat_pair_unsat"   "unsat" "(?:[a-z]+\\d)+" "(assert (= w \"abc\"))"
make_test "124_password_sat"        "sat"   "(?=.*\\d)(?=.*[a-z]).{8,64}" "(assert (= w \"hello123\"))"
make_test "125_password_unsat"      "unsat" "(?=.*\\d)(?=.*[a-z]).{8,64}" "(assert (= w \"hello123\")) (assert (= (str.len w) 5))"

# --- 15. Complex & Edge Cases ---
make_test "126_complex_escapes_class_sat"   "sat"   "[\\^\\-\\]]+" "(assert (= w \"^-]^\"))"
make_test "127_complex_escapes_class_unsat" "unsat" "[\\^\\-\\]]+" "(assert (= w \"a\"))"
make_test "128_mixed_lookahead_sat"   "sat"   "(?=.*\\d)(?!.*admin).+" "(assert (= w \"user123_test\"))"
make_test "129_mixed_lookahead_unsat" "unsat" "(?=.*\\d)(?!.*admin).+" "(assert (= w \"admin_user_42\"))"
make_test "130_xml_tags_sat"   "sat"   "<([a-z]+)(?:\\s+[^>]+)?>.*</\\1>" "(assert (= w \"<div id=\\\"main\\\">obsah</div>\"))"
make_test "131_xml_tags_unsat" "unsat" "<([a-z]+)(?:\\s+[^>]+)?>.*</\\1>" "(assert (= w \"<div id=\\\"main\\\">obsah</span>\"))"
make_test "132_word_boundary_edge_unsat" "unsat" "\\b\\W+\\b" "(assert (= w \" - \"))"
make_test "133_heavy_repeat_sat" "sat" "(?:a|b){50}" "(assert (= (str.len w) 50)) (assert (= w \"ababababababababababababababababababababababababab\"))"
make_test "135_explosive_alternation_sat" "sat" "(?:a{2,4}b|b{1,3}a){5,8}" "(assert (= (str.len w) 30))"
make_test "136_complex_login_sat" "sat" \
"^(?=.*[A-Z])(?=.*\\d)(?:[a-zA-Z0-9_]{3,10})(?:-(?:foo|bar|baz)){1,3}$" \
"(assert (= w \"User123-foo-bar\"))"
make_test "137_nested_alt_sat" "sat" \
"^(?:([a-c]{2}|[d-f]{3})(?:\\d{2}|[XYZ]{1,2}))(?:_[^aeiou\\W]{2,4})?$" \
"(assert (= w \"ab12_bcdf\"))"
make_test "138_boundary_edge_sat" "sat" \
"\\b(?:[A-Za-z]{2,4}\\d{1,2})(?:[^\\w\\s]{1,2})(?:\\w{3})\\b" \
"(assert (= w \"Abc12!@xyz\"))"
make_test "139_optional_layers_sat" "sat" \
"^(?:https?|ftp)://(?:[a-z0-9]+(?:-[a-z0-9]+)*\\.)+[a-z]{2,6}(?:/[\\w\\-./?%&=]*)?$" \
"(assert (= w \"https://sub-domain.example-site.com/path/to/file?x=1\"))"
make_test "140_structural_constraints_sat" "sat" \
"^(?=.*[a-z])(?=.*[A-Z])(?=.*\\d)(?:[A-Za-z\\d]{2,5}-){2}[A-Za-z\\d]{2,5}$" \
"(assert (= w \"Ab1c-De2F-gh3\"))"

make_test "141_branch_explosion_sat" "sat" \
"^(?:(?=.{8,12}$)(?=.*[A-Z])(?=.*\\d)(?:[a-z]{2}|[A-Z]{2}|\\d{2}|[_-]{2})){4}$" \
"(assert (= w \"abCD12__\"))"

make_test "142_anchor_lookahead_branch_sat" "sat" \
"^(?:\
(?:(?=.{6,10}$)[a-z]{2}\\d{2})|\
(?:(?=.*[A-Z])[A-Z]{3}_)|\
(?:(?=.*\\d)[a-zA-Z]{1,3}\\d{1,2})|\
(?:\\w{4})\
){2}$" \
"(assert (= w \"ab12XYZ_\"))"



# =============================================================================
# TEST RUNNER
# =============================================================================
PASSED=0
FAILED=0
TIMED_OUT=0
TOTAL=0
SOLVER_BUG=0

for test_file in "$TEST_DIR"/*.smt2; do
    TOTAL=$((TOTAL + 1))
    EXPECTED=$(grep ":status" "$test_file" | awk '{print $3}' | tr -d ')')
    OUTPUT=$(timeout "$TIMEOUT" "$Z3_BIN" smt.string_solver=noodler "$test_file" 2>&1)
    EXIT_CODE=$?

    if [ "$EXIT_CODE" -eq 124 ]; then RESULT="timeout"
    elif echo "$OUTPUT" | grep -q "BUG:"; then RESULT="bug"
    elif echo "$OUTPUT" | grep -q "^unsat$"; then RESULT="unsat"
    elif echo "$OUTPUT" | grep -q "^sat$"; then RESULT="sat"
    else RESULT="unknown"; fi

    NAME=$(basename "$test_file" .smt2)

    if [ "$RESULT" = "$EXPECTED" ]; then
        echo -e "[\033[32mPASS\033[0m] $NAME"
        PASSED=$((PASSED + 1))
    elif [ "$RESULT" = "bug" ]; then
        echo -e "[\033[34mSOLVER BUG\033[\0m] $NAME"
        SOLVER_BUG=$((SOLVER_BUG + 1))
    elif [ "$RESULT" = "timeout" ]; then
        echo -e "[\033[33mTIME\033[0m] $NAME  (limit: ${TIMEOUT}s)"
        TIMED_OUT=$((TIMED_OUT + 1))
    else
        echo -e "[\033[31mFAIL\033[0m] $NAME"
        printf  "        Expected : %s\n" "$EXPECTED"
        printf  "        Got      : %s\n" "$RESULT"
        if [ "$RESULT" = "unknown" ]; then
            echo "        Z3 output (first 5 lines):"
            echo "$OUTPUT" | head -5 | sed 's/^/         /'
        fi
        FAILED=$((FAILED + 1))
    fi
done

printf "\nResults: %d passed  %d failed  %d bugged  %d timed out  (total: %d)\n" "$PASSED" "$FAILED" "$SOLVER_BUG" "$TIMED_OUT" "$TOTAL"
[ $((PASSED + SOLVER_BUG)) -eq "$TOTAL" ] && exit 0 || exit 1