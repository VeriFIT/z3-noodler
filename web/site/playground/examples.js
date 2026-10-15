// Example SMT-LIB scripts shown in the "Load an example" menu of the Z3-Noodler web page.
//
// Each entry has:
//   id          short kebab-case identifier
//   title       short title shown in the menu
//   description one or two sentences: what the example shows and the expected answer
//   code        a complete SMT-LIB 2.6 script
//   args        extra command-line arguments for the solver (e.g. "model=true" for get-model)
//
// Every example has been checked against a native Z3-Noodler build: the answer is the one stated in
// the description and it is found in well under a second.
window.NOODLER_EXAMPLES = [
  {
    id: "hello-world",
    title: "Hello, world!",
    description:
      'A word equation with a regular constraint: split "hello world" into two words. ' +
      'Expected: sat, with the model x = "hello" and y = "world".',
    code: `; Hello, world! Split a sentence into two words.
(set-logic QF_SLIA)

(declare-const x String)
(declare-const y String)

; A word equation: x, a space and y together spell "hello world".
(assert (= (str.++ x " " y) "hello world"))

; A regular constraint: x is a non-empty word of lowercase letters,
; so it cannot contain the space.
(assert (str.in_re x (re.+ (re.range "a" "z"))))

(check-sat)
(get-model)
`,
    args: ["model=true"],
  },

  {
    id: "password-policy",
    title: "Model generation: a password",
    description:
      "Model generation: the solver invents a password that satisfies a policy given by several " +
      "regular constraints, a length bound and a forbidden substring. Expected: sat, and get-value " +
      "prints one such password.",
    code: `; Let the solver invent a password that satisfies a password policy.
(set-logic QF_SLIA)

(declare-const pw String)

; Allowed characters: letters, digits and the special characters ! # ?
(assert (str.in_re pw (re.+ (re.union (re.range "a" "z")
                                      (re.range "A" "Z")
                                      (re.range "0" "9")
                                      (str.to_re "!") (str.to_re "#") (str.to_re "?")))))

; 10 to 12 characters long.
(assert (<= 10 (str.len pw) 12))

; At least one digit, one uppercase letter, one lowercase letter and one special character.
(assert (str.in_re pw (re.++ re.all (re.range "0" "9") re.all)))
(assert (str.in_re pw (re.++ re.all (re.range "A" "Z") re.all)))
(assert (str.in_re pw (re.++ re.all (re.range "a" "z") re.all)))
(assert (str.in_re pw (re.++ re.all (re.union (str.to_re "!") (str.to_re "#") (str.to_re "?")) re.all)))

; No two digits in a row.
(assert (not (str.in_re pw (re.++ re.all (re.range "0" "9") (re.range "0" "9") re.all))))

; The password must not contain the user name.
(assert (not (str.contains pw "alice")))

(check-sat)
; Print just the value of pw (get-model would print all variables).
(get-value (pw))
`,
    args: ["model=true"],
  },

  {
    id: "split-unsat",
    title: "Equation + regexes: unsat",
    description:
      "Splits one string at the separator # in two ways; since the left side has only one #, the " +
      'solver must align the separators, forcing y = u, but y never contains "aa" while u must. ' +
      "Expected: unsat.",
    code: `; One string, split at the separator # in two different ways.
(set-logic QF_S)

(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const u String)

(assert (= (str.++ x "#" y) (str.++ z "#" u)))

; x and y are sequences of the block "ab" (so the left side has exactly one #).
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))

; z consists of lowercase letters only (it cannot contain #).
(assert (str.in_re z (re.* (re.range "a" "z"))))

; u contains "aa" somewhere (it may contain anything else, even more # characters).
(assert (str.in_re u (re.++ re.all (str.to_re "aa") re.all)))

; The only # on the left must be the # right after z, hence x = z and y = u.
; But y, a sequence of "ab" blocks, never contains "aa".
(check-sat)
`,
    args: [],
  },

  {
    id: "commutation",
    title: "Commutation: xy = yx",
    description:
      "Two words commute (xy = yx) exactly when they are powers of the same word, so with x a power " +
      'of "ab", y must have even length and |y| = 5 is impossible. Expected: unsat (with 6 instead of 5 it is sat).',
    code: `; The commutation equation xy = yx.
; It holds exactly when x and y are powers of a common word w
; (x = w^i and y = w^j for some i, j >= 0).
(set-logic QF_SLIA)

(declare-const x String)
(declare-const y String)

(assert (= (str.++ x y) (str.++ y x)))

; x is a non-empty power of "ab" ...
(assert (str.in_re x (re.+ (str.to_re "ab"))))

; ... so y must be a power of "ab" as well, which has even length.
(assert (= (str.len y) 5))

(check-sat)
; Try changing the length to 6: the answer becomes sat (with y = "ababab").
`,
    args: [],
  },

  {
    id: "equation-lengths",
    title: "Equation + lengths: xx = yyy",
    description:
      "A word equation with integer arithmetic over lengths: xx = yyy implies 2|x| = 3|y|, so " +
      "|x| = 6, |y| = 4 and both are powers of a two-letter word. " +
      'Expected: sat, e.g. x = "ababab", y = "abab".',
    code: `; A word equation combined with linear integer arithmetic over lengths.
(set-logic QF_SLIA)

(declare-const x String)
(declare-const y String)

; Two copies of x spell the same string as three copies of y.
(assert (= (str.++ x x) (str.++ y y y)))

; The lengths of x and y add up to 10 (so |x| = 6 and |y| = 4).
(assert (= (+ (str.len x) (str.len y)) 10))

; x contains "ab".
(assert (str.contains x "ab"))

(check-sat)
(get-model)
`,
    args: ["model=true"],
  },

  {
    id: "disequation",
    title: "Disequation",
    description:
      'Two different strings from (ab)* cannot have the same length: the strings of (ab)* of a given ' +
      "length are unique. Expected: unsat.",
    code: `; A disequation (x is different from y) with regular and length constraints.
(set-logic QF_SLIA)

(declare-const x String)
(declare-const y String)

(assert (not (= x y)))

; Both strings are sequences of the block "ab" ...
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))

; ... of the same length, which makes them equal.
(assert (= (str.len x) (str.len y)))

(check-sat)
`,
    args: [],
  },

  {
    id: "replace-sanitizer",
    title: "str.replace_all: a broken sanitizer",
    description:
      'A naive sanitizer deletes every "../" from a path with str.replace_all; the solver finds an ' +
      'input for which the result still contains "../". Expected: sat, e.g. input = "....//".',
    code: `; A naive path sanitizer deletes every occurrence of "../" from the input.
; Can the sanitized path still contain "../"?
(set-logic QF_SLIA)

(declare-const input String)
(declare-const sanitized String)

; str.replace_all replaces all (non-overlapping, leftmost) occurrences.
(assert (= sanitized (str.replace_all input "../" "")))

; The sanitized path still goes up a directory.
(assert (str.contains sanitized "../"))

; Look for a short attack.
(assert (<= (str.len input) 6))

(check-sat)
(get-model)
`,
    args: ["model=true"],
  },

  {
    id: "string-int-conversion",
    title: "String-integer conversion",
    description:
      "str.from_int and str.to_int relate numbers to their decimal representations (str.to_int " +
      'allows leading zeros). Expected: sat with n = 999, x = "999" and y = "001000".',
    code: `; Conversions between strings and integers.
(set-logic QF_SLIA)

(declare-const n Int)
(declare-const x String)
(declare-const y String)

; x is the decimal representation of n ...
(assert (= x (str.from_int n)))
; ... which consists of nines only, and n is between 100 and 5000.
(assert (str.in_re x (re.+ (str.to_re "9"))))
(assert (and (> n 100) (< n 5000)))

; y is a 6-digit string denoting n + 1 (str.to_int accepts leading zeros).
(assert (= (str.to_int y) (+ n 1)))
(assert (= (str.len y) 6))

(check-sat)
(get-model)
`,
    args: ["model=true"],
  },

  {
    id: "position-functions",
    title: "indexof, substr, at: key=value",
    description:
      'Parses a key=value string with str.indexof, str.substr and str.at, requiring the key "user" ' +
      'and a lowercase value starting with "r". Expected: sat, with s = "user=r" followed by four lowercase letters.',
    code: `; Parse a "key=value" string with position functions.
(set-logic QF_SLIA)

(declare-const s String)
(declare-const key String)
(declare-const value String)
(declare-const i Int)

; i is the position of the first "=" in s (str.indexof returns -1 if there is none).
(assert (= i (str.indexof s "=" 0)))
(assert (>= i 0))

; key is the part before the "=", value the part after it.
(assert (= key (str.substr s 0 i)))
(assert (= value (str.substr s (+ i 1) (- (str.len s) (+ i 1)))))

; The key is "user", the value is a lowercase word starting with "r".
(assert (= key "user"))
(assert (str.in_re value (re.+ (re.range "a" "z"))))
(assert (= (str.at value 0) "r"))

; The whole string has 10 characters.
(assert (= (str.len s) 10))

(check-sat)
(get-model)
`,
    args: ["model=true"],
  },

  {
    id: "not-contains",
    title: "Not-contains",
    description:
      'All of X, Y, Z are powers of "abc", so ZYX is a power of "abc" no longer than XYXZ and always ' +
      "occurs in it as a prefix. Expected: unsat.",
    code: `; A not-contains constraint over string variables.
(set-logic QF_S)

(declare-const X String)
(declare-const Y String)
(declare-const Z String)

; X, Y and Z are all repetitions of "abc".
(assert (str.in_re X (re.* (str.to_re "abc"))))
(assert (str.in_re Y (re.* (str.to_re "abc"))))
(assert (str.in_re Z (re.* (str.to_re "abc"))))

; XYXZ does not contain ZYX as a substring.
(assert (not (str.contains (str.++ X Y X Z) (str.++ Z Y X))))

; Both concatenations are repetitions of "abc" and ZYX is not longer than XYXZ,
; so ZYX is a prefix of XYXZ.
(check-sat)
`,
    args: [],
  },

  {
    id: "ecma-backreference",
    title: "ECMAScript regex with backreference",
    description:
      "re.from_ecma2020 accepts JavaScript regex syntax, here with a backreference \\1 that forces " +
      "the closing HTML tag to repeat the opening one (a non-regular language). Expected: sat with a " +
      '4-letter tag, e.g. x = "<aaaa>hello world</aaaa>".',
    code: `; ECMAScript (JavaScript) regular expressions with a backreference.
; The pattern matches an HTML element whose closing tag repeats the opening one:
; group 1 captures the tag name and \\1 must match the same text again.
; (The pattern is written in single quotes, where backslashes are kept as they are.)
(set-logic QF_SLIA)

(declare-const x String)
(declare-const tag String)
(declare-const close String)

(assert (str.in_re x (re.from_ecma2020 '<([a-z]+)>[a-z ]*</\\1>')))

; x starts with an opening tag and the text "hello world"; the rest is unknown.
(assert (= x (str.++ "<" tag ">hello world</" close)))

; The whole element has 24 characters.
(assert (= (str.len x) 24))

(check-sat)
(get-model)
; Since |x| = 16 + 2 * |tag|, the length 24 forces a 4-letter tag.
; Try the length 25: the answer becomes unsat.
`,
    args: ["model=true"],
  },

  {
    id: "to-lower-upper",
    title: "Case conversion: to_lower/to_upper",
    description:
      "str.to_lower and str.to_upper (Z3-Noodler extensions, same semantics as in cvc5) convert " +
      'ASCII letters. Expected: sat, with x a capitalization of "admin" other than "admin" itself ' +
      '(e.g. "ADMIN") and y = "noodler".',
    code: `; Case conversion with str.to_lower and str.to_upper (Z3-Noodler extensions).
(set-logic QF_SLIA)

(declare-const x String)
(declare-const y String)

; A case-insensitive check: x is "admin" after conversion to lowercase,
; but x itself is not "admin".
(assert (= (str.to_lower x) "admin"))
(assert (not (= x "admin")))

; y is a lowercase word whose uppercase version is "NOODLER".
(assert (= (str.to_upper y) "NOODLER"))
(assert (str.in_re y (re.* (re.range "a" "z"))))

(check-sat)
(get-model)
`,
    args: ["model=true"],
  },
];
