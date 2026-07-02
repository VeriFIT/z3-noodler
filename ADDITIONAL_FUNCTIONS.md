# Additional string functions
Other than the constraints defined in the [SMT-LIB theory of strings](https://smt-lib.org/theories-UnicodeStrings.shtml), Z3-Noodler can handle the following functions:

## `(str.to_real String Real)`
Converts a string representation of a (positive) real number to the corresponding number. The string representation can either be a positive integer with leading zeros (similarly as in `str.to_int`) or it can contain one decimal separator `.`. It evaluates to `-1.0` otherwise.  
Examples:
 - `(str.to_real "4562")` → `4562.0`
 - `(str.to_real "-4562")` → `-1.0`
 - `(str.to_real "45.62")` → `45.62`
 - `(str.to_real "00045.620000")` → `45.62`
 - `(str.to_real "")` → `-1.0`
 - `(str.to_real ".456")` → `0.456`
 - `(str.to_real "8494.")` → `8494.0`
 - `(str.to_real ".")` → `-1.0`
 - `(str.to_real "4564a")` → `-1.0`
 - `(str.to_real "4564e3")` → `-1.0`

## `(str.from_real Real Int String)`
Transforms a positive real number `r` to a string `s` with a corresponding number of decimal places `n`. If either `n` or `r` is negative, it evaluates to the empty string.  
Examples:
 - `(str.from_real 4.56 5)` → `"4.56000"`
 - `(str.from_real 4.56 0)` → `"4"`
 - `(str.from_real 4.56 1)` → `"4.5"`
 - `(str.from_real -4.56 -5)` → `""`
 - `(str.from_real -4.56 5)` → `""`
 - `(str.from_real 4.56 -5)` → `""`

## `(str.to_lower String String)`
Converts all uppercase ASCII characters (`0x41` - `0x5A`) to lowercase.
This function is equivalent to [cvc5's `str.to_lower`](https://cvc5.github.io/docs-ci/docs-main/theories/strings.html).  
Examples:
 - `(str.to_lower "abcd")` → `"abcd"`
 - `(str.to_lower "aBcD")` → `"abcd"`
 - `(str.to_lower "AČĎ")` → `"aČĎ"`

## `(str.to_upper String String)`
Converts all lowercase ASCII characters (`0x61` - `0x7A`) to uppercase.
This function is equivalent to [cvc5's `str.to_upper`](https://cvc5.github.io/docs-ci/docs-main/theories/strings.html).  
Examples:
 - `(str.to_upper "ABCD")` → `"ABCD"`
 - `(str.to_upper "aBcD")` → `"ABCD"`
 - `(str.to_upper "ačď")` → `"Ačď"`

## `(str.update String Int String String)`
Starts replacing characters in the first string by characters in the second string at the given index.
The length of the resulting string will be the same as the first string.
If the index is outside the first string, the first string gets returned.
This function is equivalent to [cvc5's `str.update`](https://cvc5.github.io/docs-ci/docs-main/theories/strings.html).  
Examples:
 - `(str.update "123456" 2 "ab")` → `"12ab56"`
 - `(str.update "1234" 2 "ab")` → `"12ab"`
 - `(str.update "1234" 2 "abcd")` → `"12ab"`
 - `(str.update "1234" -1 "ab")` → `"1234"`
 - `(str.update "1234" 4 "ab")` → `"1234"`
 - `(str.update "1234" 0 "abcd")` → `"abcd"`
 - `(str.update "1234" 0 "abcdef")` → `"abcd"`

## `(str.trim String String)`
Trims the whitespace at the beginning and end of the given string.
We consider the following characters as whitespace: space, form feed, line feed, carriage return, horizontal tab, vertical tab (ASCII `0x09` - `0x0D` and `0x20`).  
Examples:
 - `(str.trim "aa")` → `"aa"`
 - `(str.trim "   aa")` → `"aa"`
 - `(str.trim "aa   ")` → `"aa"`
 - `(str.trim "     ")` → `""`
 - `(str.trim "\u{9}\u{A}\u{B}\u{C}\u{D}  aa  \u{9}\u{A}\u{B}\u{C}\u{D}")` → `"aa"`
 - `(str.trim "  a  a  ")` → `"a  a"`

## `(str.in_re String (re.from_ecma2020 String) Bool)`
Tests whether a string belongs to the language described by an ECMAScript 2020 regular expression pattern.
The pattern is given as a string literal and is interpreted according to the [ECMAScript 2020 RegExp specification](https://262.ecma-international.org/11.0/#sec-patterns).
You can use (nonstandard) single-quote string notation (`''`) to represent the pattern.
In this notation, every character (even Unicode) is represented as is, so you write a string such as `'[0-9\ы═ы║ы╒ыёыєы╔ыіыїы╗ы╘]'`.
Furthermore, you can use the option/parameter `str.ecma_engine_semantics=true` to mimic ecma regex engine semantics by implicitly wrapping regex in Σ*, by default this is turned off.
The default behaviour is equivalent to [Ostrich's `re.from_ecma2020`](https://github.com/uuverifiers/ostrich/#additional-regular-expression-constructors).

Supported ECMAScript regex features:

- Standard character classes: `.`, `\d`, `\D`, `\s`, `\S`, `\w`, `\W`
- Character class expressions: `[...]`, `[^...]`, character ranges `[a-z]`
- Anchors: `^` (start of string), `$` (end of string)
- Quantifiers: `*`, `+`, `?`, `{n}`, `{n,}`, `{n,m}` (greedy and lazy variants)
- Alternation: `|`
- Non-capturing groups: `(?:...)`
- Capturing groups: `(...)`, named groups `(?<name>...)`
- Backreferences: `\1`, `\k<name>`
- Lookahead assertions: `(?=...)` (positive), `(?!...)` (negative)
- Lookbehind assertions: `(?<=...)` (positive), `(?<!...)` (negative)
- Word boundary assertions: `\b`, `\B`
- Unicode escape sequences: `\uXXXX`, `\u{XXXXX}`

Limitations:

- Non-regular constructs (backreferences, lookarounds) cannot appear under unbounded quantifiers (`*`, `+`).
- Negative lookarounds whose inner pattern itself contains non-regular constructs (e.g. backreferences) are not supported.

Examples:

- `(str.in_re x (re.from_ecma2020 'a'))` — `x` equals `"a"`
- `(str.in_re x (re.from_ecma2020 '(a)\1'))` — `x` equals `"aa"` (backreference: group 1 captures `"a"`, then repeats it)
- `(str.in_re x (re.from_ecma2020 '(a*b)\1'))` — `x` is in `{ww | w in a*b}`, e.g. `"bb"`, `"abab"`
- `(str.in_re x (re.from_ecma2020 '(ab)\1'))` — `x` equals `"abab"`

## `(str.delete String Int Int String)`
Similar to `str.substr`, but it deletes the substring instead of returning it.
The part to delete is given by an index and a length.
If the index is outside the string or the length is non-positive, the original string gets returned.  
Examples:
 - `(str.delete "AAxxxxBB" 2 4)` → `"AABB"`
 - `(str.delete "xxxxAABB" 0 4)` → `"AABB"`
 - `(str.delete "AAxxxx" 2 99)` → `"AA"`
 - `(str.delete "xxxx" 0 4)` → `""`
 - `(str.delete "xxxx" 0 99)` → `""`
 - `(str.delete "aaaa" -1 2)` → `"aaaa"`
 - `(str.delete "aaaa" 2 0)` → `"aaaa"`
 - `(str.delete "aaaa" 2 -1)` → `"aaaa"`
 - `(str.delete "aaaa" 10 2)` → `"aaaa"`
