; The pattern is matched as the sequence of code points given by the string literal, \u{c3}\u{a9} are two
; characters (not the UTF-8 encoding of U+E9) in the pattern as well as in the string.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "\u{c3}\u{a9}"))
(assert (str.in_re x ((_ re.from_regex ecma2020) "^\u{c3}\u{a9}$")))

(check-sat)
