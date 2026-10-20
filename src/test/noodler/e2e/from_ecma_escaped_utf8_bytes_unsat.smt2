; The pattern is matched as the sequence of code points given by the string literal, \u{c3}\u{a9} are two
; characters (not the UTF-8 encoding of U+E9), so they do not match the single character U+E9.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "\u{e9}"))
(assert (str.in_re x ((_ re.from_regex ecma2020) "^\u{c3}\u{a9}$")))

(check-sat)
