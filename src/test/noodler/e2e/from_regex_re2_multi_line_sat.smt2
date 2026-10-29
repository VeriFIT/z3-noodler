; In RE2, ^ and $ match at the start and the end of lines with the flag m, e.g., x = "a\u{a}b\u{a}c".
(set-logic QF_S)
(set-info :status sat)
(set-option :smt.str.ecma_engine_semantics true)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex re2) "(?m)^b$")))
(assert (str.prefixof "a\u{a}" x))
(assert (str.suffixof "\u{a}c" x))
(assert (= (str.len x) 5))

(check-sat)
