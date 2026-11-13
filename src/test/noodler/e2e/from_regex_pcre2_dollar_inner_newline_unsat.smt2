; In PCRE2, $ does not match before a \n inside the text without the flag m.
(set-logic QF_S)
(set-info :status unsat)
(set-option :smt.str.ecma_engine_semantics true)

(declare-const x String)

(assert (= x "a\u{a}b"))
(assert (str.in_re x ((_ re.from_regex pcre2) "a$")))

(check-sat)
