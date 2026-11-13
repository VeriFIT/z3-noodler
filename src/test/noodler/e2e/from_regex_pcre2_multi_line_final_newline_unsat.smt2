; In PCRE2, ^ with the flag m does not match after a \n that ends the text.
(set-logic QF_S)
(set-info :status unsat)
(set-option :smt.str.ecma_engine_semantics true)

(declare-const x String)

(assert (= x "a\u{a}"))
(assert (str.in_re x ((_ re.from_regex pcre2) '(?m)a\n^')))

(check-sat)
