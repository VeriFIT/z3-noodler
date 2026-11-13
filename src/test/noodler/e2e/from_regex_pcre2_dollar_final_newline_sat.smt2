; In PCRE2, $ matches at the end of the text and also before a \n that ends the text (like \Z).
(set-logic QF_S)
(set-info :status sat)
(set-option :smt.str.ecma_engine_semantics true)

(declare-const x String)

(assert (= x "a\u{a}"))
(assert (str.in_re x ((_ re.from_regex pcre2) "a$")))

(check-sat)
