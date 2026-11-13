; In PCRE2, \z matches only at the end of the text, not before a final \n.
(set-logic QF_S)
(set-info :status unsat)
(set-option :smt.str.ecma_engine_semantics true)

(declare-const x String)

(assert (= x "a\u{a}"))
(assert (str.in_re x ((_ re.from_regex pcre2) 'a\z')))

(check-sat)
