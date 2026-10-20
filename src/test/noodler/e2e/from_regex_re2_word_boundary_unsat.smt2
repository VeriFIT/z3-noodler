; In RE2, \b is an ASCII word boundary, "ab" is not a word in "cab".
(set-logic QF_S)
(set-info :status unsat)
(set-option :smt.str.ecma_engine_semantics true)

(declare-const x String)

(assert (= x "cab"))
(assert (str.in_re x ((_ re.from_regex re2) '\bab\b')))

(check-sat)
