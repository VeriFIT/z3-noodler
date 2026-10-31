; The flavor is a symbol index, so it can coincide with the name of a declared constant.
(set-logic QF_S)
(set-info :status sat)

(declare-const ecma2020 String)

(assert (str.in_re ecma2020 ((_ re.from_regex ecma2020) "(a)\1")))

(check-sat)
(get-model)
