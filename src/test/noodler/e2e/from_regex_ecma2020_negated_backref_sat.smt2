; The negated membership is encoded with a quantifier, so the models of the string variables are needed by the
; quantifier instantiation even if they are not requested, e.g., x = "ab".
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (not (str.in_re x ((_ re.from_regex ecma2020) "(a|b)\1"))))
(assert (str.in_re x (re.++ (re.union (str.to_re "a") (str.to_re "b")) (re.union (str.to_re "a") (str.to_re "b")))))

(check-sat)
