(set-logic QF_S)
(set-info :status sat)
; the intersection is empty: the words start with different letters
(assert (= re.none (re.inter (re.++ (str.to_re "a") re.all) (re.++ (str.to_re "b") re.all))))
(check-sat)
