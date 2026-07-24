(set-option :produce-models true)
(set-info :status unsat)
(assert (str.in_rat "abc" "vb" (rat.invert (str.to_rat "abc" "vb"))))

(check-sat)
