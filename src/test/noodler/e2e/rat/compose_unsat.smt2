(set-option :produce-models true)
(set-info :status unsat)
(declare-const s String)
(declare-const t String)
(assert (str.in_rat s t (rat.compose (str.to_rat "abc" "cdf") (str.to_rat "cd" "vb"))))

(check-sat)
