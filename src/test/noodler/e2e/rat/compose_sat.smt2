(set-option :produce-models true)
(set-info :status sat)
(assert (str.in_rat "abc" "vb" (rat.compose (str.to_rat "abc" "cdf") (str.to_rat "cdf" "vb"))))

(check-sat)
(get-model)
