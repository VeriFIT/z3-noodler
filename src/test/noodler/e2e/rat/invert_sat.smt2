(set-option :produce-models true)
(set-info :status sat)
(assert (str.in_rat "vb" "abc" (rat.invert (str.to_rat "abc" "vb"))))

(check-sat)
(get-model)
