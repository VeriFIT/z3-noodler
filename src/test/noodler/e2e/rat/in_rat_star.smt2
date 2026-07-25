(set-option :produce-models true)
(set-info :status sat)
(declare-const s String)
(declare-const t String)

(assert (str.in_rat s t (rat.* (rat.++ (str.to_rat "gf" "vvaw") (str.to_rat "asd" "fdas")))))
(assert (> (str.len s) 4))

(check-sat)
(get-model)
