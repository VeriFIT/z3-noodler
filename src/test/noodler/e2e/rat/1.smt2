(set-option :produce-models true)
(set-info :status sat)
(declare-const R RatRel)
(declare-const S RatRel)
(declare-const s String)
(declare-const t String)
(assert (= R (rat.++ (str.to_rat "gf" "vvaw") (str.to_rat "asd" "fdas"))))
(assert (= S (rat.union (str.to_rat "1648" "354848") (str.to_rat ")@$(#*" "%$*"))))

(assert (str.in_rat s t (rat.* R)))
(assert (> (str.len s) 4))

(check-sat)
(get-model)
