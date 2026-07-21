(set-option :produce-models true)
(set-info :status unsat)
(declare-const s String)
(declare-const t String)

(assert (str.in_rat s t (rat.union (rat.union (str.to_rat "1648" "354848") (str.to_rat ")@$(#*" "%$*")) (rat.++ (str.to_rat "gf" "vvaw") (str.to_rat "asd" "fdas")))))
(assert (= (str.len s) 4))

(check-sat)
