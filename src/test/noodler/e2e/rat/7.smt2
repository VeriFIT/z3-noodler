(set-option :produce-models true)
(set-info :status unsat)
(declare-const s String)
(declare-const t String)
(assert (str.in_rat s t (rat.left re.all)))
(assert (distinct t ""))

(check-sat)
