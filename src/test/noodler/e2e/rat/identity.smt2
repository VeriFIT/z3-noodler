(set-option :produce-models true)
(set-info :status unsat)
(declare-const s String)
(declare-const t String)
(assert (str.in_rat s t (rat.identity re.all)))
(assert (distinct (str.len s) (str.len t)))

(check-sat)
