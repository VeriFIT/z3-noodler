; https://github.com/VeriFIT/z3-noodler/issues/449
; Reached through str.indexof (tightest prefix emits a not-contains with a one-letter needle).
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const t String)
(assert (= (str.len t) 1))
(assert (= (str.indexof "babb" t 0) 1))
(check-sat)
