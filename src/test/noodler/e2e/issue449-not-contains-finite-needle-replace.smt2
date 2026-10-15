; https://github.com/VeriFIT/z3-noodler/issues/449
; Reached through str.replace.
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const t String)
(declare-const r String)
(assert (= (str.len t) 1))
(assert (= r (str.replace "babb" t "c")))
(assert (= r "bcbb"))
(check-sat)
