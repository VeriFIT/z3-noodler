(set-option :produce-models true)
(set-info :status sat)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const w String)

; Input side "x ++ y" contains only variables (no length vars), so it is
; merged into one automaton by get_automata_and_division_of_concatenation.
; x is later substituted by "w ++ a", but that does not change that the
; original transducer's input side has more than one term. This used to
; produce an invalid model, because get_model assigned a preimage word of
; T(z) directly to x alone, ignoring that the real input is x ++ y.
(assert (str.in_rat (str.++ x y) z (rat.* (rat.union (str.to_rat "a" "b") (str.to_rat "b" "b")))))
(assert (str.in_re x (re.+ (str.to_re "a"))))
(assert (str.in_re y (re.+ (str.to_re "b"))))
(assert (str.in_re z (re.++ (str.to_re "bb") (re.* (str.to_re "b")))))
(assert (= x (str.++ w "a")))

(check-sat)
(get-model)
