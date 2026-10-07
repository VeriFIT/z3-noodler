(set-option :produce-models true)
(set-info :status sat)
(declare-const x String)
(declare-const y String)

; y = swap("b" ++ x), where swap exchanges a <-> b letter by letter.
; The input side "b" ++ x is a concatenation of a literal and a non-length
; variable that get_automata_and_division_of_concatenation merges into a
; single automaton with no length variables, which used to make
; process_transducer store a non-simple transducer (input side with more
; than one term) and produce an invalid model for x/y.
(assert (str.in_rat (str.++ "b" x) y (rat.* (rat.union (str.to_rat "a" "b") (str.to_rat "b" "a")))))

(check-sat)
(get-model)
