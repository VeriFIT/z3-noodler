(set-logic ALL)
(set-info :status unsat)

(declare-const s String)
(declare-const i@3 Int)
(assert (str.in_re s (re.++ (re.++ (re.* (str.to_re "a")) (re.* (str.to_re "b"))) (re.* (str.to_re "c")))))
(assert
    (or
        (<= (str.len s) i@3)
        (not (<= (str.len s) i@3))
    )
)
(assert (distinct (str.at s i@3) "a"))
(assert (<= 0 i@3))
(assert (<= i@3 (ite (str.contains s "b") (str.indexof s "b" 0) (ite (str.contains s "c") (str.indexof s "c" 0) (str.len s)))))
(assert
    ; (not
        (or
            (< i@3 (ite (str.contains s "b") (str.indexof s "b" 0) (ite (str.contains s "c") (str.indexof s "c" 0) (str.len s))))
            (> i@3 (ite (str.contains s "c") (str.indexof s "c" 0) (str.len s)))
        )
    ; )
)
(check-sat)
(exit)
