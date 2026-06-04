(set-logic QF_S)
(set-info :status unsat)

(declare-fun X () String)
(declare-fun Y () String)
(declare-fun Z () String)

(assert
    (and
        (not (str.contains (str.++ X Y X Z) (str.++ Z Y X)))
        (str.in_re X (re.* (str.to_re "abc")))
        (str.in_re Y (re.* (str.to_re "abc")))
        (str.in_re Z (re.* (str.to_re "abc")))
    )
)
(check-sat)
(exit)
