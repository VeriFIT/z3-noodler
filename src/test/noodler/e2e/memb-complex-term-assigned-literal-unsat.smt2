; a membership of a complex term (y ++ z): its axiom must use the literal assigned to the membership
; rewriting the membership again gave a different term (the prefix factoring of re.union is not idempotent), so the axiom constrained an unassigned copy (unsound sat)
; the digits are written out, as a repetition {n} becomes a single re.loop, which the factoring handles at once
(set-logic QF_SLIA)
(set-info :status unsat)
(set-option :smt.str.ecma_engine_semantics true)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= x (str.++ y z)))
(assert (or (= y "a") (= y "b")))
(assert (or (= z "c") (= z "d")))
(assert (str.in_re x ((_ re.from_regex ecma2020) "[0-9][0-9][0-9][0-9][0-9]|[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9]")))
(check-sat)
