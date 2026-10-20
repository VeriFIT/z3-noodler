; The existential of the fresh variables of an optional anchor is not eliminated by the rewriter for x = "a". The
; negative axiom with a quantifier was added also for the positive membership, and the model of x requested by the
; quantifier instantiation crashed, since the models were not produced.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex ecma2020) "(?:^)?a")))
(assert (= x "a"))

(check-sat)
