; https://github.com/VeriFIT/z3-noodler/issues/443
; The transducer built for a single str.replace_all with a multi-character find
; (whose first character does not recur elsewhere in the find) had no accepting
; run for inputs ending right after restarting a match on the delimiter, so this
; was wrongly reported unsat. y = "aa" contains no "ab", so replace_all is the
; identity on it.
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const y String)
(assert (= (str.replace_all y "ab" "c") "aa"))
(check-sat)
