; https://github.com/VeriFIT/z3-noodler/issues/443
; Same root cause as issue443.smt2, but with the restarted match occurring in
; the middle of a longer suffix constraint rather than right at the end of a
; literal equality. Expected sat, e.g. y = "abaa", z = "caa".
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const y String)
(declare-const z String)
(assert (= z (str.replace_all y "ab" "c")))
(assert (str.in_re z (re.++ (str.to_re "c") re.all)))
(assert (str.suffixof "aa" y))
(check-sat)
