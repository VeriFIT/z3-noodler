(set-logic QF_SLIA)
(set-info :status sat)

; to lower
(declare-const x String)
(assert (= (str.to_lower x) "aaa"))
(assert (str.in_re x (re.* (str.to_re "A"))))
; to lower rewriter
(declare-const y String)
(assert (= y (str.to_lower "AAa")))
(assert (str.in_re y (re.* (str.to_re "a"))))

; to upper
(declare-const a String)
(assert (= (str.to_upper a) "AAA"))
(assert (str.in_re a (re.* (str.to_re "a"))))
; to upper rewriter
(declare-const b String)
(assert (= b (str.to_upper "aAa")))
(assert (str.in_re b (re.* (str.to_re "A"))))

; to upper more complicated
(declare-const u String)
(assert (= u (str.to_upper "aAamMmzZz")))
(assert (str.in_re u (re.++ (re.* (str.to_re "A")) (re.* (str.to_re "M")) (re.* (str.to_re "Z")))))
(declare-const v String)
(assert (= (str.to_upper v) "AAAMMMZZZ"))
(assert (str.in_re v (re.++ (re.* (str.to_re "a")) (re.* (str.to_re "m")) (re.* (str.to_re "z")))))

; to lower more complicated
(declare-const z String)
(assert (= z (str.to_lower "aAamMmzZz")))
(assert (str.in_re z (re.++ (re.* (str.to_re "a")) (re.* (str.to_re "m")) (re.* (str.to_re "z")))))
(declare-const zz String)
(assert (= (str.to_lower zz) "aaammmzzz"))
(assert (str.in_re zz (re.++ (re.* (str.to_re "A")) (re.* (str.to_re "M")) (re.* (str.to_re "Z")))))

; non-ASCII characters
(assert (= (str.to_upper "ač ď") "Ač ď"))
(assert (= (str.to_lower "AČ Ď") "aČ Ď"))

(check-sat)
