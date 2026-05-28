(set-logic QF_SLIA)
(set-info :status sat)

; update
(declare-const u String)
(assert (= (str.update u 3 "bb") "aaabbaaa"))
(assert (str.in_re u (re.* (str.to_re "a"))))
(assert (= (str.len u) 8))

; overflow
(declare-const x String)
(assert (= (str.update x 3 "bcdefghijklmn") "aaabcdef"))
(assert (str.in_re x (re.* (str.to_re "a"))))
(assert (= (str.len x) 8))

; index too big
(declare-const y String)
(assert (= (str.update y 8 "bcdefghijklmn") "aaaaaaaa"))
(assert (str.in_re y (re.* (str.to_re "a"))))
(assert (= (str.len y) 8))

; index too small
(declare-const z String)
(assert (= (str.update z -1 "bcdefghijklmn") "aaaaaaaa"))
(assert (str.in_re z (re.* (str.to_re "a"))))
(assert (= (str.len z) 8))

; empty update string
(declare-const v String)
(assert (= (str.update v 3 "") "aaaaaaaa"))
(assert (str.in_re v (re.* (str.to_re "a"))))
(assert (= (str.len v) 8))

; more complicated example
(declare-const i Int)
(declare-const o String)
(declare-const res String)
(declare-const p String)
(assert (str.in_re o (re.* (str.to_re "a"))))
(assert (= (str.len o) 8))
(assert (= (str.len p) 20))
(assert (> i 3))
(assert (= (str.update o (div i 2) p) res))
(assert (str.in_re res (re.++ (re.* (str.to_re "a")) (re.+ (str.to_re "b")) (str.to_re "aa"))))

; rewriter
(assert (= (str.update "aaaaaaaa" 3 "bb") "aaabbaaa"))
(assert (= (str.update "aaaaaaaa" 3 "bcdefghijklmn") "aaabcdef"))
(assert (= (str.update "aaaaaaaa" 8 "bcdefghijklmn") "aaaaaaaa"))
(assert (= (str.update "aaaaaaaa" 9 "bcdefghijklmn") "aaaaaaaa"))
(assert (= (str.update "aaaaaaaa" 0 "bcdefghijklmn") "bcdefghi"))
(assert (= (str.update "aaaaaaaa" -1 "bcdefghijklmn") "aaaaaaaa"))
(assert (= (str.update "aaaaaaaa" 3 "") "aaaaaaaa"))

(check-sat)
