(set-logic QF_SLIA)
(set-info :status sat)

; trim
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= (str.trim x) "a"))
(assert (= (str.++ z y z) x))
(assert (= y "\u{9}\u{A}\u{B}\u{C}\u{D}a\u{9}\u{A}\u{B}\u{C}\u{D}"))
(assert (str.in_re z (re.* (str.to_re " "))))
(assert (> (str.len x) 20))
(assert (> (str.len z) 1))

(assert (= (str.trim (str.++ z "aaa")) "aaa"))
(assert (= (str.trim (str.++ "aaa" z)) "aaa"))
(assert (= (str.trim (str.++ z "aaa" z)) "aaa"))
(assert (= (str.trim z) ""))

(declare-const empty String)
(assert (str.in_re empty (str.to_re "")))
(assert (= (str.trim empty) ""))

; Rewriter
(assert (= (str.trim "a") "a"))
(assert (= (str.trim " a") "a"))
(assert (= (str.trim "a ") "a"))
(assert (= (str.trim " a ") "a"))
(assert (= (str.trim "aa") "aa"))
(assert (= (str.trim "   aa") "aa"))
(assert (= (str.trim "aa   ") "aa"))
(assert (= (str.trim "     ") ""))
(assert (= (str.trim "") ""))
(assert (= (str.trim "\u{9}\u{A}\u{B}\u{C}\u{D}  aa  \u{9}\u{A}\u{B}\u{C}\u{D}") "aa"))
(assert (= (str.trim "  a a  ") "a a"))

(check-sat)
