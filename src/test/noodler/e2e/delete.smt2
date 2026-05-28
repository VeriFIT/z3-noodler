(set-logic QF_SLIA)
(set-info :status sat)

(declare-const x String)
(declare-const a String)
(declare-const b String)
(assert (= x (str.++ a b)))
(assert (str.in_re a (re.* (str.to_re "a"))))
(assert (str.in_re b (re.* (str.to_re "b"))))
(assert (= (str.len a) 4))
(assert (= (str.len b) 4))

; x = aaaabbbb

(assert (= (str.delete x 2 4) "aabb"))
(assert (= (str.delete x 2 10) "aa"))
(assert (= (str.delete x 2 5) "aab"))
(assert (= (str.delete x 2 6) "aa"))
(assert (= (str.delete x 2 7) "aa"))
(assert (= (str.delete x 0 8) ""))
(assert (= (str.delete x 0 99) ""))
(assert (= (str.delete x -1 4) "aaaabbbb"))
(assert (= (str.delete x 8 2) "aaaabbbb"))
(assert (= (str.delete x 9 2) "aaaabbbb"))
(assert (= (str.delete x 2 -2) "aaaabbbb"))

; variable index and length
(declare-const i Int)
(declare-const j Int)
(declare-const u String)
(assert (= u (str.++ a b)))
; u = aaaabbbb
(assert (= (str.delete u i j) "aabb"))

; rewriter
(assert (= (str.delete "aaxxxxbb" 2 4) "aabb"))
(assert (= (str.delete "xxxxaabb" 0 4) "aabb"))
(assert (= (str.delete "aaxxxx" 2 99) "aa"))
(assert (= (str.delete "aaxxxx" 2 4) "aa"))
(assert (= (str.delete "xxxx" 0 4) ""))
(assert (= (str.delete "xxxx" 0 5) ""))
(assert (= (str.delete "xxxx" 0 99) ""))
(assert (= (str.delete "aaaa" -1 2) "aaaa"))
(assert (= (str.delete "aaaa" 2 0) "aaaa"))
(assert (= (str.delete "aaaa" 2 -1) "aaaa"))
(assert (= (str.delete "aaaa" 10 2) "aaaa"))

(check-sat)
