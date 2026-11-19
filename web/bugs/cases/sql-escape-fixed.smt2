; The fix: escape the escape character first (or, better, use a prepared
; statement).
;
;   $esc = str_replace("'", "\\'", str_replace("\\", "\\\\", $name));
;
; Can the attacker still break out of the literal?  (unsat = no)
(set-logic QF_SLIA)
(declare-const name String)
(define-fun escaped () String
  (str.replace_all (str.replace_all name "\u{5c}" "\u{5c}\u{5c}") "'" "\u{5c}'"))
(assert (not (str.in_re escaped (re.from_ecma2020 '([^\x27\\]|\\.)*'))))
(check-sat)
