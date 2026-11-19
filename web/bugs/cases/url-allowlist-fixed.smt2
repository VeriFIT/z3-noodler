; The fix: escape the dot.
;
;   const ALLOWED = /^https:\/\/(www|api)\.example\.com\//;
;
; (unsat = every allowed url goes to a subdomain of example.com)
(set-logic QF_SLIA)
(declare-const url String)
(declare-const host String)
(declare-const path String)
(assert (str.in_re url (re.from_ecma2020 '^https://(www|api)\.example\.com/.*')))
(assert (= url (str.++ "https://" host "/" path)))
(assert (str.in_re host (re.+ (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "-") (str.to_re ".")))))
(assert (str.suffixof ".com" host))                          ; registrable by the attacker
(assert (not (str.in_re host (re.from_ecma2020 '([a-z0-9-]+\.)*example\.com'))))
(check-sat)
