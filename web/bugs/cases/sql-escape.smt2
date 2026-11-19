; SQL injection: hand-made escaping of a quoted string literal (MySQL-style
; literals, where "\" escapes the next character).
;
;   $sql = "SELECT * FROM users WHERE name = '"
;        . str_replace("'", "\\'", $name) . "'";
;
; The literal stays closed iff the escaped text is a sequence of ordinary
; characters and backslash escapes: ([^'\\]|\\.)*.  Can the attacker break
; out of the literal and append SQL of their choice?
(set-logic QF_SLIA)
(declare-const name String)
(define-fun escaped () String (str.replace_all name "'" "\u{5c}'"))
(assert (not (str.in_re escaped (re.from_ecma2020 '([^\x27\\]|\\.)*'))))
(assert (str.suffixof " OR 1=1 -- " name))
(check-sat)
(get-model)
