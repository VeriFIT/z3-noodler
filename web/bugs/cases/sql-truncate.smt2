; Escaping is now correct, but the escaped value is cut to fit a 16-character
; column (or a log line, or a cache key) *after* escaping:
;
;   $esc = str_replace("'", "\\'", str_replace("\\", "\\\\", $name));
;   $esc = substr($esc, 0, 16);
;
; Can the cut leave an unfinished escape that eats the closing quote?
(set-logic QF_SLIA)
(declare-const name String)
(define-fun escaped () String
  (str.replace_all (str.replace_all name "\u{5c}" "\u{5c}\u{5c}") "'" "\u{5c}'"))
(define-fun cut () String (str.substr escaped 0 16))
(assert (not (str.in_re cut (re.from_ecma2020 '([^\x27\\]|\\.)*'))))
(assert (str.in_re name (re.* (re.union (re.range "a" "z") (str.to_re "'")))))  ; only letters and quotes
(check-sat)
(get-model)
