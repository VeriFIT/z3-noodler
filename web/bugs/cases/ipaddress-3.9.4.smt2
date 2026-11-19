; CPython 3.9.4, ipaddress (CVE-2021-29921).  An SSRF guard:
;
;   def is_allowed(host):
;       return not ipaddress.ip_address(host).is_private
;   ...
;   if is_allowed(host): urllib.request.urlopen(f"http://{host}/")
;
; ipaddress reads every octet as decimal, but the C library that opens the
; connection (inet_aton) reads an octet with a leading 0 as octal.
(set-logic QF_SLIA)
(declare-const o1 String) (declare-const o2 String) (declare-const o3 String) (declare-const o4 String)
(declare-const host String)
(assert (= host (str.++ o1 "." o2 "." o3 "." o4)))

; ipaddress._parse_octet: 1-3 ASCII digits, value at most 255
(define-fun py_octet_ok ((o String)) Bool
  (and (str.in_re o ((_ re.loop 1 3) (re.range "0" "9"))) (<= (str.to_int o) 255)))

; inet_aton (glibc, used by getaddrinfo): a leading 0 means octal
(define-fun digit ((o String) (i Int)) Int (str.to_int (str.at o i)))
(define-fun aton_octet ((o String)) Int
  (ite (and (str.prefixof "0" o) (> (str.len o) 1))
       (ite (= (str.len o) 2) (digit o 1) (+ (* 8 (digit o 1)) (digit o 2)))
       (str.to_int o)))
(define-fun aton_ok ((o String)) Bool
  (or (not (str.prefixof "0" o)) (str.in_re o (re.+ (re.range "0" "7")))))

; RFC 1918 private and loopback ranges
(define-fun private ((a Int) (b Int)) Bool
  (or (= a 10) (= a 127) (and (= a 172) (<= 16 b 31)) (and (= a 192) (= b 168))))

(assert (and (py_octet_ok o1) (py_octet_ok o2) (py_octet_ok o3) (py_octet_ok o4)))
(assert (and (aton_ok o1) (aton_ok o2) (aton_ok o3) (aton_ok o4)))
; Python thinks the address is public, the C library connects to a private one.
(assert (not (private (str.to_int o1) (str.to_int o2))))
(assert (private (aton_octet o1) (aton_octet o2)))
(check-sat)
(get-model)
