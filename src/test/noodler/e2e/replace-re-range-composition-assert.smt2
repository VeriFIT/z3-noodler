(set-logic QF_SLIA)
(set-info :status sat)
; Regression test for https://github.com/VeriFIT/z3-noodler/issues/398
; str.replace_re with a re.range argument used to trigger an assertion
; failure in MATA's NFT composition (SynchronizationProperties::get_synchronization_types).
(declare-const s String)
(assert (= (str.replace_re s (re.range "0" "1") "#") "#"))
(check-sat)
