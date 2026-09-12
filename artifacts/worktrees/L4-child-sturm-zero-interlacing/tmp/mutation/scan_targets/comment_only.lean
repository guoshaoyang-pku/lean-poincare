/-
Pass-6 gate-sensitivity mutation target (false-positive control) — **not part of the
release tree**.

Every forbidden token below occurs only inside comments or a string literal and must NOT be
flagged by `input/d5-tools/scan_forbidden.py`:
  sorry, axiom, unsafe, native_decide, proof_wanted, sorryAx, admit.
`tools/acceptance_pass6.py` requires zero hard matches in this file, so the sensitivity check
on `real_sorry.lean` cannot be satisfied by a scanner that simply flags everything.
-/
def p6_scan_clean_string : String := "sorry axiom unsafe native_decide proof_wanted sorryAx admit"

theorem p6_scan_clean : True := trivial
