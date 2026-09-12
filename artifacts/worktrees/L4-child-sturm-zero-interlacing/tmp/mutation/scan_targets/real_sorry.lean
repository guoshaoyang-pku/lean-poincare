/-
Pass-6 gate-sensitivity mutation target — **not part of the release tree**.

This file contains a genuine `sorry` in code (the proof of `p6_scan_mutation`), so
`input/d5-tools/scan_forbidden.py` must flag it.  The file is intentionally not compiled;
only the scanner runs over it.  `tools/acceptance_pass6.py` requires a hard match here.
-/
theorem p6_scan_mutation : False := by sorry
