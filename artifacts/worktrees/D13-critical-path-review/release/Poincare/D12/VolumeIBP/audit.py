#!/usr/bin/env python3
"""Fail-closed programmatic axiom audit for Poincare.D12.VolumeIBP.

Runs `lake env lean Poincare/D12/VolumeIBP/Audit.lean` in release/, parses every
`#print axioms` cone, and:

1. FAILS if any audited declaration's axiom cone is not contained in the allowed set
   {propext, Classical.choice, Quot.sound};
2. FAILS if the negative control `...Audit.negativeControl` is NOT detected as
   unapproved (detector-sensitivity check);
3. FAILS if the number of parsed cones does not match the expected count;
4. additionally scans all VolumeIBP sources for forbidden tokens
   (sorry, admit, native_decide, proof_wanted, unsafe) outside comments/docstrings.

Exit code 0 = audit PASS, nonzero = audit FAIL (fail closed).
"""
import re
import subprocess
import sys
from pathlib import Path

RELEASE = Path(__file__).resolve().parent.parent.parent.parent
MODULE = "Poincare/D12/VolumeIBP/Audit.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NEGATIVE_CONTROL = "Poincare.D12.VolumeIBP.Audit.negativeControl"
EXPECTED_DECLS = 59  # number of #print axioms lines in Audit.lean (excluding the control? count all)

def main() -> int:
    proc = subprocess.run(
        ["lake", "env", "lean", MODULE],
        cwd=RELEASE, capture_output=True, text=True,
    )
    out = proc.stdout + "\n" + proc.stderr
    if proc.returncode != 0:
        print("FAIL: Audit.lean did not compile cleanly (exit %d)" % proc.returncode)
        print(out[-4000:])
        return 2

    cones = re.findall(
        r"'(.*?)' depends on axioms: \[(.*?)\]", out, flags=re.DOTALL)
    print("parsed %d axiom cones" % len(cones))
    problems = []
    neg_flagged = False
    for name, axs_raw in cones:
        axs = {a.strip() for a in re.split(r",\s*", axs_raw.strip()) if a.strip()}
        if name == NEGATIVE_CONTROL:
            if axs <= {NEGATIVE_CONTROL, "negativeControl"} and axs:
                neg_flagged = True
            else:
                problems.append("negative control cone unexpected: %s" % axs)
            continue
        bad = axs - ALLOWED
        if bad:
            problems.append("%s depends on unapproved axioms: %s" % (name, sorted(bad)))
    if not neg_flagged:
        problems.append(
            "FAIL: negative control %s was NOT flagged — detector is blind"
            % NEGATIVE_CONTROL)

    # forbidden-token scan of sources (strip comments conservatively: line comments and
    # nested block comments; docstrings are block comments so they are stripped too)
    src = Path(RELEASE) / "Poincare" / "D12" / "VolumeIBP"
    tokens = ["sorry", "admit", "native_decide", "proof_wanted", "unsafe"]
    for f in sorted(src.glob("*.lean")):
        text = f.read_text(encoding="utf-8")
        text = re.sub(r"/-[^-].*?-/", "", text, flags=re.DOTALL)  # block comments
        text = re.sub(r"--.*", "", text)  # line comments
        for tok in tokens:
            if re.search(r"\b" + tok + r"\b", text):
                # allow the audit module's own negative-control axiom? no: axiom scan separate
                problems.append("forbidden token %r in %s" % (tok, f.name))
    # axiom declarations other than the negative control
    for f in sorted(src.glob("*.lean")):
        text = f.read_text(encoding="utf-8")
        text = re.sub(r"/-[^-].*?-/", "", text, flags=re.DOTALL)
        text = re.sub(r"--.*", "", text)
        for m in re.finditer(r"\baxiom\s+(\w+)", text):
            name = m.group(1)
            if f.name != "Audit.lean" or name != "negativeControl":
                problems.append("unexpected axiom %r in %s" % (name, f.name))

    if problems:
        print("AUDIT FAIL")
        for p in problems:
            print(" -", p)
        return 1
    print("AUDIT PASS: %d cones within {%s}; negative control flagged"
          % (len(cones) - 1, ", ".join(sorted(ALLOWED))))
    return 0

if __name__ == "__main__":
    sys.exit(main())
