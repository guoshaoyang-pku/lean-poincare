#!/usr/bin/env python3
"""Re-run a producer's `tools/d12_axiom_audit.py` against the *staged* byte-copy
of the same release inside this audit worktree.

The producer worktree is only read (the tool source is hashed against the
card's recorded `source_hashes` entry); every write (lean oleans, negative
control scratch) stays under this worktree.

Usage: python3 audit360/r12/rerun_producer_axiom_audit.py <card>
"""
import hashlib
import importlib.util
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
WT = HERE.parent.parent
PROD = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees")


def main():
    card = sys.argv[1]
    tool = PROD / card / "tools" / "d12_axiom_audit.py"
    staged = WT / "audit360" / "pkgs" / card
    tool_sha = hashlib.sha256(tool.read_bytes()).hexdigest()
    card_json = PROD / card / "longrun" / "results" / f"{card}.json"
    recorded = json.loads(card_json.read_text())["source_hashes"].get("tools/d12_axiom_audit.py")
    print(f"producer tool sha256 {tool_sha} recorded {recorded} match={tool_sha == recorded}")

    spec = importlib.util.spec_from_file_location("prod_d12ax", tool)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    if hasattr(mod, "RELEASE"):
        mod.RELEASE = str(staged)
    if hasattr(mod, "WORKTREE"):
        mod.WORKTREE = staged
        mod.RELEASE = staged

        scratch = HERE / "scratch"
        scratch.mkdir(parents=True, exist_ok=True)
        control = scratch / f"neg_axiom_control_{card}.lean"
        control.write_text(
            "import Mathlib.Tactic\n"
            "axiom fakeD12Axiom : True\n"
            "theorem usesFakeD12Axiom : True := fakeD12Axiom\n"
            "#print axioms usesFakeD12Axiom\n",
            encoding="utf-8")

        def negative_control():
            proc = mod.subprocess.run(["lake", "env", "lean", str(control)],
                                      cwd=str(mod.RELEASE), capture_output=True,
                                      text=True, timeout=600)
            flagged = False
            for line in proc.stdout.splitlines():
                name, axioms = mod.parse_axioms_line(line)
                if name == "usesFakeD12Axiom" and axioms and (axioms - mod.ALLOWED):
                    flagged = True
            errors = []
            if proc.returncode != 0:
                errors.append("negative control: lean did not compile the control file")
            if not flagged:
                errors.append("negative control: fake axiom was NOT flagged by the parser (fail-open!)")
            else:
                print("OK   negative control: fake axiom correctly flagged")
            return errors

        mod.negative_control = negative_control

    env = dict(os.environ)
    env["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
    env["PATH"] = env["ELAN_HOME"] + "/bin:" + env.get("PATH", "")
    os.environ.update(env)
    rc = mod.main()
    print(f"PRODUCER-AUDIT-RERUN {card}: rc={rc} (staged release: {staged})")
    return rc


if __name__ == "__main__":
    sys.exit(main())
