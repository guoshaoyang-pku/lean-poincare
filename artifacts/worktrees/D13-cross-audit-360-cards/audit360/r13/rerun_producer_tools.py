#!/usr/bin/env python3
"""A3 round-13: re-execute the producers' own tools/d12_axiom_audit.py against
the round-13 COLD-REBUILT package copies (not the round-11 staged copies).

The producer tool source is read from the producer worktree and hashed against
the card's recorded source_hashes entry.  Every write stays in this worktree.

Usage: python3 audit360/r13/rerun_producer_tools.py [card ...]
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
CARDS = sys.argv[1:] or ["D12-tensor-maximum-bochner", "D12-triangulation-topology"]


def run(card):
    tool = PROD / card / "tools" / "d12_axiom_audit.py"
    rebuild = WT / "audit360" / "r13" / "rebuild" / card
    tool_sha = hashlib.sha256(tool.read_bytes()).hexdigest()
    card_json = PROD / card / "longrun" / "results" / f"{card}.json"
    recorded = json.loads(card_json.read_text())["source_hashes"].get("tools/d12_axiom_audit.py")
    print(f"[{card}] producer tool sha256 {tool_sha} recorded {recorded} match={tool_sha == recorded}")
    spec = importlib.util.spec_from_file_location("prod_d12ax_" + card.replace("-", "_"), tool)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    if hasattr(mod, "RELEASE"):
        mod.RELEASE = Path(rebuild)
    if hasattr(mod, "WORKTREE"):
        mod.WORKTREE = Path(rebuild)
        mod.RELEASE = Path(rebuild)

        def negative_control():
            scratch = HERE / "scratch"
            scratch.mkdir(parents=True, exist_ok=True)
            control = scratch / f"neg_axiom_control_{card}.lean"
            control.write_text(
                "import Mathlib.Tactic\naxiom fakeD12Axiom : True\n"
                "theorem usesFakeD12Axiom : True := fakeD12Axiom\n"
                "#print axioms usesFakeD12Axiom\n", encoding="utf-8")
            env2 = dict(os.environ)
            env2["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
            env2["PATH"] = env2["ELAN_HOME"] + "/bin:" + env2.get("PATH", "")
            proc = mod.subprocess.run(["lake", "env", "lean", str(control)],
                                      cwd=str(mod.RELEASE), capture_output=True,
                                      text=True, timeout=600, env=env2)
            flagged = False
            for line in proc.stdout.splitlines():
                name, axioms = mod.parse_axioms_line(line)
                if name == "usesFakeD12Axiom" and axioms and (axioms - mod.ALLOWED):
                    flagged = True
            errors = []
            if proc.returncode != 0:
                errors.append("negative control did not compile")
            if not flagged:
                errors.append("negative control NOT flagged (fail-open)")
            else:
                print("OK   negative control: fake axiom correctly flagged")
            return errors

        mod.negative_control = negative_control
    env = dict(os.environ)
    env["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
    env["PATH"] = env["ELAN_HOME"] + "/bin:" + env.get("PATH", "")
    os.environ.update(env)
    rc = mod.main()
    print(f"PRODUCER-TOOL-RERUN {card}: rc={rc} (cold-rebuilt release: {rebuild})")
    return rc


if __name__ == "__main__":
    rcs = {c: run(c) for c in CARDS}
    print("rcs:", rcs)
    sys.exit(0 if all(v == 0 for v in rcs.values()) else 1)
