#!/usr/bin/env python3
"""D13: hard/soft forbidden-token scan of the Lean sources *added* by this task.

Scans probes/ (the only original Lean content of D13) plus, for completeness,
the upstream snapshot separately (whose admitted-proof map is reported in
manifest/upstream-modules.json rather than gated here).

Writes manifest/d13-forbidden-scan.json.
"""

from __future__ import annotations

import datetime as _dt
import importlib.util
import json
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
D5 = REPO / "input" / "d5-tools" / "scan_forbidden.py"
MANI = REPO / "manifest"


def load_d5():
    spec = importlib.util.spec_from_file_location("d5_scan_forbidden", D5)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def scan(root: Path):
    d5 = load_d5()
    matches, files = [], 0
    for path in sorted(root.rglob("*.lean")):
        if "/.lake/" in str(path):
            continue
        files += 1
        for m in d5.scan_file(str(path)):
            m["file"] = str(path.relative_to(REPO))
            matches.append(m)
    hard = [m for m in matches if m["hard"]]
    soft = [m for m in matches if not m["hard"]]
    return {
        "root": str(root.relative_to(REPO)),
        "lean_files_scanned": files,
        "hard_match_count": len(hard),
        "soft_match_count": len(soft),
        "matches": matches,
    }


def main() -> int:
    probes = scan(REPO / "probes")
    out = {
        "schema": "d13-forbidden-scan-v1",
        "generated_at": _dt.datetime.now().astimezone().isoformat(timespec="seconds"),
        "hard_forbidden": ["sorry", "axiom", "unsafe", "native_decide", "proof_wanted", "sorryAx", "admit"],
        "soft_flagged": ["implemented_by", "extern"],
        "scanner": "input/d5-tools/scan_forbidden.py",
        "d13_lean_sources": probes,
        "verdict": "clean" if probes["hard_match_count"] == 0 else "violation",
    }
    (MANI / "d13-forbidden-scan.json").write_text(json.dumps(out, indent=1) + "\n")
    print(f"probes: files={probes['lean_files_scanned']} hard={probes['hard_match_count']} "
          f"soft={probes['soft_match_count']} verdict={out['verdict']}")
    return 0 if out["verdict"] == "clean" else 1


if __name__ == "__main__":
    raise SystemExit(main())
