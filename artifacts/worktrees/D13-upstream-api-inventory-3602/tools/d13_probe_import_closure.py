#!/usr/bin/env python3
"""D13 import-closure admission check.

For each adapter probe under probes/D13Probes, compute the transitive closure
of `import` statements that resolve to modules inside the preserved upstream
snapshot, and report whether any module in that closure contains a
hard-forbidden token (in particular `sorry`).  This is the machine check
behind the claim "the probes do not import admitted upstream proofs".

Writes manifest/d13-probe-import-closure.json.
"""

from __future__ import annotations

import datetime as _dt
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SNAP = REPO / "third_party" / "frenzymath" / "Poincare-Conjecture"
PROBES = REPO / "probes" / "D13Probes"
MANI = REPO / "manifest"

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.«»]+)\s*$", re.MULTILINE)


def upstream_modules() -> dict:
    """module name -> path for every Lean file in the snapshot.

    Lake module names are relative to each package root, not to the snapshot
    root: `shared/Shared/Foo.lean` is module `Shared.Foo`, and
    `formalized-sources/DoCarmo/DoCarmoLib/Bar.lean` is module
    `DoCarmoLib.Bar`.
    """
    roots = [SNAP / "shared", SNAP / "PoincareConjecture"]
    fs = SNAP / "formalized-sources"
    if fs.is_dir():
        roots += [d for d in sorted(fs.iterdir()) if d.is_dir()]
    out = {}
    for p in SNAP.rglob("*.lean"):
        if "/.lake/" in str(p):
            continue
        for r in roots:
            try:
                rel = p.relative_to(r).as_posix()
            except ValueError:
                continue
            out[rel[: -len(".lean")].replace("/", ".")] = p
            break
    return out


def main() -> int:
    mods = upstream_modules()
    scanned = json.loads((MANI / "upstream-modules.json").read_text())["modules"]
    # file -> hard tokens
    tokens_by_file = {
        f: set(m.get("tokens", {})) for f, m in scanned.items()
    }
    relpath = {v: k for k, v in mods.items()}

    report = []
    for probe in sorted(PROBES.glob("*.lean")):
        text = probe.read_text()
        roots = IMPORT_RE.findall(text)
        seen, stack = set(), list(roots)
        upstream_closure = []
        missing = []
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            seen.add(m)
            if m not in mods:
                missing.append(m)
                continue
            upstream_closure.append(m)
            sub = IMPORT_RE.findall(mods[m].read_text(encoding="utf-8", errors="replace"))
            stack.extend(sub)
        admitted = []
        wholesale = []
        for m in upstream_closure:
            rel = relpath[mods[m]]
            toks = tokens_by_file.get(rel, set())
            if toks & {"sorry", "admit", "axiom", "sorryAx", "unsafe", "native_decide", "proof_wanted"}:
                admitted.append({"module": m, "tokens": sorted(toks)})
            head = mods[m].read_text(encoding="utf-8", errors="replace")
            if re.search(r"^import Mathlib\s*$", head, re.MULTILINE):
                wholesale.append(m)
        report.append(
            {
                "probe": probe.name,
                "direct_imports": roots,
                "upstream_closure_size": len(upstream_closure),
                "upstream_closure": sorted(upstream_closure),
                "mathlib_imports": sorted({m for m in seen if m.startswith("Mathlib")}),
                "upstream_modules_importing_mathlib_wholesale": sorted(wholesale),
                "unresolved_imports": sorted(set(missing)),
                "modules_with_hard_tokens": admitted,
                "admitted_proof_imported": bool(admitted),
            }
        )

    out = {
        "schema": "d13-probe-import-closure-v1",
        "generated_at": _dt.datetime.now().astimezone().isoformat(timespec="seconds"),
        "probes": report,
        "verdict": (
            "clean"
            if not any(r["admitted_proof_imported"] for r in report)
            else "admits_upstream_proofs"
        ),
    }
    (MANI / "d13-probe-import-closure.json").write_text(
        json.dumps(out, indent=1) + "\n"
    )
    for r in report:
        print(
            f"{r['probe']:24} upstream_closure={r['upstream_closure_size']:3} "
            f"mathlib_imports={len(r['mathlib_imports']):3} "
            f"admitted={len(r['modules_with_hard_tokens'])}"
        )
    print("verdict:", out["verdict"])
    return 0 if out["verdict"] == "clean" else 1


if __name__ == "__main__":
    raise SystemExit(main())
