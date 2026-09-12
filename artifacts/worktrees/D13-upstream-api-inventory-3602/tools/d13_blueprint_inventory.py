#!/usr/bin/env python3
"""D13 blueprint inventory.

The upstream repository carries a Lean blueprint per source project.  Each
mathematical environment (theorem/lemma/proposition/definition/...) has a
`\\label{...}` and may be marked `\\notready`, i.e. stated in the blueprint but
not yet formalised.  Those entries are the "upstream source claim" class of the
D13 classification: asserts something, but no Lean declaration is offered.

Writes manifest/upstream-blueprint-inventory.json.
"""

from __future__ import annotations

import datetime as _dt
import json
import re
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SNAP = REPO / "third_party" / "frenzymath" / "Poincare-Conjecture"
MANI = REPO / "manifest"

ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition|remark|example|"
    r"conjecture|claim|exercise|notation)\}(.*?)\\end\{\1\}",
    re.S,
)
LABEL_RE = re.compile(r"\\label\{([^}]*)\}")


def package_of(path: Path) -> str:
    rel = path.relative_to(SNAP).as_posix()
    if rel.startswith("formalized-sources/"):
        return rel.split("/")[1]
    return rel.split("/")[0]


def main() -> int:
    entries = []
    for tex in sorted(SNAP.rglob("*.tex")):
        if "blueprint" not in tex.as_posix():
            continue
        text = tex.read_text(encoding="utf-8", errors="replace")
        for m in ENV_RE.finditer(text):
            kind, body = m.group(1), m.group(2)
            labels = LABEL_RE.findall(body)
            entries.append(
                {
                    "package": package_of(tex),
                    "file": tex.relative_to(SNAP).as_posix(),
                    "line": text[: m.start()].count("\n") + 1,
                    "environment": kind,
                    "label": labels[0] if labels else None,
                    "notready": "\\notready" in body,
                    "has_proof": "\\begin{proof}" in body,
                }
            )

    per_pkg = {}
    for e in entries:
        p = per_pkg.setdefault(
            e["package"], {"environments": 0, "notready": 0, "with_proof": 0, "by_kind": {}}
        )
        p["environments"] += 1
        p["by_kind"][e["environment"]] = p["by_kind"].get(e["environment"], 0) + 1
        if e["notready"]:
            p["notready"] += 1
        if e["has_proof"]:
            p["with_proof"] += 1

    out = {
        "schema": "d13-upstream-blueprint-inventory-v1",
        "generated_at": _dt.datetime.now().astimezone().isoformat(timespec="seconds"),
        "source": "third_party/frenzymath/Poincare-Conjecture/*/blueprint/**/*.tex",
        "total_environments": len(entries),
        "total_notready": sum(1 for e in entries if e["notready"]),
        "packages": per_pkg,
        "notready_entries": [e for e in entries if e["notready"]],
    }
    (MANI / "upstream-blueprint-inventory.json").write_text(json.dumps(out, indent=1) + "\n")
    print(f"environments={len(entries)} notready={out['total_notready']}")
    for p, v in sorted(per_pkg.items()):
        print(f"  {p:22} env={v['environments']:5} notready={v['notready']:4} proof={v['with_proof']:5}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
