#!/usr/bin/env python3
"""Novelty check: authored theorems must not silently duplicate upstream ones.

For every declaration discovered in the authored adapter sources (the same
discovery used to generate the axiom audit) this script compares its short name
against every declaration name in the pinned upstream snapshot
(`evidence/upstream-qualified-names.json`).

Policy, fail closed:

* `alias` declarations are *intentional* renamings; they are exempt and counted.
* A non-alias authored declaration whose short name matches a **public**
  upstream declaration is a FAIL: the adapter would be presenting an upstream
  statement as a local contribution.  If the duplication is deliberate (for
  example re-deriving an upstream `private` lemma that downstream cannot
  consume), it must be listed in `PRIVATE_OK` with a justification.
* A match against an upstream `private` declaration is reported as a
  re-derivation and is allowed (the upstream name is not consumable), but it
  must also appear in `PRIVATE_OK` so the decision is recorded, not accidental.

Usage: check-novelty.py <worktree-root>
"""
import json
import re
import sys
from importlib.machinery import SourceFileLoader
from pathlib import Path

HERE = Path(__file__).resolve().parent
mk = SourceFileLoader("makeaudit", str(HERE / "make-audit-file.py")).load_module()

# Authored declarations that deliberately reuse an upstream *private* short name
# (with justification).  Public collisions are never allowed.
PRIVATE_OK = {
    "UpstreamAdapters.DownstreamGeometry.euclidean_curvatureFormAt_eq_zero":
        "upstream MorganTianLib.euclidean_curvatureFormAt_eq_zero is `private` "
        "(EuclideanExample.lean:34) and not consumable; this is the documented "
        "public re-derivation, recorded as such in claim-classification.json",
}


def is_private(snapshot: Path, rel_file: str, line: int) -> bool:
    """True if the upstream declaration at file:line carries `private`."""
    p = snapshot / rel_file
    if not p.exists():
        return False
    src = p.read_text(errors="replace").splitlines()
    # walk upwards over the declaration line and any attribute/modifier lines
    for i in range(min(line, len(src)) - 1, max(0, line - 6), -1):
        s = src[i].strip()
        if s.startswith("@["):
            continue
        if re.match(r"^(private|protected)\b", s):
            return True
        if re.match(r"^(theorem|lemma|def|abbrev|structure|instance|noncomputable)\b", s):
            return False
    return False


def main():
    root = Path(sys.argv[1]).resolve()
    snapshot = root / "third_party" / "frenzymath" / "Poincare-Conjecture"
    decls, _ = mk.discover(root / "adapters")
    qn = json.loads((root / "evidence" / "upstream-qualified-names.json").read_text())
    index = {}
    for _kw, pkgs in qn.items():
        for pkg, hits in pkgs.items():
            for h in hits:
                index.setdefault(h["name"].rsplit(".", 1)[-1], []).append(h)

    aliases = [d for d in decls if d["kind"] == "alias"]
    failures, rederivations, public_dups = [], [], []
    for d in decls:
        if d["kind"] == "alias":
            continue
        short = d["name"].rsplit(".", 1)[-1]
        hits = index.get(short, [])
        if not hits:
            continue
        entry = []
        for h in hits:
            priv = is_private(snapshot, h["file"], h["line"])
            entry.append((h["name"], h["file"], h["line"], priv))
        public = [e for e in entry if not e[3]]
        private = [e for e in entry if e[3]]
        if d["name"] in PRIVATE_OK:
            # allow-listed only as a re-derivation of an upstream *private*
            # declaration; if the upstream name became public, fail closed
            if public or not private:
                failures.append(
                    f"{d['name']} is allow-listed as a private-name re-derivation "
                    f"but its upstream match is not private: {entry}")
        elif public:
            public_dups.append((d["name"], public))
        elif private and d["name"] not in PRIVATE_OK:
            failures.append(
                f"{d['name']}: private-name re-derivation of "
                + "; ".join(f"{n} ({f}:{l})" for n, f, l, _ in private)
                + " is not recorded in PRIVATE_OK")
        for e in entry:
            rederivations.append((d["name"], e))

    declared = {d["name"] for d in decls}
    for name in sorted(set(PRIVATE_OK) - declared):
        failures.append(f"PRIVATE_OK entry `{name}` has no authored declaration "
                        "(stale allowlist entry)")

    print(f"novelty: {len(decls)} authored declarations "
          f"({len(aliases)} intentional alias renamings exempt)")
    print(f"  short-name matches with upstream declarations: {len(rederivations)}")
    for n, (up, f, l, p) in sorted(rederivations):
        print(f"    {n}  ~  {up} ({f}:{l}, {'private' if p else 'public'})")
    if public_dups:
        print("NOVELTY CHECK FAILED: non-alias authored declarations duplicate "
              "PUBLIC upstream declarations:")
        for n, hits in public_dups:
            print("  -", n, "->", hits)
        return 1
    if failures:
        print("NOVELTY CHECK FAILED: unrecorded short-name matches:")
        for f in failures:
            print("  -", f)
        return 1
    print("NOVELTY CHECK PASSED: no non-alias authored declaration duplicates a "
          "public upstream declaration; allowed private-name re-derivations are "
          "recorded in PRIVATE_OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
