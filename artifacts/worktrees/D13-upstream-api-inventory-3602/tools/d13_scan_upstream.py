#!/usr/bin/env python3
"""D13 upstream inventory scanner.

Scans the preserved frenzymath/Poincare-Conjecture snapshot under
third_party/frenzymath/Poincare-Conjecture and produces a machine-readable
inventory of

  * Lake packages: package name, pinned toolchain, pinned mathlib revision,
    library roots, file/line counts, license;
  * Lean modules: per-module line counts and comment/string-aware counts of
    the D5 hard-forbidden tokens (sorry, axiom, unsafe, native_decide,
    proof_wanted, sorryAx, admit);
  * top-level declarations: name, kind, module, file, line, statement head,
    and whether the declaration's own body contains an admitted step.

Everything is read-only with respect to the upstream snapshot.  The script
never rewrites upstream files.

Usage:
  python3 tools/d13_scan_upstream.py <upstream_root> <out_dir>
"""

from __future__ import annotations

import datetime as _dt
import importlib.util
import json
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
D5_SCANNER = REPO / "input" / "d5-tools" / "scan_forbidden.py"


def _load_d5_scanner():
    spec = importlib.util.spec_from_file_location("d5_scan_forbidden", D5_SCANNER)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


D5 = _load_d5_scanner()
HARD = list(D5.HARD)
SOFT = list(D5.SOFT)
PATTERNS = {t: re.compile(r"\b" + re.escape(t) + r"\b") for t in HARD + SOFT}

DECL_KEYWORDS = (
    "theorem|lemma|def|abbrev|structure|class|instance|axiom|opaque|example|"
    "inductive"
)
MODIFIERS = r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)"
    + MODIFIERS
    + r"(?P<kind>"
    + DECL_KEYWORDS
    + r")\b[ \t]*(?P<rest>.*)$",
    re.MULTILINE,
)
ATTR_RE = re.compile(r"^\s*@\[(.*)\]\s*$")
NAME_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_'\.\!]*)")
STRUCT_KINDS = {"structure", "class", "inductive"}
DATA_KINDS = {"def", "abbrev", "instance", "opaque"}
PROOF_KINDS = {"theorem", "lemma", "example"}

TOPIC_PATTERNS = {
    "geometry": re.compile(
        r"riemann|connection|curvature|geodesic|metric|jacobi|tensor|manifold|"
        r"tangent|levi|covariant|exponential|isometr|submanifold|hypersurface|"
        r"shape[_ ]?operator|second[_ ]?fundamental|bundle|frame|chart|"
        r"parallel|ricci|scalar|sectional|volume|distance|hopf|killing|"
        r"lie[_ ]?derivative|differential[_ ]?form|orientation|chern|"
        r"laplace[_ ]?beltrami|harmonic",
        re.IGNORECASE,
    ),
    "pde_heat": re.compile(
        r"heat|parabolic|laplac|maximum[_ ]?principle|sobolev|elliptic|"
        r"\bpde\b|wave|energy|estimate|regularity|schauder|holder|gradient|"
        r"weak[_ ]?solution|distribution|dirichlet|neumann|harnack|"
        r"mean[_ ]?value|green|fundamental[_ ]?solution|caccioppoli|"
        r"interior|boundary|morrey|garding|de[_ ]?giorgi|nash|moser|"
        r"semigroup|eigenvalue|spectral|steklov|poincare[_ ]?inequality|"
        r"reaction|diffusion|drift|entropy|monotonicity",
        re.IGNORECASE,
    ),
    "topology": re.compile(
        r"topolog|homotop|homolog|fundamental[_ ]?group|covering|simply[_ ]?connected|"
        r"manifold|surgery|compact|sphere|cell[_ ]?complex|\bcw\b|fibration|"
        r"fiber|fibre|triangulat|homeomorph|embedding|neighborhood|retract|"
        r"brouwer|fixed[_ ]?point|degree|mapping[_ ]?class|handle|bordism|"
        r"cobordism|knot|thom|obstruction|characteristic[_ ]?class|"
        r"van[_ ]?kampen|seifert|connected[_ ]?sum|irreducible|prime|"
        r"poincare[_ ]?duality|excision|mayer[_ ]?vietoris|spectral[_ ]?sequence",
        re.IGNORECASE,
    ),
}


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return path.read_text(encoding="utf-8", errors="replace")


def split_code(text: str):
    """Return comment/string-blanked code using the D5 scanner helper."""
    return D5.strip_comments_and_strings(text)


def decl_statement(code: str, start: int, kind: str) -> str:
    """Statement head: text from `start` to the first depth-0 `:=` / `where`."""
    depth = 0
    i = start
    n = len(code)
    while i < n:
        c = code[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "\n" and depth <= 0:
            # end of the header line; a declaration may continue on the next
            # line only if the line ends with a connector or opens a binder
            rest = code[i + 1 : i + 200].lstrip()
            if rest.startswith((":", "→", "->", "|", "(", "[", "{", "∀", "∃", ",")):
                pass
            else:
                break
        elif depth <= 0 and c == ":" and code[i : i + 2] == ":=":
            break
        elif depth <= 0 and code.startswith("where", i):
            break
        elif depth <= 0 and c in "|" and kind in STRUCT_KINDS:
            break
        i += 1
        if i - start > 1200:
            break
    return " ".join(code[start:i].split())


def module_name(path: Path, root: Path) -> str:
    """Lake module name: path relative to the owning package root."""
    roots = [root / "shared", root / "PoincareConjecture"]
    fs = root / "formalized-sources"
    if fs.is_dir():
        roots += [d for d in sorted(fs.iterdir()) if d.is_dir()]
    for r in roots:
        try:
            rel = path.relative_to(r).as_posix()
        except ValueError:
            continue
        return rel[: -len(".lean")].replace("/", ".")
    return str(path.relative_to(root))[: -len(".lean")].replace(os.sep, ".")


def scan_module(path: Path, root: Path):
    text = read_text(path)
    code = split_code(text)
    rel = str(path.relative_to(root))
    module = module_name(path, root)
    lines = text.count("\n") + (0 if text.endswith("\n") else 1)

    token_counts = {}
    for tok, pat in PATTERNS.items():
        matches = list(pat.finditer(code))
        if matches:
            token_counts[tok] = len(matches)

    decls = []
    matches = list(DECL_RE.finditer(code))
    for idx, m in enumerate(matches):
        kind = m.group("kind")
        rest = m.group("rest")
        nm = NAME_RE.match(rest.strip())
        name = nm.group(1) if nm else ""
        start = m.start()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(code)
        body = code[start:end]
        admitted = bool(re.search(r"\bsorry\b|\badmit\b", body)) or kind == "axiom"
        stmt = decl_statement(code, start, kind)
        # attributes directly above the declaration
        head = code[max(0, start - 400) : start]
        attrs = [a.group(1).strip() for a in ATTR_RE.finditer(head)]
        decls.append(
            {
                "name": name,
                "kind": kind,
                "module": module,
                "file": rel,
                "line": text[: start].count("\n") + 1
                if False
                else code[:start].count("\n") + 1,
                "statement_head": stmt[:600],
                "attributes": attrs[-2:],
                "admitted": admitted,
                "has_sorry": bool(re.search(r"\bsorry\b", body)),
                "is_axiom": kind == "axiom",
            }
        )
    return {
        "module": module,
        "file": rel,
        "lines": lines,
        "decl_count": len(decls),
        "tokens": token_counts,
        "decls": decls,
    }


def package_of(rel: str) -> str:
    parts = rel.split(os.sep)
    if parts[0] == "shared":
        return "shared"
    if parts[0] == "PoincareConjecture":
        return "PoincareConjecture"
    if parts[0] == "formalized-sources" and len(parts) > 1:
        return parts[1]
    return parts[0]


def lean_libraries(pkg_dir: Path):
    lf = pkg_dir / "lakefile.lean"
    out = []
    if lf.exists():
        txt = lf.read_text(encoding="utf-8", errors="replace")
        for m in re.finditer(r"lean_lib\s+(\w+)", txt):
            out.append(m.group(1))
    return out


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__)
        return 2
    root = Path(sys.argv[1]).resolve()
    out_dir = Path(sys.argv[2]).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    sys.path.insert(0, str(D5_SCANNER.parent))
    files = sorted(root.rglob("*.lean"))
    modules = {}
    for f in files:
        try:
            info = scan_module(f, root)
        except Exception as exc:  # pragma: no cover - defensive
            info = {
                "module": str(f.relative_to(root)),
                "file": str(f.relative_to(root)),
                "lines": 0,
                "decl_count": 0,
                "tokens": {},
                "decls": [],
                "error": repr(exc),
            }
        modules[info["file"]] = info

    # package aggregation
    pkg_map = {}
    for rel, info in modules.items():
        pkg = package_of(rel)
        entry = pkg_map.setdefault(
            pkg,
            {
                "package": pkg,
                "files": 0,
                "lines": 0,
                "decls": 0,
                "admitted_decls": 0,
                "axiom_decls": 0,
                "modules_with_admissions": [],
                "token_totals": {},
                "dir": None,
            },
        )
        entry["files"] += 1
        entry["lines"] += info["lines"]
        entry["decls"] += info["decl_count"]
        for d in info["decls"]:
            if d["admitted"]:
                entry["admitted_decls"] += 1
            if d["is_axiom"]:
                entry["axiom_decls"] += 1
        if info["tokens"]:
            entry["modules_with_admissions"].append(rel)
        for t, c in info["tokens"].items():
            entry["token_totals"][t] = entry["token_totals"].get(t, 0) + c

    # attach pin metadata from the package directory
    for pkg, entry in pkg_map.items():
        if pkg == "shared":
            pkg_dir = root / "shared"
        elif pkg == "PoincareConjecture":
            pkg_dir = root / "PoincareConjecture"
        else:
            pkg_dir = root / "formalized-sources" / pkg
        entry["dir"] = str(pkg_dir.relative_to(root))
        tc = pkg_dir / "lean-toolchain"
        entry["lean_toolchain"] = (
            tc.read_text().strip() if tc.exists() else None
        )
        man = pkg_dir / "lake-manifest.json"
        pins = {}
        if man.exists():
            try:
                data = json.loads(man.read_text())
                for p in data.get("packages", []):
                    pins[p.get("name")] = p.get("rev")
            except Exception:
                pins = {}
        entry["manifest_pins"] = pins
        entry["lean_libraries"] = lean_libraries(pkg_dir)
        entry["mathlib_rev"] = pins.get("mathlib")
        entry["toolchain_matches_snapshot"] = (
            entry["lean_toolchain"] == "leanprover/lean4:v4.32.1"
        )
        entry["mathlib_rev_matches_snapshot"] = (
            entry["mathlib_rev"] == "520045ab14e26149ee970e2e617ca04b09bde5d6"
        )

    # topic tagging per module (relevant to geometry / heat-PDE / topology)
    for rel, info in modules.items():
        tags = []
        for topic, pat in TOPIC_PATTERNS.items():
            if pat.search(rel) or any(pat.search(d["name"]) for d in info["decls"][:200]):
                tags.append(topic)
        info["topics"] = tags

    lic = root / "LICENSE"
    lic_text = lic.read_text(encoding="utf-8", errors="replace") if lic.exists() else ""
    lic_id = "Apache-2.0" if "Apache License" in lic_text else "unknown"

    stamp = _dt.datetime.now().astimezone().isoformat(timespec="seconds")
    modules_out = {
        "schema": "d13-upstream-modules-v1",
        "generated_at": stamp,
        "upstream_root": str(root),
        "file_count": len(files),
        "total_lines": sum(m["lines"] for m in modules.values()),
        "modules": modules,
    }
    (out_dir / "upstream-modules.json").write_text(
        json.dumps(modules_out, indent=1, sort_keys=False) + "\n"
    )
    packages_out = {
        "schema": "d13-upstream-packages-v1",
        "generated_at": stamp,
        "upstream_root": str(root),
        "license": lic_id,
        "license_file": "LICENSE" if lic.exists() else None,
        "packages": pkg_map,
    }
    (out_dir / "upstream-packages.json").write_text(
        json.dumps(packages_out, indent=1, sort_keys=False) + "\n"
    )

    # compact human summary
    summary = {
        "schema": "d13-upstream-summary-v1",
        "generated_at": stamp,
        "license": lic_id,
        "file_count": len(files),
        "total_lines": sum(m["lines"] for m in modules.values()),
        "packages": {
            p: {
                "files": e["files"],
                "lines": e["lines"],
                "decls": e["decls"],
                "admitted_decls": e["admitted_decls"],
                "axiom_decls": e["axiom_decls"],
                "lean_toolchain": e["lean_toolchain"],
                "mathlib_rev": e["mathlib_rev"],
                "lean_libraries": e["lean_libraries"],
                "modules_with_admissions": len(e["modules_with_admissions"]),
                "token_totals": e["token_totals"],
            }
            for p, e in sorted(pkg_map.items())
        },
    }
    (out_dir / "upstream-summary.json").write_text(
        json.dumps(summary, indent=1, sort_keys=False) + "\n"
    )
    print(json.dumps(summary["packages"], indent=1)[:4000])
    print(f"[scan] files={len(files)} packages={len(pkg_map)} -> {out_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
