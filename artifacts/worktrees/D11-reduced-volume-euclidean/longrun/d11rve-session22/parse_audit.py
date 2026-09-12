#!/usr/bin/env python3
"""Session22 independent parser for the D11 #print axioms audit.

Reads:
  * the Audit.lean source (to know which names were requested),
  * the raw `lake env lean Audit.lean` output (compiled in this session).

Emits JSON: per-name axiom lists, cone histogram, nonstandard list, coverage info.
Written from scratch this session; does not import any prior session's parser.
"""
import json
import re
import sys

ROOT = "/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-reduced-volume-euclidean"
AUDIT = f"{ROOT}/release/Poincare/D11/ReducedVolume/Audit.lean"
RAW = f"{ROOT}/longrun/d11rve-session22/compile_Audit.log"
CONTENT = [
    f"{ROOT}/release/Poincare/D11/ReducedVolume/Basic.lean",
    f"{ROOT}/release/Poincare/D11/ReducedVolume/StraightRays.lean",
    f"{ROOT}/release/Poincare/D11/ReducedVolume/Volume.lean",
    f"{ROOT}/release/Poincare/D11/ReducedVolume/Statements.lean",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

# --- 1. Names requested by Audit.lean, in order ---
audit_text = open(AUDIT).read()
requested = re.findall(r"^#print axioms\s+(\S+)\s*$", audit_text, re.M)

# --- 2. Parse raw output. A report is `'<name>' depends on axioms: [ ... ]`,
#        possibly wrapped over several lines. ---
raw = open(RAW).read()
# strip wrapping: collapse newlines that are inside a bracketed report
reports = {}
pending_name = None
buf = ""
for line in raw.splitlines():
    if line.startswith("'") and "' depends on axioms:" in line:
        if pending_name is not None:
            reports[pending_name] = buf
        head, rest = line.split("' depends on axioms:", 1)
        pending_name = head.lstrip("'")
        buf = rest
    elif line.startswith("'") and "' does not depend on any axioms" in line:
        if pending_name is not None:
            reports[pending_name] = buf
        pending_name = line.split("' does not depend on any axioms", 1)[0].lstrip("'")
        buf = "__NONE__"
    elif pending_name is not None:
        buf += " " + line
if pending_name is not None:
    reports[pending_name] = buf

parsed = {}
for name, body in reports.items():
    if body == "__NONE__":
        parsed[name] = None  # does not depend on any axioms
        continue
    m = re.search(r"\[(.*)\]", body, re.S)
    if not m:
        parsed[name] = None  # "does not depend on any axioms"
        continue
    items = [x.strip() for x in m.group(1).replace("\n", " ").split(",") if x.strip()]
    parsed[name] = items

# --- 3. Coverage: every audit request answered? every source declaration audited? ---
# `#print axioms foo` inside the namespace reports the fully qualified
# `Poincare.D11.ReducedVolume.foo`; match on the short (last) component.
parsed_by_short = {}
for full in parsed:
    short = full.rsplit(".", 1)[-1]
    assert short not in parsed_by_short, f"ambiguous short name {short}"
    parsed_by_short[short] = full
missing_reports = [n for n in requested if n not in parsed_by_short]
extra_reports = [n for n in parsed_by_short if n not in requested]

# declarations in the four content modules (def/theorem/structure/abbrev/instance)
decl_re = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|public\s+)*"
    r"(?:def|theorem|lemma|structure|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_'.]*)",
    re.M,
)
source_decls = []
for path in CONTENT:
    for m in decl_re.finditer(open(path).read()):
        source_decls.append(m.group(1))

# names in source are unqualified (inside the namespace); audit names are fully qualified
short_requested = [n.rsplit(".", 1)[-1] for n in requested]
unaudited = sorted(set(source_decls) - set(short_requested))
unmatched_requests = sorted(set(short_requested) - set(source_decls))

cone_hist = {}
nonstandard = []
for name in requested:
    cone = parsed.get(parsed_by_short[name])
    if cone is None:
        key = "[]"
    else:
        key = "[" + ", ".join(cone) + "]"
    cone_hist[key] = cone_hist.get(key, 0) + 1
    bad = [a for a in (cone or []) if a not in ALLOWED]
    if bad:
        nonstandard.append({"name": name, "axioms": cone})

union = sorted({a for cone in parsed.values() if cone for a in cone})
result = {
    "requested_count": len(requested),
    "reported_count": len(parsed),
    "missing_reports": missing_reports,
    "extra_reports": extra_reports,
    "source_declaration_count": len(source_decls),
    "source_declarations_unaudited": unaudited,
    "audit_requests_without_source_declaration": unmatched_requests,
    "cone_histogram": cone_hist,
    "union_of_all_cones": union,
    "nonstandard": nonstandard,
    "all_within_allowed": (not nonstandard) and set(union) <= ALLOWED,
    "per_declaration": {n: parsed[parsed_by_short[n]] for n in requested},
}
print(json.dumps(result, indent=1))
json.dump(result, open(f"{ROOT}/longrun/d11rve-session22/axiom_audit.json", "w"), indent=1)

ok = (
    not missing_reports
    and not nonstandard
    and set(union) <= ALLOWED
    and len(requested) == len(parsed_by_short)
)
print("\nVERDICT:", "OK" if ok else "FAIL", file=sys.stderr)
sys.exit(0 if ok else 1)
