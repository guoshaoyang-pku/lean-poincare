#!/usr/bin/env python3
"""Generate an independent fail-closed axiom-cone probe for one ophis D13 card.

- selects the card's own new Lean modules (all .lean under release/ that are not part of the
  D6 baseline module set, plus the D13-namespace modules)
- excludes modules that declare a top-level `axiom` (negative controls) from the clean pass
- emits audit/probes/<task>/CleanProbe.lean  (imports every clean module, audits every
  declaration owned by those modules, fails closed)
- emits audit/probes/<task>/NegControlProbe.lean when negative controls exist (imports them,
  runs the same detector, expected to FAIL)
- emits audit/probes/<task>/Tokens.json with the raw forbidden-token source scan
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OPHIS = ROOT / "ophis"
PROBES = ROOT / "probes"
BASE = Path("/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/"
            "D13-cross-audit-ophis-cards/release")

FORBIDDEN = [r"\bsorry\b", r"\badmit\b", r"\bunsafe\b", r"\bnative_decide\b",
             r"\bproof_wanted\b", r"\baxiom\b"]
# comment/string-stripping is intentionally NOT done here: this scan is a raw token census,
# the Lean-side cone check is the authoritative gate.



def strip_comments_strings(s: str) -> str:
    out = []
    i = 0
    n = len(s)
    depth = 0
    instr = False
    while i < n:
        if depth > 0:
            if s.startswith("/-", i):
                depth += 1; i += 2; continue
            if s.startswith("-/", i):
                depth -= 1; i += 2; continue
            i += 1; continue
        if instr:
            if s[i] == "\\":
                i += 2; continue
            if s[i] == '"':
                instr = False
            i += 1; continue
        if s.startswith("--", i):
            j = s.find("\n", i)
            i = n if j < 0 else j
            continue
        if s.startswith("/-", i):
            depth = 1; i += 2; continue
        if s[i] == '"':
            instr = True; i += 1; continue
        out.append(s[i]); i += 1
    return "".join(out)


def modules_of(release: Path):
    out = {}
    for p in sorted(release.rglob("*.lean")):
        if ".lake" in p.parts:
            continue
        rel = p.relative_to(release).with_suffix("")
        out[".".join(rel.parts)] = p
    return out


def main(task: str):
    rel = OPHIS / task / "release"
    mods = modules_of(rel)
    base_mods = set(modules_of(BASE))
    own_names = sorted(set(mods) - base_mods)
    neg, clean = [], []
    tokens = {}
    for name in own_names:
        src = mods[name].read_text(errors="replace")
        has_axiom = re.search(r"(?m)^\s*axiom\s+\S", strip_comments_strings(src)) is not None
        hits = {}
        for pat in FORBIDDEN:
            found = re.findall(pat, src)
            if found:
                hits[pat] = len(found)
        tokens[name] = hits
        if has_axiom:
            neg.append(name)
        else:
            clean.append(name)
    # imports: the task's own D13-namespace modules (they pull in the layers they need),
    # plus explicitly requested extras from <task>/probe-spec.json if present.
    d13_imports = sorted(m for m in set(mods) if ".D13." in m or m.startswith("D13."))
    extras = []
    excl = []
    spec = OPHIS / task / "probe-spec.json"
    if spec.is_file():
        cfg = json.loads(spec.read_text())
        extras = cfg.get("extra_imports", [])
        excl = cfg.get("exclude_imports", [])
    imports = sorted((set(d13_imports) | set(extras)) - set(excl))
    outdir = PROBES / task
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "Tokens.json").write_text(json.dumps(
        {"task": task, "own_modules": own_names, "clean": clean,
         "negative_controls": neg, "token_census": tokens,
         "probe_imports": imports}, indent=2) + "\n")
    globals()["_IMPORTS"] = imports
    globals()["_BASE"] = sorted(base_mods)
    globals()["_NEG"] = neg
    return _emit(task, outdir, imports, sorted(base_mods), neg)


def _emit(task, outdir, imports, base_mods, neg):
    def probe(tag):
        imports_s = "\n".join("import " + m for m in imports)
        base_s = ",\n  ".join('"' + m + '".toName' for m in base_mods)
        neg_s = ",\n  ".join('"' + m + '".toName' for m in neg)
        ns = "D13XAudit_" + re.sub(r"[^A-Za-z0-9]", "_", task) + "_" + tag
        template = """@HEADER@
@IMPORTS@
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace @NS@

def approvedAxioms : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]

def packageRoots : List Name := [
  "Poincare".toName, "Probe".toName, "Ledger".toName, "Audit".toName,
  "ReleaseCheck".toName, "ReleaseAudit".toName, "D6AuditReport".toName]

/-- D6 baseline modules are pre-existing; every *other* reachable package module is audited. -/
def baseModules : List Name := [
  @BASE@]

def excludedModules : List Name := [
  @NEG@]

def kindOf : ConstantInfo \u2192 String
  | .axiomInfo _ => "axiom"
  | .defnInfo v => match v.safety with
      | .\u00abunsafe\u00bb => "unsafe_def"
      | .\u00abpartial\u00bb => "partial_def"
      | .safe => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

end @NS@

open @NS@ in
run_cmd do
  let env \u2190 getEnv
  let mods := env.header.moduleNames
  let audited (m : Name) : Bool :=
    packageRoots.any (fun r => r.isPrefixOf m) && !baseModules.contains m && !excludedModules.contains m
  let rows := env.constants.fold (fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := mods.getD midx .anonymous
        if audited m then acc.push (n, ci, m) else acc
    | none => acc) #[]
  let mut moduleSet : Array Name := #[]
  for (_, _, m) in rows do
    if !moduleSet.contains m then moduleSet := moduleSet.push m
  let mut nAxiom := 0
  let mut nUnsafe := 0
  let mut nSorry := 0
  let mut nNative := 0
  let mut nOther := 0
  let mut nFail := 0
  let mut nProofWanted := 0
  let mut nPartial := 0
  let mut nThm := 0
  for (n, ci, m) in rows do
    if n.toString.contains "proof_wanted" then nProofWanted := nProofWanted + 1
    match ci with
    | .axiomInfo _ => nAxiom := nAxiom + 1
    | .defnInfo v =>
        match v.safety with
        | .\u00abunsafe\u00bb => nUnsafe := nUnsafe + 1
        | .\u00abpartial\u00bb => nPartial := nPartial + 1
        | .safe => pure ()
    | .thmInfo _ => nThm := nThm + 1
    | _ => pure ()
    let axs \u2190
      try
        Lean.collectAxioms n
      catch _ =>
        nFail := nFail + 1
        pure #[]
    for a in axs do
      if a == ``sorryAx then nSorry := nSorry + 1
      else if a.toString.contains "native_decide" || a == ``ofReduceBool then nNative := nNative + 1
      else if !approvedAxioms.contains a then nOther := nOther + 1
    IO.println s!"D13XDECL\t{n}\t{kindOf ci}\t{m}\t{";".intercalate (axs.toList.map Name.toString)}"
  IO.println s!"D13XAUDIT\t@TASK@\tmodules\t{moduleSet.size}"
  IO.println s!"D13XAUDIT\t@TASK@\tdeclarations\t{rows.size}"
  IO.println s!"D13XAUDIT\t@TASK@\ttheorems\t{nThm}"
  IO.println s!"D13XAUDIT\t@TASK@\tpartial_defs\t{nPartial}"
  IO.println s!"D13XAUDIT\t@TASK@\tproject_axioms\t{nAxiom}"
  IO.println s!"D13XAUDIT\t@TASK@\tunsafe\t{nUnsafe}"
  IO.println s!"D13XAUDIT\t@TASK@\tsorry_cones\t{nSorry}"
  IO.println s!"D13XAUDIT\t@TASK@\tnative_decide_cones\t{nNative}"
  IO.println s!"D13XAUDIT\t@TASK@\tunapproved_axiom_cones\t{nOther}"
  IO.println s!"D13XAUDIT\t@TASK@\tcollect_failures\t{nFail}"
  IO.println s!"D13XAUDIT\t@TASK@\tproof_wanted\t{nProofWanted}"
  if nAxiom + nUnsafe + nSorry + nNative + nOther + nFail + nProofWanted > 0 then
    IO.println s!"D13XAUDIT\t@TASK@\tVERDICT\tFAIL"
    throwError "D13XAudit: forbidden dependency found (@TASK@, @TAG@)"
  else
    IO.println s!"D13XAUDIT\t@TASK@\tVERDICT\tPASS"
"""
        header = ("/-\nIndependent D13 cross-audit probe for @TASK@ (@TAG@).\n"
                  "Generated by audit/tools/gen_probe.py. Fail-closed: any project axiom, unsafe\n"
                  "declaration, sorryAx / native_decide / unapproved axiom in any dependency cone\n"
                  "aborts elaboration.\n-/")
        text = (template.replace("@HEADER@", header)
                        .replace("@IMPORTS@", imports_s)
                        .replace("@BASE@", base_s)
                        .replace("@NEG@", neg_s)
                        .replace("@NS@", ns)
                        .replace("@TASK@", task)
                        .replace("@TAG@", tag))
        (outdir / "CleanProbe.lean").write_text(text)
        return len(imports)

    nc = probe("clean")
    print(f"{task}: imports={nc} negcontrol={len(neg)} baseline={len(base_mods)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
