#!/usr/bin/env python3
"""Generate import-closure partitions of the release package and one fail-closed
axiom/dependency audit module per partition.

Some release modules vendor byte-equal copies of declarations that already exist in
another module (a worktree-scoped workaround), so no single Lean environment can
import the whole package.  This script parses the `import` graph, computes the set
of modules whose transitive closure contains a duplicated declaration cluster, and
splits the package into import-disjoint groups.  Every module is a seed of exactly
one group, so every declaration is audited exactly once.

Usage: gen_grouped_audit.py [vendorfiles...]
       (default vendored cluster = the three Poincare.D7.Monotonicity copies)
"""
import os
import sys

ROOT = "release"
OUTDIR = "baseline/audit"

DEFAULT_VENDORED = [
    "Poincare.D7.Monotonicity.BochnerCertificate",
    "Poincare.D7.Monotonicity.BochnerGradientEstimate",
    "Poincare.D7.Monotonicity.ConjugateHeatCertificate",
]

EXPECTED_BAD = [
    "d12NegControlBadAxiom",
    "d12NegControlBadTheorem",
    "Poincare.D12.VolumeIBP.Audit.negativeControl",
]

BODY = r'''
open Lean Elab Command

namespace L1BaselineAudit@LABEL@

/-- Modules whose declarations are enumerated in this partition. -/
def targetModules : Array Name := #[
@MODULES@
]

/-- Kernel axioms approved for this baseline. -/
def approvedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Documented negative controls: their cones MUST be flagged. -/
def expectedBad : Array Name := #[
@BAD@
]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v =>
      if v.safety == .unsafe then "unsafe_def"
      else if v.safety == .partial then "partial_def" else "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "recursor"

end L1BaselineAudit@LABEL@

open L1BaselineAudit@LABEL@ in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let rows : Array (Name × ConstantInfo × Name) :=
    env.constants.fold (fun acc n ci =>
      match env.getModuleIdxFor? n with
      | some midx =>
          let m := mods.getD midx .anonymous
          if targetModules.contains m then acc.push (n, ci, m) else acc
      | none => acc) #[]
  let mut nDecl : Nat := 0
  let mut nTheorem : Nat := 0
  let mut nDef : Nat := 0
  let mut nAxiom : Nat := 0
  let mut nUnsafe : Nat := 0
  let mut nPartial : Nat := 0
  let mut nSorry : Nat := 0
  let mut nNative : Nat := 0
  let mut nUnexpected : Nat := 0
  let mut nExpectedSeen : Nat := 0
  let mut nCollectFail : Nat := 0
  let mut modulesSeen : Array Name := #[]
  let mut deps : Array String := #[]
  for (n, ci, m) in rows do
    if !modulesSeen.contains m then modulesSeen := modulesSeen.push m
    nDecl := nDecl + 1
    let kind := kindOf ci
    if kind == "theorem" then nTheorem := nTheorem + 1
    if kind == "def" || kind == "partial_def" then nDef := nDef + 1
    if kind == "axiom" then nAxiom := nAxiom + 1
    if kind == "unsafe_def" then nUnsafe := nUnsafe + 1
    if kind == "partial_def" then nPartial := nPartial + 1
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    for d in used do
      match env.getModuleIdxFor? d with
      | some didx =>
          if targetModules.contains (mods.getD didx .anonymous) then
            deps := deps.push s!"{n}\t{d}"
      | none => pure ()
    let axs ←
      try
        Lean.collectAxioms n
      catch _ =>
        nCollectFail := nCollectFail + 1
        pure #[]
    let extra := axs.filter (fun a => !approvedAxioms.contains a)
    if extra.contains `sorryAx then nSorry := nSorry + 1
    if extra.any (fun a => a.toString.contains "native") then nNative := nNative + 1
    if !extra.isEmpty then
      if expectedBad.contains n then nExpectedSeen := nExpectedSeen + 1
      else nUnexpected := nUnexpected + 1
    IO.println s!"L1AXROW\t{n}\t{kind}\t{m}\t{String.intercalate "," (axs.toList.map toString)}\t{String.intercalate "," (extra.toList.map toString)}\t{n.isInternal}"
  for m in modulesSeen do
    IO.println s!"L1MOD\t{m}\t{(rows.filter (fun r => r.2.2 == m)).size}"
  for d in deps do IO.println s!"L1DEP\t{d}"
  IO.println s!"L1SUM\tpartition\t@LABEL@"
  IO.println s!"L1SUM\tdeclarations\t{nDecl}"
  IO.println s!"L1SUM\ttheorems\t{nTheorem}"
  IO.println s!"L1SUM\tdefs\t{nDef}"
  IO.println s!"L1SUM\taxioms\t{nAxiom}"
  IO.println s!"L1SUM\tunsafe\t{nUnsafe}"
  IO.println s!"L1SUM\tpartial\t{nPartial}"
  IO.println s!"L1SUM\tsorry\t{nSorry}"
  IO.println s!"L1SUM\tnative\t{nNative}"
  IO.println s!"L1SUM\tunexpected_violations\t{nUnexpected}"
  IO.println s!"L1SUM\texpected_negative_controls_seen\t{nExpectedSeen}"
  IO.println s!"L1SUM\tcollect_failures\t{nCollectFail}"
  IO.println s!"L1SUM\tpackage_modules_with_declarations\t{modulesSeen.size}"
  IO.println s!"L1SUM\tdeclared_modules_imported\t{targetModules.size}"
  IO.println s!"L1SUM\tdep_edges\t{deps.size}"
  let ok := nUnexpected == 0 && nCollectFail == 0 && nSorry == 0
    && nUnsafe == 0 && nNative == 0
    && (nExpectedSeen == 0 || nExpectedSeen == expectedBad.size)
  if ok then
    IO.println "L1AXVERDICT\tPASS"
  else
    IO.println "L1AXVERDICT\tFAIL"
    throwError "L1 baseline axiom audit @LABEL@ FAILED (unexpected={nUnexpected}, collect_fail={nCollectFail}, sorry={nSorry}, unsafe={nUnsafe}, native={nNative}, expected_seen={nExpectedSeen}/{expectedBad.size})"
'''


def modules_and_imports():
    mods = []
    imports = {}
    for dirpath, dirnames, filenames in os.walk(ROOT):
        if ".lake" in dirpath.split(os.sep):
            continue
        for f in sorted(filenames):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            m = os.path.relpath(p, ROOT)[:-5].replace(os.sep, ".")
            mods.append(m)
            imps = []
            for line in open(p, encoding="utf-8", errors="replace"):
                line = line.strip()
                if line.startswith("import "):
                    for tok in line[len("import "):].split():
                        imps.append(tok)
                elif line and not line.startswith(("--", "/-", "#", "@", "import")):
                    pass
            imports[m] = imps
    return sorted(mods), imports


def closure(mod, imports, cache):
    if mod in cache:
        return cache[mod]
    seen = {mod}
    stack = [mod]
    while stack:
        m = stack.pop()
        for i in imports.get(m, []):
            if i not in seen:
                seen.add(i)
                stack.append(i)
    cache[mod] = seen
    return seen


def main():
    vendored = sys.argv[1:] or DEFAULT_VENDORED
    mods, imports = modules_and_imports()
    built = [m for m in mods if m not in ("D6LedgerProbe", "ReleaseClaims")]
    cache = {}
    group2 = sorted(m for m in built if any(v in closure(m, imports, cache) for v in vendored))
    group1 = [m for m in built if m not in set(group2)]
    groups = [("G1", group1), ("G2", group2)]
    os.makedirs(OUTDIR, exist_ok=True)
    summary = {"vendored_clusters": vendored, "total_modules": len(built),
               "groups": {lab: {"count": len(g), "modules": g} for lab, g in groups}}
    import json
    json.dump(summary, open(os.path.join(OUTDIR, "partition.json"), "w"), indent=1)
    for lab, g in groups:
        body = ("/- GENERATED by baseline/tools/gen_grouped_audit.py — do not edit. -/\n"
                + "\n".join(f"import {m}" for m in g) + "\n"
                + BODY.replace("@LABEL@", lab)
                .replace("@MODULES@", ",\n".join(f"  `{m}" for m in g))
                .replace("@BAD@", ",\n".join(f"  `{n}" for n in EXPECTED_BAD)))
        with open(os.path.join(OUTDIR, f"AxiomAudit_{lab}.lean"), "w") as f:
            f.write(body)
        print(f"{lab}: {len(g)} modules -> {OUTDIR}/AxiomAudit_{lab}.lean")
    print("G2 members:", group2)


if __name__ == "__main__":
    main()
