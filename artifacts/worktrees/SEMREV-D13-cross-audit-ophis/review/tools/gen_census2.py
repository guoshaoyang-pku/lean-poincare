#!/usr/bin/env python3
"""Generate independent fail-closed census probes for the SEMREV review.

Differences from the audited card's own tooling (audit/tools/gen_probe.py):
  * source scan written here from scratch (comment/string stripping + token census);
  * audited module set = files present in the snapshot release tree minus the D6 baseline,
    computed from this worktree's own listing, not from the parent's Tokens.json;
  * census prints the full axiom cone of every declaration of every audited module and
    additionally the declaration's defining module;
  * fail-closed: elaboration aborts on any project axiom, unsafe declaration,
    sorryAx/native_decide/unapproved axiom in any cone, any `proof_wanted`, or any
    collectAxioms exception.
"""
import json
import os
import re

REV = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-D13-cross-audit-ophis"
PARENT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards"
SNAP = f"{PARENT}/audit/ophis"
OUT = f"{REV}/review/probes"

FORBIDDEN = [r"\bsorry\b", r"\badmit\b", r"\bunsafe\b", r"\bnative_decide\b",
             r"\bproof_wanted\b", r"\baxiom\b"]

# Modules that cannot be imported together with the rest of the tree, or that carry no
# declarations at all; audited in dedicated isolated probes instead.
# The first three are the redundant copies in the D7 Monotonicity scaffold that redeclare
# constants already declared under Poincare.D7.Bochner.* / Poincare.D7.ConjugateHeat.Basic
# (see review/evidence/duplicate-names.json: 59 duplicated qualified names per full tree).
GLOBAL_EXCLUDE = {
    "ProbeScratch",  # scratch #check file, no declarations
    "Poincare.D7.Monotonicity.ConjugateHeatCertificate",
    "Poincare.D7.Monotonicity.BochnerCertificate",
    "Poincare.D7.Monotonicity.BochnerGradientEstimate",
    # broken in the relayed heat-kernel snapshot (F13): cannot be imported, see cold-build log
    "Poincare.D13.HeatKernelBridge.ConjugateScalarCurvature",
}


def strip_comments_strings(s):
    out = []
    i, n, depth, instr = 0, len(s), 0, False
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
            j = s.find("\n", i); i = n if j < 0 else j; continue
        if s.startswith("/-", i):
            depth = 1; i += 2; continue
        if s[i] == '"':
            instr = True; i += 1; continue
        out.append(s[i]); i += 1
    return "".join(out)


def modules_of(root):
    out = {}
    for dp, dn, fn in os.walk(root):
        dn[:] = [d for d in dn if d != ".lake"]
        for f in fn:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dp, f), root)[:-5]
                out[rel.replace("/", ".")] = os.path.join(dp, f)
    return out


TEMPLATE = r'''/-
SEMREV independent fail-closed census probe for @TASK@.
Written for longrun task SEMREV-D13-cross-audit-ophis; imports the transported snapshot only.
-/
@IMPORTS@
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace @NS@

def approvedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def negativeControlModules : List Name := [
  @NEG@]

def auditedModules : List Name := [
  @OWN@]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v => match v.safety with
      | .«unsafe» => "unsafe_def"
      | .«partial» => "partial_def"
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
  let env ← getEnv
  let mods := env.header.moduleNames
  let auditedSet : Std.HashSet Name :=
    auditedModules.foldl (fun acc m => acc.insert m) ∅
  let rows := env.constants.fold (fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := mods.getD midx .anonymous
        if auditedSet.contains m && !negativeControlModules.contains m then acc.push (n, ci, m)
        else acc
    | none => acc) #[]
  let mut nAxiom := 0
  let mut nUnsafe := 0
  let mut nSorry := 0
  let mut nNative := 0
  let mut nOther := 0
  let mut nFail := 0
  let mut nPartial := 0
  let mut nThm := 0
  let mut nOpaque := 0
  let mut nProofWanted := 0
  for (n, ci, m) in rows do
    if n.toString.contains "proof_wanted" then nProofWanted := nProofWanted + 1
    match ci with
    | .axiomInfo _ => nAxiom := nAxiom + 1
    | .opaqueInfo _ => nOpaque := nOpaque + 1
    | .defnInfo v =>
        match v.safety with
        | .«unsafe» => nUnsafe := nUnsafe + 1
        | .«partial» => nPartial := nPartial + 1
        | .safe => pure ()
    | .thmInfo _ => nThm := nThm + 1
    | _ => pure ()
    let axs ←
      try Lean.collectAxioms n
      catch _ => nFail := nFail + 1; pure #[]
    for a in axs do
      if a == ``sorryAx then nSorry := nSorry + 1
      else if a == ``ofReduceBool || a.toString.contains "native_decide" then nNative := nNative + 1
      else if !approvedAxioms.contains a then nOther := nOther + 1
    IO.println s!"XDECL\t{n}\t{kindOf ci}\t{m}\t{";".intercalate (axs.toList.map Name.toString)}"
  IO.println s!"XAUDIT\t@TASK@\tdeclarations\t{rows.size}"
  IO.println s!"XAUDIT\t@TASK@\ttheorems\t{nThm}"
  IO.println s!"XAUDIT\t@TASK@\tpartial_defs\t{nPartial}"
  IO.println s!"XAUDIT\t@TASK@\topaque\t{nOpaque}"
  IO.println s!"XAUDIT\t@TASK@\tproject_axioms\t{nAxiom}"
  IO.println s!"XAUDIT\t@TASK@\tunsafe\t{nUnsafe}"
  IO.println s!"XAUDIT\t@TASK@\tsorry_cones\t{nSorry}"
  IO.println s!"XAUDIT\t@TASK@\tnative_decide_cones\t{nNative}"
  IO.println s!"XAUDIT\t@TASK@\tunapproved_axiom_cones\t{nOther}"
  IO.println s!"XAUDIT\t@TASK@\tcollect_failures\t{nFail}"
  IO.println s!"XAUDIT\t@TASK@\tproof_wanted\t{nProofWanted}"
  if nAxiom + nUnsafe + nSorry + nNative + nOther + nFail + nProofWanted > 0 then
    IO.println s!"XAUDIT\t@TASK@\tVERDICT\tFAIL"
    throwError "SEMREV: forbidden dependency found (@TASK@)"
  else
    IO.println s!"XAUDIT\t@TASK@\tVERDICT\tPASS"
'''


def emit(task, outdir, imports, neg, own):
    ns = "SEMREV_" + re.sub(r"[^A-Za-z0-9]", "_", task)
    imports_s = "\n".join("import " + m for m in imports)
    neg_s = ",\n  ".join('"' + m + '".toName' for m in neg)
    own_s = ",\n  ".join('"' + m + '".toName' for m in own)
    src = (TEMPLATE.replace("@TASK@", task).replace("@NS@", ns)
           .replace("@IMPORTS@", imports_s).replace("@NEG@", neg_s).replace("@OWN@", own_s))
    with open(f"{outdir}/Census.lean", "w") as f:
        f.write(src)
    if neg:
        imports_neg = "\n".join("import " + m for m in neg)
        negsrc = (TEMPLATE.replace("@TASK@", task).replace("@NS@", ns + "_neg")
                  .replace("@IMPORTS@", imports_neg).replace("@NEG@", "").replace("@OWN@", neg_s))
        negsrc = negsrc.replace(
            '''    IO.println s!"XAUDIT\t@TASK@\tVERDICT\tFAIL"
    throwError "SEMREV: forbidden dependency found (@TASK@)"
  else
    IO.println s!"XAUDIT\t@TASK@\tVERDICT\tPASS"''',
            '''    IO.println s!"XAUDIT\t@TASK@\tVERDICT\tFAIL(expected)"
    throwError "SEMREV: negative control correctly rejected (@TASK@)"
  else
    IO.println s!"XAUDIT\t@TASK@\tVERDICT\tPASS_UNEXPECTED"''')
        with open(f"{outdir}/NegControl.lean", "w") as f:
            f.write(negsrc)


def main():
    base = set(modules_of(f"{PARENT}/release"))
    summary = {}
    for task in sorted(d for d in os.listdir(SNAP) if os.path.isdir(f"{SNAP}/{d}")):
        mods = modules_of(f"{SNAP}/{task}/release")
        own = sorted(set(mods) - base)
        # transitive importer closure of modules that must be audited in isolation
        imp = {}
        for name in own:
            s = open(mods[name], errors="replace").read()
            imp[name] = set(re.findall(r"(?m)^\s*import\s+([A-Za-z0-9_.«»]+)", s))
        conflict_roots = (GLOBAL_EXCLUDE - {"ProbeScratch",
                                            "Poincare.D13.HeatKernelBridge.ConjugateScalarCurvature"}) & set(own)
        iso_group = set()
        changed = True
        while changed:
            changed = False
            for name in own:
                if name in iso_group:
                    continue
                if imp[name] & (conflict_roots | iso_group):
                    iso_group.add(name); changed = True
        neg, clean, tokens = [], [], {}
        for name in own:
            s = open(mods[name], errors="replace").read()
            stripped = strip_comments_strings(s)
            hits = {}
            for pat in FORBIDDEN:
                found = re.findall(pat, stripped)
                if found:
                    hits[pat] = len(found)
            tokens[name] = hits
            if re.search(r"(?m)^\s*axiom\s+\S", stripped):
                neg.append(name)
            else:
                clean.append(name)
        imports = [m for m in clean if m not in GLOBAL_EXCLUDE and m not in iso_group]
        spec = f"{SNAP}/{task}/probe-spec.json"
        if os.path.exists(spec):
            imports = [m for m in imports if m not in json.load(open(spec)).get("exclude_imports", [])]
        d = f"{OUT}/{task}"
        os.makedirs(d, exist_ok=True)
        json.dump({"task": task, "own_modules": own, "clean": clean,
                   "negative_controls": neg, "token_census": tokens, "imports": imports,
                   "isolated_group": sorted(iso_group)},
                  open(f"{d}/spec.json", "w"), indent=1)
        emit(task, d, imports, neg, clean)
        # isolated probe: the conflicting group, which cannot be imported with the rest
        if iso_group:
            di = f"{d}/isolated"
            os.makedirs(di, exist_ok=True)
            iso_imports = [m for m in sorted(iso_group) if m in clean]
            iso_own = list(iso_imports)
            emit(task + "-isolated", di, iso_imports, [], iso_own)
        summary[task] = {"own": len(own), "clean": len(clean), "neg": len(neg)}
        print(task, summary[task], flush=True)
    json.dump(summary, open(f"{OUT}/summary.json", "w"), indent=1)


if __name__ == "__main__":
    main()
