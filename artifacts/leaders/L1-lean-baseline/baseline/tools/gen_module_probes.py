#!/usr/bin/env python3
"""Generate one declaration-inventory probe per authored release module.

Each probe imports exactly one module and prints the constants *declared* in that
module (`MD <module> <name> <kind>` lines).  Running all probes gives the
declaration inventory needed to (a) enumerate declarations per module and
(b) compute which modules declare the same name and therefore cannot be imported
together.
"""
import os
import sys

ROOT = "release"
OUTDIR = "baseline/audit/probes"

KIND = '''def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v =>
      if v.safety == .unsafe then "unsafe_def"
      else if v.safety == .partial then "partial_def" else "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "recursor"'''

TEMPLATE = '''import Lean.Elab.Command
import @MOD@

open Lean Elab Command

namespace Probe@IDX@

@KIND@

end Probe@IDX@

open Probe@IDX@ in
run_cmd do
  let env ← getEnv
  let target : Name := `@MOD@
  let mut out : Array (Name × String) := #[]
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
        if env.header.moduleNames.getD idx .anonymous == target then
          out := out.push (n, kindOf ci)
    | none => pure ()
  for (n, k) in out do
    IO.println s!"MD\\t{target}\\t{n}\\t{k}"
'''


def main():
    mods = []
    for dirpath, dirnames, filenames in os.walk(ROOT):
        if ".lake" in dirpath.split(os.sep):
            continue
        for f in sorted(filenames):
            if f.endswith(".lean"):
                p = os.path.relpath(os.path.join(dirpath, f), ROOT)
                mods.append(p[:-5].replace(os.sep, "."))
    mods.sort()
    skip = {"D6LedgerProbe", "ReleaseClaims"}
    mods = [m for m in mods if m not in skip]
    os.makedirs(OUTDIR, exist_ok=True)
    manifest = []
    for i, m in enumerate(mods):
        path = os.path.join(OUTDIR, f"{i:04d}.lean")
        body = (TEMPLATE.replace("@IDX@", f"{i:04d}").replace("@MOD@", m)
                .replace("@KIND@", KIND))
        with open(path, "w") as f:
            f.write(body)
        manifest.append((i, m))
    with open(os.path.join(OUTDIR, "manifest.tsv"), "w") as f:
        for i, m in manifest:
            f.write(f"{i:04d}\t{m}\n")
    print(f"wrote {len(manifest)} probes to {OUTDIR}")


if __name__ == "__main__":
    sys.exit(main())
