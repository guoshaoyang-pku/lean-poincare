/-
D9-adversarial-audit-release — probe: auxiliary `_unsafe_rec` constants and theorem
dependence on non-safe definitions.

The D6 axiom report (`manifest/axiom-report.json`) records `partial_def: 2`, naming
`D4Audit.sqTraj._unsafe_rec` and `Poincare.Longrun.Surgery.SurgeryChain.append._unsafe_rec`,
yet no source file in the release contains the keyword `partial`.  This probe answers, from
the kernel environment itself:

* does a *fresh* ordinary structural recursion (`D9Probe.g`) synthesise a `_unsafe_rec`
  companion, i.e. is `_unsafe_rec` a compiler-internal artefact rather than authored code?
* what exactly are the two shipped `_unsafe_rec` constants (type, safety)?
* does any release theorem's type or proof term mention a non-safe (`.unsafe`/`.partial`)
  definition?  (A theorem may not unfold such a definition, so this is a hygiene check,
  not by itself a soundness failure.)

Output lines are prefixed `PROBE` and are parsed into the D9 result card.
-/
import ReleaseCheck

open Lean

namespace D9Probe

/-- Fresh structural recursion; if Lean synthesises `D9Probe.g._unsafe_rec` for this,
then `_unsafe_rec` companions are ordinary compiler auxiliaries for structural recursion. -/
def g : ℕ → ℕ
  | 0 => 0
  | n + 1 => g n

end D9Probe

run_cmd do
  let env ← getEnv
  IO.println s!"PROBE\tfresh_g_f\t{env.contains `D9Probe.g._f}"
  IO.println s!"PROBE\tfresh_g_unsafe_rec\t{env.contains `D9Probe.g._unsafe_rec}"
  let mut n_unsafe := 0
  let mut n_partial := 0
  let mut unsafe_names : Array Name := #[]
  let mut partial_names : Array Name := #[]
  let isProject (n : Name) : Bool :=
    ["D4Audit", "D5ReleaseCheck", "D9Probe", "D9Audit", "Poincare", "Probe",
     "Ledger", "Audit", "Perelman", "ReleaseCheck", "ReleaseAudit"].any fun r =>
      (r.toName).isPrefixOf n
  for (n, ci) in env.constants.toList do
    if isProject n then
      match ci with
      | .defnInfo v =>
        if v.safety == .«unsafe» then
          n_unsafe := n_unsafe + 1; unsafe_names := unsafe_names.push n
        else if v.safety == .«partial» then
          n_partial := n_partial + 1; partial_names := partial_names.push n
      | _ => pure ()
  IO.println s!"PROBE\tproject_unsafe_defs\t{n_unsafe}"
  IO.println s!"PROBE\tproject_partial_defs\t{n_partial}"
  for n in unsafe_names do IO.println s!"PROBE\tunsafe_def\t{n}"
  for n in partial_names do IO.println s!"PROBE\tpartial_def\t{n}"
  -- does any release theorem mention a non-safe def?
  let mut dependent : Array (Name × Name) := #[]
  for (n, ci) in env.constants.toList do
    if isProject n then
      match ci with
      | .thmInfo _ =>
        for c in ci.getUsedConstantsAsSet do
          match env.find? c with
          | some (.defnInfo v) =>
            if v.safety != .safe then dependent := dependent.push (n, c)
          | _ => pure ()
      | _ => pure ()
  IO.println s!"PROBE\ttheorems_depending_on_nonsafe\t{dependent.size}"
  for (n, c) in dependent do IO.println s!"PROBE\ttheorem_nonsafe_dep\t{n}\t{c}"
