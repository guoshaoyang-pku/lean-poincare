-- A3 round-13 direct-reference dump (generated)
import Poincare.D12.TensorMaximumBochner.Audit
import Poincare.D12.TensorMaximumBochner.BochnerIdentity
import Poincare.D12.TensorMaximumBochner.PositivityPreservation
import Poincare.D12.TensorMaximumBochner.So3Model
import Poincare.D12.TensorMaximumBochner.So3Polynomial
import Poincare.D12.TensorMaximumBochner.So3RicciFlow
import Poincare.D12.TensorMaximumBochner.TangentCone
import Poincare.D12.TensorMaximumBochner.TensorCalculus

open Lean Elab Command
namespace A3R13U

partial def refsOf (e : Expr) (acc : Std.HashSet Name) : Std.HashSet Name :=
  match e with
  | .app f a         => refsOf a (refsOf f acc)
  | .lam _ t b _     => refsOf b (refsOf t acc)
  | .forallE _ t b _ => refsOf b (refsOf t acc)
  | .letE _ t v b _  => refsOf b (refsOf v (refsOf t acc))
  | .mdata _ b       => refsOf b acc
  | .proj _ _ b      => refsOf b acc
  | .const n _       => acc.insert n
  | _                => acc

def dump : CommandElabM Unit := do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if (`Poincare.D12).isPrefixOf n then
      let mut tv : Std.HashSet Name := {}
      tv := refsOf ci.type tv
      match ci.value? (allowOpaque := true) with
      | some v => tv := refsOf v tv
      | none => pure ()
      match ci with
      | .inductInfo ind => for c in ind.ctors do tv := tv.insert c
      | _ => pure ()
      let mut vonly : Std.HashSet Name := {}
      match ci.value? (allowOpaque := true) with
      | some v => vonly := refsOf v vonly
      | none => pure ()
      logInfo m!"A3R13U|REFS|{n}|tv|{tv.toList.map Name.toString}"
      logInfo m!"A3R13U|REFS|{n}|v|{vonly.toList.map Name.toString}"

end A3R13U

run_cmd A3R13U.dump
