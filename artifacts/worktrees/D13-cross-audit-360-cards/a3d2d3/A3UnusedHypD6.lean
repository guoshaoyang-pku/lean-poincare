-- A3: unused-binder screen of the D6 release namespace
import ReleaseCheck

open Lean Elab Command

namespace A3Unused

partial def usedBinders (e : Expr) : Std.HashSet Nat :=
  go e 0 {}
where
  go (e : Expr) (depth : Nat) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
    match e with
    | .bvar i => if i < depth then acc.insert (depth - 1 - i) else acc
    | .lam _ d b _ => go b (depth + 1) (go d depth acc)
    | .forallE _ d b _ => go b (depth + 1) (go d depth acc)
    | .app f a => go a depth (go f depth acc)
    | .letE _ t v b _ => go b (depth + 1) (go v depth (go t depth acc))
    | .mdata _ b => go b depth acc
    | .proj _ _ b => go b depth acc
    | _ => acc

partial def leadingLams (e : Expr) : Nat :=
  match e with
  | .lam _ _ b _ => leadingLams b + 1
  | _ => 0

partial def leadingForalls (e : Expr) : Nat :=
  match e with
  | .forallE _ _ b _ => leadingForalls b + 1
  | _ => 0

partial def binderInfos (e : Expr) : List (Name × Expr × BinderInfo) :=
  match e with
  | .forallE n d b bi => (n, d, bi) :: binderInfos b
  | _ => []

def binderTag (bi : BinderInfo) : String :=
  if bi == BinderInfo.instImplicit then "instance"
  else if bi == BinderInfo.implicit then "implicit"
  else if bi == BinderInfo.strictImplicit then "strictImplicit"
  else "explicit"

end A3Unused

run_cmd do
  let env ← getEnv
  let roots : List Name := [`Poincare, `Audit, `Ledger]
  let mut targets : List Name := []
  for (n, _ci) in env.constants.toList do
    if roots.any (fun r => r.isPrefixOf n) then targets := n :: targets
  let ts := targets.reverse
  let mut flagged : Nat := 0
  let mut explicitFlagged : Nat := 0
  let mut checked : Nat := 0
  let mut skipped : Nat := 0
  for t in ts do
    match env.find? t with
    | none => skipped := skipped + 1
    | some ci =>
      let v? := match ci with
        | .thmInfo v => some v.value
        | .defnInfo v => some v.value
        | _ => none
      match v? with
      | none => skipped := skipped + 1
      | some v =>
        let nv := A3Unused.leadingLams v
        let nt := A3Unused.leadingForalls ci.type
        if nv == nt && nv > 0 then
          checked := checked + 1
          let used := A3Unused.usedBinders v
          let infos := A3Unused.binderInfos ci.type
          for i in List.range nv do
            if !used.contains i then
              let (n, d, bi) := infos[i]!
              flagged := flagged + 1
              let tag := A3Unused.binderTag bi
              if tag == "explicit" then explicitFlagged := explicitFlagged + 1
              logInfo m!"A3UNUSED-FLAG: {t} binder#{i} ({n} : {d}) [{tag}]"
        else
          skipped := skipped + 1
  logInfo m!"A3UNUSED: checked {checked}, skipped {skipped}, flags {flagged}, explicit flags {explicitFlagged}"
