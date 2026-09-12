-- A3: type dump of the D6 release namespace
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
  let mut n : Nat := 0
  for (nm, ci) in env.constants.toList do
    if roots.any (fun r => r.isPrefixOf nm) then
      n := n + 1
      logInfo m!"A3TYPE {nm} : {ci.type}"
  logInfo m!"A3TYPE-COUNT: {n}"
