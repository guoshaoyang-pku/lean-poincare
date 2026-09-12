/-
D13 adapter probe: shared (book-independent infrastructure).
Upstream: frenzymath/Poincare-Conjecture @ bb91a091f0b968f8bbe8d861e025a88d82b161be,
package `shared`, pinned to Lean v4.32.1 + mathlib 520045ab.  Read-only consumer:
this probe only imports and re-checks upstream declarations.
-/
import Shared.MetricGeometry.LengthSpace
import Shared.Topology.FiberBundleT2
import Shared.Algebraic.BilinearForm.Basic
import Shared.Algebraic.BilinearForm.Riesz
import Shared.Algebraic.Auxiliary.OrthonormalBasisDiagonal

open Bundle

/-! ## Entry-point checks (elaboration of `#check` is the compile evidence) -/

#check @Shared.pathLength
#check @Shared.LengthSpace
#check @Shared.LengthSpace.edist_le_pathLength

#check @BilinearForm.Form
#check @BilinearForm.inner
#check @BilinearForm.IsSymm
#check @BilinearForm.IsPosDef
#check @BilinearForm.inner_comm
#check @BilinearForm.inner_self_pos
#check @BilinearForm.IsPosDef.nondegenerate
#check @BilinearForm.toDual
#check @BilinearForm.riesz
#check @BilinearForm.riesz_inner
#check @BilinearForm.riesz_unique

#check @FiberBundle.t2Space_totalSpace
#check @TangentBundle.t2Space

/-! ## Adapter terms: consuming the upstream API from a client package -/

-- The adapter terms below are deliberately `def`s: they are terms built from
-- upstream declarations, not new mathematical claims.  The style linter that
-- asks for `theorem` on proposition-valued definitions is disabled for them.
set_option linter.defProp false

noncomputable def d13_pathLength := @Shared.pathLength
noncomputable def d13_riesz := @BilinearForm.riesz
noncomputable def d13_riesz_unique := @BilinearForm.riesz_unique
@[reducible] noncomputable def d13_t2TangentBundle := @TangentBundle.t2Space

/-! ## Axiom footprint of the consumed declarations -/

#print axioms Shared.LengthSpace.edist_le_pathLength
#print axioms BilinearForm.riesz
#print axioms BilinearForm.riesz_unique
#print axioms FiberBundle.t2Space_totalSpace
#print axioms TangentBundle.t2Space
