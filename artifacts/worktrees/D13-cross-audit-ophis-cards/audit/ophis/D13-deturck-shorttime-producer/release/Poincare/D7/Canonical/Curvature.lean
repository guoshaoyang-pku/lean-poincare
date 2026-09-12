/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-canonical-neighborhood)

**D7 canonical-neighborhood interface, part 2: the curvature normalization supplied by the
D7 curvature layer.**

`Poincare.D7.Canonical.Basic` defines `CurvatureScaleDatum r`, the curvature slot of the
canonical-neighborhood certificate: an algebraic `RiemannCurvatureData` with a nondegenerate
plane of sectional curvature `1/r²`.  This module inhabits that slot at the scale `r = 2` with
the D7 non-flat model `so3` of `Poincare.D7.Curvature.Example`, whose sectional curvature on
the `e₀`–`e₁` plane is kernel-checked to be `1/4 = 1/2²`.

This is the curvature-layer non-vacuity check of the canonical-neighborhood interface: the
certificate's curvature normalization is realized by a genuine (algebraic) curvature datum of
the D7 curvature layer, not merely assumed.

Every proof is complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

import Poincare.D7.Canonical.Basic
import Poincare.D7.Curvature.Example

set_option autoImplicit false

namespace Poincare
namespace D7
namespace Canonical

open Poincare.D7.Curvature
open Poincare.D7.Curvature.So3

noncomputable section

/-- **The D7 non-flat model realizes the curvature scale `2`.**  The `so(3)` mean-connection
datum has sectional curvature `1/4` on the plane spanned by `e₀` and `e₁`, which is exactly
`1/2²`. -/
noncomputable def so3CurvatureScaleDatum : CurvatureScaleDatum.{0, 0} 2 where
  V := So3.V
  ι := Fin 3
  data := So3.so3
  planeX := So3.e 0
  planeY := So3.e 1
  nondegenerate := So3.so3_isNondegenerate2Plane_e0_e1
  sectional_eq := by
    rw [So3.so3_sectionalCurvature_e0_e1]
    norm_num

/-- **The curvature normalization at scale `2` is inhabited**, by the D7 `so(3)` model. -/
theorem nonempty_curvatureScaleDatum_two : Nonempty (CurvatureScaleDatum.{0, 0} 2) :=
  ⟨so3CurvatureScaleDatum⟩

/-- **The normalization equation of the `so(3)` datum**, stated with the structure's instance
fields brought into scope by `letI`.  The value `1/4 = 1/2²` is the kernel-checked sectional
curvature of the `e₀`–`e₁` plane. -/
theorem so3CurvatureScaleDatum_sectional :
    letI := so3CurvatureScaleDatum.inst₁
    letI := so3CurvatureScaleDatum.inst₂
    letI := so3CurvatureScaleDatum.inst₃
    letI := so3CurvatureScaleDatum.inst₄
    letI := so3CurvatureScaleDatum.inst₅
    so3CurvatureScaleDatum.data.sectionalCurvature so3CurvatureScaleDatum.planeX
      so3CurvatureScaleDatum.planeY = 1 / 4 := by
  show So3.so3.sectionalCurvature (So3.e 0) (So3.e 1) = 1 / 4
  exact So3.so3_sectionalCurvature_e0_e1

end

end Canonical
end D7
end Poincare
