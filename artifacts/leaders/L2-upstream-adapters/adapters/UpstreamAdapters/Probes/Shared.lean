import Shared
import Shared.MetricGeometry.LengthSpace
import Shared.Algebraic.BilinearForm.Basic
import Shared.Algebraic.BilinearForm.Riesz
import Shared.Topology.FiberBundleT2

/-!
# Compile-time API probes: Shared (book-agnostic infrastructure)

Each `#check` is a compile-time assertion that the named upstream declaration
exists and elaborates against the pinned toolchain (`leanprover/lean4:v4.32.1`,
mathlib `520045ab`).  A missing or renamed declaration turns this file into a
compile error, so a successful `lake build` is evidence that the inventory is
not prose-only.  No upstream proof is copied into this package.
-/

namespace UpstreamAdapters.Probes.Shared

-- Metric geometry: length spaces (Burago-Burago-Ivanov layer)
#check @Shared.pathLength
#check @Shared.LengthSpace
#check @Shared.LengthSpace.edist_le_pathLength

-- Algebraic core: Riesz extraction for positive-definite bilinear forms
#check @BilinearForm.Form
#check @BilinearForm.inner
#check @BilinearForm.IsPosDef
#check @BilinearForm.toDual
#check @BilinearForm.IsPosDef.nondegenerate
#check @BilinearForm.toDual_injective
#check @BilinearForm.inner_eq_iff_eq
#check @BilinearForm.toDualEquiv
#check @BilinearForm.riesz
#check @BilinearForm.riesz_inner
#check @BilinearForm.riesz_unique

-- Topology: T2 of total spaces of fibre bundles / tangent bundles
#check @FiberBundle.t2Space_totalSpace
#check @TangentBundle.t2Space

end UpstreamAdapters.Probes.Shared
