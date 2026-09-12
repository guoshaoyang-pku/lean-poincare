/-
Copyright (c) 2026 The Poincaré formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-surgery-neck-extinction)

**D7 surgery flow, part 1: surgery procedure data consuming canonical neighborhoods.**

This module extends the accepted D3 surgery ledger (`Poincare.Longrun.Surgery`) with the
canonical-neighborhood data at which a neck surgery is actually performed.  The D3 ledger
records a surgery datum `SurgeryDatum X Y` (pre/post manifolds, the cut neck, the relation and
the cut/cap loci) together with the preservation obligations `SurgeryCertificate`.  The
canonical-neighborhood interface (`Poincare.D7.Canonical`) supplies, at a scale `r`, the
classification datum `CanonicalNeighborhoodCertificate ε κ r X` whose three alternatives are
`neck`, `cap` and `compactSpherical`.

A Ricci-flow-with-surgery step is the following composite object:

* a D3 surgery datum `D : SurgeryDatum X Y` with its preservation certificate;
* a canonical-neighborhood certificate of kind `neck` at scale `r` on a pointed region, the
  region in which the surgery is performed;
* an identification of the D3 cut neck with that region;
* the surgery time and the curvature threshold at which the step is triggered.

`SurgeryProcedureData P D` bundles exactly this data.  It is the interface consumed by the
surgery-time ledger (`Poincare.D7.SurgeryFlow.Times`) and by the extinction skeleton
(`Poincare.D7.SurgeryFlow.Extinction`).

## Main definitions

* `SurgeryProcedureData P D` — the composite procedure datum described above;
* `SurgeryProcedureData.neck` — the ε-neck extracted from the canonical certificate;
* `ProcedureChain P X Y` — a finite chain of procedure data, extending the D3 `SurgeryChain`;
* `ProcedureChain.toSurgeryChain` — the forgetful map to the D3 ledger;
* `ProcedureChain.certificate` — the D3 `ChainCertificate` assembled from the procedure
  ledgers, so every checked D3 chain theorem applies verbatim.

## Main results

* `SurgeryProcedureData.toSurgeryCertificate` and the three preservation projections;
* `SurgeryProcedureData.neck_kind`, `neck_radius_pos`, `neck_scale` — the checked properties of
  the extracted ε-neck;
* `ProcedureChain.simplyConnected_preserved`, `...compact_preserved`,
  `...orientable_preserved` — preservation along a procedure chain, via the D3 chain theorem;
* `realLineProcedure` — a kernel-checked inhabitant of `SurgeryProcedureData` built from the
  D7 line-cylinder certificate, showing the interface is not vacuous.

Every proof is complete: no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

import Poincare.D7.Canonical.Models
import Poincare.Longrun.Surgery.Toy

set_option autoImplicit false

universe u

namespace Poincare.D7.SurgeryFlow

open Poincare.D7.Compactness
open Poincare.D7.Canonical
open Poincare.Longrun.Surgery

noncomputable section

/-! ## 1. The procedure datum -/

/-- **Surgery procedure datum.**  A single Ricci-flow-with-surgery step at interface level: the
D3 surgery datum `D` together with its D3 preservation certificate (`ledger`), the
canonical-neighborhood certificate at the surgery scale (`certificate`, of kind `neck`), an
identification of the D3 cut neck with the certified region (`neckEquiv`), and the surgery time
and curvature threshold (`time`, `curvatureThreshold`, `curvatureExceedsThreshold`).

The geometric existence of such a datum — that a sufficiently curved region really carries a
canonical neck certificate, that the neck is separating and that the cut-and-cap is admissible
— is *not* proved here; it is the missing input isolated in
`Poincare.D7.SurgeryFlow.Statements`.  This structure is the interface that a future proof of
the neck analysis must inhabit. -/
structure SurgeryProcedureData (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) : Type (u + 2) where
  /-- The D3 preservation obligations of the step. -/
  ledger : SurgeryCertificate P D
  /-- The canonical-neighborhood error scale `ε > 0`. -/
  epsilon : ℝ
  /-- The error scale is positive. -/
  epsilon_pos : 0 < epsilon
  /-- The noncollapsing constant `κ > 0`. -/
  kappa : ℝ
  /-- The noncollapsing constant is positive. -/
  kappa_pos : 0 < kappa
  /-- The canonical-neighborhood scale `r > 0`. -/
  radius : ℝ
  /-- The scale is positive. -/
  radius_pos : 0 < radius
  /-- The pointed region carrying the canonical-neighborhood certificate. -/
  neckRegion : PointedMetricSpace.{u}
  /-- The canonical-neighborhood certificate at scale `radius`. -/
  certificate : CanonicalNeighborhoodCertificate epsilon kappa radius neckRegion
  /-- The certificate is of the neck alternative, the only kind on which surgery cuts. -/
  kind_eq_neck : certificate.kind = CanonicalKind.neck
  /-- The D3 cut neck is identified with the certified region. -/
  neckEquiv : D.neck.Carrier ≃ neckRegion
  /-- The time at which the surgery is performed. -/
  time : ℝ
  /-- The curvature threshold triggering the surgery. -/
  curvatureThreshold : ℝ
  /-- The curvature threshold is positive. -/
  curvatureThreshold_pos : 0 < curvatureThreshold
  /-- Opaque: the curvature at the surgery time reaches the threshold (missing a-priori
  curvature estimate; named in `Poincare.D7.SurgeryFlow.Statements`). -/
  curvatureExceedsThreshold : Prop

namespace SurgeryProcedureData

variable {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}} {D : SurgeryDatum X Y}

/-- The D3 preservation certificate carried by a procedure datum. -/
theorem toSurgeryCertificate (S : SurgeryProcedureData P D) : SurgeryCertificate P D :=
  S.ledger

/-- Compactness is preserved by a procedure step (D3 obligation). -/
theorem compact_preserved (S : SurgeryProcedureData P D) : P.Compact X → P.Compact Y :=
  S.ledger.compact_preserved

/-- Orientability is preserved by a procedure step (D3 obligation). -/
theorem orientable_preserved (S : SurgeryProcedureData P D) : P.Orientable X → P.Orientable Y :=
  S.ledger.orientable_preserved

/-- The target topological invariant is preserved by a procedure step (D3 obligation). -/
theorem simplyConnected_preserved (S : SurgeryProcedureData P D) :
    P.SimplyConnected X → P.SimplyConnected Y :=
  S.ledger.simplyConnected_preserved

/-- The ε-neck extracted from the canonical-neighborhood certificate.  This is the region that
the geometric neck analysis cuts along. -/
def neck (S : SurgeryProcedureData P D) : EpsilonNeck S.epsilon S.radius S.neckRegion :=
  S.certificate.neckOf S.kind_eq_neck

/-- The extracted neck has the stated scale. -/
theorem neck_model_radius (S : SurgeryProcedureData P D) :
    S.neck.model.radius = S.radius :=
  S.neck.radius_eq

/-- The extracted neck scale is positive. -/
theorem neck_radius_pos (S : SurgeryProcedureData P D) : 0 < S.radius :=
  S.neck.radius_pos

/-- The extracted neck is ε-close to its cylinder model. -/
theorem neck_approx_distortion (S : SurgeryProcedureData P D) (x y : S.neckRegion) :
    |dist (S.neck.approx.approx x) (S.neck.approx.approx y) - dist x y| ≤ S.epsilon :=
  S.neck.approx.distortion x y

/-- The cross-section diameter of the extracted neck model is `π r`. -/
theorem neck_antipodal_dist (S : SurgeryProcedureData P D) :
    dist S.neck.model.space.base S.neck.model.antipodal = Real.pi * S.radius :=
  S.neck.antipodal_dist

/-- The curvature normalization slot of the certificate. -/
def curvatureScale (S : SurgeryProcedureData P D) : CurvatureScaleDatum S.radius :=
  S.certificate.curvature

/-- The metric noncollapsing shadow of the certificate. -/
def noncollapsing (S : SurgeryProcedureData P D) : MetricNoncollapsing S.kappa S.radius S.neckRegion :=
  S.certificate.noncollapsing

/-- The certificate scale is positive, read through the procedure datum. -/
theorem certificate_scale_pos (S : SurgeryProcedureData P D) : 0 < S.radius :=
  S.certificate.scale_pos

end SurgeryProcedureData

/-! ## 2. Extending the D3 surgery ledger to procedure chains -/

/-- **A finite chain of surgery procedure data.**  This is the D3 `SurgeryChain` with each step
enriched by a `SurgeryProcedureData`, i.e. by the canonical-neighborhood data at which the step
is performed. -/
inductive ProcedureChain (P : LedgerPredicates.{u}) : TopSpace.{u} → TopSpace.{u} → Type (u + 2)
  | nil (X : TopSpace.{u}) : ProcedureChain P X X
  | step {X Y Z : TopSpace.{u}} (D : SurgeryDatum X Y) (S : SurgeryProcedureData P D)
      (c : ProcedureChain P Y Z) : ProcedureChain P X Z

namespace ProcedureChain

variable {P : LedgerPredicates.{u}}

/-- The forgetful map from a procedure chain to the underlying D3 surgery chain. -/
def toSurgeryChain : {X Y : TopSpace.{u}} → ProcedureChain P X Y → SurgeryChain X Y
  | _, _, .nil X => .nil X
  | _, _, .step D _ c => .step D (toSurgeryChain c)

@[simp]
theorem toSurgeryChain_nil (X : TopSpace.{u}) :
    (ProcedureChain.nil (P := P) X).toSurgeryChain = SurgeryChain.nil X := rfl

@[simp]
theorem toSurgeryChain_step {X Y Z : TopSpace.{u}} (D : SurgeryDatum X Y)
    (S : SurgeryProcedureData P D) (c : ProcedureChain P Y Z) :
    (ProcedureChain.step D S c).toSurgeryChain = SurgeryChain.step D c.toSurgeryChain := rfl

/-- **The D3 chain certificate of a procedure chain.**  Each procedure datum carries its D3
preservation certificate, so the underlying D3 chain is certified.  This is the checked
extension of the D3 ledger: every theorem proved for `ChainCertificate` applies to procedure
chains without reproof. -/
theorem certificate : {X Y : TopSpace.{u}} → (c : ProcedureChain P X Y) →
    ChainCertificate P c.toSurgeryChain
  | _, _, .nil X => .nil X
  | _, _, .step _ S c => .step S.ledger (certificate c)

/-- Compactness is preserved along a procedure chain. -/
theorem compact_preserved {X Y : TopSpace.{u}} {c : ProcedureChain P X Y} :
    P.Compact X → P.Compact Y :=
  ChainCertificate.compact_preserved c.certificate

/-- Orientability is preserved along a procedure chain. -/
theorem orientable_preserved {X Y : TopSpace.{u}} {c : ProcedureChain P X Y} :
    P.Orientable X → P.Orientable Y :=
  ChainCertificate.orientable_preserved c.certificate

/-- The target topological invariant is preserved along a procedure chain. -/
theorem simplyConnected_preserved {X Y : TopSpace.{u}} {c : ProcedureChain P X Y} :
    P.SimplyConnected X → P.SimplyConnected Y :=
  ChainCertificate.simplyConnected_preserved c.certificate

end ProcedureChain

/-! ## 3. Non-vacuity: a concrete procedure datum -/

/-- The real line as a bundled topological space. -/
abbrev realLineTop : TopSpace.{0} where
  Carrier := ℝ
  topology := inferInstance

/-- The trivial D3 surgery datum on the real line; its cut neck is the line itself. -/
def realLineDatum : SurgeryDatum realLineTop realLineTop :=
  SurgeryDatum.trivial realLineTop

/-- **A concrete procedure datum.**  The D3 ledger certificate is the trivial one, and the
canonical-neighborhood certificate is the checked line-cylinder certificate at scale `2`
(`Poincare.D7.Canonical.lineCylinder_certificate`), whose kind is `neck` by construction.  This
shows that `SurgeryProcedureData` is inhabited and that its field system is consistent. -/
def realLineProcedure : SurgeryProcedureData toyLedger realLineDatum where
  ledger := ⟨fun h => h, fun h => h, fun h => h⟩
  epsilon := 1
  epsilon_pos := by norm_num
  kappa := 1
  kappa_pos := by norm_num
  radius := 2
  radius_pos := by norm_num
  neckRegion := lineCylinderInterface.space
  certificate :=
    lineCylinder_certificate (ε := 1) (κ := 1) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_three])
  kind_eq_neck := rfl
  neckEquiv := Equiv.refl ℝ
  time := 0
  curvatureThreshold := 1
  curvatureThreshold_pos := by norm_num
  curvatureExceedsThreshold := True

/-- **The procedure interface is inhabited.**  The concrete real-line procedure datum is a
kernel-checked witness. -/
theorem exists_surgeryProcedureData :
    Nonempty (SurgeryProcedureData toyLedger realLineDatum) :=
  ⟨realLineProcedure⟩

/-- The concrete procedure datum extracts a genuine ε-neck of scale `2`. -/
theorem realLineProcedure_neck_radius : realLineProcedure.radius = 2 := rfl

/-- A one-step procedure chain on the real line. -/
def realLineProcedureChain : ProcedureChain toyLedger realLineTop realLineTop :=
  .step realLineDatum realLineProcedure (.nil realLineTop)

/-- The concrete procedure chain forgets to the one-step D3 chain. -/
theorem realLineProcedureChain_toSurgeryChain :
    realLineProcedureChain.toSurgeryChain = .step realLineDatum (.nil realLineTop) := rfl

/-- The concrete procedure chain is certified in the D3 ledger. -/
theorem realLineProcedureChain_simplyConnected :
    toyLedger.SimplyConnected realLineTop → toyLedger.SimplyConnected realLineTop :=
  realLineProcedureChain.simplyConnected_preserved

end

end Poincare.D7.SurgeryFlow
