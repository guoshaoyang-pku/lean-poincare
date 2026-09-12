/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-divergence-ibp)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.haveILetI false

/-!
# Poincare.D7.Divergence.Basic

**D7 divergence / integration-by-parts layer, part 1: the incidence data of a finite oriented
graph, the discrete divergence, the boundary flux, and the integration-by-parts certificate.**

This module is part of the `D7-divergence-ibp` task. It consumes the accepted D7 scaffold
unchanged and adds only files under `Poincare/D7/Divergence/`.

## The discrete model

A finite oriented graph is described by `DivergenceData V E`: a finite vertex type `V`, a finite
edge type `E`, and the tail/head maps `src, tgt : E → V`. Every edge carries a real flow
`F : E → ℝ`, oriented from `src` to `tgt`.

* `DivergenceData.outFlow F v` — the total flow leaving `v` along edges whose tail is `v`;
* `DivergenceData.inFlow F v` — the total flow entering `v` along edges whose head is `v`;
* `DivergenceData.divergence F v = outFlow F v - inFlow F v` — the **discrete divergence**, the net
  outflow at `v`.

For a region `S : Finset V` (the "interior"), the module defines

* `DivergenceData.outFlux F S` / `DivergenceData.inFlux F S` — the total flux over the edges with
  tail (resp. head) in `S`;
* `DivergenceData.boundaryFlux F S` — the **boundary flux**: the flow along the edges with exactly
  one endpoint in `S`, taken with the outward sign;
* `DivergenceData.gradientPairing F φ S` — the interior pairing `∑_e F e (φ (tgt e) - φ (src e))`
  over the edges with both endpoints in `S`;
* `DivergenceData.divPairing F φ S` — the interior pairing `∑_{v ∈ S} φ v * divergence F v`;
* `DivergenceData.boundaryPairing F φ S` — the boundary pairing of `φ` against the boundary flux.

The main theorem of `Poincare.D7.Divergence.Graph` is the **discrete divergence theorem**
`∑_{v ∈ S} divergence F v = boundaryFlux F S`, and its pairing form
`divPairing + gradientPairing = boundaryPairing` (discrete integration by parts on a graph).

## The certificate

`IBPCertificate` records an integration-by-parts identity together with its **explicit boundary
terms**: the outgoing and incoming boundary pairings are fields, and the identity
`interiorTerm + fluxTerm = outBoundary - inBoundary` is a proof field. Every graph or slab
integration-by-parts identity of this layer is packaged as an `IBPCertificate`, so the boundary
bookkeeping is part of the kernel-checked datum rather than prose.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Finset

namespace Poincare.D7.Divergence

/-- **The incidence data of a finite oriented graph**, i.e. the data that defines a discrete
divergence operator. The vertex and edge types are finite, and every edge is oriented from its
tail `src` to its head `tgt`. -/
structure DivergenceData (V E : Type*) [Fintype V] [Fintype E] [DecidableEq V] where
  /-- The tail (source) of an oriented edge. -/
  src : E → V
  /-- The head (target) of an oriented edge. -/
  tgt : E → V

/-! ## The integration-by-parts certificate -/

/-- **Integration-by-parts certificate.** A certified discrete integration-by-parts identity with
explicit boundary terms: the interior (divergence) pairing, the interior (flux/gradient) pairing,
the outgoing boundary pairing, and the incoming boundary pairing, together with the proof of

`interiorTerm + fluxTerm = outBoundary - inBoundary`.

For the discrete graph layer the instance is `DivergenceData.ibpCertificate`; for the
finite-difference slab it is `Poincare.D7.Divergence.slabIBPCertificate`. -/
structure IBPCertificate where
  /-- The interior divergence pairing `∑_v φ v * divergence F v`. -/
  interiorTerm : ℝ
  /-- The interior flux pairing `∑_e F e * (φ (tgt e) - φ (src e))`. -/
  fluxTerm : ℝ
  /-- The outgoing boundary pairing (the flow leaving the region). -/
  outBoundary : ℝ
  /-- The incoming boundary pairing (the flow entering the region). -/
  inBoundary : ℝ
  /-- The certified integration-by-parts identity. -/
  ibp : interiorTerm + fluxTerm = outBoundary - inBoundary

namespace IBPCertificate

/-- The boundary term of a certificate: outgoing minus incoming boundary pairing. -/
def boundaryTerm (C : IBPCertificate) : ℝ := C.outBoundary - C.inBoundary

/-- The certified identity, rewritten in terms of the boundary term. -/
theorem ibp' (C : IBPCertificate) : C.interiorTerm + C.fluxTerm = C.boundaryTerm := C.ibp

/-- A certificate with vanishing boundary term certifies that the interior pairings cancel. -/
theorem eq_zero_of_boundaryTerm_eq_zero (C : IBPCertificate) (h : C.boundaryTerm = 0) :
    C.interiorTerm + C.fluxTerm = 0 := by
  rw [C.ibp', h]

/-- The interior term of a certificate with vanishing boundary term is the negative of the flux
term. -/
theorem interiorTerm_eq_neg_fluxTerm_of_boundaryTerm_eq_zero (C : IBPCertificate)
    (h : C.boundaryTerm = 0) : C.interiorTerm = -C.fluxTerm := by
  have := C.eq_zero_of_boundaryTerm_eq_zero h
  linarith

end IBPCertificate

namespace DivergenceData

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The total flow leaving the vertex `v`, i.e. the sum of the flow over the edges whose tail is
`v`. -/
def outFlow (D : DivergenceData V E) (F : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e = v), F e

/-- The total flow entering the vertex `v`, i.e. the sum of the flow over the edges whose head is
`v`. -/
def inFlow (D : DivergenceData V E) (F : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e = v), F e

/-- **The discrete divergence** of a flow at a vertex: the net outflow `outFlow - inFlow`. -/
def divergence (D : DivergenceData V E) (F : E → ℝ) (v : V) : ℝ :=
  D.outFlow F v - D.inFlow F v

/-- The total flux over the edges whose tail lies in the region `S`. -/
def outFlux (D : DivergenceData V E) (F : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S), F e

/-- The total flux over the edges whose head lies in the region `S`. -/
def inFlux (D : DivergenceData V E) (F : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S), F e

/-- **The boundary flux** of a flow through the boundary of a region `S`: the flow along the edges
with exactly one endpoint in `S`, taken with the outward sign. An edge leaving `S` contributes
`+F e`; an edge entering `S` contributes `-F e`. -/
def boundaryFlux (D : DivergenceData V E) (F : E → ℝ) (S : Finset V) : ℝ :=
  (∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∉ S), F e)
    - ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∉ S), F e

/-- The pairing `∑_e φ (src e) * F e` over the edges whose tail lies in `S`. -/
def outPairing (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S), φ (D.src e) * F e

/-- The pairing `∑_e φ (tgt e) * F e` over the edges whose head lies in `S`. -/
def inPairing (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S), φ (D.tgt e) * F e

/-- **The outgoing boundary pairing**: the pairing `φ (src e) * F e` over the edges leaving the
region `S`. This is the explicit outgoing boundary term of the integration-by-parts identity. -/
def boundaryOut (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∉ S),
    φ (D.src e) * F e

/-- **The incoming boundary pairing**: the pairing `φ (tgt e) * F e` over the edges entering the
region `S`. This is the explicit incoming boundary term of the integration-by-parts identity. -/
def boundaryIn (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∉ S),
    φ (D.tgt e) * F e

/-- **The boundary pairing**: the outgoing boundary pairing minus the incoming boundary pairing. -/
def boundaryPairing (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) : ℝ :=
  D.boundaryOut F φ S - D.boundaryIn F φ S

/-- The interior flux pairing `∑_e F e * (φ (tgt e) - φ (src e))` over the edges with both
endpoints in the region `S`. -/
def gradientPairing (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∈ S),
    F e * (φ (D.tgt e) - φ (D.src e))

/-- The interior divergence pairing `∑_{v ∈ S} φ v * divergence F v`. -/
def divPairing (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) : ℝ :=
  ∑ v ∈ S, φ v * D.divergence F v

/-- The pairing `∑_e φ (src e) * F e` over the edges with both endpoints in `S`. This is the
interior part of `outPairing` and the left-hand side of the interior cancellation. -/
def bothPairing (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∈ S),
    φ (D.src e) * F e

/-- The pairing `∑_e φ (tgt e) * F e` over the edges with both endpoints in `S`. This is the
interior part of `inPairing`. -/
def bothPairing' (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∈ S),
    φ (D.tgt e) * F e

/-! ## Combinatorial lemmas about finite sums -/

/-- **Fiberwise summation over a region.** Summing the fibers of a map `g : ι → κ` over a finite
region `S` is the same as summing over the preimage of `S`. -/
lemma sum_fiber_of_mem {ι κ : Type*} [Fintype κ] [DecidableEq κ] (s : Finset ι)
    (g : ι → κ) (f : ι → ℝ) (S : Finset κ) :
    ∑ j ∈ S, ∑ i ∈ s.filter (fun i => g i = j), f i
      = ∑ i ∈ s.filter (fun i => g i ∈ S), f i := by
  calc ∑ j ∈ S, ∑ i ∈ s.filter (fun i => g i = j), f i
      = ∑ j ∈ S, ∑ i ∈ s, if g i = j then f i else 0 := by
        simp only [Finset.sum_filter]
    _ = ∑ i ∈ s, ∑ j ∈ S, if g i = j then f i else 0 := by rw [Finset.sum_comm]
    _ = ∑ i ∈ s, if g i ∈ S then f i else 0 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_ite_eq]
    _ = ∑ i ∈ s.filter (fun i => g i ∈ S), f i := by rw [Finset.sum_filter]

/-- **Splitting a filtered sum** along a second decidable predicate: the sum over `p` is the sum
over `p ∧ q` plus the sum over `p ∧ ¬q`. -/
lemma sum_filter_split {ι : Type*} (p q : ι → Prop) [DecidablePred p] [DecidablePred q]
    (f : ι → ℝ) (s : Finset ι) :
    ∑ i ∈ s.filter p, f i
      = (∑ i ∈ s.filter (fun i => p i ∧ q i), f i)
        + ∑ i ∈ s.filter (fun i => p i ∧ ¬q i), f i := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hp : p i <;> by_cases hq : q i <;> simp [hp, hq]

/-- **The interior pairings differ by the gradient pairing.** The `src`-evaluated interior pairing
minus the `tgt`-evaluated interior pairing is the negative of the gradient pairing, since the two
sums run over the same set of interior edges. -/
lemma bothPairing_sub_bothPairing' (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ)
    (S : Finset V) : D.bothPairing F φ S - D.bothPairing' F φ S = -D.gradientPairing F φ S := by
  have hcongr : D.bothPairing' F φ S
      = ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∈ S),
          φ (D.tgt e) * F e := by
    simp only [bothPairing']
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext e
    simp [and_comm]
  simp only [bothPairing, gradientPairing] at hcongr ⊢
  rw [hcongr, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  ring

/-! ## Fiberwise forms of the flow sums -/

/-- The sum of the outgoing flows over a region is the outgoing flux. -/
lemma sum_outFlow (D : DivergenceData V E) (F : E → ℝ) (S : Finset V) :
    ∑ v ∈ S, D.outFlow F v = D.outFlux F S := by
  simpa [outFlow, outFlux] using
    (sum_fiber_of_mem (s := (Finset.univ : Finset E)) (g := D.src) (f := F) (S := S))

/-- The sum of the incoming flows over a region is the incoming flux. -/
lemma sum_inFlow (D : DivergenceData V E) (F : E → ℝ) (S : Finset V) :
    ∑ v ∈ S, D.inFlow F v = D.inFlux F S := by
  simpa [inFlow, inFlux] using
    (sum_fiber_of_mem (s := (Finset.univ : Finset E)) (g := D.tgt) (f := F) (S := S))

/-- The pairing of a potential against the outgoing flows over a region is the outgoing pairing. -/
lemma sum_mul_outFlow (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) :
    ∑ v ∈ S, φ v * D.outFlow F v = D.outPairing F φ S := by
  have h : ∀ v ∈ S, φ v * D.outFlow F v
      = ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e = v), φ (D.src e) * F e := by
    intro v _
    rw [outFlow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    have hsrc : D.src e = v := by simpa using he
    rw [hsrc]
  calc ∑ v ∈ S, φ v * D.outFlow F v
      = ∑ v ∈ S, ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e = v),
          φ (D.src e) * F e := Finset.sum_congr rfl h
    _ = ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S),
          φ (D.src e) * F e :=
        sum_fiber_of_mem (s := (Finset.univ : Finset E)) (g := D.src)
          (f := fun e => φ (D.src e) * F e) (S := S)
    _ = D.outPairing F φ S := rfl

/-- The pairing of a potential against the incoming flows over a region is the incoming pairing. -/
lemma sum_mul_inFlow (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) :
    ∑ v ∈ S, φ v * D.inFlow F v = D.inPairing F φ S := by
  have h : ∀ v ∈ S, φ v * D.inFlow F v
      = ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e = v), φ (D.tgt e) * F e := by
    intro v _
    rw [inFlow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    have htgt : D.tgt e = v := by simpa using he
    rw [htgt]
  calc ∑ v ∈ S, φ v * D.inFlow F v
      = ∑ v ∈ S, ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e = v),
          φ (D.tgt e) * F e := Finset.sum_congr rfl h
    _ = ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S),
          φ (D.tgt e) * F e :=
        sum_fiber_of_mem (s := (Finset.univ : Finset E)) (g := D.tgt)
          (f := fun e => φ (D.tgt e) * F e) (S := S)
    _ = D.inPairing F φ S := rfl

end DivergenceData

end Poincare.D7.Divergence
