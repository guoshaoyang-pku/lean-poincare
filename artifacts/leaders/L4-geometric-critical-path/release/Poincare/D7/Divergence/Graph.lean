/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-divergence-ibp)
-/

import Poincare.D7.Divergence.Basic

set_option linter.style.haveILetI false

/-!
# Poincare.D7.Divergence.Graph

**D7 divergence / integration-by-parts layer, part 2: the discrete divergence theorem on a finite
oriented graph and discrete integration by parts with explicit boundary terms.**

Let `D : DivergenceData V E` be a finite oriented graph and `F : E → ℝ` a flow.

* `DivergenceData.sum_divergence_eq_boundaryFlux` — the **discrete divergence theorem**: for every
  region `S : Finset V`,
  `∑_{v ∈ S} divergence F v = boundaryFlux F S`.
  Each edge with both endpoints in `S` contributes `+F e` to the divergence at its tail and
  `-F e` to the divergence at its head, so the interior contributions cancel; only the edges with
  exactly one endpoint in `S` survive, with the outward sign.
* `DivergenceData.graph_ibp` — **discrete integration by parts on a graph**: for every potential
  `φ : V → ℝ`,
  `divPairing F φ S + gradientPairing F φ S = boundaryPairing F φ S`.
  Here `divPairing = ∑_{v ∈ S} φ v * divergence F v`, the interior flux pairing is
  `gradientPairing = ∑_e F e * (φ (tgt e) - φ (src e))` over the interior edges, and the boundary
  pairing is the outgoing boundary term minus the incoming boundary term
  (`boundaryOut`, `boundaryIn`).
* `DivergenceData.ibpCertificate` — the `IBPCertificate` carrying the identity together with its
  explicit boundary terms `boundaryOut` and `boundaryIn`.
* `DivergenceData.sum_divergence_univ_eq_zero` — **flow conservation on a closed graph**: summing
  the divergence over all vertices gives zero.
* `DivergenceData.sum_divergence_eq_zero_of_closed` — flow conservation on any region with no
  boundary edge (`∀ e, src e ∈ S ↔ tgt e ∈ S`).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Finset

namespace Poincare.D7.Divergence

namespace DivergenceData

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **The discrete divergence theorem on a finite oriented graph.** The sum of the divergences
over the vertices of a region `S` equals the flux through the boundary of `S`. -/
theorem sum_divergence_eq_boundaryFlux (D : DivergenceData V E) (F : E → ℝ) (S : Finset V) :
    ∑ v ∈ S, D.divergence F v = D.boundaryFlux F S := by
  have hdiv : ∑ v ∈ S, D.divergence F v = D.outFlux F S - D.inFlux F S := by
    simp only [divergence]
    rw [Finset.sum_sub_distrib, D.sum_outFlow, D.sum_inFlow]
  have hsplit_out := sum_filter_split (s := (Finset.univ : Finset E))
    (p := fun e => D.src e ∈ S) (q := fun e => D.tgt e ∈ S) F
  have hsplit_in := sum_filter_split (s := (Finset.univ : Finset E))
    (p := fun e => D.tgt e ∈ S) (q := fun e => D.src e ∈ S) F
  have hboth :
      (∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∈ S), F e)
        = ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∈ S),
            F e := by
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext e
    simp [and_comm]
  rw [hdiv, outFlux, inFlux, hsplit_out, hsplit_in, hboth, boundaryFlux]
  ring

/-- **Discrete integration by parts on a finite oriented graph.** The divergence pairing plus the
interior flux pairing equals the boundary pairing, whose outgoing and incoming parts are the
explicit boundary terms `boundaryOut` and `boundaryIn`. -/
theorem graph_ibp (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) :
    D.divPairing F φ S + D.gradientPairing F φ S = D.boundaryPairing F φ S := by
  have hdiv : D.divPairing F φ S = D.outPairing F φ S - D.inPairing F φ S := by
    have h : ∀ v ∈ S, φ v * D.divergence F v
        = φ v * D.outFlow F v - φ v * D.inFlow F v := by
      intro v _
      rw [divergence, mul_sub]
    simp only [divPairing]
    rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, D.sum_mul_outFlow, D.sum_mul_inFlow]
  have hout : D.outPairing F φ S = D.bothPairing F φ S + D.boundaryOut F φ S := by
    simp only [outPairing, bothPairing, boundaryOut]
    exact sum_filter_split (s := (Finset.univ : Finset E))
      (p := fun e => D.src e ∈ S) (q := fun e => D.tgt e ∈ S) (fun e => φ (D.src e) * F e)
  have hin : D.inPairing F φ S = D.bothPairing' F φ S + D.boundaryIn F φ S := by
    simp only [inPairing, bothPairing', boundaryIn]
    exact sum_filter_split (s := (Finset.univ : Finset E))
      (p := fun e => D.tgt e ∈ S) (q := fun e => D.src e ∈ S) (fun e => φ (D.tgt e) * F e)
  have hbnd : D.boundaryPairing F φ S = D.boundaryOut F φ S - D.boundaryIn F φ S := rfl
  have hboth := D.bothPairing_sub_bothPairing' F φ S
  linarith

/-- **The integration-by-parts certificate of a finite graph**, carrying the divergence pairing,
the interior flux pairing, and the explicit outgoing/incoming boundary pairings. -/
def ibpCertificate (D : DivergenceData V E) (F : E → ℝ) (φ : V → ℝ) (S : Finset V) :
    IBPCertificate where
  interiorTerm := D.divPairing F φ S
  fluxTerm := D.gradientPairing F φ S
  outBoundary := D.boundaryOut F φ S
  inBoundary := D.boundaryIn F φ S
  ibp := D.graph_ibp F φ S

/-- The boundary pairing of the constant potential `1` is the boundary flux. -/
theorem boundaryPairing_one (D : DivergenceData V E) (F : E → ℝ) (S : Finset V) :
    D.boundaryPairing F (fun _ => 1) S = D.boundaryFlux F S := by
  simp [boundaryPairing, boundaryOut, boundaryIn, boundaryFlux]

/-- The interior flux pairing of the constant potential `1` vanishes. -/
theorem gradientPairing_one (D : DivergenceData V E) (F : E → ℝ) (S : Finset V) :
    D.gradientPairing F (fun _ => 1) S = 0 := by
  simp [gradientPairing]

/-- The divergence theorem is the integration-by-parts identity for the constant potential `1`:
the interior flux pairing vanishes and the boundary pairing is the boundary flux. -/
theorem sum_divergence_eq_boundaryFlux_of_ibp (D : DivergenceData V E) (F : E → ℝ)
    (S : Finset V) : ∑ v ∈ S, D.divergence F v = D.boundaryFlux F S := by
  have h := D.graph_ibp F (fun _ => 1) S
  rw [D.gradientPairing_one, add_zero, D.boundaryPairing_one] at h
  simpa [divPairing] using h

/-- **Flow conservation on a closed graph.** The divergence summed over all vertices vanishes. -/
theorem sum_divergence_univ_eq_zero (D : DivergenceData V E) (F : E → ℝ) :
    ∑ v : V, D.divergence F v = 0 := by
  have h := D.sum_divergence_eq_boundaryFlux F Finset.univ
  simpa [boundaryFlux] using h

/-- **Flow conservation on a region without boundary.** If no edge crosses the boundary of `S`
(in the undirected sense), then the divergence summed over `S` vanishes. -/
theorem sum_divergence_eq_zero_of_closed (D : DivergenceData V E) (F : E → ℝ) (S : Finset V)
    (h : ∀ e, D.src e ∈ S ↔ D.tgt e ∈ S) : ∑ v ∈ S, D.divergence F v = 0 := by
  have hout : (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∉ S) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e _
    rintro ⟨hs, ht⟩
    exact ht ((h e).1 hs)
  have hin : (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∉ S) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e _
    rintro ⟨ht, hs⟩
    exact hs ((h e).2 ht)
  rw [D.sum_divergence_eq_boundaryFlux F S]
  simp [boundaryFlux, hout, hin]

end DivergenceData

end Poincare.D7.Divergence
