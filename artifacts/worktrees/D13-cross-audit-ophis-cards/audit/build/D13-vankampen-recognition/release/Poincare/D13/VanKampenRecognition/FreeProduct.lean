/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-vankampen-recognition)

**D13 van Kampen recognition, part 1: free-product group lemmas and the
surjectivity-to-triviality step.**

The group-theoretic half of the van Kampen argument for `𝕊³`: the canonical
map of the van Kampen theorem goes from the free product of the fundamental
groups of the cover members to the fundamental group of the ambient space.
Two elementary lemmas about `Monoid.CoprodI`:

* a free product all of whose factors are subsingletons is a subsingleton
  (`FreeProduct_subsingleton`, by induction on words);
* a free product that is a subsingleton has subsingleton factors
  (`FreeProduct_factor_subsingleton`, via the injectivity of the canonical
  inclusions `Monoid.CoprodI.of_injective`).

Combining the first lemma with the ported surjectivity half of van Kampen
(`HatcherLib.vanKampenMap_surjective`, a proved theorem of the vendored
frenzymath HatcherLib cluster) gives the basic computation: if every member
of a path-connected open cover with path-connected pairwise intersections has
trivial fundamental group, then so does the ambient space
(`fundamentalGroup_subsingleton_of_cover`).

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.VKPort.HatcherLib.Ch1.VanKampen

set_option autoImplicit false

noncomputable section

namespace Poincare.D13.VanKampenRecognition

open HatcherLib

/-! ## 1. Free products of subsingleton groups -/

/-- **A free product all of whose factors are subsingletons is a subsingleton.**
Induction on words: `1 = 1`, and `CoprodI.of i m * x = 1` because `m = 1`
(its factor is a subsingleton) and `x = 1` (induction hypothesis). -/
theorem FreeProduct_subsingleton {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    (h : ∀ i, Subsingleton (G i)) : Subsingleton (Monoid.CoprodI G) := by
  refine ⟨fun w w' => ?_⟩
  have hone : ∀ w : Monoid.CoprodI G, w = 1 := by
    intro w
    induction w using Monoid.CoprodI.induction_left with
    | one => rfl
    | mul m x ih =>
        have hm : m = 1 := Subsingleton.elim m 1
        calc Monoid.CoprodI.of (M := G) m * x
          _ = Monoid.CoprodI.of (M := G) 1 * x := by rw [hm]
          _ = 1 * x := by rw [map_one]
          _ = x := one_mul x
          _ = 1 := ih
  rw [hone w, hone w']

/-- **A free product that is a subsingleton has subsingleton factors.**  The
canonical inclusion `Monoid.CoprodI.of : G i →* Monoid.CoprodI G` is injective
(mathlib's `Monoid.CoprodI.of_injective`), so any two elements of `G i` are
equal because their images are. -/
theorem FreeProduct_factor_subsingleton {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    (h : Subsingleton (Monoid.CoprodI G)) (i : ι) : Subsingleton (G i) :=
  ⟨fun g g' => Monoid.CoprodI.of_injective (M := G) (i := i)
    (Subsingleton.elim (Monoid.CoprodI.of (M := G) (i := i) g)
      (Monoid.CoprodI.of (M := G) (i := i) g'))⟩

/-! ## 2. Trivial cover groups give a trivial ambient fundamental group -/

/-- **The surjectivity half of van Kampen: trivial members give a trivial group.**
Every class in `FundamentalGroup X x₀` is the image of a word in the free product
(`HatcherLib.vanKampenMap_surjective`, the ported loop-decomposition theorem);
two classes lift to two words, which are equal because the free product is a
subsingleton (`FreeProduct_subsingleton`).  Hence the fundamental group is a
subsingleton. -/
theorem fundamentalGroup_subsingleton_of_cover {X : Type*} [TopologicalSpace X] {x₀ : X}
    {ι : Type*} (cover : PathConnectedOpenCover x₀ ι)
    (h : ∀ i, Subsingleton (CoverFundamentalGroup cover i)) :
    Subsingleton (FundamentalGroup X x₀) := by
  refine ⟨fun g g' => ?_⟩
  rcases vanKampenMap_surjective cover g with ⟨w, hw⟩
  rcases vanKampenMap_surjective cover g' with ⟨w', hw'⟩
  rw [← hw, ← hw']
  congr 1
  exact (FreeProduct_subsingleton (G := fun i => CoverFundamentalGroup cover i) h).elim w w'

end Poincare.D13.VanKampenRecognition

end
