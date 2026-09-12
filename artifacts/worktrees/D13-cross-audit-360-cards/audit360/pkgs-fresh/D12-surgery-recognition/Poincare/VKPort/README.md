# VKPort — ported frenzymath van Kampen cluster (EXPERIMENTAL, not part of the D12 audit deliverable)

## Provenance

- **Source:** frenzymath `Poincare-Conjecture`, vendored snapshot
  `third_party/frenzymath/Poincare-Conjecture` at commit
  `bb91a091f0b968f8bbe8d861e025a88d82b161be`
  (upstream repo: https://github.com/frenzymath/Poincare-Conjecture).
- **Files ported:** `formalized-sources/Hatcher/HatcherLib/Ch1/`
  `{BasicConstructions, AlgebraicConstructions, VanKampen, VanKampenGrid,
   VanKampenWordCalculus, VanKampenSweep, VanKampenSubdivision,
   VanKampenAdaptedGrid, VanKampenGlobalSweep}.lean`.
- **License:** Apache 2.0 (upstream `LICENSE`).
- **Upstream is sorry-free:** 0 `sorry`/`admit` tactics in all ported files
  (the two `admit` grep hits are prose in docstrings).
- **Target toolchain:** Lean `4.34.0-rc2`, mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
  (upstream was Lean 4.32.1, mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`).

## Modifications (relative to upstream; everything else is verbatim)

1. `BasicConstructions.lean`: removed the two lemmas
   `fundamentalGroup_basepointTransport_comp_map` and
   `fundamentalGroup_basepointTransport_comp_mapOfEq_symm` (unused by the
   cluster; their proof scripts rely on old mathlib transparency behavior).
   (34 diff lines total, mostly the deletions and the import-prefix rewrite.)
2. `VanKampen.lean` (`vanKampenMap_factor`): replaced the single
   `rw [vanKampenMap, freeProductLift, freeProductInclusion, Monoid.CoprodI.lift_of]`
   by a typed `let fi` + `change` + `rw [Monoid.CoprodI.lift_of (fi := fi) (i := i)]`
   (new mathlib's `Monoid.CoprodI` transparency behavior). (12 diff lines incl. imports.)
3. `VanKampenGrid.lean`: `VanKampenCellTouchesVertex` changed from `def` to
   `abbrev` (pure `Prop` disjunction; makes rewrite matching robust). (4 diff lines.)

## Build / audit status

- `cd release && lake build Poincare.VKPort.HatcherLib.Ch1.VanKampenGlobalSweep
  Poincare.VKPort.HatcherLib.Ch1.VanKampenSubdivision
  Poincare.VKPort.HatcherLib.Ch1.VanKampenAdaptedGrid` — exit 0 (3107 jobs).
- `#print axioms` on `HatcherLib.vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected`
  and `HatcherLib.vanKampenMap_surjective` ⊆ `{propext, Classical.choice, Quot.sound}`.

## Key statements available for SR-4

- `PathConnectedOpenCover`, `VanKampenFactorizationsConnected`,
  `vanKampenMap : FreeProduct (fun i => CoverFundamentalGroup cover i) →* FundamentalGroup X x₀`
  (`vanKampenMap_surjective`),
  `vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected` (kernel of the
  van Kampen map is the normal closure of the pairwise-overlap relators),
  `exists_vanKampenRectangularSubdivision`, the grid/sweep machinery
  (`VanKampenGlobalSweep`, `VanKampenAdaptedGrid`) that produces
  `VanKampenFactorizationsConnected` for rectangular subdivisions.

## Remaining to close SR-4 (next invocation)

1. Build the `PathConnectedOpenCover` of the iterated connected sum from the
   `ConnectedSumDecompositionV2` data (punctured pieces + collar overlaps,
   pairwise overlaps path-connected).
2. Feed it through the subdivision/sweep machinery to obtain
   `VanKampenFactorizationsConnected`.
3. Group theory: a free product `*ᵢ Gᵢ ⧸ N` with trivial quotient forces each
   `Gᵢ` trivial (⇒ `SimplyConnectedSpace` of the pieces from that of `X`).
4. Wire the resulting `vanKampen` input into
   `ConnectedSumDecomposition.mkV2`/`stage6Target_of_v3hypotheses`.

This port is infrastructure only: no D12 deliverable module imports it yet, and
no D12 result claims rely on it.
