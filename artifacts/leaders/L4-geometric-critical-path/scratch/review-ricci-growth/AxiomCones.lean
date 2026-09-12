/-
Reviewer scratch: axiom cones for every top-level declaration of
Poincare/L4/Compactness/RicciGrowthChain.lean (M1), plus proof-term inspection.
Not part of the release tree.
-/
import Poincare.L4.Compactness.RicciGrowthChain

open Poincare.L4.Compactness

-- Main user-facing declarations
#print axioms UniformRicciBallGrowth
#print axioms UniformRicciBallGrowth.A_nonneg
#print axioms UniformRicciBallGrowth.intervalIntegrable_A
#print axioms UniformRicciBallGrowth.radialVolume_eq_zero_of_nonpos
#print axioms UniformRicciBallGrowth.radialVolume_nonneg
#print axioms UniformRicciBallGrowth.radialVolume_mono
#print axioms UniformRicciBallGrowth.radialVolume_eq_of_ge
#print axioms UniformRicciBallGrowth.radialVolume_pos
#print axioms UniformRicciBallGrowth.radialVolume_halving
#print axioms UniformRicciBallGrowth.doublingNNReal
#print axioms UniformRicciBallGrowth.toUniformMeasureGrowth
#print axioms totallyBounded_of_uniformRicciBallGrowth
#print axioms isCompact_of_uniformRicciBallGrowth
#print axioms exists_pointed_subseq_of_uniformRicciBallGrowth

-- Auto-generated structure machinery / projections
-- (note: this structure does not generate `ext`/`ext_iff`, since it is not `@[ext]`)
#print axioms UniformRicciBallGrowth.mk
#print axioms UniformRicciBallGrowth.rec
#print axioms UniformRicciBallGrowth.recOn
#print axioms UniformRicciBallGrowth.casesOn
#print axioms UniformRicciBallGrowth.μ
#print axioms UniformRicciBallGrowth.d
#print axioms UniformRicciBallGrowth.hd
#print axioms UniformRicciBallGrowth.T
#print axioms UniformRicciBallGrowth.hT
#print axioms UniformRicciBallGrowth.Cn
#print axioms UniformRicciBallGrowth.hCn
#print axioms UniformRicciBallGrowth.t₀
#print axioms UniformRicciBallGrowth.ht₀
#print axioms UniformRicciBallGrowth.ht₀T
#print axioms UniformRicciBallGrowth.k
#print axioms UniformRicciBallGrowth.m
#print axioms UniformRicciBallGrowth.dm
#print axioms UniformRicciBallGrowth.A
#print axioms UniformRicciBallGrowth.dA
#print axioms UniformRicciBallGrowth.hk
#print axioms UniformRicciBallGrowth.hineq
#print axioms UniformRicciBallGrowth.hm
#print axioms UniformRicciBallGrowth.hmcont
#print axioms UniformRicciBallGrowth.hnorm
#print axioms UniformRicciBallGrowth.hA
#print axioms UniformRicciBallGrowth.hAcont
#print axioms UniformRicciBallGrowth.hApos
#print axioms UniformRicciBallGrowth.hA0
#print axioms UniformRicciBallGrowth.hmA
#print axioms UniformRicciBallGrowth.hAint
#print axioms UniformRicciBallGrowth.realize
#print axioms UniformRicciBallGrowth.A_nonpos
#print axioms UniformRicciBallGrowth.A_saturate
#print axioms UniformRicciBallGrowth.R
#print axioms UniformRicciBallGrowth.hRT
#print axioms UniformRicciBallGrowth.exhaust

-- Proof-term inspection of the two central derivations: which declarations occur?
set_option pp.maxSteps 10000000 in
#print UniformRicciBallGrowth.radialVolume_halving
set_option pp.maxSteps 10000000 in
#print UniformRicciBallGrowth.toUniformMeasureGrowth
