/-
Reviewer scratch: print proof bodies (not elided) for the two central derivations,
to record which declarations occur in them. Not part of the release tree.
-/
import Poincare.L4.Compactness.RicciGrowthChain

open Poincare.L4.Compactness

set_option pp.proofs true in
set_option pp.maxSteps 10000000 in
#print UniformRicciBallGrowth.toUniformMeasureGrowth._proof_1

set_option pp.proofs true in
set_option pp.maxSteps 10000000 in
#print UniformRicciBallGrowth.toUniformMeasureGrowth._proof_2

set_option pp.proofs true in
set_option pp.maxSteps 10000000 in
#print UniformRicciBallGrowth.toUniformMeasureGrowth._proof_3

set_option pp.proofs true in
set_option pp.maxSteps 10000000 in
#print UniformRicciBallGrowth.toUniformMeasureGrowth._proof_4

set_option pp.proofs true in
set_option pp.maxSteps 10000000 in
#print UniformRicciBallGrowth.radialVolume_halving
