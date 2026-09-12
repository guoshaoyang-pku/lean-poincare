/-
Reviewer scratch: proof bodies of the three downstream theorems of M1, plus type
comparison with the round-5 theorems they are claimed to consume.
Not part of the release tree.
-/
import Poincare.L4.Compactness.RicciGrowthChain

open Poincare.L4.Compactness

-- Exact statements of the round-5 theorems (for syntactic comparison).
#check @totallyBounded_of_uniformMeasureGrowth
#check @isCompact_of_uniformMeasureGrowth
#check @exists_pointed_subseq_of_uniformMeasureGrowth

-- Exact statements of M1's downstream theorems.
#check @totallyBounded_of_uniformRicciBallGrowth
#check @isCompact_of_uniformRicciBallGrowth
#check @exists_pointed_subseq_of_uniformRicciBallGrowth

-- Proof bodies: each must be a direct application of the round-5 theorem.
set_option pp.proofs true in
set_option pp.maxSteps 10000000 in
#print totallyBounded_of_uniformRicciBallGrowth

set_option pp.proofs true in
set_option pp.maxSteps 10000000 in
#print isCompact_of_uniformRicciBallGrowth

set_option pp.proofs true in
set_option pp.maxSteps 10000000 in
#print exists_pointed_subseq_of_uniformRicciBallGrowth
