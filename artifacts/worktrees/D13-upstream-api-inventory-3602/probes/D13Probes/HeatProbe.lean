/-
D13 adapter probe: Evans, *Partial Differential Equations*, heat equation and
maximum principle.  Upstream: frenzymath/Poincare-Conjecture @
bb91a091f0b968f8bbe8d861e025a88d82b161be, package `formalized-sources/Evans`
(EvansLib), pinned to Lean v4.32.1 + mathlib 520045ab.  Read-only consumer.
-/
import EvansLib.Ch02.Heat
import EvansLib.Ch02.HeatIVP
import EvansLib.Ch02.HeatIVPSmooth
import EvansLib.Ch02.HeatMaxPrinciple
import EvansLib.Ch02.HeatCauchyMaxPrinciple
import EvansLib.Ch02.HeatCauchyMaximum
import EvansLib.Ch02.HeatMeanValue

open EvansLib

/-! ## Heat kernel and Cauchy problem -/

#check @heatKernelSpatial
#check @heatKernelSpatial_contDiff
#check @heatKernelSpatial_integral
#check @heatKernelSpatial_solves_heat
#check @heatLog
#check @heatKernel

#check @heatSolution
#check @heatSolution_pos
#check @heatSolution_solves_heat
#check @heatSolution_contDiffOn
#check @heatSolution_isSolutionOfIVP

/-! ## Maximum principles and mean-value formula -/

#check @exists_parabolicBoundary_isMaxOn
#check @heat_cauchy_maxPrinciple_smallTime
#check @heat_cauchy_uniqueness_smallTime
#check @heatMeanValueWeight
#check @heatMeanValueIntegral

-- The adapter terms below are deliberately `def`s: they are terms built from
-- upstream declarations, not new mathematical claims.  The style linter that
-- asks for `theorem` on proposition-valued definitions is disabled for them.
set_option linter.defProp false

/-! ## Adapter terms -/

noncomputable def d13_heatKernel := @heatKernel
noncomputable def d13_heatSolution := @heatSolution
noncomputable def d13_heatKernel_solves_heat := @heatKernelSpatial_solves_heat
noncomputable def d13_heatSolution_solves_heat := @heatSolution_solves_heat
noncomputable def d13_parabolicBoundary_max := @exists_parabolicBoundary_isMaxOn
noncomputable def d13_heatCauchy_max := @heat_cauchy_maxPrinciple_smallTime

/-! ## Axiom footprint -/

#print axioms heatKernelSpatial_solves_heat
#print axioms heatSolution_solves_heat
#print axioms heatSolution_isSolutionOfIVP
#print axioms exists_parabolicBoundary_isMaxOn
#print axioms heat_cauchy_maxPrinciple_smallTime
