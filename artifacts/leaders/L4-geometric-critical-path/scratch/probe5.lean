import Poincare.L4.Compactness.FamilyCoversWitness
import Poincare.L4.Compactness.MeasureGrowthChain
open GromovHausdorff MeasureTheory Set Metric
open Poincare.L4.Compactness
#check @Measure.dirac_apply_of_not_mem
#check @Measure.dirac_apply
example : MeasurableSingletonClass (GHSpace.Rep (toGHSpace (Disc 2))) := inferInstance
#check @IsometryEquiv.dist_eq
#check @IsometryEquiv.symm_apply_apply
#check @IsometryEquiv.apply_symm_apply
#check @IsometryEquiv.injective
#check @Disc.dist_eq_one
#check @Disc.dist_eq_zero
#check @Disc.dist_le_one
#check @Fin.eq_zero_or_eq_last
#check (by decide : (0 : Disc 2) ≠ 1)
#check @mem_closedBall
#check @Metric.mem_closedBall
