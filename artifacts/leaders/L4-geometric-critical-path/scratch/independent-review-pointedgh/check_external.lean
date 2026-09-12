import Poincare.L4.PointedGH.Instances

-- external lemmas the proofs lean on: confirm non-degenerate statements
#check @GromovHausdorff.ghDist_le_hausdorffDist
#check @Metric.exists_dist_lt_of_hausdorffDist_lt
#check @Metric.exists_dist_lt_of_hausdorffDist_lt'
#check @GromovHausdorff.hausdorffDist_optimal
#check @Metric.hausdorffDist_le_of_mem_dist
#check @IsCompact.tendsto_subseq
#check @GromovHausdorff.dist_ghDist
#check @Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv
#check @Poincare.D12.GeometricCompactness.ghDist_congr_left
#check @GromovHausdorff.totallyBounded
