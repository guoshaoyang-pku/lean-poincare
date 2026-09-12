# Reference copies (read-only, not part of the build)

This directory holds read-only reference copies of artifacts from other worktrees that bear
on `L4-child-conjugate-point-bound`. They are **not** imported by the release package and are
kept only for provenance comparison; the deliverable's import closure is listed in
`manifest/l4cp-verification.json` and does not include any file here.

| file | source | sha256 | role |
| --- | --- | --- | --- |
| `leader-ConjugatePointBound.lean.txt` | `leaders/L4-geometric-critical-path/release/Poincare/L4/GeodesicComparison/ConjugatePointBound.lean` (round 2) | `b8658fdbf922019bdde16c8ff607c81f7dd21bb955df7b4706ee9863a74780c2` | the L4 leader's earlier endpoint file; consulted as reference for the endpoint route, not imported |
| `leader-SturmZeroCount.lean.txt` | `leaders/L4-geometric-critical-path/release/Poincare/L4/GeodesicComparison/SturmZeroCount.lean` (round 3) | `5c1d421d3f7528f333c2afa8a2838ce64699ae860692f374081527addc238c4a` | sibling Sturm zero-counting artifact (context only) |

The deliverable's own imports are byte-identical copies of:

* D10 `Poincare/D10/JacobiConstantCurvature/{Basic,ODE,Comparison}.lean` and D12
  `Poincare/D12/ComparisonGeodesics/{Definitions,SingularRiccati,ModelEuclidean,VolumeRatio,SturmComparison}.lean`
  from `leaders/L1-lean-baseline/release` (canonical);
* L4 `Poincare/L4/GeodesicComparison/{RauchBridge,DownstreamComparison,ConstantCurvatureRauch}.lean`
  from `leaders/L4-geometric-critical-path/release`.

All eleven hashes are pinned in `tools/l4cp_verify.py` and re-checked by its provenance gate.
