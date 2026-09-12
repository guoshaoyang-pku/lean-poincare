# Poincare.Longrun.Topology

Stage-D3 topology interface layer (task `D3-kappa-ledger`).

**This is not a proof of the Poincaré conjecture and not a proof of Perelman's
no-local-collapsing theorem.**  It is an explicit, kernel-checked interface layer: the
structures below fix the hypotheses and conclusions that the missing theorems must
produce, and every mathematical assertion beyond a definition is either a checked lemma
or a hypothesis field.

## Files

| Module | Contents |
| --- | --- |
| `Basic.lean` | model spaces `EuclideanThree = ℝ³`, `SphereThree = 𝕊³`, `ThreeManifoldModel = 𝓡 3` |
| `CompactThreeManifold.lean` | `class CompactThreeManifold M` (atlas + `C^∞` + compact + Hausdorff + connected + nonempty) and 7 checked consequences (plus the generated parent projections) |
| `Noncollapsing.lean` | `abbrev CurvatureBoundedOn`, `structure KappaNoncollapsingCertificate`, and 6 checked consequences |
| `NormalizedVolume.lean` | `structure NormalizedVolumeLowerBound` (abstract `vol : M → ℝ`), `def normalizedBallVolume`, `structure NormalizedBallVolumeLowerBound`, the equivalence with the κ-certificate, and 16 checked consequences |
| `Stage6Bridge.lean` | connection to `Poincare.Stage6.poincareConjectureTopologicalThree`, `Poincare.Stage6.sphereThreeSimplyConnected`, `Poincare.Stage6.sphereThreePiOneTrivial` |
| `MissingTheorems.lean` | statement-only ledger (`def ... : Prop`) of the exact missing theorems for κ-non-collapsing and sphere recognition, with checked companions |
| `AxiomAudit.lean` | `#print axioms` for all 71 audited declarations |

## Interfaces

```lean
class CompactThreeManifold (M : Type*) [TopologicalSpace M]
    extends ChartedSpace EuclideanThree M, IsManifold ThreeManifoldModel ∞ M,
      CompactSpace M, T2Space M, ConnectedSpace M where
  nonempty : Nonempty M

abbrev CurvatureBoundedOn (M : Type*) := M → ℝ → Prop

structure KappaNoncollapsingCertificate (M : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (κ r₀ : ℝ) : Prop where
  kappa_pos : 0 < κ
  r0_pos : 0 < r₀
  volume_ball_lower : ∀ x r, 0 < r → r ≤ r₀ → K x r →
    ENNReal.ofReal (κ * r ^ 3) ≤ μ (Metric.eball x (ENNReal.ofReal r))

structure NormalizedVolumeLowerBound (M : Type*) (vol : M → ℝ) (v₀ : ℝ) : Prop where
  lower_bound : ∀ x, v₀ ≤ vol x
```

The normalized-ball interface is `NormalizedBallVolumeLowerBound M μ K κ r₀`, and

```lean
theorem kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound :
  KappaNoncollapsingCertificate M μ K κ r₀ ↔
    NormalizedBallVolumeLowerBound M μ K κ r₀
```

is a checked equivalence for `0 < κ`, `0 < r₀` (the `ℝ≥0∞` division-by-`r³` bookkeeping
`κ ≤ μ(B)/r³ ↔ κ r³ ≤ μ(B)` is done in the kernel).

## Build

The worktree is an isolated Lake package pinned to mathlib rev
`7974e751bece493b6ff508039423ca9fa2452fa8`, Lean `4.34.0-rc2`:

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH=$ELAN_HOME/bin:$PATH
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D3_kappa_ledger
lake build Poincare                 # exit code: 0
lake env lean Poincare/Longrun/Topology/AxiomAudit.lean   # exit code: 0
```

`Poincare/Stage6` is a read-only symlink to the shared Stage6 sources and `.lake/packages`
is a read-only symlink to the shared mathlib cache; no shared file is written or modified.

## Constraint compliance

The Lean sources contain no unproved holes, no extra logical postulates, no kernel
bypasses and no native evaluation.  Statement-only declarations are confined to the
clearly named `missing...` ledger in `MissingTheorems.lean` and are accompanied by checked
shape lemmas and consequences.  Of the 71 audited declarations, 70 depend only on the three
standard Lean kernel postulates `propext`, `Classical.choice`, `Quot.sound`, and the
remaining one depends on no axioms (see `AxiomAudit.lean`).
