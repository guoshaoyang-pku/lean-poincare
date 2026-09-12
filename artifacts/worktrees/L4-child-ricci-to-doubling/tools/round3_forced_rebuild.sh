#!/usr/bin/env bash
# Round-3 independent acceptance: forced recompilation + fresh fail-closed axiom audits.
set -u
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-ricci-to-doubling
REL=$WT/release
LOG=$WT/logs/round3-rebuild.log
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd "$REL" || exit 99

echo "=== round-3 forced rebuild $(date -u +%Y-%m-%dT%H:%M:%SZ) ==="
echo "--- removing oleans of the two new modules ---"
K=Poincare/L4/Compactness
for m in RicciToDoubling RicciToDoublingHyperbolic; do
  for ext in olean ilean trace hash; do
    f=.lake/build/lib/lean/$K/$m.$ext
    if [ -e "$f" ]; then rm -f "$f"; echo "removed $f"; fi
  done
done
echo "--- lake build ---"
lake build Poincare.D12.ComparisonGeodesics.ModelEuclidean Poincare.D12.ComparisonGeodesics.VolumeRatio Poincare.L4.Compactness.CoveringStability Poincare.L4.Compactness.DoublingToCovers Poincare.L4.Compactness.MeasureGrowthCovers Poincare.L4.Compactness.RicciToDoubling Poincare.L4.Compactness.RicciToDoublingHyperbolic
echo "BUILD-EXIT=$?"
echo "--- axiom audit 1 (Euclidean + interface) ---"
lake env lean Audit/RicciToDoublingAudit.lean
echo "AUDIT1-EXIT=$?"
echo "--- axiom audit 2 (hyperbolic) ---"
lake env lean Audit/RicciToDoublingHyperbolicAudit.lean
echo "AUDIT2-EXIT=$?"
