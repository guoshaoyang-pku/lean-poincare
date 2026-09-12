#!/bin/bash
# D13: end-to-end probe pipeline once the pinned toolchain is unpacked.
#   1. fetch pinned mathlib + transitive deps (shallow, exact revs)
#   2. build the selected adapter probes (cheap -> expensive)
#   3. collect exit codes + classify declarations
#   4. regenerate the result card
set -uo pipefail
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-upstream-api-inventory-3602
cd "$WT"
export ELAN_HOME="$WT/.elan-home"
export ALL_PROXY=socks5h://127.0.0.1:1080
export PATH="/data/home/guoshaoyang/workdir/lean_poincare/elan/bin:$PATH"

echo "[pipeline] start $(date -Is)"
echo "[pipeline] lean: $(lean --version 2>&1) (exit $?)"
echo "[pipeline] lake: $(lake --version 2>&1) (exit $?)"

tools/d13_fetch_mathlib.sh; echo "[pipeline] mathlib fetch exit=$?"
tools/d13_fetch_deps.sh;   echo "[pipeline] deps fetch exit=$?"

tools/d13_build_probes.sh \
  D13Probes.SharedProbe \
  D13Probes.TopologyProbe \
  D13Probes.HeatProbe \
  D13Probes.PetersenProbe \
  D13Probes.GeometryProbe \
  D13Probes.ComparisonProbe
echo "[pipeline] builds done $(date -Is)"

python3 tools/d13_collect_probe_results.py
python3 tools/d13_make_result_card.py
echo "[pipeline] end $(date -Is)"
