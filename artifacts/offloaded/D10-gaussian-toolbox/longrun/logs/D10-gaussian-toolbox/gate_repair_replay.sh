#!/usr/bin/env bash
# Exact repair applied to the D10-gaussian-toolbox worktree after compile-gate
# attempt 1, plus the faithful full-tree gate re-run used as evidence.
#
# Background: the dispatcher's compile gate runs, for every `.lean` file in the
# worktree (skipping `.lake`/`.git`/`.dshpkg`), the command
#
#     lake env lean <absolute file path>        (cwd = worktree root)
#
# At attempt 1 the worktree-root `.lake` was a real directory whose nested
# `packages`/`build` symlinks were not resolved by that invocation, so the very
# first import (`Mathlib.*`) failed with `unknown module prefix 'Mathlib'` and
# every file failed.  The repair restores the root workspace to the layout used
# by the already-promoted worktrees (e.g. D10-bochner-euclidean):
#
#     .lake -> release/.lake
#
# together with a root `lakefile.toml` that declares the release package as a
# `lean_lib`, so that `lake env lean` from the worktree root puts the mathlib
# oleans (release/.lake/packages -> shared package cache) and the prebuilt D6/D10
# oleans (release/.lake/build/lib/lean) on LEAN_PATH.
#
# The gate passes no `-o`, so the D10 modules that import each other also need
# their oleans prebuilt in release/.lake/build/lib/lean/Poincare/D10/GaussianToolbox/.
#
# No authored `.lean` file was modified by this repair.
set -euo pipefail
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-gaussian-toolbox
cd "$WT"

# ---- 1. root workspace layout -------------------------------------------------
rm -rf .lake
ln -s release/.lake .lake

cat > lakefile.toml <<'EOF'
# Worktree-level Lake workspace for the longrun compile gate.
#
# The compile gate runs `lake env lean <file>` with cwd = this worktree root for
# every `.lean` file in the tree.  The actual release package lives in
# `release/` (with its prebuilt `.lake`), so this root workspace mirrors that
# package: same toolchain pin, same mathlib revision, and a `.lake` symlink to
# `release/.lake`, which puts every prebuilt release/mathlib olean on
# `LEAN_PATH` without copying or rebuilding anything.
name = "PoincareWorktree"
version = "0.1.0"
description = "Root workspace wrapper around the D6 release package in release/ for the longrun compile gate"

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "master"

[[lean_lib]]
name = "Poincare"
srcDir = "release"
globs = ["Poincare.+"]
EOF

# ---- 2. prebuild the D10 oleans the gate relies on ----------------------------
OUT=release/.lake/build/lib/lean/Poincare/D10/GaussianToolbox
mkdir -p "$OUT"
lake env lean -o "$OUT/Basic.olean"        release/Poincare/D10/GaussianToolbox/Basic.lean
lake env lean -o "$OUT/Convolution.olean"  release/Poincare/D10/GaussianToolbox/Convolution.lean
lake env lean -o "$OUT/Multivariate.olean" release/Poincare/D10/GaussianToolbox/Multivariate.lean

# ---- 3. smoke check + full-tree gate re-run -----------------------------------
lake env lean release/Poincare/D10/GaussianToolbox/PrintAxioms.lean

python3 - <<'PY'
import json, os, subprocess, time
WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-gaussian-toolbox"
ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")
files = []
for dirpath, dirnames, filenames in os.walk(WT):
    dirnames[:] = [d for d in dirnames if d not in (".lake", ".git", ".dshpkg")]
    for fn in filenames:
        if fn.endswith(".lean"):
            files.append(os.path.join(dirpath, fn))
files.sort()
bad = []
for f in files:
    r = subprocess.run(["lake", "env", "lean", f], cwd=WT, env=ENV,
                       capture_output=True, text=True, timeout=1800)
    if r.returncode != 0:
        bad.append((f, r.returncode))
print(f"{len(files)} files checked, {len(bad)} failures")
for f, rc in bad:
    print("FAIL", f, rc)
raise SystemExit(1 if bad else 0)
PY
