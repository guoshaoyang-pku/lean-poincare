# D10-bochner-euclidean — result card

- **Task id:** `D10-bochner-euclidean`
- **Stage / lane:** D10 / Euclidean analysis (Bochner identity)
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-bochner-euclidean`
- **Scaffold:** `cp -al ../D6_weekly_release/. .` (see §10 for the one deviation);
  new Lean files only under `release/Poincare/D10/BochnerEuclidean/`
- **Generated:** `2026-09-10T01:29:11+00:00` (UTC); **re-verified after gate repair:**
  `2026-09-10T01:53:45+00:00` (UTC); **harness gate closed out:** `2026-09-10T02:12:36+00:00` (UTC)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (Lean 4.34.0-rc2), mathlib rev
  `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Verdict:** **D10 COMPLETE — THE BOCHNER IDENTITY ON `EuclideanSpace ℝ (Fin n)` IS
  FULLY PROVED, KERNEL-CHECKED AND AXIOM-CLEAN; 40/40 AUDITED DECLARATIONS (31
  THEOREMS/LEMMAS + 9 DEFINITIONS) LIE IN THE STANDARD CONE
  `[propext, Classical.choice, Quot.sound]`; NO `sorry`, `axiom`, `unsafe`,
  `native_decide` OR `proof_wanted` ANYWHERE**

> **Honesty boundary.** Nothing here is assumed. `grad`, `hess` and `lap` are *defined*
> from mathlib's `fderiv`; the identity is proved componentwise by explicitly
> differentiating the finite sums `∑ᵢ (∂ᵢu)²` with the product/power/sum rules for
> `fderiv` and Clairaut's theorem (`ContDiffAt.isSymmSndFDerivAt`). No Bochner-type
> identity is invoked. The only conventions worth recording are (a) `‖Hess u‖²` denotes
> the Hilbert–Schmidt (Frobenius) norm `∑ᵢⱼ (∂ᵢ∂ⱼu)²`, which is its standard meaning in
> the Bochner identity — the operator norm of the Hessian is a different quantity, and
> (b) `lap` agrees with mathlib's `Laplacian.laplacian`, `grad` agrees with mathlib's
> `gradient` (both proved in `Compat.lean`).

## 1. Deliverables

| file (under `release/Poincare/D10/BochnerEuclidean/`) | lines | sha256 | role |
|---|---|---|---|
| `Basic.lean` | 209 | `2af81d989146a7c7596e55175621e267f6363807a2b1c7f286e7135c2536c617` | definitions of `D`, `grad`, `hess`, `lap`, `gradNormSq`, `hessNormSq`, `gradLapDot`, `Harmonic`; elementary calculus of `D` (sum/product/power rules, Clairaut, third-order index swap) |
| `Bochner.lean` | 172 | `7e3cf8e991e2fa13696810356dce2cb83b0aef8a5d0bfca0d3048634835d7ed8` | computation of `D Δ` and `D²Δ` of `‖∇u‖²`; **Bochner identity**, componentwise and in geometric form; bridge lemmas |
| `Corollary.lean` | 51 | `4e361b0bbbaf4fb15cdc4df79077834bdb7b02865fc0873543160abf1ffcca18` | harmonic case: `Δ‖∇u‖² = 2‖Hess u‖² ≥ 0` (subharmonicity of the energy density) |
| `Compat.lean` | 61 | `436892ae8d09fe7b27f56cb66aed46d762a2cc97d1b05c4caee624a084e8a8c6` | `grad = gradient`, `lap = Laplacian.laplacian`: the definitions are the standard ones |
| `Axioms.lean` | 78 | `ef59f0b56b6bb402cf6077b3472fee5a5944767e8c646cec12a9cec51d8c2b7d` | consolidated `#print axioms` driver for the 31 lemmas/theorems and the 9 definitions (declares nothing) |

571 lines of new Lean in total. No mathematical source outside
`release/Poincare/D10/BochnerEuclidean/` was added or modified. The only other
files touched are the two required artifacts
`longrun/results/D10-bochner-euclidean.{md,json}`, the verification logs in
`longrun/logs/D10-*`, and the four worktree-root build-infrastructure files
(`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `.lake → release/.lake`)
required to make the harness compile gate — which runs `lake env lean <file>`
with cwd = the worktree root — able to resolve the toolchain and the prebuilt
mathlib; see §10.

## 2. Definitions (all from `fderiv`)

Throughout, `n : ℕ`, `E n := EuclideanSpace ℝ (Fin n)`, and
`basis i := EuclideanSpace.single i 1` is the `i`-th standard basis vector.

| declaration | statement |
|---|---|
| `D i u x` | `= fderiv ℝ u x (basis i)` — the coordinate derivative `∂ᵢu(x)` |
| `grad u x` | `= ∑ i, D i u x • basis i` — the gradient `∇u(x)` |
| `gradNormSq u x` | `= ∑ i, (D i u x)^2` — `‖∇u(x)‖²` in coordinates |
| `hess u x` | `= fderiv ℝ (fderiv ℝ u) x : E n →L[ℝ] E n →L[ℝ] ℝ` — the Hessian `D²u(x)` |
| `hessNormSq u x` | `= ∑ i, ∑ j, (D i (D j u) x)^2` — the Hilbert–Schmidt norm `‖Hess u(x)‖²` |
| `lap u x` | `= ∑ i, D i (D i u) x` — the Laplacian `Δu(x)` (trace of the Hessian) |
| `gradLapDot u x` | `= ∑ i, D i u x * D i (lap u) x` — the pairing `⟨∇u, ∇Δu⟩` |
| `Harmonic u` | `= ∀ x, lap u x = 0` |

Every derivative in sight is a genuine mathlib `fderiv`; nothing is axiomatised or
postulated. `Compat.lean` proves `grad_eq_gradient : grad u x = gradient u x` and
`lap_eq_laplacian : lap u x = Laplacian.laplacian u x` (for `ContDiff ℝ 2 u`), so these
are the standard gradient/Laplacian.

## 3. Task requirements → evidence

| requirement | evidence |
|---|---|
| 1. Define gradient, Hessian and Laplacian for smooth scalar functions on `EuclideanSpace ℝ (Fin n)` from `fderiv` | `Basic.lean`: `D`, `grad`, `hess`, `lap` (plus `gradNormSq`, `hessNormSq`, `gradLapDot`); `D_apply` is `rfl`; `Compat.lean`: `grad_eq_gradient`, `lap_eq_laplacian` |
| 2. Prove `Δ(‖∇u‖²) = 2‖Hess u‖² + 2⟨∇u, ∇(Δu)⟩` unconditionally for `C³` functions, honestly componentwise | `bochner_identity (hu : ContDiff ℝ 3 u) (x) : lap (fun y => ‖grad u y‖^2) x = 2 * hessNormSq u x + 2 * ⟪grad u x, grad (lap u) x⟫_ℝ`; the fully expanded componentwise form is `bochner_identity_components (hu) (x) : lap (gradNormSq u) x = 2 * hessNormSq u x + 2 * gradLapDot u x` |
| 3. Corollary: harmonic `u` ⟹ `Δ(‖∇u‖²) = 2‖Hess u‖² ≥ 0` | `harmonic_lap_gradNormSq`, `hessNormSq_nonneg`, `harmonic_lap_gradNormSq_nonneg`, `harmonic_energy_density_subharmonic` (conjunction of the equality and the inequality) |
| 4. Record `#print axioms`; every theorem only in `[propext, Classical.choice, Quot.sound]` | `Axioms.lean` audits **40** declarations (31 lemmas/theorems + 9 definitions); **40/40** report exactly `[propext, Classical.choice, Quot.sound]`; raw output `longrun/logs/D10-axioms-audit.txt` |
| no `sorry` / `axiom` / `unsafe` / `native_decide` / `proof_wanted` | release scanner `input/d5-tools/scan_forbidden.py release/Poincare/D10/BochnerEuclidean`: `hard_match_count = 0`, `soft_match_count = 0`, exit 0 (`longrun/logs/D10-forbidden-scan.json`); every compiled file has 0 warnings |
| compile every authored file (`lake env lean`, exit 0) | 5/5 files exit 0 (table in §5); worktree-wide gate check 69/69 exit 0 (§5, §10) |

## 4. The computation, honestly componentwise

Write `Dᵢ := D i` for the coordinate derivative and `w_k := D_k u`. The only calculus
inputs are mathlib's `fderiv_fun_sum`, `fderiv_fun_mul`, `fderiv_fun_pow`,
`fderiv_const_mul`, `fderiv_const`, and `ContDiffAt.isSymmSndFDerivAt` (Clairaut); the
rest is finite-sum algebra over `Fin n`:

1. `gradNormSq u = ∑ k, (w_k)²`, hence
   `Dᵢ (gradNormSq u) x = ∑ k, 2 · w_k(x) · Dᵢw_k(x)`  (`D_gradNormSq`).
2. Differentiating once more,
   `DᵢDᵢ (gradNormSq u) x = ∑ k [ 2·(Dᵢw_k(x))² + 2·w_k(x)·DᵢDᵢw_k(x) ]`
   (`DD_gradNormSq`).
3. Summing over `i` and splitting the sum:
   `Δ(‖∇u‖²)(x) = 2·∑ᵢ∑ₖ (DᵢDₖu(x))² + 2·∑ᵢ∑ₖ w_k(x)·DᵢDᵢw_k(x)`.
   The first term is `2·hessNormSq u x` by definition. For the second, `Finset.sum_comm`
   swaps the indices and `Finset.mul_sum` factors `w_k`; the third-order index swap
   `DᵢDᵢDₖu = DₖDᵢDᵢu` (`DDD_comm`) — proved from Clairaut applied to `u` and to `Dᵢu` —
   identifies the inner sum with `Dₖ(Δu)(x)` (`D_lap`). This is
   `bochner_identity_components`.
4. The geometric form `bochner_identity` follows from the bridges
   `norm_sq_grad : ‖grad u x‖² = gradNormSq u x`,
   `inner_grad_grad_lap : ⟪grad u x, grad (lap u) x⟫_ℝ = gradLapDot u x`,
   `hessNormSq_eq : hessNormSq u x = ∑ᵢ∑ⱼ (hess u x (basis i) (basis j))²`.

No identity is assumed at any point: the equality is derived.

## 5. Kernel verification (every command exit 0)

| step | command (cwd `release/`) | exit | log |
|---|---|---|---|
| compile definitions + calculus | `lake env lean Poincare/D10/BochnerEuclidean/Basic.lean` | 0 | `longrun/logs/D10-Basic.compile.log` (empty) |
| compile Bochner identity | `lake env lean Poincare/D10/BochnerEuclidean/Bochner.lean` | 0 | `longrun/logs/D10-Bochner.compile.log` (empty) |
| compile harmonic corollary | `lake env lean Poincare/D10/BochnerEuclidean/Corollary.lean` | 0 | `longrun/logs/D10-Corollary.compile.log` (empty) |
| compile mathlib compatibility | `lake env lean Poincare/D10/BochnerEuclidean/Compat.lean` | 0 | `longrun/logs/D10-Compat.compile.log` (empty) |
| axiom audit driver | `lake env lean Poincare/D10/BochnerEuclidean/Axioms.lean` | 0 | `longrun/logs/D10-Axioms.compile.log`, `longrun/logs/D10-axioms-audit.txt` |
| module build (all five modules) | `lake build Poincare.D10.BochnerEuclidean.Axioms` | 0 | `longrun/logs/D10-lake-build.log` |
| forbidden-token scan | `python3 input/d5-tools/scan_forbidden.py Poincare/D10/BochnerEuclidean` | 0 | `longrun/logs/D10-forbidden-scan.json` |
| **harness compile gate** (`dispatch360.py::compile_gate`, run by the dispatcher itself) | see §10, §11 | 0 | `state/D10-bochner-euclidean/gate.json`: **`ok = true`, 69/69 files exit 0**, `checked_at = 2026-09-10T10:03:48+0800`; dispatcher logged `PROMOTE D10-bochner-euclidean verified (gate 69 files)` at the same instant |
| worktree-wide compile gate replica (same procedure, re-run for this attempt) | see §10, §11 and `longrun/logs/gate_replica.py` | 0 | `longrun/logs/gate_replica_attempt2.log`, `longrun/logs/gate_replica.json` (**69/69 files exit 0, 0 failures**, 273.1 s) |
| full release package build (populates every olean the gate needs) | `cd release && lake build` | 0 | `longrun/logs/D10-full-build.log` |

All five per-file compile logs contain **0 error and 0 warning lines** (the `Axioms` log
additionally carries the `#print axioms` transcript); the machine-readable summary of the
exit codes is `longrun/logs/D10-verification.txt`.

## 6. `#print axioms` record

`Axioms.lean` prints every declaration of the development: **40 declarations** — the 31
lemmas/theorems plus the 9 definitions `basis`, `D`, `grad`, `gradNormSq`, `hess`,
`hessNormSq`, `lap`, `gradLapDot`, `Harmonic`. All 40 have axiom cone exactly
`[propext, Classical.choice, Quot.sound]` (the standard Lean/mathlib cone); **0** depend
on `sorryAx`, `native_decide`, `unsafe`, a custom `axiom`, or anything else.

| group | declarations |
|---|---|
| `Basic.lean` (15) | `basis_apply`, `D_apply`, `D_of_contDiff`, `D_of_contDiffAt`, `D_add`, `D_const`, `D_mul`, `D_const_mul`, `D_pow_two`, `D_sum`, `fderiv_D`, `D_D`, `D_comm`, `DDD_comm`, `D_lap` |
| `Bochner.lean` (8) | `D_gradNormSq`, `DD_gradNormSq`, `bochner_identity_components`, `grad_apply`, `norm_sq_grad`, `inner_grad_grad_lap`, `hessNormSq_eq`, `bochner_identity` |
| `Corollary.lean` (4) | `hessNormSq_nonneg`, `harmonic_lap_gradNormSq`, `harmonic_lap_gradNormSq_nonneg`, `harmonic_energy_density_subharmonic` |
| `Compat.lean` (4) | `sum_basis`, `inner_basis_right`, `grad_eq_gradient`, `lap_eq_laplacian` |
| definitions (9) | `basis`, `D`, `grad`, `gradNormSq`, `hess`, `hessNormSq`, `lap`, `gradLapDot`, `Harmonic` |

The driver additionally `#print`s the two headline statements; their fully elaborated
types are recorded at the end of `longrun/logs/D10-axioms-audit.txt`.

## 7. Headline statements (verbatim from Lean)

```lean
theorem bochner_identity (hu : ContDiff ℝ 3 u) (x : E n) :
    lap (fun y => ‖grad u y‖ ^ 2) x
      = 2 * hessNormSq u x + 2 * ⟪grad u x, grad (lap u) x⟫_ℝ

theorem harmonic_energy_density_subharmonic (hu : ContDiff ℝ 3 u) (hh : Harmonic u)
    (x : E n) :
    lap (fun y => ‖grad u y‖ ^ 2) x = 2 * hessNormSq u x ∧
      0 ≤ lap (fun y => ‖grad u y‖ ^ 2) x
```

## 8. Reproduction

```bash
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-bochner-euclidean/release
for f in Basic Bochner Corollary Compat Axioms; do
  lake env lean Poincare/D10/BochnerEuclidean/$f.lean || echo "FAIL $f"
done
lake build Poincare.D10.BochnerEuclidean.Axioms
python3 ../input/d5-tools/scan_forbidden.py Poincare/D10/BochnerEuclidean
```

The worktree-wide gate itself (69/69 exit 0) is reproduced exactly by

```bash
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-bochner-euclidean
python3 longrun/logs/gate_replica.py     # writes longrun/logs/gate_replica.json
```

## 9. Negative results / limits

- The development is restricted to **Euclidean space** `EuclideanSpace ℝ (Fin n)`. It does
  not treat Riemannian manifolds, the Weitzenböck formula with curvature, or any
  Ricci-flow application.
- `‖Hess u‖²` is the Hilbert–Schmidt norm. No claim is made about the operator norm of
  the Hessian.
- The `C³` hypothesis is used exactly where third-order mixed partials are swapped
  (`DDD_comm`) and where the second derivatives are differentiated; the statement is not
  weakened to `C²`.

## 10. Scaffold note

The instructed `cp -al ../D6_weekly_release/. .` failed with `Invalid cross-device link`
(`EXDEV`) on the prebuilt `.lake` tree: the worktree and the shared prebuilt mathlib live
on different mounts as far as hard-linking is concerned. The scaffold was therefore
materialised with a real copy (`cp -a`) of the small non-`.lake` part, and
`release/.lake/packages` is a symlink to the shared pinned mathlib prebuild
(`.../D6_weekly_release/release/.lake/packages`), exactly as in the sibling worktrees
(e.g. `D9-cheeger-gromov-compactness`). This affects only build infrastructure; the
authored sources, their hashes and the verification results above are independent of it.

## 11. Compile-gate repair (attempt 2): what failed, what was changed, and the outcome

When the repair was queued, the dispatcher deleted
`state/D10-bochner-euclidean/gate.json` (`dispatch360.py` lines 153–155), so the per-file
exit codes were not available at first; the gate was therefore reproduced locally with the
dispatcher's exact procedure (`longrun/logs/gate_replica.py`). The working `gate.json` has
since been produced by the dispatcher itself; its contents are recorded below.

The harness compile gate (`longrun/bin/dispatch360.py::compile_gate`) does **not** run
from `release/`. It walks the whole worktree and executes

```python
subprocess.run(["lake", "env", "lean", <absolute path>], cwd=<worktree root>, env=...)
```

for every `.lean` file outside `.lake`, `.git`, `.dshpkg`. Two infrastructure facts made
that fail even though the five authored files compiled from `release/`:

1. **No toolchain at the worktree root.** `elan` resolves the toolchain from a
   `lean-toolchain` file found in the cwd or an ancestor. The worktree root had none, so
   `lake env lean` aborted with *"no default toolchain configured"*. Fixed by adding a
   root `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`).
2. **No Lake workspace at the worktree root, and missing oleans.** The root had no
   `lakefile.toml`/`lake-manifest.json`, and `release/.lake/build/lib/lean` contained only
   the 5 oleans of the D10 target, so every file importing another release module failed
   with *"object file ... does not exist"* / *"unknown module prefix"*. Fixed by adding a
   root `lakefile.toml` (package `PoincareWorktree`, one `lean_lib Poincare` with
   `srcDir = "release"`, mathlib `rev = "master"`), copying
   `release/lake-manifest.json` to the root, symlinking `.lake → release/.lake` (so the
   prebuilt mathlib oleans are on `LEAN_PATH` without rebuilding), and running
   `lake build` once in `release/` to populate the remaining release oleans
   (exit 0, `longrun/logs/D10-full-build.log`).

**No mathematical file was changed by the repair.** All five D10 sources, and every
pre-existing release source, are byte-identical to the previous verified run (hashes
unchanged); the only edits are the four root-level build-infrastructure files, the logs,
and this card. After the repair the exact gate procedure compiles **69/69 `.lean` files
with exit 0** (`longrun/logs/gate_replica.json`), the five per-file checks are re-run and
still exit 0, `lake build Poincare.D10.BochnerEuclidean.Axioms` exits 0, the 40-declaration
axiom audit still reports the cone `[propext, Classical.choice, Quot.sound]` for all 40,
and the forbidden-token scan still reports `hard_match_count = 0`.

### Outcome: the harness gate now passes

The dispatcher itself re-ran `compile_gate` on this worktree and wrote
`state/D10-bochner-euclidean/gate.json`:

* `"ok": true`, **69 files checked, 0 non-zero exits**, `checked_at = 2026-09-10T10:03:48+0800`;
* the dispatcher log records `2026-09-10T10:03:48+0800 PROMOTE D10-bochner-euclidean
  verified (gate 69 files)`.

Independently, this attempt re-ran the identical procedure as a replica
(`longrun/logs/gate_replica_attempt2.log`: **69/69 exit 0, 0 failures**, 273.1 s),
re-ran the audit driver `lake env lean Poincare/D10/BochnerEuclidean/Axioms.lean`
(**40/40 declarations in the cone `[propext, Classical.choice, Quot.sound]`**, 0 occurrences
of `sorryAx`/`native_decide`; raw output `longrun/logs/D10-axioms-audit.txt`) and the
forbidden-token scan (**hard_match_count = 0, soft_match_count = 0**, exit 0). The five
authored files are unchanged from §1: sha256 `2af81d98…`, `7e3cf8e9…`, `4e361b0b…`,
`436892ae…`, `ef59f0b5…`, 571 lines total.

### Central-mirror (ophis) build note

The relay mirroring this worktree to the central machine excludes `.lake/`, so the five
D10 oleans are not transferred. To keep the central gate self-contained, the dependency
cone was built on the mirror (`lake build Poincare.D10.BochnerEuclidean.Axioms`, exit 0,
2508 jobs, artifacts only), after verifying that the mirrored sources are byte-identical
to the ones listed in §1 (sha256 checked on the mirror), and all five files were then
re-compiled there with `lake env lean` (**5/5 exit 0**, `Basic`, `Bochner`, `Corollary`,
`Compat`, `Axioms`). No authored source was modified on either machine.

TASK_DONE — card: `longrun/results/D10-bochner-euclidean.md` / `.json`
