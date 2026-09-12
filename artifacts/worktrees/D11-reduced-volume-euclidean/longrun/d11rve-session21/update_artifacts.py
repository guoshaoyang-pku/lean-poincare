import json, re

AT = "2026-09-11T09:21:30Z"

SECTION = r"""
## 26. Session re-verification (2026-09-11, session21)

Continuation invocation.  The checkpoint was not trusted: the whole gate set was re-run from
scratch from the worktree root, and one **new** independent check was added — a *non-vacuity
probe* that instantiates the headline theorems at concrete dimensions, times and points and
closes the resulting numeric equalities.  No Lean source was changed.

| gate | command | result |
| --- | --- | --- |
| per-file compile | `lake env lean release/Poincare/D11/ReducedVolume/<F>.lean` × 7 | **7/7 exit 0, 0 warning/error lines** (`longrun/d11rve-session21/compile_<F>.log`, `gate_exit_codes.txt`) |
| whole release package | `lake build` (worktree root) | **exit 0**, "Build completed successfully (9155 jobs)", 0 error lines (`longrun/d11rve-session21/lake_build.log`) |
| axiom audit | `lake env lean …/Audit.lean` + independent parser freshly written this session (`parse_audit.py`) | **74/74 declarations**: `[propext, Classical.choice, Quot.sound]` (71), `[]` (2), `[propext]` (1); union of all cones `= {propext, Classical.choice, Quot.sound}` exactly; **0 nonstandard** (`audit_raw.log`, `axiom_audit.json`) |
| audit coverage | regex extraction of every `theorem`/`def`/`structure` in the four content modules vs the 74 `#print axioms` commands | **exact bijection 74 = 74**: 0 source declarations unaudited, 0 audit commands without a source declaration (the single regex artefact `and` is a prose word inside the `Statements.lean` module docstring, not a declaration) |
| forbidden tokens | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/ReducedVolume` | **0 hard, 0 soft**, **7 files actually scanned** (`forbidden_scan.json`).  Method note: the scanner's `os.walk` interface needs a *directory*; passing the seven file paths scans 0 files and yields a vacuous `0` — the directory form was used |
| source integrity | `sha256sum` × 7 | **7/7 byte-identical** to §1 (Basic `388b62ae`, StraightRays `16a1fa77`, Volume `a6d2bf62`, Statements `c823d0e7`, All `0e8ef1d5`, Probe `81ebdefe`, Audit `51c19cfa`) |
| **non-vacuity probe (new)** | `lake env lean longrun/d11rve-session21/NonVacuityProbe.lean` (outside the release tree) | **exit 0, 0 warnings** (`nonvac_probe.log`): 17 `example` instantiations + 2 concrete norm lemmas, e.g. `heatKernelReducedDistance 1 1 1 = 1/4`, `heatKernelReducedDistance 1 4 4 = 1`, `reducedVolume 2 1 = 1`, `reducedVolume 3 7 = 1`, `euclideanReducedVolume 4 2 = 1`, `LlengthAlong (straightRay 4 1) … 0 1 = 8`, `reducedLengthAlong … = 4`, `IsLMinimizer (straightRayLPath 4 1)`, `AntitoneOn (euclideanReducedVolumeCertificate 2).volume (Ioi 0)`, and `(euclideanManifoldReducedVolumeInterface 2).reducedVolume 1 = 1` |

**Why the non-vacuity probe matters.**  The release theorems are universally quantified over
`n`, `τ > 0` and the point, so a compiling proof alone does not exclude a statement whose
hypotheses are unsatisfiable or whose conclusion is degenerate.  The probe closes genuinely
numeric statements: `Ṽ = 1` becomes an equality between two real numbers that both evaluate to
`1`, and the `L`-length claim becomes the numeric equality `8 = 8`.  Together with
`gaussianKernel_integral : ∫ K = 1` (D10 `Mass.lean`) — whose value is `1`, not `0` — this
rules out the vacuous reading of `reducedVolume_eq_one`.  The probe is compiled but is *not*
part of the release tree and is not imported by `All.lean`.

**Mathematical re-read (this session).**  `Basic.lean`, `Volume.lean` and the statement blocks
of `StraightRays.lean` / `Statements.lean` were re-read at definition level and confirm:
`flatLIntegrand = √τ·(0 + ‖γ'‖²)` (the task's `∫√τ(|γ'|²+R) dτ` with `R = 0`);
`heatKernelReducedDistance := -log((4πτ)^{n/2} K)` with
`heatKernelReducedDistance_eq : ℓ = ‖x‖²/(4τ)`; `heatKernel_asymptotics` the inverse identity;
`minimizer_iff_eq_straightRay` a genuine two-sided characterisation (both directions proved);
`reducedVolumeIntegrand_eq_gaussianKernel` then `gaussianKernel_integral` giving
`reducedVolume_eq_one : Ṽ(τ) = 1`; `ReducedVolumeMonotonicityTheorem` a `def … : Prop` (a
statement, never an axiom) proved for the Euclidean instantiation.  The §25 honesty boundary
stands: RLV-5 (second variation) and RLV-7 (reduced-length differential inequality) are
*bypassed* in the flat computation rather than instantiated — not a gap in any proved theorem.

No change to any authored file or verdict in this session.  Checkpoint updated
(`checkpoint.json` + `longrun/checkpoint.json`, `fresh_reverification_session21_2026_09_11`);
`longrun/results/D11-reduced-volume-euclidean.json` gains the session21 entry.  All seven
authored files are byte-identical to the ones whose hashes are recorded in §1, so this
re-verification certifies exactly the previously reported artifact.

"""

# ---------- 1. markdown card ----------
md = "longrun/results/D11-reduced-volume-euclidean.md"
s = open(md, encoding="utf-8").read()
assert "## 26." not in s, "section 26 already present"
LAST = "**Last line:** TASK_DONE — card: `longrun/results/D11-reduced-volume-euclidean.md`"
assert s.rstrip().endswith(LAST), "unexpected card tail"
head = s.rstrip()[: -len(LAST)].rstrip("\n")
s2 = head + "\n" + SECTION.rstrip("\n") + "\n\n" + LAST + "\n"
open(md, "w", encoding="utf-8").write(s2)
print("md updated; last line:", repr(s2.rstrip().splitlines()[-1]))

# ---------- 2. json card ----------
jc = "longrun/results/D11-reduced-volume-euclidean.json"
d = json.load(open(jc, encoding="utf-8"))
entry = {
    "session": "session21",
    "at": AT,
    "per_file_compile": "7/7 exit 0, 0 warning/error lines (longrun/d11rve-session21/compile_<F>.log, gate_exit_codes.txt)",
    "lake_build": "exit 0, Build completed successfully (9155 jobs), 0 error lines (longrun/d11rve-session21/lake_build.log)",
    "axiom_audit": "74/74 declarations; 71 x [propext, Classical.choice, Quot.sound], 2 x [], 1 x [propext]; union = {propext, Classical.choice, Quot.sound}; 0 nonstandard (longrun/d11rve-session21/axiom_audit.json, parse_audit.py)",
    "audit_coverage": "74/74 content declarations audited (exact bijection; 0 unaudited, 0 orphan audit commands)",
    "forbidden_tokens": "0 hard, 0 soft, 7 files actually scanned (longrun/d11rve-session21/forbidden_scan.json); note: directory form of os.walk required, file-path form scans 0 files",
    "source_hashes_unchanged": True,
    "non_vacuity_probe": "NEW: longrun/d11rve-session21/NonVacuityProbe.lean compiled exit 0, 0 warnings; 17 example instantiations + 2 norm lemmas, e.g. reducedVolume 2 1 = 1, reducedVolume 3 7 = 1, LlengthAlong (straightRay 4 1) 0 1 = 8, reducedLengthAlong = 4, heatKernelReducedDistance 1 1 1 = 1/4, (euclideanManifoldReducedVolumeInterface 2).reducedVolume 1 = 1; not part of the release tree",
    "math_reread": "flatLIntegrand = sqrt(tau)*(0 + |gamma'|^2); heatKernelReducedDistance = -log((4 pi tau)^(n/2) K) with eq : l = |x|^2/(4 tau); minimizer_iff_eq_straightRay two-sided; reducedVolume_eq_one via gaussianKernel_integral = 1; ReducedVolumeMonotonicityTheorem is def ... : Prop proved in the Euclidean case",
    "honesty_boundary_restated": "RLV-5 (second variation/index form) and RLV-7 (reduced-length differential inequality) are bypassed, not instantiated, in the flat computation; no proved theorem is affected",
    "verdict_unchanged": "TASK_DONE",
}
d.setdefault("reverifications", []).append(entry)
d["session_reverification"] = entry
d["reverified_at"] = AT
d["last_verified_at"] = AT
json.dump(d, open(jc, "w", encoding="utf-8"), indent=1)
print("json card updated; reverifications len:", len(d["reverifications"]))

# ---------- 3. checkpoints ----------
for cp in ["checkpoint.json", "longrun/checkpoint.json"]:
    try:
        c = json.load(open(cp, encoding="utf-8"))
    except FileNotFoundError:
        print("skip missing", cp); continue
    c["updated_at"] = AT
    c["status"]["result_card"] = "longrun/results/D11-reduced-volume-euclidean.md + .json (written)"
    c["status"]["reverification"] = (
        "session21 (2026-09-11): fresh compile gate 7/7 exit 0 (longrun/d11rve-session21/), "
        "axiom audit 74/74 with 0 nonstandard (71 x [propext, Classical.choice, Quot.sound], "
        "1 x [propext], 2 x []), audit coverage 74/74 exact bijection, lake build exit 0 "
        "(9155 jobs), forbidden scan 0 hard/0 soft over 7 files, 7/7 source hashes unchanged; "
        "NEW non-vacuity probe compiled exit 0 (17 concrete instantiations); verdict TASK_DONE"
    )
    c["fresh_reverification_session21_2026_09_11"] = {
        "per_file_compile": "7/7 exit 0 (longrun/d11rve-session21/gate_exit_codes.txt)",
        "lake_build": "exit 0, 9155 jobs, Build completed successfully (longrun/d11rve-session21/lake_build.log)",
        "axiom_audit": "74/74; 71 x [propext, Classical.choice, Quot.sound], 2 x [], 1 x [propext]; 0 nonstandard (longrun/d11rve-session21/axiom_audit.json)",
        "audit_coverage": "74/74 exact bijection",
        "forbidden_tokens": "0 hard, 0 soft, 7 files scanned (longrun/d11rve-session21/forbidden_scan.json)",
        "source_hashes_unchanged": "7/7 match card section 1",
        "non_vacuity_probe": "longrun/d11rve-session21/NonVacuityProbe.lean exit 0, 0 warnings; 17 examples + 2 norm lemmas",
        "verdict_unchanged": "TASK_DONE",
    }
    c["final_line"] = "TASK_DONE"
    c["card_path"] = "longrun/results/D11-reduced-volume-euclidean.md"
    json.dump(c, open(cp, "w", encoding="utf-8"), indent=1)
    print("checkpoint updated:", cp)
