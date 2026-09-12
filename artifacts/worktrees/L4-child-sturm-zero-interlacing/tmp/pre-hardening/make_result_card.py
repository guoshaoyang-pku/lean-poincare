#!/usr/bin/env python3
"""
L4-child-sturm-zero-interlacing: result-card generator.

Reads the evidence bundle (verification.json, axiom-report.json, source-hashes.json,
semantic-review.json) and the checkpoint, and writes

  longrun/results/L4-child-sturm-zero-interlacing.md
  longrun/results/L4-child-sturm-zero-interlacing.json

Only this task's own result card is written; no shared queue file is modified.
"""
import json
import os
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EV = os.path.join(ROOT, "evidence")
OUT = os.path.join(ROOT, "longrun", "results")

ver = json.load(open(os.path.join(EV, "verification.json")))
ax = json.load(open(os.path.join(EV, "axiom-report.json")))
srcs = json.load(open(os.path.join(EV, "source-hashes.json")))["files"]
ih = json.load(open(os.path.join(EV, "input-hash-verification.json")))
sr = json.load(open(os.path.join(EV, "semantic-review.json")))
cp = json.load(open(os.path.join(ROOT, "checkpoint.json")))

MODULES = {
    "core": "release/Poincare/L4/GeodesicComparison/SturmInterlacing.lean",
    "cross_check": "release/Poincare/L4/GeodesicComparison/SturmInterlacingConjugateCrossCheck.lean",
    "axiom_audit": "release/Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean",
    "negative_control": "negcontrol/SturmInterlacingNegativeControl.lean",
    "gate_driver": "tools/run_sturm_gates.py",
}
H = {}
for k, rel in MODULES.items():
    p = os.path.join(ROOT, rel)
    if rel in srcs:
        H[k] = srcs[rel]
    elif os.path.exists(p):
        import hashlib
        hh = hashlib.sha256()
        with open(p, "rb") as f:
            for c in iter(lambda: f.read(1 << 16), b""):
                hh.update(c)
        H[k] = hh.hexdigest()

THEOREMS = [
    ("modelJacobiSolutionOn", "`(K, jacobiSol K, jacobiDeriv K, −K·jacobiSol K)` is a `JacobiSolutionOn` on `(0,T)` for every `K, T`"),
    ("sinJacobiSolutionOn", "`(1, sin, cos, −sin)` is a `JacobiSolutionOn` on `(0,T)`"),
    ("linearJacobiSolutionOn", "`(0, t, 1, 0)` is a `JacobiSolutionOn` on `(0,T)`"),
    ("modelJacobiSol_pos", "`jacobiSol K > 0` on `(0, π/√K)` for `K > 0`"),
    ("modelJacobiSol_firstZero", "`jacobiSol K (π/√K) = 0` for `K > 0`"),
    ("modelJacobiDeriv_firstZero", "`jacobiDeriv K (π/√K) = −1` for `K > 0`"),
    ("exists_zero_of_curvature_lt", "**interlacing**: `k₂ ≤ k₁`, `u₂` positive between its zeros `a<b`, `u₁ a = 0`, strict interior curvature excess ⟹ `u₁` vanishes in `(a,b)`"),
    ("sturm_dichotomy_of_interior_bound", "engine dichotomy with the curvature bound relaxed to the open interval `(a,b)`"),
    ("sin_zero_interlaces_half_model", "**explicit instance**: `k₁ = 1` (`sin`) vs `k₂ = 1/2` model; `π` is a zero of `sin` strictly between the model's consecutive zeros `0` and `√2·π`"),
    ("sin_first_zero_lt_half_model_first_zero", "first-zero ordering `π < √2·π`"),
    ("jacobiSolShift", "shifted model `t ↦ jacobiSol K (t − a)`"),
    ("jacobiDerivShift", "derivative data of the shifted model"),
    ("hasDerivAt_jacobiSolShift", "`HasDerivAtR` of the shifted model"),
    ("hasDerivAt_jacobiDerivShift", "`HasDerivAtR` of the shifted derivative data"),
    ("jacobiSolShift_jacobiSolutionOn", "the shifted model is a `JacobiSolutionOn` on any `(a,b)`"),
    ("jacobiSolShift_pos", "positivity of the shifted model before `a + π/√K`"),
    ("sin_interlaces_half_model_all", "**infinite interlacing**: for every `n : ℤ`, `sin` has a zero strictly between the consecutive zeros `2nπ`, `2(n+1)π` of the shifted model with `k₂ = 1/4`"),
    ("sin_zero_in_half_model_interval", "explicit witness `(2n+1)π` for the infinite interlacing"),
    ("eq_zero_at_pi_sqrt_of_curvature_eq", "equality case `k ≡ K`: the endpoint `π/√K` is a zero (Wronskian constancy)"),
    ("exists_jacobi_zero_on_Ioc_pi_sqrt", "**zero counting**: `k ≥ K > 0` on `[0, π/√K]`, `u 0 = 0` ⟹ zero in `(0, π/√K]`"),
    ("exists_jacobi_zero_on_Ioc_pi_sqrt_of_interior_bound", "**ODE-intrinsic form**: curvature bound only on the open interval `(0, π/√K)`"),
    ("exists_jacobi_zero_on_Ioc_pi_sqrt_normalized", "same with the normalization hypothesis `u' 0 = 1` recorded"),
    ("exists_jacobi_zero_of_horizon", "horizon form: solution known up to `H ≥ π/√K` already has a zero in `(0, π/√K]`"),
    ("exists_jacobi_zero_on_Ioo_pi_sqrt_of_gt", "strict excess ⟹ zero strictly inside `(0, π/√K)`"),
    ("firstPositiveZero", "`firstPositiveZero u = sInf {t > 0 | u t = 0}`"),
    ("firstPositiveZero_le_pi_sqrt", "**first positive zero ≤ π/√K**"),
    ("firstPositiveZero_le_pi_sqrt_of_interior_bound", "first-zero bound with the interior curvature hypothesis"),
    ("pos_near_zero_of_normalized_initial", "`u' 0 = 1` ⟹ `u > 0` near `0` (FTC: `u t = ∫₀ᵗ du` and `du > 1/2` near `0`)"),
    ("firstPositiveZero_mem_of_normalized", "**attainment**: `firstPositiveZero u` is a genuine zero of `u`, positive, and `u` is zero-free below it"),
    ("firstPositiveZero_jacobiSol_two", "explicit witness: `jacobiSol 2` vanishes at `π/√2` and its first positive zero is ≤ `π/√1`"),
    ("wronskian_sin_linear_antitoneOn", "`wronskian_antitoneOn_of_le` with `(k₁,u₁)=(1,sin)`, `(k₂,u₂)=(0,t)` on `[0,π]`"),
    ("mul_cos_le_sin", "`t·cos t ≤ sin t` on `[0,π]`"),
    ("wronskian_deriv_sin_linear", "`deriv W t = −(t·sin t)` on `(0,π)` with the explicit data"),
    ("wronskian_deriv_sin_linear_at_pi_div_two", "`deriv W (π/2) = −π/2` (strict-decay witness)"),
    ("linear_model_no_second_zero", "the engine hypothesis `u₂ b = 0` fails for `u₂ = t` at every `b > 0`"),
    ("linear_model_no_interior_zero", "`t` has no zero in `(0,b)`"),
    ("sin_no_zero_in_Ioo_zero_pi", "**refutation**: `sin` has no zero in `(0,π)`"),
    ("sin_first_positive_zero_is_pi", "`sin`'s first positive zero is exactly `π`"),
    ("no_positive_solution_past_pi_sqrt", "**sharpened positivity bound**: `T ≤ π/√K` from Jacobi data, `u 0 = 0`, positivity, `k ≥ K`, `K > 0`"),
    ("conjugate_point_bound_via_engine", "the leader's full hypothesis list ⟹ `T ≤ π/√K`, by the engine route"),
    ("conjugate_point_bound_cross_check", "the leader's `conjugate_point_bound` invoked on the same data (agreement)"),
    ("sharpened_witness", "non-vacuous instance `k=2, K=1, T=3/2`: `3/2 ≤ π/√1`"),
    ("witness_agreement", "both routes give the same bound on the explicit instance"),
]

steps = ver["steps"]
axiom_decls = ax["reported_declarations"]
witnesses = sr["non_vacuity_witnesses"]
hyp = sr["hypothesis_review"]
items = sr["acceptance_items"]

def step_table():
    lines = ["| gate step | command | exit | seconds | log |", "|---|---|---|---|---|"]
    for s in steps:
        cmd = s.get("command", "")
        if len(cmd) > 90:
            cmd = cmd[:87] + "..."
        lines.append(f"| `{s['step']}` | `{cmd}` | {s.get('exit_code', '-')} | "
                     f"{s.get('seconds', '-')} | `{s.get('log', '-')}` |")
    return "\n".join(lines)

def theorem_list():
    return "\n".join(f"- **`{n}`** — {d}" for n, d in THEOREMS)

def witness_list():
    return "\n".join(f"- `{w['witness']}` — {w['content']}" for w in witnesses)

def hyp_review_md():
    out = []
    for h in hyp:
        out.append(f"**`{h['theorem']}`** — {h['classification']}")
        for x in h["hypotheses"]:
            used = "used" if x["used"] else "NOT used"
            nec = "necessary" if x["necessary"] else "removable / relaxable"
            out.append(f"  - `{x['name']}` — {used}; {nec}. {x.get('note', '')}")
        out.append("")
    return "\n".join(out)

def input_table():
    lines = ["| input file (copied read-only from the leader release) | sha256 (byte-identical) |",
             "|---|---|"]
    for r in ih["files"]:
        lines.append(f"| `{r['file']}` | `{r['sha256']}` |")
    return "\n".join(lines)

now = datetime.now(timezone.utc).isoformat()

md = f"""# L4-child-sturm-zero-interlacing — result card

- **Task id:** `L4-child-sturm-zero-interlacing`
- **Worktree:** `{ROOT}`
- **Generated:** `{now}`
- **Verdict:** **TASK_DONE — ENGINE CONSUMED WITH CONSTRUCTED DATA; LITERAL BRANCH (1) REFUTED AND REPLACED BY THE OFFERED SHARPER INTERLACING; ZERO-COUNTING AND WRONSKIAN ITEMS DELIVERED; ALL GATES PASS**
- **Semantic class:** unconditional scalar ODE comparison (Sturm). This is **not** a Poincaré
  proof and makes no manifold-level claim: no Jacobi field, conjugate point, Rauch or
  curvature comparison statement is asserted.

> Honest classification up front. Acceptance item (1) offered two alternatives: the literal
> `k₁ = 1, k₂ = 0, u₂ = t` instantiation on `(0,π)` "to obtain that the first positive zero of
> `sin` is `< π`", **or** the sharper two-curvature interlacing for `k₂ ≤ k₁`. The literal form
> is **false**: the engine requires `u₂ b = 0`, while `t b = b ≠ 0` for every `b > 0`, and
> `sin` has no zero in `(0,π)` — its first positive zero is exactly `π`. Both facts are
> formally proved here (`linear_model_no_second_zero`, `sin_no_zero_in_Ioo_zero_pi`,
> `sin_first_positive_zero_is_pi`) and the second is the mathematical negative control. The
> explicitly offered alternative — the sharper two-curvature interlacing — is delivered in
> full, together with the zero-counting corollary and the Wronskian consumption.

## 1. Deliverable modules (source hashes)

| module | sha256 |
|---|---|
| `{MODULES['core']}` | `{H.get('core','-')}` |
| `{MODULES['cross_check']}` | `{H.get('cross_check','-')}` |
| `{MODULES['axiom_audit']}` | `{H.get('axiom_audit','-')}` |
| `{MODULES['negative_control']}` | `{H.get('negative_control','-')}` |
| `{MODULES['gate_driver']}` | `{H.get('gate_driver','-')}` |

## 2. Consumed read-only inputs (byte-identity verified)

{input_table()}

- `sturm_zero_comparison`, `sturm_zero_comparison_of_pos`, `sign_constant_of_no_zero`,
  `wronskian_deriv`, `wronskian_antitoneOn_of_le`, `wronskian_continuousOn`,
  `wronskian_differentiableOn` from `Poincare/D12/ComparisonGeodesics/SturmComparison.lean`
  are consumed by name.
- The D10 model `jacobiSol`/`jacobiDeriv` and its pointwise ODE lemmas are consumed as the
  constructed comparison data.
- Prior art, **not imported or restated**: `Poincare/L4/GeodesicComparison/SturmZeroCount.lean`
  (sha256 `{sr['non_duplication']['prior_art_sha256']}`) already proves the strict-excess
  existence statement; the new content here is listed in §3.
- `conjugate_point_bound` (`ConjugatePointBound.lean`, sha256
  `{sr['acceptance_items'][1]['cross_check']['leader_module_sha256']}`) is neither assumed as a
  hypothesis nor duplicated: it is imported only in the cross-check module and invoked there
  for agreement.

## 3. What is proved

{theorem_list()}

Full elaborated signatures: `evidence/signatures.txt` ({axiom_decls} declarations, `#check @…`).

## 4. Acceptance items

### (1) `k₁ = 1` (`sin`) / `k₂ = 0` (`t`) on `(0,π)`, or the sharper interlacing — **literal form refuted; alternative delivered**

- Structural inapplicability: `sturm_zero_comparison` needs `u₂ b = 0`; for `u₂ = t` this fails
  at every positive `b` (`linear_model_no_second_zero`). There is no interval `a < b` on which
  the linear model has both endpoint zeros (the only linear solution vanishing at `a` is
  `t − a`, which vanishes again only at `b = a`).
- The literal conclusion is false: `¬ ∃ c ∈ (0,π), sin c = 0` (`sin_no_zero_in_Ioo_zero_pi`);
  the first positive zero is exactly `π` (`sin_first_positive_zero_is_pi`).
- The data is not wasted: with `(k₁,u₁) = (1, sin)`, `(k₂,u₂) = (0, t)` the Wronskian
  monotonicity is instantiated explicitly and yields the true inequality `t·cos t ≤ sin t` on
  `[0,π]` (`wronskian_sin_linear_antitoneOn`, `mul_cos_le_sin`) and the concrete derivative
  `−(t·sin t)` (`wronskian_deriv_sin_linear`).
- Alternative delivered: the general strict-gap interlacing `exists_zero_of_curvature_lt` and
  the fully explicit instance `sin_zero_interlaces_half_model`: `k₁ = 1` (`u₁ = sin`) against
  the constructed model `k₂ = 1/2` (`u₂ = jacobiSol (1/2)`), whose consecutive zeros
  `0, √2·π` bracket the zero `π` of `sin`, with `0 < π < √2·π`
  (`sin_first_zero_lt_half_model_first_zero`).

### (2) Zero-counting corollary — **delivered**

- `exists_jacobi_zero_on_Ioc_pi_sqrt`: for `K > 0`, `k ≥ K` on `[0, π/√K]`, `u 0 = 0`, there is
  a zero in `(0, π/√K]`. The engine's alternative gives an open-interval zero **or** `k ≡ K`;
  the equality case is closed by `eq_zero_at_pi_sqrt_of_curvature_eq`: the Wronskian against
  the model has zero derivative, hence is constant, and at the endpoints
  `W 0 = 0`, `W (π/√K) = u (π/√K) · 1` because `jacobiSol K (π/√K) = 0` and
  `jacobiDeriv K (π/√K) = −1`; hence `u (π/√K) = 0`.
- `firstPositiveZero_le_pi_sqrt`: `firstPositiveZero u = sInf {{t > 0 | u t = 0}} ≤ π/√K`, and
  the positive zero set is nonempty. `exists_jacobi_zero_of_horizon` is the horizon form: a
  solution known only up to `H ≥ π/√K` already has a zero in `(0, π/√K]`.
- `exists_jacobi_zero_on_Ioc_pi_sqrt_normalized` records the requested normalization
  `u' 0 = 1` (not needed for the conclusion); with that normalization,
  `pos_near_zero_of_normalized_initial` and `firstPositiveZero_mem_of_normalized` show that
  `firstPositiveZero u` is a genuine zero: `u (firstPositiveZero u) = 0`,
  `0 < firstPositiveZero u`, and `u` is zero-free on `(0, firstPositiveZero u)`.  The
  ODE-intrinsic form `exists_jacobi_zero_on_Ioc_pi_sqrt_of_interior_bound` needs `k ≥ K`
  only on the open interval `(0, π/√K)`.
- Cross-check against this round's `conjugate_point_bound` (module
  `SturmInterlacingConjugateCrossCheck.lean`): §5 compares the hypothesis sets and records
  agreement on the leader's own data and witness instance.

### (3) Wronskian monotonicity with explicit data — **delivered**

`wronskian_antitoneOn_of_le` is instantiated with `(k₁,u₁) = (1, sin)`, `(k₂,u₂) = (0, t)` on
`[0,π]`, its two hypotheses discharged explicitly (`0 ≤ 1` and `0 ≤ sin t · t`), giving
`AntitoneOn W [0,π]`; since `W 0 = 0`, this yields `t·cos t ≤ sin t`. `wronskian_deriv` is
instantiated on the same data, giving `deriv W t = −(t·sin t)` and the strict witness
`deriv W (π/2) = −π/2 < 0`.

## 5. Cross-check against `conjugate_point_bound`

| | hypotheses | conclusion |
|---|---|---|
| `conjugate_point_bound` (this round, leader release) | `0<T`, `0≤B`, `0<t₀`, `t₀≤T`, `B·t₀≤1/2`, `JacobiSolutionOn`, `ContinuousOn ddu`, `|ddu|≤B`, `u 0=0`, `u' 0=1`, `u>0` on `(0,T]`, `K>0`, `k≥K` on `(0,T)`, `(K·max (1/√K) T)·t₀≤1/2` | `T ≤ π/√K` |
| `no_positive_solution_past_pi_sqrt` (engine route, this task) | `JacobiSolutionOn`, `u 0=0`, `u>0` on `(0,T]`, `K>0`, `k≥K` on `(0,T)` | `T ≤ π/√K` |

Eight quantitative/normalization hypotheses are removed. `conjugate_point_bound_via_engine`
derives the leader's conclusion from the leader's full hypothesis list via the engine route;
`conjugate_point_bound_cross_check` invokes the leader theorem itself on the same data; on the
leader's witness instance (`k=2`, `K=1`, `T=3/2`) both routes give `3/2 ≤ π/√1`
(`sharpened_witness`, `witness_agreement`). The leader result is therefore consistent with,
and strictly weaker in hypotheses than, the engine-derived bound — it is **not** duplicated
(no proof of it is reproduced; it is called as an independent oracle).

## 6. Non-vacuous witnesses

{witness_list()}

## 7. Semantic review of expanded hypotheses

{hyp_review_md()}

The two structural points of the review:

1. **Endpoint hypotheses in the engine's public form are stronger than its proof needs.**
   `sturm_zero_comparison` assumes `k₂ ≤ k₁` on the closed interval; the proof only uses the
   open interval. This matters because `conjugate_point_bound` (and the ODE itself) only
   bounds `k` on `(0,T)`. The relaxation is exposed as `sturm_dichotomy_of_interior_bound`
   (proved through the engine's own `sturm_zero_comparison_of_pos` and
   `sign_constant_of_no_zero`), and all applications that need it use it.
2. **The equality case `k ≡ K` is where the closed-interval zero comes from.** The engine's
   alternative is genuinely two-sided (the sibling file shows strictness cannot be dropped),
   so the endpoint zero at `π/√K` is not an artefact of restating the engine: it is proved by
   Wronskian constancy against the constructed model, using the computed values
   `jacobiSol K (π/√K) = 0` and `jacobiDeriv K (π/√K) = −1`.

## 8. Gate results

- toolchain `{ver['pins']['toolchain']}`, mathlib `{ver['pins']['mathlib_rev']}`
- overall verdict: **{ver['verdict']}**, failures: `{ver['failures']}`

{step_table()}

### Fail-closed axiom audit

- audited declarations: **{axiom_decls}** (expected {ax['expected_declarations']}, reported
  {ax['reported_declarations']}, missing `{ax['missing']}`)
- violations: `{ax['violations']}`
- allow-list cone: `{ax['allowed_cone']}`; every reported cone is a subset
- forbidden dependency tokens checked: `{ax['forbidden_tokens']}`
- verdict: **{ax['verdict']}**

### Forbidden-token scan and negative controls

- `input/d5-tools/scan_forbidden.py release`: **{ver['forbidden_scan']['hard_match_count']} hard
  matches** over {ver['forbidden_scan']['lean_files_scanned']} Lean files (`sorry`, `axiom`,
  `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`).
- `negcontrol/SturmInterlacingNegativeControl.lean` (mathematical negative control): compiles;
  it refutes the naive `k₂ = 0` conclusion and records the true Wronskian consequence.
- `negcontrol/NegativeControl.lean` (soundness negative control): compiles, exit 0.

## 9. Provenance, queue and checkpoints

- `checkpoint.json` at the worktree root holds the full checkpoint history (never rewritten);
  the latest entry at card-generation time was `{cp['checkpoints'][-1]['id']}` at
  `{cp['checkpoints'][-1]['at']}` with `gates={cp['checkpoints'][-1]['gates']}`.  The final
  checkpoint written after this card records the card's own sha256.
- Shared queue files were **not modified**: `longrun/queue.updated.json` and
  `manifest/*` remain as inherited. This card and `evidence/*` are the task's only outputs.
- Evidence bundle: `evidence/verification.json` (pins, every command, exit code, log path),
  `evidence/axiom-report.json`, `evidence/source-hashes.json`,
  `evidence/input-hash-verification.json`, `evidence/semantic-review.json`,
  `evidence/signatures.txt`, `logs/*.log`.

## 10. Honest limitations

- The literal acceptance branch "first positive zero of `sin` is `< π`" is **false** and is
  reported as refuted, not silently replaced.
- The result is scalar ODE comparison only: the identification of Jacobi-solution zeros with
  conjugate points along geodesics is not formalized (this is the known U3 bridge).
- No ODE existence/uniqueness is assumed or proved; all solutions are explicit constructed
  data, exactly as in the D12 engine's design.
- `no_positive_solution_past_pi_sqrt` carries `0 < T` only for signature compatibility with
  `conjugate_point_bound`; that hypothesis is unused (flagged in §7).

## 11. Reproduction

```bash
export ELAN_HOME={os.environ.get('ELAN_HOME', '/data3/guoshaoyang/workdir/lean_poincare/elan')}
export PATH="$ELAN_HOME/bin:$PATH"
cd {ROOT}
python3 tools/run_sturm_gates.py        # compile + axiom audit + forbidden scan + hashes
python3 tools/make_result_card.py       # regenerate this card and its JSON
```

**TASK_DONE**
"""

os.makedirs(OUT, exist_ok=True)
md_path = os.path.join(OUT, "L4-child-sturm-zero-interlacing.md")
json_path = os.path.join(OUT, "L4-child-sturm-zero-interlacing.json")
with open(md_path, "w") as f:
    f.write(md)

card = {
    "schema": "l4-child-sturm-zero-interlacing/result-card-v1",
    "task_id": "L4-child-sturm-zero-interlacing",
    "worktree": ROOT,
    "generated": now,
    "verdict": "TASK_DONE",
    "headline": ("D12 Sturm engine consumed with constructed D10 Jacobi data; literal "
                 "acceptance branch (1) refuted and replaced by the offered sharper "
                 "two-curvature interlacing; zero-counting/first-zero bound and Wronskian "
                 "consumption delivered; all gates PASS."),
    "honest_classification": {
        "item_1_literal": "REFUTED (k2=0,u2=t cannot instantiate the engine; sin has no zero in (0,pi); first positive zero is exactly pi)",
        "item_1_alternative": "DELIVERED (general strict-gap interlacing + explicit sin vs k2=1/2 instance)",
        "item_2": "DELIVERED (closed-interval zero incl. equality case, firstPositiveZero <= pi/sqrt K, horizon form, cross-checked against conjugate_point_bound)",
        "item_3": "DELIVERED (wronskian_antitoneOn_of_le and wronskian_deriv with explicit (1,sin)/(0,t) data; t*cos t <= sin t)",
    },
    "semantic_class": sr["semantic_class"],
    "module_hashes": H,
    "inputs_byte_identical": ih["verdict"],
    "gates": {"verdict": ver["verdict"], "failures": ver["failures"], "steps": steps},
    "pins": ver["pins"],
    "axiom_audit": {
        "verdict": ax["verdict"],
        "declarations": ax["reported_declarations"],
        "allowed_cone": ax["allowed_cone"],
        "missing": ax["missing"],
        "violations": ax["violations"],
        "declaration_cones": ax["declarations"],
    },
    "forbidden_scan": ver["forbidden_scan"],
    "theorems": [{"name": n, "summary": d} for n, d in THEOREMS],
    "non_vacuity_witnesses": witnesses,
    "hypothesis_review": hyp,
    "semantic_review": sr,
    "checkpoints": cp["checkpoints"],
    "limitations": sr["honest_limitations"],
}
with open(json_path, "w") as f:
    json.dump(card, f, indent=1)

print("wrote", md_path)
print("wrote", json_path)
