#!/usr/bin/env python3
"""Fail-closed programmatic axiom audit for the D12-tensor-maximum-bochner authored modules.

Usage (from the worktree root):
    python3 tools/d12_axiom_audit.py

It runs `lake env lean` on each authored Lean file (cwd = release/), parses every
`#print axioms X` output line, and fails if any declaration depends on an axiom outside the
allow-list {propext, Classical.choice, Quot.sound}.

Fail-closed properties checked:
  * the compiler must exit 0 for every file (no sorry/axiom/admit of any kind survives);
  * FORBIDDEN TOKENS: after stripping comments and docstrings, no occurrence of
    sorry/admit/axiom/unsafe/native_decide/proof_wanted is allowed in any authored file;
  * every `#print axioms` line must parse and be audited (a missing line is an error);
  * COVERAGE: every top-level declaration of every authored file (theorem/lemma/def/abbrev/
    structure/instance) must itself be listed in a `#print axioms` line of that file, so a
    new declaration cannot silently escape the audit.  The extracted set is reported, and any
    declaration that is not covered is an error (with no exemption list);
  * a built-in negative control runs the same parser against a file that uses a fake axiom
    and the parser must flag it; if the control is not flagged the script exits nonzero.
"""
import re
import subprocess
import sys
from pathlib import Path

WORKTREE = Path(__file__).resolve().parent.parent
RELEASE = WORKTREE / "release"
FILES = [
    "Poincare/D12/TensorMaximumBochner/TensorCalculus.lean",
    "Poincare/D12/TensorMaximumBochner/PositivityPreservation.lean",
    "Poincare/D12/TensorMaximumBochner/Audit.lean",
    "Poincare/D12/TensorMaximumBochner/BochnerIdentity.lean",
    "Poincare/D12/TensorMaximumBochner/So3Model.lean",
    "Poincare/D12/TensorMaximumBochner/So3Polynomial.lean",
    "Poincare/D12/TensorMaximumBochner/So3RicciFlow.lean",
    "Poincare/D12/TensorMaximumBochner/TangentCone.lean",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PRINT_LINE = re.compile(r"^'([^']+)' depends on axioms: \[(.*)\]\s*$")
DECL_LINE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+|protected\s+)?"
    r"(theorem|lemma|def|abbrev|structure|instance)\s+([A-Za-z_][A-Za-z0-9_'.]*)",
    flags=re.M,
)


def short_name(full: str) -> str:
    return full.split(".")[-1]


def parse_axioms_line(line: str):
    m0 = re.match(r"^'([^']+)' does not depend on any axioms\s*$", line)
    if m0:
        return m0.group(1), set()
    m = PRINT_LINE.match(line)
    if not m:
        return None, None
    name = m.group(1)
    rest = m.group(2).strip()
    axioms = set()
    if rest:
        for chunk in rest.split(","):
            chunk = chunk.strip()
            if chunk:
                axioms.add(chunk)
    return name, axioms


def audit_file(relpath: str, expected_names: list[str]) -> list[str]:
    src = RELEASE / relpath
    text = src.read_text(encoding="utf-8")
    declared = re.findall(r"^#print axioms (\S+)", text, flags=re.M)
    errors: list[str] = []
    if not declared:
        errors.append(f"{relpath}: no #print axioms lines found (refusing empty audit)")
        return errors
    # COVERAGE (fail-closed): every top-level declaration must be listed for audit.
    declared_short = {short_name(d) for d in declared}
    decls = DECL_LINE.findall(text)
    uncovered = [n for _, n in decls if n not in declared_short]
    if uncovered:
        errors.append(
            f"{relpath}: {len(uncovered)} declaration(s) not covered by #print axioms "
            f"(fail-closed): {sorted(uncovered)}"
        )
    print(f"COVERAGE {relpath}: {len(decls)} declarations extracted, "
          f"{len(decls) - len(uncovered)} audited by #print axioms")
    proc = subprocess.run(
        ["lake", "env", "lean", relpath],
        cwd=RELEASE,
        capture_output=True,
        text=True,
        timeout=1800,
    )
    if proc.returncode != 0:
        errors.append(f"{relpath}: lean exited {proc.returncode}")
        errors.append(proc.stdout[-4000:])
        return errors
    audited = {}
    lines = proc.stdout.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        m0 = re.match(r"^'([^']+)' does not depend on any axioms\s*$", line)
        if m0:
            audited[m0.group(1)] = set()
            i += 1
            continue
        m = re.match(r"^'([^']+)' depends on axioms: \[(.*)$", line)
        if m:
            name, rest = m.group(1), m.group(2)
            while "]" not in rest and i + 1 < len(lines):
                i += 1
                rest += " " + lines[i]
            rest = rest.rstrip("]").strip()
            axioms = {c.strip() for c in rest.split(",") if c.strip()}
            audited[name] = axioms
        i += 1
    for name in declared:
        full = [k for k in audited if k == name or k.endswith("." + name)]
        if not full:
            errors.append(f"{relpath}: declaration {name} listed for audit but no axioms line parsed")
            continue
        axioms = audited[full[0]]
        bad = sorted(axioms - ALLOWED)
        if bad:
            errors.append(f"{relpath}: {name} depends on unapproved axioms {bad}")
        else:
            print(f"OK   {relpath} :: {name} -> {sorted(axioms)}")
    for name in expected_names:
        if not any(name == d or name.endswith("." + d) for d in declared):
            errors.append(f"{relpath}: expected declaration {name} not in #print axioms list")
    return errors


FORBIDDEN = ("sorry", "admit", "axiom", "unsafe", "native_decide", "proof_wanted")


def strip_comments(text: str) -> str:
    """Remove nested block comments (`/- ... -/`, including `/-!` and `/--` doc comments) and
    `--` line comments, so that documentation containing the forbidden words is not scanned."""
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def forbidden_scan() -> list[str]:
    """Fail-closed scan for forbidden tokens in the *code* of every authored file."""
    errors: list[str] = []
    pattern = re.compile(r"\b(" + "|".join(FORBIDDEN) + r")\b")
    for rel in FILES:
        code = strip_comments((RELEASE / rel).read_text(encoding="utf-8"))
        hits = sorted(set(pattern.findall(code)))
        if hits:
            errors.append(f"{rel}: forbidden token(s) in code: {hits}")
    if not errors:
        print("OK   forbidden-token scan: no sorry/admit/axiom/unsafe/native_decide/"
              "proof_wanted in the code of any task file")
    return errors


def negative_control() -> list[str]:
    """The parser must flag a declaration built on a fake axiom."""
    control = WORKTREE / "scratch" / "neg_axiom_control.lean"
    control.parent.mkdir(parents=True, exist_ok=True)
    control.write_text(
        "import Mathlib.Tactic\n"
        "axiom fakeD12Axiom : True\n"
        "theorem usesFakeD12Axiom : True := fakeD12Axiom\n"
        "#print axioms usesFakeD12Axiom\n",
        encoding="utf-8",
    )
    proc = subprocess.run(
        ["lake", "env", "lean", "../scratch/neg_axiom_control.lean"],
        cwd=RELEASE,
        capture_output=True,
        text=True,
        timeout=600,
    )
    flagged = False
    for line in proc.stdout.splitlines():
        name, axioms = parse_axioms_line(line)
        if name == "usesFakeD12Axiom" and axioms and (axioms - ALLOWED):
            flagged = True
    errors = []
    if proc.returncode != 0:
        errors.append("negative control: lean did not compile the control file")
    if not flagged:
        errors.append("negative control: fake axiom was NOT flagged by the parser (fail-open!)")
    else:
        print("OK   negative control: fake axiom correctly flagged")
    return errors


def main() -> int:
    expected = {
        FILES[0]: [
            "Poincare.D12.TensorMaximumBochner.LeviCivitaIdentities.curvatureForm_add_last_pair",
            "Poincare.D12.TensorMaximumBochner.LeviCivitaIdentities.curvatureForm_last_pair_skew",
            "Poincare.D12.TensorMaximumBochner.LeviCivitaIdentities.curvatureForm_pair_symm",
            "Poincare.D12.TensorMaximumBochner.LeviCivitaIdentities.ricci_eq_sum_curvatureForm",
            "Poincare.D12.TensorMaximumBochner.LeviCivitaIdentities.ricci_symm",
        ],
        FILES[1]: [
            "Poincare.D12.TensorMaximumBochner.lambdaInv",
            "Poincare.D12.TensorMaximumBochner.quadSelfPath",
            "Poincare.D12.TensorMaximumBochner.quadSelfSquareSub",
            "Poincare.D12.TensorMaximumBochner.exists_first_zero",
            "Poincare.D12.TensorMaximumBochner.nonneg_of_nonneg_init_of_deriv_nonneg_on_nonpos",
            "Poincare.D12.TensorMaximumBochner.nonneg_of_nonneg_init_of_deriv_nonneg_on_nonpos_Icc",
            "Poincare.D12.TensorMaximumBochner.staysPosSemidef_of_tangent",
            "Poincare.D12.TensorMaximumBochner.staysPosSemidef_of_tangent_Icc",
            "Poincare.D12.TensorMaximumBochner.staysPosSemidef_of_field",
            "Poincare.D12.TensorMaximumBochner.tangentCondition_selfSq_sub_self",
            "Poincare.D12.TensorMaximumBochner.hasDerivAt_lambdaInv",
            "Poincare.D12.TensorMaximumBochner.lambdaInv_sq_sub",
            "Poincare.D12.TensorMaximumBochner.diagonal_hasDerivAt",
            "Poincare.D12.TensorMaximumBochner.quadSelfPath_posSemidef",
            "Poincare.D12.TensorMaximumBochner.quadSelfPath_hermitian",
            "Poincare.D12.TensorMaximumBochner.quadSelfPath_solves",
            "Poincare.D12.TensorMaximumBochner.quadSelfPath_stays_posSemidef",
            "Poincare.D12.TensorMaximumBochner.negSqrtCounterexample",
        ],
        FILES[2]: [
            "Poincare.D12.TensorMaximumBochner.Audit.discrete_max_principle_is_scalar",
            "Poincare.D12.TensorMaximumBochner.Audit.bochnerStatement_is_statement_only",
            "Poincare.D12.TensorMaximumBochner.Audit.zero_bridge_is_zero_calculus",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_pair_symm_audited",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_matrix_example_audited",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_so3_ricci_term_audited",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_so3_bochner_audited",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_so3_gradsq_nonvacuous",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_so3_lap_X0_audited",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_so3_laplacian_nondegenerate",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_so3_strict_bochner_audited",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_horizon_max_principle_audited",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_so3_ricci_flow_audited",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_so3_metric_posSemidef_audited",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_so3_metric_posDef_audited",
            "Poincare.D12.TensorMaximumBochner.Audit.d12_so3_metric_extinction_audited",
        ],
        FILES[3]: [
            "Poincare.D12.TensorMaximumBochner.Bochner.gA",
            "Poincare.D12.TensorMaximumBochner.Bochner.gamma",
            "Poincare.D12.TensorMaximumBochner.Bochner.cG",
            "Poincare.D12.TensorMaximumBochner.Bochner.cG_self",
            "Poincare.D12.TensorMaximumBochner.Bochner.ui",
            "Poincare.D12.TensorMaximumBochner.Bochner.H",
            "Poincare.D12.TensorMaximumBochner.Bochner.lap",
            "Poincare.D12.TensorMaximumBochner.Bochner.gradSq",
            "Poincare.D12.TensorMaximumBochner.Bochner.hessSq",
            "Poincare.D12.TensorMaximumBochner.Bochner.gradInner",
            "Poincare.D12.TensorMaximumBochner.Bochner.VecField",
            "Poincare.D12.TensorMaximumBochner.Bochner.fieldInner",
            "Poincare.D12.TensorMaximumBochner.Bochner.gammaX",
            "Poincare.D12.TensorMaximumBochner.Bochner.nablaField",
            "Poincare.D12.TensorMaximumBochner.Bochner.eField",
            "Poincare.D12.TensorMaximumBochner.Bochner.gradField",
            "Poincare.D12.TensorMaximumBochner.Bochner.gammaX_swap",
            "Poincare.D12.TensorMaximumBochner.Bochner.ricciForm",
            "Poincare.D12.TensorMaximumBochner.Bochner.DerivationData",
            "Poincare.D12.TensorMaximumBochner.Bochner.D_one",
            "Poincare.D12.TensorMaximumBochner.Bochner.D_const",
            "Poincare.D12.TensorMaximumBochner.Bochner.eq_zero_of_eq_neg_self",
            "Poincare.D12.TensorMaximumBochner.Bochner.gamma_swap",
            "Poincare.D12.TensorMaximumBochner.Bochner.cG_antisym",
            "Poincare.D12.TensorMaximumBochner.Bochner.cG_eq_torsion",
            "Poincare.D12.TensorMaximumBochner.Bochner.D_expand",
            "Poincare.D12.TensorMaximumBochner.Bochner.D_nabla",
            "Poincare.D12.TensorMaximumBochner.Bochner.D_comm_apply",
            "Poincare.D12.TensorMaximumBochner.Bochner.D_second_comm_apply",
            "Poincare.D12.TensorMaximumBochner.Bochner.hessian_symm",
            "Poincare.D12.TensorMaximumBochner.Bochner.sum_swap_apply",
            "Poincare.D12.TensorMaximumBochner.Bochner.sum_gammaX_bilin_pair",
            "Poincare.D12.TensorMaximumBochner.Bochner.nablaField_metric",
            "Poincare.D12.TensorMaximumBochner.Bochner.nablaField_grad_hessian",
            "Poincare.D12.TensorMaximumBochner.Bochner.fieldInner_eField",
            "Poincare.D12.TensorMaximumBochner.Bochner.nablaField_eField",
            "Poincare.D12.TensorMaximumBochner.Bochner.nablaField_grad_coeff",
            "Poincare.D12.TensorMaximumBochner.Bochner.sum_gammaX_quad",
            "Poincare.D12.TensorMaximumBochner.Bochner.D_gradSq",
            "Poincare.D12.TensorMaximumBochner.Bochner.fieldLaplacian",
            "Poincare.D12.TensorMaximumBochner.Bochner.curvatureForm_as_gamma",
            "Poincare.D12.TensorMaximumBochner.Bochner.ricciForm_eq_sum_gamma",
            "Poincare.D12.TensorMaximumBochner.Bochner.ricciContraction",
        ],
        FILES[4]: [
            "Poincare.D12.TensorMaximumBochner.So3.Vec3",
            "Poincare.D12.TensorMaximumBochner.So3.stdMetric",
            "Poincare.D12.TensorMaximumBochner.So3.crossBracket",
            "Poincare.D12.TensorMaximumBochner.So3.crossMetricSkew",
            "Poincare.D12.TensorMaximumBochner.So3.crossLeviCivita",
            "Poincare.D12.TensorMaximumBochner.So3.curvature_eq_quarter_doubleBracket",
            "Poincare.D12.TensorMaximumBochner.So3.ricci_eq_half_metric",
            "Poincare.D12.TensorMaximumBochner.So3.sectional_nonflat",
        ],
        FILES[5]: [
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.Poly3",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.so3e1",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.xVec",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.polyVec",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.rotVec",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.rotVec_expand",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.pderiv_rotVec",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.Dfun",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.Dfun_add_f",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.Dfun_smul_f",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.rotVec_add",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.rotVec_smul",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.Dfun_add_X",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.Dfun_smul_X",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.Dlin",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.D",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.sum_rotVec_pderiv_mul",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.sum_rotVec_mul_pderiv",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.evalAt",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.ui_X0",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.dot_xVec_polyVec_basis",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.dot_polyVec_basis_self",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.D_leibniz",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.D_generator",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.D_rotVec",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.bracket_generator",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.bracket_deriv_apply",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.crossDerivation",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.gA_half_mul_two",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.ricciForm_so3",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.ricciContraction_so3",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.bochner_identity_so3",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.bochner_identity_so3_curvature",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.bochner_identity_so3_eval",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.bochner_inequality_so3",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.bochner_inequality_so3_strict",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.gradSq_X0_at_e1",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.gradSq_X0_at_e1_pos",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.bochner_strict_at_e1",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.Dfun_zero",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.nabla_self",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.H_self_X0",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.lap_X0",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.lap_X0_ne_zero",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.laplacian_gradSq_nonneg_of_harmonic",
            "Poincare.D12.TensorMaximumBochner.So3Polynomial.laplacian_gradSq_pos_of_harmonic",
        ],
        FILES[6]: [
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.idMatrix",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.negIdMatrix",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricForm",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.stdMetric_basis_eq",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.idMatrix_as_matrix",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.negIdMatrix_as_matrix",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_as_matrix",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricForm_apply",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.gram_metricMatrix",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_hasDerivAt",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_differentiableAt",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_deriv",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_isHermitian",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_zero",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_posSemidef_zero",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.dotProduct_mulVec_smul_one",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.dotProduct_mulVec_metricMatrix",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.dotProduct_mulVec_negIdMatrix",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_tangent",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.ricciFlow_equation",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_posSemidef",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_posDef",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricForm_nonneg",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_at_one",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_not_posDef_at_one",
            "Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricForm_at_zero_nonvacuous",
        ],
        FILES[7]: [
            "Poincare.D12.TensorMaximumBochner.KernelTangent",
            "Poincare.D12.TensorMaximumBochner.StrictKernelTangent",
            "Poincare.D12.TensorMaximumBochner.FeasibleDirection",
            "Poincare.D12.TensorMaximumBochner.continuous_dotProduct_mulVec",
            "Poincare.D12.TensorMaximumBochner.kernelTangent_of_feasibleDirection",
            "Poincare.D12.TensorMaximumBochner.kernelTangent_of_posSemidef_path",
            "Poincare.D12.TensorMaximumBochner.counterexampleA",
            "Poincare.D12.TensorMaximumBochner.counterexampleN",
            "Poincare.D12.TensorMaximumBochner.counterexampleA_posSemidef",
            "Poincare.D12.TensorMaximumBochner.counterexampleA_isHermitian",
            "Poincare.D12.TensorMaximumBochner.counterexample_kernelTangent",
            "Poincare.D12.TensorMaximumBochner.counterexample_not_feasible",
            "Poincare.D12.TensorMaximumBochner.kernelTangent_not_feasible",
            "Poincare.D12.TensorMaximumBochner.adjugate_eq_det_smul_inv",
            "Poincare.D12.TensorMaximumBochner.adjugate_posSemidef",
            "Poincare.D12.TensorMaximumBochner.hamiltonField",
            "Poincare.D12.TensorMaximumBochner.dotProduct_mulVec_sq",
            "Poincare.D12.TensorMaximumBochner.hamiltonField_kernelTangent",
            "Poincare.D12.TensorMaximumBochner.hamiltonField_not_strengthened",
            "Poincare.D12.TensorMaximumBochner.hamiltonField_kernel_witness",
            "Poincare.D12.TensorMaximumBochner.counterexample_nondegenerate",
        ],
    }
    errors: list[str] = []
    for f in FILES:
        errors.extend(audit_file(f, expected[f]))
    errors.extend(forbidden_scan())
    errors.extend(negative_control())
    if errors:
        print("\nAUDIT FAILED:")
        for e in errors:
            print("  " + e)
        return 1
    print("\nAXIOM AUDIT PASS: all declarations depend only on {propext, Classical.choice, Quot.sound}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
