#!/usr/bin/env python3
"""Round-4 independent numeric verification of the scalar/model formulas.

Extends the round-3 numeric checks with the round-4 elementary closed form of the hyperbolic
model volume `V̄(s) = ∫₀ˢ (sinh(κt)/κ)^d dt = (κ⁻¹)^(d+1) J_d(κ s)`.

Checks (all to floating-point tolerance, independent of the Lean proofs):
  A. Euclidean closed form V̄(t)=t^(d+1)/(d+1): ratio (R/r)^(d+1), doubling 2^(d+1), Riccati;
  B. hyperbolic model: Riccati equality (finite difference), log-derivative, normalization,
     d=1,κ=1 evaluated volume/doubling;
  C. NEW round-4: the recursion
        J_0(x)=x, J_1(x)=cosh x − 1,
        J_{d+2}(x)=(sinh(x)^(d+1)·cosh x − (d+1)·J_d(x))/(d+2)
     against high-accuracy quadrature of sinh^d, for d = 1..8, x positive and negative;
  D. NEW round-4: the substitution identity (κ⁻¹)^(d+1) J_d(κ s) against quadrature of
     (sinh(κt)/κ)^d for κ = 0.3, 1, 2.5 and d = 1..5;
  E. NEW round-4: the elementary evaluations J_2(x)=(sinh x cosh x − x)/2,
     J_3(x)=(sinh(x)^2 cosh x − 2(cosh x − 1))/3, and the d=2 ratio;
  F. snowflake joint-witness arithmetic (A(t)=4|t|, sqrt-metric balls, Lebesgue).
"""
import json, math, datetime

ok_all = True
res = {"schema": "l4-child-ricci-to-doubling/round4-numeric-v1",
       "generated_at": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"), "checks": []}


def check(name, ok, detail):
    global ok_all
    ok_all &= ok
    res["checks"].append({"name": name, "ok": bool(ok), "detail": detail})


def quad(f, a, b, n=400001):
    """Composite Simpson on [a,b] (n odd)."""
    if a == b:
        return 0.0
    h = (b - a) / (n - 1)
    s = 0.0
    for i in range(n):
        w = 1 if i in (0, n - 1) else (4 if i % 2 else 2)
        s += w * f(a + i * h)
    return s * h / 3


# A. Euclidean closed form + doubling + Riccati -------------------------------------------------
for d in (1, 2, 3, 5):
    V = lambda t: t ** (d + 1) / (d + 1)
    for r, R in ((0.3, 1.7), (1.0, 1.0), (0.1, 9.0)):
        lhs, rhs = V(R) / V(r), (R / r) ** (d + 1)
        check(f"euclid_ratio(d={d},r={r},R={R})", abs(lhs - rhs) < 1e-9 * max(1, abs(rhs)),
              {"ratio": lhs, "closed_form": rhs})
        lhs2, rhs2 = V(2 * r), 2 ** (d + 1) * V(r)
        check(f"euclid_doubling(d={d},r={r})", abs(lhs2 - rhs2) < 1e-9 * max(1, abs(rhs2)),
              {"V2r": lhs2, "2^(d+1)Vr": rhs2})
for d in (1, 3):
    for t in (0.4, 1.3, 5.0):
        m, dm = d / t, -d / t ** 2
        check(f"euclid_riccati(d={d},t={t})", abs(dm + m ** 2 / d) < 1e-12,
              {"value": dm + m ** 2 / d})

# B. Hyperbolic model ---------------------------------------------------------------------------
def hyp(d, k, t):
    A = (math.sinh(k * t) / k) ** d
    m = d * k * math.cosh(k * t) / math.sinh(k * t)
    dA = d * (math.sinh(k * t) / k) ** (d - 1) * math.cosh(k * t)
    return A, m, dA


for d in (1, 2, 3):
    for k in (0.5, 1.0, 2.0):
        for t in (0.3, 1.1, 4.0):
            A, m, dA = hyp(d, k, t)
            mfd = (hyp(d, k, t + 1e-6)[1] - hyp(d, k, t - 1e-6)[1]) / 2e-6
            check(f"hyp_riccati(d={d},k={k},t={t})", abs(mfd + m ** 2 / d - d * k ** 2) < 1e-4,
                  {"riccati_residual": mfd + m ** 2 / d - d * k ** 2})
            check(f"hyp_logderiv(d={d},k={k},t={t})", abs(dA / A - m) < 1e-9 * max(1, abs(m)),
                  {"dA/A": dA / A, "m": m})
            check(f"hyp_normalized(d={d},k={k},t={t})", abs(m - d / t) <= d * k + 1e-9,
                  {"|m-d/t|": abs(m - d / t), "d*k": d * k})
for s in (0.2, 1.0, 2.5):
    V, V2 = math.cosh(s) - 1, math.cosh(2 * s) - 1
    check(f"hyp_d1k1_volume(s={s})", abs(V - quad(math.sinh, 0.0, s)) < 1e-6,
          {"cosh-1": V})
    check(f"hyp_d1k1_doubling(s={s})", abs(V2 / V - 2 * (math.cosh(s) + 1)) < 1e-9,
          {"ratio": V2 / V, "2(cosh s+1)": 2 * (math.cosh(s) + 1)})

# C. Round-4 recursion J_d against quadrature of sinh^d ----------------------------------------
def J(d, x):
    if d == 0:
        return x
    if d == 1:
        return math.cosh(x) - 1
    jm2, jm1 = x, math.cosh(x) - 1          # J_0, J_1
    # iterate forward: J_{n+2} = (sinh^{n+1} cosh - (n+1) J_n) / (n+2)
    n = 0
    while n + 2 <= d:
        jn = ((math.sinh(x)) ** (n + 1) * math.cosh(x) - (n + 1) * jm2) / (n + 2)
        jm2, jm1 = jm1, jn
        n += 1
    return jm1 if d >= 1 else x


max_err_rec = 0.0
for d in range(1, 9):
    for x in (0.15, 0.5, 1.0, 2.3, 4.0, -0.4, -1.2, -2.6):
        exact = quad(lambda t: math.sinh(t) ** d, 0.0, x)
        approx = J(d, x)
        err = abs(exact - approx) / max(1.0, abs(exact))
        max_err_rec = max(max_err_rec, err)
        check(f"closedform_J(d={d},x={x})", err < 1e-6,
              {"quadrature": exact, "recursion": approx, "rel_err": err})
check("closedform_J_max_rel_err", max_err_rec < 1e-6, {"max_rel_err": max_err_rec})

# D. Round-4 substitution identity --------------------------------------------------------------
max_err_sub = 0.0
for d in range(1, 6):
    for k in (0.3, 1.0, 2.5):
        for s in (0.4, 1.2, 2.0):
            exact = quad(lambda t: (math.sinh(k * t) / k) ** d, 0.0, s)
            closed = (k ** -1) ** (d + 1) * J(d, k * s)
            err = abs(exact - closed) / max(1.0, abs(exact))
            max_err_sub = max(max_err_sub, err)
            check(f"modelvolume_closedform(d={d},k={k},s={s})", err < 1e-6,
                  {"quadrature": exact, "closed_form": closed, "rel_err": err})
            ratio_q = quad(lambda t: (math.sinh(k * t) / k) ** d, 0.0, 2 * s) / exact
            ratio_c = J(d, k * (2 * s)) / J(d, k * s)
            check(f"modelratio_closedform(d={d},k={k},s={s})",
                  abs(ratio_q - ratio_c) < 1e-6 * max(1, abs(ratio_c)),
                  {"quadrature_ratio": ratio_q, "closed_ratio": ratio_c})
check("modelvolume_closedform_max_rel_err", max_err_sub < 1e-6, {"max_rel_err": max_err_sub})

# D2. Round-4 substitution identity, signed radii and signed kappa (the Lean statement claims
#     equality for ALL real s and all kappa != 0, so the boundary directions are exercised).
max_err_signed = 0.0
for d in (1, 2, 3, 4):
    for k in (0.3, -0.8, 1.0, -2.5):
        for s in (-0.7, -1.5, 0.0, 0.45, 1.6):
            exact = quad(lambda t: (math.sinh(k * t) / k) ** d, 0.0, s)
            closed = (k ** -1) ** (d + 1) * J(d, k * s)
            err = abs(exact - closed) / max(1.0, abs(exact))
            max_err_signed = max(max_err_signed, err)
            check(f"modelvolume_closedform_signed(d={d},k={k},s={s})", err < 1e-6,
                  {"quadrature": exact, "closed_form": closed, "rel_err": err})
check("modelvolume_closedform_signed_max_rel_err", max_err_signed < 1e-6,
      {"max_rel_err": max_err_signed})

# E. Round-4 elementary evaluations -------------------------------------------------------------
for x in (0.1, 0.9, 2.2, -0.6):
    j2 = (math.sinh(x) * math.cosh(x) - x) / 2
    j3 = (math.sinh(x) ** 2 * math.cosh(x) - 2 * (math.cosh(x) - 1)) / 3
    check(f"J2_elementary(x={x})", abs(J(2, x) - j2) < 1e-12, {"J": J(2, x), "formula": j2})
    check(f"J3_elementary(x={x})", abs(J(3, x) - j3) < 1e-12, {"J": J(3, x), "formula": j3})
for k in (0.4, 1.0, 1.7):
    for r, R in ((0.3, 1.4), (0.7, 0.7)):
        lhs = J(2, k * R) / J(2, k * r)
        rhs = ((math.sinh(k * R) * math.cosh(k * R) - k * R) /
               (math.sinh(k * r) * math.cosh(k * r) - k * r))
        check(f"d2_ratio_elementary(k={k},r={r},R={R})",
              abs(lhs - rhs) < 1e-9 * max(1, abs(rhs)), {"ratio": lhs, "elementary": rhs})
for s in (0.2, 1.0, 2.5):
    # hypModelA_one_one_volume_closedForm: (1⁻¹)^(1+1) * J_1(1*s) = cosh s − 1
    check(f"d1k1_closedform_agrees(s={s})",
          abs((1.0 ** -1) ** 2 * J(1, 1.0 * s) - (math.cosh(s) - 1)) < 1e-12,
          {"closed": (1.0 ** -1) ** 2 * J(1, 1.0 * s), "cosh s - 1": math.cosh(s) - 1})

# F. Snowflake joint witness --------------------------------------------------------------------
for s in (-1.3, -0.5, 0.0, 0.25, 1.0, 2.7):
    V = quad(lambda t: 4 * abs(t), 0.0, s)
    exact = 2 * s * abs(s)
    check(f"snowflake_radialVolume(s={s})", abs(V - exact) < 1e-6 * max(1, abs(exact)),
          {"quadrature": V, "2s|s|": exact})
    ball = 2 * s * s if s >= 0 else 0.0
    check(f"snowflake_ball(s={s})", abs(ball - max(exact, 0.0)) < 1e-12,
          {"lebesgue_ball": ball, "ofReal(V)": max(exact, 0.0)})
for t in (0.1, 0.7, 3.3, 9.9):
    ricc = -1 / t ** 2 + (1 / t) ** 2
    check(f"snowflake_scalar_hypotheses(t={t})",
          abs(ricc) < 1e-12 and abs(1 / t - 4 / (4 * t)) < 1e-12, {"riccati": ricc})

res["pass"] = bool(ok_all)
res["summary"] = {"checks": len(res["checks"]),
                  "failed": [c["name"] for c in res["checks"] if not c["ok"]],
                  "closedform_J_max_rel_err": max_err_rec,
                  "modelvolume_closedform_max_rel_err": max_err_sub,
                  "modelvolume_closedform_signed_max_rel_err": max_err_signed}
out = "evidence/round4-numeric-checks.json"
json.dump(res, open(out, "w"), indent=1)
print(json.dumps(res["summary"], indent=1))
print("ROUND4-NUMERIC:", "PASS" if res["pass"] else "FAIL", "->", out)
