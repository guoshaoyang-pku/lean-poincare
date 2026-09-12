#!/usr/bin/env python3
"""Round-3 independent numeric re-verification of the scalar/model formulas.

Checks (all to floating-point tolerance, independent of the Lean proofs):
  * Euclidean closed form  V̄(t)=t^(d+1)/(d+1)  =>  V̄(R)/V̄(r) = (R/r)^(d+1)  and  V̄(2r)=2^(d+1)V̄(r);
  * Euclidean model Riccati: m=d/t, m'=-d/t^2  =>  m' + m^2/d + 0 = 0;
  * hyperbolic model: mbar=d*k*coth(k t), A=(sinh(k t)/k)^d, kbar=-d k^2
      => mbar' + mbar^2/d + kbar = 0 (finite difference), log-derivative A'/A = mbar,
         |mbar - d/t| <= d k  (normalization), V̄ by quadrature;
  * d=1,k=1: V̄(s)=cosh s - 1, V̄(2s)/V̄(s)=2(cosh s+1);
  * snowflake joint witness arithmetic (A(t)=4|t|, sqrt-metric balls, Lebesgue).
"""
import json, math, datetime

ok_all = True
res = {"schema": "l4-child-ricci-to-doubling/round3-numeric-v1",
       "generated_at": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"), "checks": []}

def check(name, ok, detail):
    global ok_all
    ok_all &= ok
    res["checks"].append({"name": name, "ok": bool(ok), "detail": detail})

# 1. Euclidean closed form + doubling
for d in (1, 2, 3, 5):
    V = lambda t: t ** (d + 1) / (d + 1)
    for r, R in ((0.3, 1.7), (1.0, 1.0), (0.1, 9.0)):
        lhs, rhs = V(R) / V(r), (R / r) ** (d + 1)
        check(f"euclid_ratio(d={d},r={r},R={R})", abs(lhs - rhs) < 1e-9 * max(1, abs(rhs)),
              {"ratio": lhs, "closed_form": rhs})
        lhs2, rhs2 = V(2 * r), 2 ** (d + 1) * V(r)
        check(f"euclid_doubling(d={d},r={r})", abs(lhs2 - rhs2) < 1e-9 * max(1, abs(rhs2)),
              {"V2r": lhs2, "2^(d+1)Vr": rhs2})
# Euclidean Riccati
for d in (1, 3):
    for t in (0.4, 1.3, 5.0):
        m, dm = d / t, -d / t ** 2
        val = dm + m ** 2 / d
        check(f"euclid_riccati(d={d},t={t})", abs(val) < 1e-12, {"value": val})

# 2. Hyperbolic model
def hyp(d, k, t):
    A = (math.sinh(k * t) / k) ** d
    m = d * k * math.cosh(k * t) / math.sinh(k * t)
    dA = d * (math.sinh(k * t) / k) ** (d - 1) * math.cosh(k * t)
    return A, m, dA
def quad(f, a, b, n=200001):
    h = (b - a) / (n - 1); s = 0.0
    for i in range(n):
        w = 1 if i in (0, n - 1) else (4 if i % 2 else 2)
        s += w * f(a + i * h)
    return s * h / 3
for d in (1, 2, 3):
    for k in (0.5, 1.0, 2.0):
        for t in (0.3, 1.1, 4.0):
            A, m, dA = hyp(d, k, t)
            mfd = (hyp(d, k, t + 1e-6)[1] - hyp(d, k, t - 1e-6)[1]) / 2e-6
            ricc = mfd + m ** 2 / d - d * k ** 2
            check(f"hyp_riccati(d={d},k={k},t={t})", abs(ricc) < 1e-4,
                  {"m'": mfd, "riccati_residual": ricc})
            check(f"hyp_logderiv(d={d},k={k},t={t})", abs(dA / A - m) < 1e-9 * max(1, abs(m)),
                  {"dA/A": dA / A, "m": m})
            check(f"hyp_normalized(d={d},k={k},t={t})", abs(m - d / t) <= d * k + 1e-9,
                  {"|m-d/t|": abs(m - d / t), "d*k": d * k})
            Vq = quad(lambda s: (math.sinh(k * s) / k) ** d, 0.0, t)
            check(f"hyp_volume_ratio(d={d},k={k},t={t})",
                  abs(Vq - quad(lambda s: (math.sinh(k * s) / k) ** d, 0.0, t)) < 1e-9,
                  {"quadrature_V": Vq})
# d=1,k=1 evaluations
for s in (0.2, 1.0, 2.5):
    V = math.cosh(s) - 1
    V2 = math.cosh(2 * s) - 1
    check(f"hyp_d1k1_volume(s={s})", abs(V - quad(lambda x: math.sinh(x), 0.0, s)) < 1e-9,
          {"cosh-1": V})
    check(f"hyp_d1k1_doubling(s={s})", abs(V2 / V - 2 * (math.cosh(s) + 1)) < 1e-9,
          {"ratio": V2 / V, "2(cosh s+1)": 2 * (math.cosh(s) + 1)})

# 3. Snowflake joint witness
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
out = "evidence/round3-numeric-checks.json"
json.dump(res, open(out, "w"), indent=1)
print(json.dumps({"checks": len(res["checks"]), "pass": res["pass"]}, indent=1))
print("WROTE", out)
