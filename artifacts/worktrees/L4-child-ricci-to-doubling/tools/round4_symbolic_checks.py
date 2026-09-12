#!/usr/bin/env python3
"""Round-4 exact symbolic verification of the hyperbolic closed form (sympy, in /tmp only).

Independently of the Lean proofs, this checks by exact computer algebra:
  * the recursion J_0=x, J_1=cosh x - 1, J_{d+2}=(sinh(x)^{d+1} cosh x - (d+1) J_d)/(d+2)
    satisfies  J_d(x) = ∫_0^x sinh(t)^d dt  and  J_d'(x) = sinh(x)^d  for d = 0..9;
  * the model-volume closed form  ∫_0^s (sinh(k t)/k)^d dt = (1/k)^{d+1} J_d(k s)
    for d = 0..5 symbolically in k, s > 0.

Comparison is done after rewriting to exponentials and expanding, so the check is exact
(rational functions of exp) rather than a floating-point quadrature check.
"""
import json
import datetime
import sympy as sp

x = sp.symbols("x", real=True)
J = {0: x, 1: sp.cosh(x) - 1}
for d in range(0, 12):
    J[d + 2] = sp.expand((sp.sinh(x) ** (d + 1) * sp.cosh(x) - (d + 1) * J[d]) / (d + 2))


def canon(e):
    return sp.expand(sp.simplify(sp.expand(e.rewrite(sp.exp))))


res = {"schema": "l4-child-ricci-to-doubling/round4-symbolic-v1",
       "generated_at": datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
       "checks": [], "pass": False}

ok = True
for d in range(0, 10):
    exact = sp.integrate(sp.sinh(x) ** d, (x, 0, x))
    di = canon(J[d] - exact)
    dd = canon(sp.diff(J[d], x) - sp.sinh(x) ** d)
    ok &= (di == 0) and (dd == 0)
    res["checks"].append({"name": f"J_{d}=integral", "difference": str(di), "ok": di == 0})
    res["checks"].append({"name": f"J_{d}'=sinh^{d}", "difference": str(dd), "ok": dd == 0})

k, s = sp.symbols("kappa s", positive=True)
for d in range(0, 6):
    lhs = sp.integrate((sp.sinh(k * x) / k) ** d, (x, 0, s))
    rhs = (1 / k) ** (d + 1) * J[d].subs(x, k * s)
    dv = canon(lhs - rhs)
    ok &= (dv == 0)
    res["checks"].append({"name": f"modelvolume_d={d}", "difference": str(dv), "ok": dv == 0})

res["pass"] = bool(ok)
res["summary"] = {"checks": len(res["checks"]),
                  "failed": [c["name"] for c in res["checks"] if not c["ok"]]}
out = "evidence/round4-symbolic-checks.json"
json.dump(res, open(out, "w"), indent=1)
print(json.dumps(res["summary"], indent=1))
print("ROUND4-SYMBOLIC:", "PASS" if res["pass"] else "FAIL", "->", out)
