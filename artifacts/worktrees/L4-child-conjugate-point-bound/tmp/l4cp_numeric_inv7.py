#!/usr/bin/env python3
"""Invocation-7 numeric cross-check for the L4 conjugate-point-bound deliverable.

Independent of the Lean proof: solves the scalar Jacobi equation
    u'' + k(t) u = 0,  u(0) = 0, u'(0) = 1
numerically and compares the first positive zero t* with the claimed bound
pi/sqrt(K) for k >= K > 0.  A counterexample to the theorem would be t* > pi/sqrt(K);
the script reports the signed margin t* - pi/sqrt(K) for several non-constant k and
for the exact non-constant-coefficient witness used by the inv7 Lean probe.

Written from scratch for this invocation; not part of the release package.
"""
import json
import math
import sys
from datetime import datetime, timezone

import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

RESULTS = []


def first_zero(k, K, tmax, rtol=1e-12, atol=1e-14):
    """First positive zero of the Jacobi solution with k, or None if none in (0,tmax]."""
    def rhs(t, y):
        return [y[1], -k(t) * y[0]]

    def ev(t, y):
        return y[0]

    ev.terminal = True
    ev.direction = -1
    # start just to the right of 0 to avoid a singular k at t = 0
    t0 = 1e-9
    y0 = [t0, 1.0]
    sol = solve_ivp(rhs, (t0, tmax), y0, events=ev, rtol=rtol, atol=atol,
                    dense_output=True, max_step=tmax / 50)
    if sol.t_events[0].size == 0:
        return None, sol
    # refine the event location on the dense interpolant
    ta = sol.t_events[0][0]
    lo, hi = max(t0, ta - 1e-6), min(tmax, ta + 1e-6)
    fa, fb = sol.sol(lo)[0], sol.sol(hi)[0]
    if fa * fb < 0:
        ta = brentq(lambda t: sol.sol(t)[0], lo, hi, xtol=1e-15, rtol=1e-15)
    return ta, sol


def record(name, k, K, tmax, expect_factor=1.0):
    tstar, sol = first_zero(k, K, tmax)
    bound = math.pi / math.sqrt(K)
    row = {
        "name": name,
        "K": K,
        "bound_pi_over_sqrtK": bound,
        "tmax": tmax,
        "first_zero": tstar,
        "margin_tstar_minus_bound": (tstar - bound) if tstar is not None else None,
        "first_zero_within_bound": (tstar is not None and tstar <= bound),
        "nfev": int(sol.nfev),
    }
    RESULTS.append(row)
    print(json.dumps(row))
    return row


def main():
    print(f"# L4 conjugate-point-bound numeric cross-check, {datetime.now(timezone.utc).isoformat()}")

    # 1. Constant coefficients: first zero must equal pi/sqrt(K) (sharp threshold).
    for K in (1.0, 2.0, 0.5, 5.0):
        tstar, _ = first_zero(lambda t: K, K, 1.2 * math.pi / math.sqrt(K))
        bound = math.pi / math.sqrt(K)
        rel = abs(tstar - bound) / bound
        RESULTS.append({
            "name": f"constant k=K={K}",
            "K": K,
            "bound_pi_over_sqrtK": bound,
            "first_zero": tstar,
            "rel_error_vs_bound": rel,
            "sharp_threshold_confirmed": rel < 1e-9,
        })
        print(json.dumps(RESULTS[-1]))

    # 2. Non-constant k >= K: first zero must be <= pi/sqrt(K), strictly below unless k == K a.e.
    cases = [
        ("k=K(1+0.02 sin^2 t), K=1", lambda t: 1.0 * (1 + 0.02 * math.sin(t) ** 2), 1.0),
        ("k=K(1+0.2 sin^2 t), K=1", lambda t: 1.0 * (1 + 0.2 * math.sin(t) ** 2), 1.0),
        ("k=K(1+0.05 cos^2(2t)), K=2", lambda t: 2.0 * (1 + 0.05 * math.cos(2 * t) ** 2), 2.0),
        ("k=K(1+t/10), K=0.5", lambda t: 0.5 * (1 + t / 10), 0.5),
        ("k=K*(1+0.5*sin^2 t), K=5", lambda t: 5.0 * (1 + 0.5 * math.sin(t) ** 2), 5.0),
    ]
    for name, k, K in cases:
        row = record(name, k, K, 1.05 * math.pi / math.sqrt(K))
        row["strictly_below_bound"] = row["margin_tstar_minus_bound"] < 0
        print(json.dumps(row))

    # 3. Adversarial: k below K somewhere must (numerically) break the bound.
    #    k = 0.8 K gives first zero pi/sqrt(0.8 K) > pi/sqrt(K): the domination K <= k is essential.
    for K in (1.0, 2.0):
        tstar, _ = first_zero(lambda t: 0.8 * K, K, 1.3 * math.pi / math.sqrt(K))
        bound = math.pi / math.sqrt(K)
        RESULTS.append({
            "name": f"adversarial k=0.8K, K={K}",
            "K": K,
            "bound_pi_over_sqrtK": bound,
            "first_zero": tstar,
            "margin_tstar_minus_bound": tstar - bound,
            "bound_violated_when_domination_dropped": tstar > bound,
        })
        print(json.dumps(RESULTS[-1]))

    # 4. The exact non-constant-coefficient witness of tmp/l4cp_probe_inv7.lean:
    #    k(t) = 2/(t(4-t)) on (0,2), u(t) = t(1-t/4), u'' = -k u, u > 0 on (0,2],
    #    K = 1/2, claimed bound 2 <= pi/sqrt(1/2) = pi*sqrt(2).
    def kW(t):
        return 2.0 / (t * (4.0 - t))

    def uW(t):
        return t * (1 - t / 4)

    def duW(t):
        return 1 - t / 2

    ts = np.linspace(1e-6, 2.0, 200001)
    u = uW(ts)
    res = np.max(np.abs(-0.5 + kW(ts) * u))  # |u'' + k u|, u'' = -1/2
    tstar, sol = first_zero(kW, 0.5, 4.5)
    gap = 2.0 - math.pi / math.sqrt(0.5)
    row = {
        "name": "inv7 exact witness k=2/(t(4-t)), K=1/2, T=2",
        "K": 0.5,
        "bound_pi_over_sqrtK": math.pi / math.sqrt(0.5),
        "T_inv7_probe": 2.0,
        "bound_at_T_satisfied": 2.0 <= math.pi / math.sqrt(0.5),
        "bound_minus_T": math.pi / math.sqrt(0.5) - 2.0,
        "u_min_on_(0,2]": float(np.min(u)),
        "u_at_2": float(uW(2.0)),
        "max_ode_residual_on_(0,2]": float(res),
        "first_zero_numeric": tstar,
        "first_zero_analytic": 4.0,
        "first_zero_rel_error": abs(tstar - 4.0) / 4.0,
        "ode_residual_zero": bool(res < 1e-12),
        "positive_on_(0,2]": bool(np.min(u) > 0),
    }
    RESULTS.append(row)
    print(json.dumps(row))

    # 5. Near-threshold numeric probe: k >= 1 with a tiny bump; t* must sit just under pi.
    row = record("near-threshold k=1+1e-4 sin^2 t, K=1", lambda t: 1 + 1e-4 * math.sin(t) ** 2, 1.0,
                 1.02 * math.pi)
    row["gap_below_pi"] = math.pi - row["first_zero"]
    print(json.dumps(row))

    ok = all(
        r.get("sharp_threshold_confirmed", True)
        and r.get("first_zero_within_bound", True)
        and r.get("bound_violated_when_domination_dropped", True)
        and r.get("bound_at_T_satisfied", True)
        and r.get("ode_residual_zero", True)
        for r in RESULTS
    )
    print(json.dumps({"ok": bool(ok), "rows": len(RESULTS)}))
    with open("logs/l4cp-numeric-inv7.json", "w") as f:
        json.dump({"generated_at": datetime.now(timezone.utc).isoformat(), "ok": bool(ok),
                   "results": RESULTS}, f, indent=1)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
