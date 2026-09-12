#!/usr/bin/env python3
"""Numeric falsification harness for the L4 ZeroSpacing theorems.

Integrates u'' + k(t) u = 0 with u(a)=0, u'(a)=1 and locates consecutive
zeros strictly to the right of a (DOP853, rtol=1e-13, atol=1e-16, brentq
refinement on the dense output).  Then checks:
  (1) k >= K on [c1, c1+pi/sqrtK] and k > K somewhere in the open interval
      ==> first zero c2 satisfies c2 - c1 < pi/sqrtK
  (2) k <= K on [c1, c2] (verified after the fact on [c1,c2])
      ==> c2 - c1 >= pi/sqrtK
Counterexample attempts use systematic and random piecewise profiles.
"""
import json
import math

import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

RTOL = 1e-13
ATOL = 1e-16
PI = math.pi
SQ = math.sqrt


def integrate_zeros(k, a, T, nsamp=60000):
    """Consecutive sign changes of u strictly right of a (max 4)."""
    def f(t, y):
        return [y[1], -k(t) * y[0]]

    sol = solve_ivp(f, [a, T], [0.0, 1.0], method="DOP853",
                    rtol=RTOL, atol=ATOL, dense_output=True)
    assert sol.success, sol.message
    ts = np.linspace(a, T, nsamp)
    us = sol.sol(ts)[0]
    zeros = []
    for i in range(len(ts) - 1):
        if ts[i] <= a:
            continue
        if us[i] == 0.0:
            zeros.append(float(ts[i]))
        elif us[i] * us[i + 1] < 0.0:
            z = brentq(lambda t: float(sol.sol(t)[0]), ts[i], ts[i + 1],
                       xtol=1e-15, rtol=8.9e-16, maxiter=200)
            zeros.append(float(z))
        if len(zeros) >= 4:
            break
    return sol, zeros


def profile_case(name, k, K, a, T, c1=None):
    c1 = a if c1 is None else c1
    sol, zs = integrate_zeros(k, a, T)
    bound = PI / SQ(K)
    out = {"name": name, "K": K, "a": a, "T": T, "c1": c1,
           "pi_over_sqrtK": bound, "zeros": [float(z) for z in zs],
           "n_zeros": len(zs)}
    if zs:
        c2 = zs[0]
        out.update(c2=c2, spacing=c2 - c1, spacing_minus_bound=c2 - c1 - bound,
                   umin=float(sol.sol(np.linspace(c1, c2, 2001))[0].min()))
    # k on the (1) hypothesis interval
    tt = np.linspace(c1, c1 + bound, 100001)
    kk = np.array([k(t) for t in tt])
    out["min_k_hyp"] = float(kk.min())
    out["max_k_hyp"] = float(kk.max())
    ti = tt[1:-1]
    out["max_k_open"] = float(max(k(t) for t in ti))
    if len(zs) >= 2:
        out["spacing2"] = zs[1] - zs[0]
    return out


def main():
    K = 1.0
    B = PI / SQ(K)
    res = []

    res.append(profile_case("const_above_1.001", lambda t: 1.001, K, 0.0, 7.0))
    res.append(profile_case("const_equal_1.0", lambda t: 1.0, K, 0.0, 7.0))
    res.append(profile_case("const_below_0.999", lambda t: 0.999, K, 0.0, 9.0))
    res.append(profile_case("const_below_0.5", lambda t: 0.5, K, 0.0, 12.0))

    # (1) profiles: k >= 1 on [0,pi], strict excess inside
    res.append(profile_case("bump_center", lambda t: 1.0 + 0.5 * math.exp(-((t - PI / 2) / 0.3) ** 2), K, 0.0, 7.0))
    res.append(profile_case("periodic_above", lambda t: 1.0 + 0.15 * (1.0 + math.sin(2.0 * t)), K, 0.0, 7.0))
    res.append(profile_case("late_gauss_0.05", lambda t: 1.0 + 0.5 * math.exp(-((t - (PI - 0.05)) / 0.02) ** 2), K, 0.0, 7.0))
    res.append(profile_case("power20_half", lambda t: 1.0 + 0.5 * max(t / PI, 0.0) ** 20, K, 0.0, 7.0))
    res.append(profile_case("tiny_power20_1e-6", lambda t: 1.0 + 1e-6 * max(t / PI, 0.0) ** 20, K, 0.0, 7.0))
    res.append(profile_case("square_bump_last_0.05", lambda t: 1.5 if PI - 0.05 <= t <= PI else 1.0, K, 0.0, 7.0))
    res.append(profile_case("excess_only_after_pi", lambda t: 1.0 if t <= PI else 1.5, K, 0.0, 7.0))
    res.append(profile_case("excess_only_at_pi", lambda t: 1.5 if abs(t - PI) < 1e-12 else 1.0, K, 0.0, 7.0))

    # (2) profiles: k <= 1
    res.append(profile_case("below_sin2", lambda t: 1.0 - 0.15 * (1.0 + math.cos(2.0 * t)), K, 0.0, 12.0))
    res.append(profile_case("below_gauss_dip", lambda t: 1.0 - 0.5 * math.exp(-((t - 1.0) / 0.2) ** 2), K, 0.0, 12.0))
    res.append(profile_case("below_late_dip", lambda t: 1.0 if t < 2.0 else 0.5, K, 0.0, 12.0))
    res.append(profile_case("below_ramp", lambda t: 1.0 - 0.4 * min(t / 5.0, 1.0), K, 0.0, 12.0))

    K2 = 2.25
    res.append(profile_case("shifted_const_above", lambda t: K2 + 0.01, K2, 1.234, 9.0))
    res.append(profile_case("shifted_bump", lambda t: K2 + 0.3 * math.exp(-((t - (1.234 + PI / SQ(K2) / 2)) / 0.2) ** 2), K2, 1.234, 9.0))
    res.append(profile_case("shifted_const_below", lambda t: K2 - 0.01, K2, 1.234, 12.0))

    # random piecewise-constant search
    rng = np.random.default_rng(20260912)
    worst_above = None
    worst_below = None
    for trial in range(60):
        nseg = 8
        edges = np.linspace(0.0, PI, nseg + 1)
        vals = K + rng.uniform(0.0, 0.8, size=nseg)
        if vals.max() <= K:
            vals[0] = K + 0.1
        def k1(t, edges=edges, vals=vals):
            i = min(int(np.searchsorted(edges, t, side="right")) - 1, nseg - 1)
            return vals[max(i, 0)]
        r = profile_case(f"rand_above_{trial}", k1, K, 0.0, 7.0)
        if r["zeros"]:
            d = r["spacing_minus_bound"]
            if worst_above is None or d > worst_above[0]:
                worst_above = (d, r["name"], r["spacing"], r["min_k_hyp"])
        vals2 = K - rng.uniform(0.0, 0.8, size=nseg)
        def k2(t, edges=edges, vals=vals2):
            i = min(int(np.searchsorted(edges, t, side="right")) - 1, nseg - 1)
            return vals2[max(i, 0)]
        r2 = profile_case(f"rand_below_{trial}", k2, K, 0.0, 12.0)
        if r2["zeros"]:
            d2 = r2["spacing_minus_bound"]
            if worst_below is None or d2 < worst_below[0]:
                worst_below = (d2, r2["name"], r2["spacing"], r2["max_k_hyp"],
                               float(max(k2(t) for t in np.linspace(0, r2["c2"], 20001))))
    res.append({"name": "SEARCH_above_worst", "value": worst_above})
    res.append({"name": "SEARCH_below_worst", "value": worst_below})

    with open("numeric_results.json", "w") as f:
        json.dump(res, f, indent=1)

    hdr = f"{'case':26s} {'c2':>18s} {'spacing':>18s} {'spacing-bound':>15s} {'min_k_hyp':>9s} {'max_k_open':>10s} {'sp2-bound':>10s}"
    print(hdr)
    for r in res:
        if "zeros" not in r:
            print(r)
            continue
        c2 = r.get("c2")
        sp2 = r.get("spacing2")
        print(f"{r['name']:26s} {c2!r:>18s} {r['spacing']!r:>18s} "
              f"{r['spacing_minus_bound']:+.3e} {r['min_k_hyp']:9.4f} "
              f"{r['max_k_open']:10.4f} "
              f"{(sp2 - r['pi_over_sqrtK']) if sp2 else float('nan'):+.3e}")


if __name__ == "__main__":
    main()
