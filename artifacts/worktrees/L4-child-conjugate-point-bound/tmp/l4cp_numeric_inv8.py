#!/usr/bin/env python3
"""Invocation-8 independent numerical falsification cross-check (NOT part of the release).

For u'' = -k(t)u with u(0)=0, u'(0)=1, compute the first positive zero T*(k) with an
adaptive RK45 integrator (scipy solve_ivp, tight tolerances, Brent event root) and compare
against the formal theorem's bound pi/sqrt(K):

  * constant k == K: the sharp model predicts T* = pi/sqrt(K) exactly (equality case);
  * non-constant k >= K: T* must be <= pi/sqrt(K); the formal theorem claims this;
  * dropped domination (k = 0.8K): T* must exceed pi/sqrt(K), proving the test detects a
    violation rather than always printing PASS.
"""
import json
import math
import sys

import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

PI = math.pi


def first_zero(k, tmax=40.0):
    def rhs(t, y):
        return [y[1], -k(t) * y[0]]

    def event(t, y):
        return y[0]

    event.terminal = True
    event.direction = -1
    sol = solve_ivp(rhs, (0.0, tmax), [0.0, 1.0], method="RK45",
                    rtol=1e-13, atol=1e-15, events=event, dense_output=True)
    if len(sol.t_events[0]) == 0:
        return None
    return float(sol.t_events[0][0])


def main():
    rows = []
    ok = True

    # 1. constant coefficient: sharp equality at the model first zero
    for K in [1.0, 2.0, 0.5, 5.0]:
        T = first_zero(lambda t, K=K: K)
        pred = PI / math.sqrt(K)
        rel = abs(T - pred) / pred
        good = rel <= 1e-9
        ok &= good
        rows.append({"case": f"constant k={K}", "T_star": T, "bound": pred,
                     "rel_err": rel, "expect": "T* == pi/sqrt(K) (sharp)",
                     "verdict": "PASS" if good else "FAIL"})

    # 2. non-constant k >= K: theorem bound must hold
    nonconst = [
        ("k=2+sin^2(t)", lambda t: 2.0 + math.sin(t) ** 2, 2.0),
        ("k=2+t/10", lambda t: 2.0 + t / 10.0, 2.0),
        ("k=1+0.5cos^2(t)", lambda t: 1.0 + 0.5 * math.cos(t) ** 2, 1.0),
        ("k=5+exp(-t)", lambda t: 5.0 + math.exp(-t), 5.0),
        ("k=0.5+1e-6 sin^2(t) (near threshold)",
         lambda t: 0.5 + 1e-6 * math.sin(t) ** 2, 0.5),
    ]
    for name, k, K in nonconst:
        T = first_zero(k)
        bound = PI / math.sqrt(K)
        good = T is not None and T <= bound
        ok &= good
        rows.append({"case": name, "T_star": T, "bound": bound,
                     "margin": None if T is None else bound - T,
                     "expect": "T* <= pi/sqrt(K)", "verdict": "PASS" if good else "FAIL"})

    # 3. adversarial: domination dropped (k = 0.8 K) must violate the bound
    for K in [2.0, 1.0]:
        T = first_zero(lambda t, K=K: 0.8 * K)
        bound = PI / math.sqrt(K)
        violated = T is not None and T > bound
        ok &= violated
        rows.append({"case": f"adversarial k=0.8*{K} (domination dropped)", "T_star": T,
                     "bound": bound, "excess": None if T is None else T - bound,
                     "expect": "T* > pi/sqrt(K)  (test must detect)",
                     "verdict": "PASS" if violated else "FAIL"})

    # 4. the k=2 model and the requested witnesses
    T2 = first_zero(lambda t: 2.0)
    wit = {"k2_first_zero": T2, "pi/sqrt2": PI / math.sqrt(2),
           "sharp_equality": abs(T2 - PI / math.sqrt(2)) <= 1e-9,
           "witness_k2_K1_2_le_pi_over_sqrt1": 2.0 <= PI / math.sqrt(1.0),
           "witness_k2_K2_2_le_pi_over_sqrt2": 2.0 <= PI / math.sqrt(2.0),
           "sharpening_pi_sqrt2_lt_pi": PI / math.sqrt(2) < PI}
    ok &= all([wit["sharp_equality"], wit["witness_k2_K1_2_le_pi_over_sqrt1"],
               wit["witness_k2_K2_2_le_pi_over_sqrt2"], wit["sharpening_pi_sqrt2_lt_pi"]])

    out = {"ok": bool(ok), "integrator": "scipy.solve_ivp RK45 rtol=1e-13 atol=1e-15, Brent event",
           "rows": rows, "witness_checks": wit}
    print(json.dumps(out, indent=1))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
