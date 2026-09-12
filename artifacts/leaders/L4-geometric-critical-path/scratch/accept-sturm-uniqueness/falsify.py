#!/usr/bin/env python3
"""
Independent numeric check for Poincare/L4/GeodesicComparison/SturmUniqueness.lean.

Integrates u'' + k(t) u = 0, u(a)=0, u'(a)=1, for nonconstant k <= K profiles,
on spans slightly below pi/sqrt(K), and looks for zeros (attempted falsification of
`no_zero_of_curvature_le_of_deriv_ne`).  Also checks proportionality of u to the
model sin(sqrt(K)(t-a)) when k == K on the interval (attempted falsification of
`exists_smul_sturmModel_of_curvature_eq` / `wronskian_sturmModel_eq_zero_of_curvature_eq`).

scipy 1.15.3 / numpy 2.2.6, DOP853, rtol=1e-13 (<= 1e-12), atol=1e-15.
"""
import numpy as np
from scipy.integrate import solve_ivp

np.set_printoptions(precision=16)
K = 1.0
A = 0.0
PI = np.pi
T_MODEL = PI / np.sqrt(K)          # model first zero, ~3.14159265358979
print(f"K={K}  a={A}  pi/sqrt(K)={T_MODEL!r}")

# ---------------------------------------------------------------- profiles
def bump(t, m, w, eps):
    return K - eps * np.exp(-((t - m) / w) ** 2)

def osc(t, m, w, eps, freq):
    return K - eps * (1.0 + np.sin(freq * t)) / 2.0

profiles = {
    # near-equality constants / localized deficits
    "const K-1e-8":                 (lambda t: K - 1e-8, K - 1e-8),
    "const K-1e-6":                 (lambda t: K - 1e-6, K - 1e-6),
    "const K-0.5":                  (lambda t: K - 0.5,  K - 0.5),
    "gauss eps=1e-8 m=1.5 w=0.05":  (lambda t: bump(t, 1.5, 0.05, 1e-8), K - 1e-8),
    "gauss eps=1e-6 m=1.5 w=0.02":  (lambda t: bump(t, 1.5, 0.02, 1e-6), K - 1e-6),
    "gauss eps=0.5  m=1.0 w=0.20":  (lambda t: bump(t, 1.0, 0.20, 0.5),  K - 0.5),
    "gauss eps=0.9  m=2.0 w=0.30":  (lambda t: bump(t, 2.0, 0.30, 0.9),  K - 0.9),
    "osc   eps=0.3 freq=13":        (lambda t: osc(t, 0, 0, 0.3, 13.0),  K - 0.3),
    "linear K*(1-t/(2pi))":         (lambda t: K * (1.0 - t / (2 * PI)), K),
    "step K on [0,1) then 0.1":     (lambda t: np.where(np.asarray(t) < 1.0, K, 0.1), K),
}

def solve(profile, T, rtol=1e-13, atol=1e-15, events=False, max_step=1e-3):
    def rhs(t, y):
        return [y[1], -profile(t) * y[0]]
    ev = None
    if events:
        ev = lambda t, y: y[0]
        ev.direction = -1
        ev.terminal = True
    return solve_ivp(rhs, (A, T), [0.0, 1.0], method="DOP853",
                     rtol=rtol, atol=atol, max_step=max_step,
                     dense_output=True, events=ev)

# ------------------------------------------- 1. no zero on span < pi/sqrt(K)
print("\n=== 1. u(T) on spans slightly below pi/sqrt(K) (must be > 0) ===")
fails = []
for delta in (1e-6, 1e-9):
    T = T_MODEL - delta
    for name, (prof, kmin) in profiles.items():
        # sanity: k <= K on [0,T]
        ts = np.linspace(A, T, 20001)
        assert np.all(np.asarray(prof(ts)) <= K + 1e-15), name
        sol = solve(prof, T)
        assert sol.success, (name, sol.message)
        uT = sol.y[0, -1]
        # dense-grid minimum (detects an interior zero even if u(T) > 0 due to two crossings)
        tt = np.linspace(A, T, 200001)
        uu = sol.sol(tt)[0]
        umin = uu.min()
        ok = (uT > 0) and (umin > -1e-12)
        if not ok:
            fails.append((name, delta, uT, umin))
        print(f"  delta={delta:.0e}  {name:34s}  u(T)={uT: .12e}  min u={umin: .6e}  "
              f"{'OK' if ok else 'ZERO FOUND'}")

# ------------------- 2. actual first zero: ratio to pi/sqrt(K) (must be >= 1)
print("\n=== 2. numerical first zero vs pi/sqrt(K) (ratio must be >= 1) ===")
for name, (prof, kmin) in profiles.items():
    sol = solve(prof, 2 * PI, events=True, max_step=1e-4)
    if sol.t_events[0].size == 0:
        print(f"  {name:34s}  no zero in (0,2pi)")
        continue
    z = float(sol.t_events[0][0])
    ratio = z / T_MODEL
    exact = PI / np.sqrt(kmin) / T_MODEL if kmin > 0 else float("nan")
    flag = "OK" if ratio >= 1.0 - 1e-9 else "COUNTEREXAMPLE?"
    if ratio < 1.0 - 1e-9:
        fails.append(("first-zero", name, z, ratio))
    extra = f"  (const-model ratio {exact:.12f})" if "const" in name else ""
    print(f"  {name:34s}  first zero={z:.12f}  ratio={ratio:.12f}  {flag}{extra}")

# --------------------------------- 3. proportionality when k == K on (a,c)
print("\n=== 3. proportionality: k == K on (0,c], c=2.0 (< pi) ===")
c = 2.0
for v0 in (1.0, 3.0, -2.0, 0.5):
    sol = solve(lambda t: K, c)
    # rescale solution for u'(0)=v0 (linearity)
    tt = np.linspace(0.0, c, 20001)
    u = v0 * sol.sol(tt)[0]
    m = np.sin(np.sqrt(K) * tt)
    lam = v0 / np.sqrt(K)
    dev = np.max(np.abs(u - lam * m))
    rel = dev / max(1.0, np.max(np.abs(u)))
    print(f"  u'(0)={v0:+.2f}: max|u - lam*sin| = {dev:.3e} (rel {rel:.3e}), lam={lam:+.12f}")

# control: k != K on part of the interval -> u is NOT proportional to sin
print("  control k = K-0.3 (not proportional):")
sol = solve(lambda t: K - 0.3, c)
tt = np.linspace(1e-9, c, 20001)
u = sol.sol(tt)[0]
m = np.sin(np.sqrt(K) * tt)
ratio_series = u / m
print(f"    u/m ranges over [{ratio_series.min():.12f}, {ratio_series.max():.12f}] "
      f"(max spread {ratio_series.max()-ratio_series.min():.3e})")

# --------------------- 4. Wronskian W = u*m' - m*u' when k == K on the interval
print("\n=== 4. Wronskian W = u*cos - sin*u' for k == K on (0,c], c=2.0 ===")
sol = solve(lambda t: K, c)
tt = np.linspace(0.0, c, 20001)
yy = sol.sol(tt)
u, du = yy[0], yy[1]
m = np.sin(np.sqrt(K) * tt)
md = np.sqrt(K) * np.cos(np.sqrt(K) * tt)
W = u * md - m * du
print(f"  max|W| = {np.max(np.abs(W)):.3e}")
print("  control k = K-0.3 (W need not vanish):")
sol2 = solve(lambda t: K - 0.3, c)
W2 = sol2.sol(tt)[0] * md - m * sol2.sol(tt)[1]
print(f"  max|W| = {np.max(np.abs(W2)):.3e}")

print("\n=== 5. direction control: k == K+1.1 (excess must force zero before pi/sqrt K) ===")
sol = solve(lambda t: K + 1.1, 2*PI, events=True)
z = float(sol.t_events[0][0])
print(f"  first zero={z:.12f}  ratio={z/T_MODEL:.12f} (<1 expected)")

print("\nFAILURES:", fails if fails else "none")
