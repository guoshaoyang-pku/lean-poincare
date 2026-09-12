#!/usr/bin/env python3
"""
Stronger adversarial numeric pass for SturmUniqueness.lean.

(a) Randomized search over many nonconstant profiles k <= K for an interior zero of
    u'' + k u = 0, u(a)=0, u'(a)=1, on (a, pi/sqrt(K) - delta].
(b) High-precision (mpmath, 60 dps) check of the near-equality constant case
    k = K - 1e-8, whose exact first zero is pi/sqrt(K-1e-8).
(c) Boundary proportionality check at k == K on (a,c) with c = pi/sqrt(K) exactly.
"""
import numpy as np
import mpmath as mp
from scipy.integrate import solve_ivp

K = 1.0
A = 0.0
PI = np.pi
T_MODEL = PI / np.sqrt(K)
rng = np.random.default_rng(20260912)

def rhs_factory(prof):
    return lambda t, y: [y[1], -prof(t) * y[0]]

def integrate(prof, T, events=False, max_step=2e-3, rtol=1e-13, atol=1e-15):
    ev = None
    if events:
        ev = lambda t, y: y[0]
        ev.direction = -1
        ev.terminal = True
    return solve_ivp(rhs_factory(prof), (A, T), [0.0, 1.0], method="DOP853",
                     rtol=rtol, atol=atol, max_step=max_step, dense_output=True, events=ev)

# (a) randomized search ------------------------------------------------------
print("=== (a) randomized search, T = pi/sqrt(K) - 1e-9 ===")
T = T_MODEL - 1e-9
tt = np.linspace(A, T, 400001)[1:]          # drop t=a where u=0 by construction
worst = (np.inf, None)
nzero = 0
N = 300
for trial in range(N):
    kind = trial % 3
    nb = 1 + rng.integers(0, 4)
    if kind == 0:                            # Gaussian dips
        ms = rng.uniform(0.2, T - 0.1, nb)
        ws = rng.uniform(0.01, 0.6, nb)
        es = 10 ** rng.uniform(-8, -0.05, nb)
        prof = lambda t, ms=ms, ws=ws, es=es: K - sum(
            e * np.exp(-((np.asarray(t) - m) / w) ** 2) for m, w, e in zip(ms, ws, es))
    elif kind == 1:                          # oscillatory dips
        eps = 10 ** rng.uniform(-8, -0.05)
        freq = rng.uniform(1.0, 25.0)
        ph = rng.uniform(0, 2 * PI)
        prof = lambda t, eps=eps, freq=freq, ph=ph: K - eps * (1 + np.sin(freq * np.asarray(t) + ph)) / 2
    else:                                    # monotone/linear deficit
        frac = 10 ** rng.uniform(-8, -0.05)
        prof = lambda t, frac=frac: K - frac * (np.asarray(t) / T)
    ts = np.linspace(A, T, 2001)
    assert np.all(np.asarray(prof(ts)) <= K + 1e-14), trial
    sol = integrate(prof, T)
    assert sol.success, (trial, sol.message)
    uu = sol.sol(tt)[0]
    umin = float(uu.min())
    if umin < worst[0]:
        worst = (umin, trial)
    if umin <= 0:
        nzero += 1
        print(f"  ZERO CANDIDATE trial={trial} kind={kind} umin={umin:.3e}")
print(f"  {N} random profiles: interior min u over (0,T] = {worst[0]:.6e} (trial {worst[1]}), "
      f"candidates with a zero: {nzero}")

# explicit near-equality profiles, fixed delta
print("\n=== (a') explicit near-equality profiles on (0, pi - delta] ===")
for delta in (1e-6, 1e-9):
    Td = T_MODEL - delta
    ttd = np.linspace(A, Td, 400001)[1:]
    cases = {
        "const 1-1e-8": lambda t: K - 1e-8,
        "gauss 1e-8 w=0.01 @pi/2": lambda t: K - 1e-8 * np.exp(-((np.asarray(t) - PI/2)/0.01)**2),
        "gauss 1e-8 w=0.5  @pi/2": lambda t: K - 1e-8 * np.exp(-((np.asarray(t) - PI/2)/0.5)**2),
        "osc 1e-8 f=20": lambda t: K - 1e-8 * (1 + np.sin(20*np.asarray(t)))/2,
        "tent 1e-8 @2.0 w=0.1": lambda t: K - 1e-8 * np.maximum(0, 1 - np.abs(np.asarray(t)-2.0)/0.1),
    }
    for name, prof in cases.items():
        sol = integrate(prof, Td)
        umin = float(sol.sol(ttd)[0].min())
        print(f"  delta={delta:.0e}  {name:28s} min u={umin: .12e}  "
              f"{'OK' if umin > 0 else 'ZERO'}")

# (b) high-precision exact check of constant near-equality -------------------
print("\n=== (b) mpmath 60-dps exact check, k = K - eps ===")
mp.mp.dps = 60
for eps in ("1e-8", "1e-6", "1e-10"):
    e = mp.mpf(eps)
    w = mp.sqrt(mp.mpf(K) - e)
    z = mp.pi / w                                  # exact first zero
    for delta in ("1e-6", "1e-9", "1e-12"):
        d = mp.mpf(delta)
        Td = mp.pi / mp.sqrt(mp.mpf(K)) - d
        val = mp.sin(w * Td)
        print(f"  eps={eps:>6} delta={delta:>6}: u(T)={mp.nstr(val, 20)}  "
              f"exact first zero={mp.nstr(z, 20)}  ratio={mp.nstr(z/(mp.pi/mp.sqrt(mp.mpf(K))), 20)}")

# (c) proportionality at the boundary c = pi/sqrt(K) -------------------------
print("\n=== (c) proportionality with k==K on (0,pi) exactly (model zero at c) ===")
c = T_MODEL
for v0 in (1.0, -1.3):
    sol = integrate(lambda t: K, c)
    ts = np.linspace(0, c, 100001)
    u = v0 * sol.sol(ts)[0]
    m = np.sin(np.sqrt(K) * ts)
    lam = v0 / np.sqrt(K)
    # avoid the endpoint where m=0 for the relative measure
    sl = slice(0, -10)
    dev = np.max(np.abs(u[sl] - lam * m[sl]))
    print(f"  u'(0)={v0:+.2f}: max|u - lam sin| on [0,c) = {dev:.3e}; lam={lam:+.12f}; "
          f"u(c)={u[-1]:.3e} (model m(c)={m[-1]:.3e})")
