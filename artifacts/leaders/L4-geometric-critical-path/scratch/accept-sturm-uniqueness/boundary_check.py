#!/usr/bin/env python3
"""
Addendum boundary spot-check for the strengthened
`no_zero_of_curvature_le_of_deriv_ne` (hspan now <= pi, conclusion on the OPEN interval).

K=1, a=0, b=pi exactly (sqrt(K)(b-a) = pi, the new boundary case).
For k == K the model zero sits AT b, so the statement must still report no zero in (0,b).
For k < K the first zero is strictly beyond b.
DOP853, rtol=1e-13, atol=1e-15.
"""
import numpy as np
from scipy.integrate import solve_ivp

K, A, PI = 1.0, 0.0, np.pi

def integrate(prof, T, events=False, max_step=1e-4):
    ev = None
    if events:
        ev = lambda t, y: y[0]
        ev.direction = -1
        ev.terminal = True
    return solve_ivp(lambda t, y: [y[1], -prof(t) * y[0]], (A, T), [0.0, 1.0],
                     method="DOP853", rtol=1e-13, atol=1e-15, max_step=max_step,
                     dense_output=True, events=ev)

profiles = {
    "const k=K=1":                lambda t: K,
    "const k=K-1e-8":             lambda t: K - 1e-8,
    "const k=0.5":                lambda t: 0.5,
    "gauss eps=0.3 m=1.0 w=0.2":  lambda t: K - 0.3 * np.exp(-((np.asarray(t) - 1.0) / 0.2) ** 2),
    "osc eps=0.3 f=13":           lambda t: K - 0.3 * (1 + np.sin(13 * np.asarray(t))) / 2,
    "step 1 -> 0.1 at pi/2":      lambda t: np.where(np.asarray(t) < PI / 2, K, 0.1),
}

print(f"boundary: a={A}  b=pi={PI!r}  sqrt(K)(b-a)={PI!r}  (new hspan is <=)")
tt = np.linspace(A, PI, 400001)
interior = (tt > 1e-9) & (tt <= PI - 1e-6)   # exclude t=a (u=0) and the endpoint itself
for name, prof in profiles.items():
    assert np.all(np.asarray(prof(tt)) <= K + 1e-15), name
    sol = integrate(prof, PI)
    uu = sol.sol(tt)[0]
    umin_int = float(uu[interior].min())
    uend = float(sol.sol(PI)[0])
    # first zero over a longer window
    sole = integrate(prof, 2 * PI, events=True)
    if sole.t_events[0].size:
        z = float(sole.t_events[0][0])
        zd = z - PI
    else:
        z, zd = float("nan"), float("nan")
    ok = umin_int > 0
    print(f"  {name:28s} min u on (0,pi-1e-6]={umin_int: .6e}  u(pi)={uend: .3e}  "
          f"first zero={z:.12f}  z-pi={zd:+.3e}  {'OK (no interior zero)' if ok else 'INTERIOR ZERO'}")
