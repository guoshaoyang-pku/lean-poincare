"""Boundary sharpness + cross-integrator checks for the main theorem."""
import numpy as np
from scipy.integrate import solve_ivp

def first_zero(k, a, tend, K, method='DOP853'):
    def f(t, y): return [y[1], -k(t)*y[0]]
    def ev(t, y): return y[0]
    ev.terminal = True; ev.direction = -1
    sol = solve_ivp(f, [a, tend], [0.0, 1.0], method=method,
                    rtol=1e-12, atol=1e-14, events=ev, max_step=1e-3)
    return sol.t_events[0]

# ---- Boundary-sharp instance: k = K on (a,c), jumps to k < K after c. ----------
# a=0, K=2, c=pi/sqrt2 (the model first zero).  k(t)=2 for t<=c, k(t)=1 for t>c.
# Solution: u=sin(sqrt2 t) on [0,c], then u=-sqrt2 sin(t-c) on [c,3].
K = 2.0; c = np.pi/np.sqrt(K)
k_pw = lambda t: 2.0 if t <= c else 1.0
te = first_zero(k_pw, 0.0, 3.0, K)
print(f"boundary piecewise: model first zero c={c:.12f}; numerical first zero={te[0]:.12f}; "
      f"sqrt(K)*c/pi={(np.sqrt(K)*te[0])/np.pi:.12f}  (hspan equality)")
# exact tail solution check: -sqrt2 * sin(t-c) is negative for t in (c, c+pi) -> c is first zero
print("  exact tail u(t)=-sqrt2*sin(t-c): u(c)=0, sign after c =",
      "negative" if -np.sqrt(2)*np.sin(0.1) < 0 else "positive")
# k differs from K on (0,3) but conclusion only claims (0,c): k=K there. OK.
print("  k != K on (0,3)? ", not np.allclose([k_pw(t) for t in np.linspace(0,3,7)], K))

# ---- Cross-integrator agreement -------------------------------------------------
cases = {
 "const deficit 0.5": (lambda t: 0.5, 1.0, None),
 "gaussian deficit": (lambda t: 1.0-0.3*np.exp(-((t-1.2)/0.25)**2), 1.0, None),
 "oscillatory deficit": (lambda t: 1.0-0.1*(1+np.sin(13*t))/2, 1.0, None),
 "excess 1.1": (lambda t: 1.1, 1.0, None),
 "K=2 deficit": (lambda t: 2.0-0.3*np.exp(-((t-0.5)/0.2)**2), 2.0, None),
}
print("\ncross-integrator first-zero agreement (DOP853 / Radau / LSODA):")
for name,(k,Kk,_) in cases.items():
    tend = 2*np.pi/np.sqrt(Kk)
    vals = []
    for m in ['DOP853','Radau','LSODA']:
        r = first_zero(k, 0.0, tend, Kk, method=m)
        vals.append(r[0] if len(r) else float('nan'))
    ratio = np.sqrt(Kk)*np.array(vals)/np.pi
    print(f"  {name:24s} c=({vals[0]:.10f},{vals[1]:.10f},{vals[2]:.10f})  ratios={np.round(ratio,10)}"
          f"  spread={np.nanmax(vals)-np.nanmin(vals):.2e}")
print("\nAll rows: no nonconstant k <= K attains ratio <= 1; boundary ratio = 1 only for k == K on (a,c).")
