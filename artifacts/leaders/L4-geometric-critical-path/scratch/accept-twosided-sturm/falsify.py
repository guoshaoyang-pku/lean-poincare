"""Independent numerical falsification attempt for
   eq_curvature_of_first_jacobi_zero_of_curvature_le.

Claim under test: k <= K on [a,c], u'' + k u = 0, u(a)=0, u>0 (or <0) on (a,c),
u(c)=0, sqrt(K)(c-a) <= pi  ==>  k == K on (a,c).

Falsification target: find smooth nonconstant k <= K with first zero c such that
sqrt(K)(c-a) <= pi while k != K somewhere in (a,c).
"""
import numpy as np
from scipy.integrate import solve_ivp

def first_zero(k, a, tend, K):
    def f(t, y): return [y[1], -k(t)*y[0]]
    def ev(t, y): return y[0]
    ev.terminal = True; ev.direction = -1
    sol = solve_ivp(f, [a, tend], [0.0, 1.0], method='DOP853',
                    rtol=1e-13, atol=1e-15, events=ev, max_step=2e-3)
    return sol.t_events[0]

def report(name, k, K, a=0.0, tend=None, known_equals=None):
    if tend is None: tend = a + 2*np.pi/np.sqrt(K)
    te = first_zero(k, a, tend, K)
    thresh = a + np.pi/np.sqrt(K)
    if len(te) == 0:
        print(f"{name}: NO ZERO in ({a},{tend:.4f})  [threshold {thresh:.6f}]")
        return None
    c = te[0]
    ratio = np.sqrt(K)*(c-a)/np.pi
    print(f"{name}: first zero c={c:.12f}, sqrt(K)(c-a)/pi={ratio:.12f}, "
          f"c-thresh={c-thresh:+.3e}, k(a+c/2)={k((a+c)/2):.6f}")
    return c

K = 1.0
# 1. sanity: k == K  -> first zero exactly pi
report("k=K=1 (exact equality)", lambda t: 1.0, K)

# 2. constant deficit  k = 1/2 < K=1 -> first zero pi/sqrt(1/2) > pi
report("k=0.5 const (deficit)", lambda t: 0.5, K)

# 3. strict excess k = 1.1 > K -> first zero < pi (direction sanity check)
report("k=1.1 const (excess)", lambda t: 1.1, K)

# 4. localized smooth deficits (Gaussian bumps) with random params
rng = np.random.default_rng(20260212)
worst = None
for trial in range(40):
    nb = rng.integers(1, 4)
    ms = rng.uniform(0.3, 2.8, nb)
    ws = rng.uniform(0.05, 0.7, nb)
    es = rng.uniform(0.01, 0.6, nb)
    k = lambda t, ms=ms, ws=ws, es=es: max(0.05, 1.0 - np.sum(es*np.exp(-((t-ms)/ws)**2)))
    c = report(f"bump trial {trial} (n={nb}, eps={np.round(es,3)})", k, K)
    if c is not None:
        r = np.sqrt(K)*c/np.pi
        if worst is None or r < worst[0]: worst = (r, trial, c, es.copy(), ms.copy(), ws.copy())
print("closest-to-threshold deficit case:", worst)

# 5. hard adversarial: extremely small/narrow deficit, expect c -> pi from above
for eps, w in [(1e-2, 0.05), (1e-3, 0.02), (1e-4, 0.01), (1e-6, 0.005), (1e-8, 0.002)]:
    m = 1.0
    k = lambda t, eps=eps, w=w, m=m: 1.0 - eps*np.exp(-((t-m)/w)**2)
    c = report(f"tiny gaussian deficit eps={eps:g}, w={w:g}", k, K)

# 6. K=2, nonconstant k <= 2, a=0, first zero must exceed pi/sqrt(2) if k != 2
K2 = 2.0
k6 = lambda t: 2.0 - 0.3*np.exp(-((t-0.5)/0.2)**2)
report("K=2, Gaussian deficit", k6, K2)

# 7. oscillatory deficit
k7 = lambda t: 1.0 - 0.2*(1+np.sin(13*t))/2
report("oscillatory deficit k=1-0.1(1+sin13t)", k7, K)

print("\nINTERPRETATION: any row with k != K and sqrt(K)(c-a)/pi <= 1 is a counterexample.")
