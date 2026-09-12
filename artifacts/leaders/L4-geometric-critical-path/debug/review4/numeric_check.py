import numpy as np
from numpy import sqrt, sinh, cosh, sin, pi, tanh

print("== numerical facts ==")
print("sinh(1/4) =", sinh(0.25), "<= 3 :", sinh(0.25) <= 3)
print("sinh(1)   =", sinh(1.0), "<= 3 :", sinh(1.0) <= 3)
print("j_{-2}(1/4) = sinh(sqrt2/4)/sqrt2 =", sinh(sqrt(2)/4)/sqrt(2), "<= 3 :", sinh(sqrt(2)/4)/sqrt(2) <= 3)
print("j_{-1}(1/4) = sinh(1/4) =", sinh(0.25), "<= 3 :", sinh(0.25) <= 3)

print("\n== direction check: log-deriv monotone increasing in |k| for k<=0 ==")
# j_k'/j_k = sqrt(-k) coth(sqrt(-k) t) for k<0 ; = 1/t for k=0
def logderiv(k, t):
    if k == 0: return 1.0/t
    a = sqrt(-k)
    return a/np.tanh(a*t)

bad = []
for K in [-0.0, -0.1, -0.5, -1.0, -2.0, -5.0]:
    for k in [K-0.1, K-0.5, K-1.0, K-2.0, -10.0]:
        if k > K: continue
        for t in [0.001, 0.01, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0, 5.0]:
            lhs = logderiv(K, t); rhs = logderiv(k, t)
            if not (lhs <= rhs + 1e-12):
                bad.append((k, K, t, lhs, rhs))
print("violations of  j_K'/j_K <= j_k'/j_k  for k <= K <= 0:", bad[:5], "count", len(bad))

bad2 = []
for K in [-0.0, -0.1, -0.5, -1.0, -2.0, -5.0]:
    for k in [K-0.1, K-0.5, K-1.0, K-2.0, -10.0]:
        if k > K: continue
        for t in [0.001, 0.01, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0, 5.0]:
            # model function j_K vs j_k
            def jsol(kk, tt):
                if kk == 0: return tt
                a = sqrt(-kk); return sinh(a*tt)/a
            if not (jsol(K,t) <= jsol(k,t) + 1e-12):
                bad2.append((k, K, t, jsol(K,t), jsol(k,t)))
print("violations of  j_K <= j_k  for k <= K <= 0:", bad2[:5], "count", len(bad2))

print("\n== ODE counterexample search for rauch_lower_of_jacobi_constCurv ==")
# Unknown solution u'' + k(t) u = 0, u(0)=0, u'(0)=1, k(t) <= K <= 0.
# Integrate with RK4 from t=0 using series start, then compare u'/u to model.

def integrate(kfun, T, n=200000):
    h = T/n
    # state (u, du, ddu) with u(0)=0, du(0)=1, ddu(0) = -k(0)*u(0) = 0
    u, du = 0.0, 1.0
    # start at t=h using Taylor: u(h) = h - k(0) h^3/6 + ..., du(h) = 1 - k(0)h^2/2
    t = h
    u = h - kfun(0.0)*h**3/6
    du = 1 - kfun(0.0)*h**2/2
    def f(t, y):
        u, du = y
        return np.array([du, -kfun(t)*u])
    ys = [(t, u, du)]
    while t < T - 1e-15:
        hh = min(h, T-t)
        y = np.array([u, du])
        k1 = f(t, y); k2 = f(t+hh/2, y+hh/2*k1); k3 = f(t+hh/2, y+hh/2*k2); k4 = f(t+hh, y+hh*k3)
        y = y + hh/6*(k1+2*k2+2*k3+k4)
        t += hh
        u, du = y
        ys.append((t, u, du))
    return ys

def model_logderiv(K, t):
    if K == 0: return 1/t
    a = sqrt(-K); return a/np.tanh(a*t)

np.random.seed(0)
worst = -1e9; worstcase = None
trials = 0
cases = []
for K in [0.0, -0.25, -1.0, -3.0]:
    for amp in [0.0, 0.5, 1.0, 2.0]:
        for om in [1.0, 3.0, 7.0]:
            # k(t) = K - amp*(1+sin(om t))/... ensure k <= K and smooth
            kf = lambda t, K=K, amp=amp, om=om: K - amp*(1 - np.cos(om*t))/2 - amp*0.0
            # ensure k(0) <= K
            T = 2.0
            ys = integrate(kf, T, n=20000)
            for (t,u,du) in ys[::max(1,len(ys)//50)]:
                if t <= 1e-9: continue
                if u <= 0: continue
                lhs = model_logderiv(K, t)
                rhs = du/u
                d = lhs - rhs
                trials += 1
                if d > worst:
                    worst = d; worstcase = (K, amp, om, t, lhs, rhs, kf(t))
                if d > 1e-9:
                    cases.append((K, amp, om, t, lhs, rhs, kf(t)))
print("trials:", trials, " worst (model - actual):", worst, worstcase)
print("violations:", cases[:5], "count", len(cases))

# Also check the integrated form j_K <= u
worst2 = -1e9; wc2 = None; cases2=[]
for K in [0.0, -0.25, -1.0, -3.0]:
    for amp in [0.0, 0.5, 1.0, 2.0]:
        for om in [1.0, 3.0, 7.0]:
            kf = lambda t, K=K, amp=amp, om=om: K - amp*(1 - np.cos(om*t))/2
            T = 2.0
            ys = integrate(kf, T, n=20000)
            for (t,u,du) in ys[::max(1,len(ys)//50)]:
                if t <= 1e-9: continue
                def jsol(kk, tt):
                    if kk == 0: return tt
                    a = sqrt(-kk); return sinh(a*tt)/a
                d = jsol(K,t) - u
                if d > worst2: worst2 = d; wc2=(K,amp,om,t,jsol(K,t),u)
                if d > 1e-9: cases2.append((K,amp,om,t,jsol(K,t),u))
print("integrated: worst (model - u):", worst2, wc2)
print("integrated violations:", cases2[:5], "count", len(cases2))

print("\n== conjugate point bound sanity ==")
# for k >= K > 0, positive solution cannot pass pi/sqrt(K)
print("pi/sqrt(1) =", pi, " pi/sqrt(2) =", pi/sqrt(2))
print("witness T=3/2 <= pi:", 1.5 <= pi)
print("j_2(3/2)=sin(3/sqrt2*sqrt2)/sqrt2 =", sin(sqrt(2)*1.5)/sqrt(2), ">0:", sin(sqrt(2)*1.5)/sqrt(2)>0)
print("T=3 with K=1,k=1,u=j_1: j_1(3)=sin(3)=", sin(3.0), ">0:", sin(3.0)>0)
