import math
from fractions import Fraction as F

# j_K(t) = sin(sqrt(K) t)/sqrt(K) for K>0, t for K=0 ; j'' = -K j
def jpp(K,t):
    if K==0: return 0.0
    return -math.sqrt(K)*math.sin(math.sqrt(K)*t)

print("=== A4: sup |j_K''| vs claimed bound K*max(1/sqrt(K),T) on (0,T)")
worst=0.0
for K in [0.0,1e-6,1e-3,0.01,0.25,1.0,2.0,4.0,10.0,100.0,1e4]:
    for T in [1e-3,0.01,0.1,0.5,1.0,3.0,10.0]:
        bound = 0.0 if K==0 else K*max(1/math.sqrt(K),T)
        sup = 0.0
        if T>0:
            # analytic sup on (0,T): if sqrt(K)*T <= pi/2 -> sqrt(K)*sin(sqrt(K)T); else sqrt(K)
            if K==0: sup=0.0
            else:
                s=math.sqrt(K)
                sup = s*math.sin(min(s*T, math.pi/2))
        ratio = (sup/bound) if bound>0 else (0.0 if sup==0 else float('inf'))
        worst=max(worst,ratio)
        if ratio>1+1e-12:
            print("  VIOLATION",K,T,sup,bound)
print("  max ratio sup/bound over grid =",worst)

print("=== A5: witness inequality j_2'/j_2 <= j_1'/j_1 on (0,1): f(t)=cot t - sqrt2*cot(sqrt2 t)")
mn=None; arg=None
N=2000000
for i in range(1,N+1):
    t=1.0*i/N
    d=1/math.tan(t) - math.sqrt(2)/math.tan(math.sqrt(2)*t)
    if mn is None or d<mn: mn=d; arg=t
print("  min f =",mn,"at t =",arg, " (strictly positive => genuine strict inequality; equality only at t->0)")
print("  f(1/4) =",1/math.tan(0.25)-math.sqrt(2)/math.tan(math.sqrt(2)*0.25))
print("  f(1/2) =",1/math.tan(0.5)-math.sqrt(2)/math.tan(math.sqrt(2)*0.5))

print("=== A3 quant hypotheses at the witness (exact rationals)")
B=F(2); t0=F(1,4); K=F(1); T=F(1)
print("  B*t0 =",B*t0,"<=1/2:",B*t0<=F(1,2))
print("  (K*max(1/sqrt K,T))*t0 : K*max(1,1)*t0 =",K*max(F(1),T)*t0,"<=1/2:",K*max(F(1),T)*t0<=F(1,2))
print("  t0<=T:",t0<=T)
print("  K=1>0, sqrt(1)*T=1 < pi:",1<math.pi)
print("  |j_2''| sup on (0,1) =",math.sqrt(2),"<= B=2:",math.sqrt(2)<=2)
