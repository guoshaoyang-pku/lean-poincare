import itertools, sympy as sp
from sympy import symbols, Symbol, expand, simplify
n=3
Gfree={}
for i in range(n):
    for j in range(n):
        for l in range(n):
            if j<l: Gfree[(i,j,l)]=Symbol(f"G{i}{j}{l}",commutative=True)
def G(i,j,l):
    if j==l: return 0
    if j<l: return Gfree[(i,j,l)]
    return -Gfree[(i,l,j)]
def c(i,j,l): return G(i,j,l)-G(j,i,l)
U=[Symbol(f"U{j}",commutative=True) for j in range(n)]
DU={(i,j):Symbol(f"DU{i}{j}",commutative=True) for i in range(n) for j in range(n)}
DDUs={(j,i,k):Symbol(f"DDUs{j}{i}{k}",commutative=True) for i in range(n) for j in range(n) for k in range(n)}
def H(i,j): return DU[(i,j)]-sum(G(i,j,l)*U[l] for l in range(n))
def gradX_gu(X,j): return DU[(X,j)]+sum(G(X,k,j)*U[k] for k in range(n))
def gradX_gradX_gu(X,j):
    Dx_inner=DDUs[(X,X,j)]+sum(G(X,k,j)*DU[(X,k)] for k in range(n))
    return Dx_inner+sum(G(X,k,j)*gradX_gu(X,k) for k in range(n))
def LapVecGu(j): return sum(gradX_gradX_gu(X,j)-sum(G(X,X,l)*gradX_gu(l,j) for l in range(n)) for X in range(n))
inner_gu_LapVec=sum(U[j]*LapVecGu(j) for j in range(n))
inner_gu_gLap=sum(U[j]*sum(DDUs[(j,k,k)]-sum(G(k,k,l)*DU[(j,l)] for l in range(n)) for k in range(n)) for j in range(n))
W=expand(inner_gu_LapVec-inner_gu_gLap)
W1 = sum(U[j]*(DDUs[(i,i,j)]-sum(G(i,j,l)*DU[(i,l)] for l in range(n))
               +sum(G(i,k,j)*H(i,k) for k in range(n))
               -sum(G(i,i,l)*H(l,j) for l in range(n))) for i in range(n) for j in range(n)) \
   - sum(U[j]*(DDUs[(j,i,i)]-sum(G(i,i,l)*DU[(j,l)] for l in range(n))) for i in range(n) for j in range(n))
red2 = {DDUs[(i,i,j)]: DDUs[(j,i,i)] + sum(c(i,j,m)*(DU[(m,i)]+DU[(i,m)]) for m in range(n)) for i in range(n) for j in range(n)}
W2=expand(W1.subs(red2))
red3 = {H(i,k): DU[(i,k)]-sum(G(i,k,p)*U[p] for p in range(n)) for i in range(n) for k in range(n)}
W3=expand(W2.subs(red3))
red4 = {DU[(m,i)]: DU[(i,m)] + sum(c(m,i,p)*U[p] for p in range(n)) for m in range(n) for i in range(n)}
W4=expand(W3.subs(red4))
# verify no DU terms remain
assert all(not (DU[(a,b)] in t.free_symbols) for t in W4.as_ordered_terms() for a in range(n) for b in range(n))
# extract A(i,j,m,p) by tracking: substitute U[q] -> t_q (symbols), G's keep index names.
# then the coefficient of t_j t_p gives sum_{i,m} A(i,j,m,p).
tj=[Symbol(f"t{j}",commutative=True) for j in range(n)]
W4t=expand(W4.subs({U[j]:tj[j] for j in range(n)}))
# coefficient of t1*t2 (as polynomial in t0,t1,t2)
coef = sp.Poly(W4t, *tj).coeff_monomial(tj[1]*tj[2])
print("coeff of t1*t2 (= sum_{i,m} A(i,1,m,2)):")
print(sp.factor(coef))
# Now split per (i,m): use G subscript patterns. Do it by substituting U->0 except tracking via derivative trick:
# A(i,j,m,p) = coefficient of t_j t_p in the summand with the given (i,m). Identify (i,m) by G's third/first index.
# We can reconstruct per-(i,m) by evaluating the expression restricted to fixed i,m in the defs:
def A(i,j,m,p):
    # from the derivation: A = 2*c(i,j,m)*c(m,i,p) - G(i,j,m)*c(m,i,p) + G(i,m,j)*c(m,i,p)
    #   + 2*G(i,i,m)*c(j,m,p) + G(i,i,m)*G(m,j,p) - G(i,m,j)*G(i,m,p)
    return 2*c(i,j,m)*c(m,i,p) - G(i,j,m)*c(m,i,p) + G(i,m,j)*c(m,i,p) + 2*G(i,i,m)*c(j,m,p) + G(i,i,m)*G(m,j,p) - G(i,m,j)*G(i,m,p)
ok=True
for j in range(n):
    for p in range(n):
        lhs=sum(A(i,j,m,p) for i in range(n) for m in range(n))
        cjp = sp.Poly(W4t, *tj).coeff_monomial(tj[j]*tj[p])
        if sp.simplify(expand(lhs-cjp))!=0:
            ok=False
            print("MISMATCH", j, p, sp.simplify(expand(lhs-cjp)))
print("A formula matches W4:", ok)
# verify total: sum_{i,j,m,p} U_j U_p A(i,j,m,p) == W4
W4A = sum(U[j]*U[p]*A(i,j,m,p) for i in range(n) for j in range(n) for m in range(n) for p in range(n))
print("A reproduces W4:", sp.simplify(expand(W4-W4A))==0)

