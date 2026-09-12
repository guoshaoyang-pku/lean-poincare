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

# Freeze the (i,m)-indices: build the W chain for FIXED i (Laplacian index) and fixed m (c-sum index).
def build_fixed(i0, m0):
    # W1 term for fixed i0, all j: U_j * [D_{i0}D_{i0}u_j - sum_l G(i0,j,l)D_{i0}u_l + sum_k G(i0,k,j)H(i0,k) - sum_l G(i0,i0,l)H(l,j)]
    #   - U_j * [D_jD_{i0}u_{i0} - sum_l G(i0,i0,l) D_j u_l]
    def Hx(i,j): return DU[(i,j)]-sum(G(i,j,l)*U[l] for l in range(n))
    def DDUred(j): 
        # D_{i0}D_{i0}u_j = D_jD_{i0}u_{i0} + c(i0,j,m0)*(D_{m0}u_{i0} + D_{i0}u_{m0})
        return DDUs[(j,i0,i0)] + c(i0,j,m0)*(DU[(m0,i0)]+DU[(i0,m0)])
    def Hx_red(i,k): return DU[(i,k)]-sum(G(i,k,p)*U[p] for p in range(n))
    W1 = sum(U[j]*(DDUred(j)-sum(G(i0,j,l)*DU[(i0,l)] for l in range(n))
                   +sum(G(i0,k,j)*Hx_red(i0,k) for k in range(n))
                   -sum(G(i0,i0,l)*Hx_red(l,j) for l in range(n))) for j in range(n)) \
       - sum(U[j]*(DDUs[(j,i0,i0)]-sum(G(i0,i0,l)*DU[(j,l)] for l in range(n))) for j in range(n))
    W2 = expand(W1)
    red4 = {DU[(m,i)]: DU[(i,m)] + sum(c(m,i,p)*U[p] for p in range(n)) for m in range(n) for i in range(n)}
    W3 = expand(W2.subs(red4))
    # DU terms should cancel; keep UU part
    W4 = expand(W3.subs({DU[(a,b)]:0 for a in range(n) for b in range(n)}))
    return W4

# A(i0,j,m0,p) = coefficient of U[j] U[p] in build_fixed(i0,m0) (with U symbols as generators)
results={}
for i0 in range(n):
    for m0 in range(n):
        W=build_fixed(i0,m0)
        for j in range(n):
            for p in range(n):
                a=sp.Poly(W,*U).coeff_monomial(U[j]*U[p])
                results[(i0,j,m0,p)]=a
# print the nonzero A's with structure
for key,val in sorted(results.items()):
    if sp.simplify(val)!=0:
        print(key, "->", sp.factor(expand(val)))
# verify: total sum reproduces W4
W4A = sum(U[j]*U[p]*results[(i,j,m,p)] for i in range(n) for j in range(n) for m in range(n) for p in range(n))
# rebuild the full W4 for comparison
def full_chain():
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
    return expand(W3.subs(red4))
W4=full_chain()
print("A formula reproduces W4:", sp.simplify(expand(W4-W4A))==0)
