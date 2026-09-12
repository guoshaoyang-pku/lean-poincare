import itertools, sympy as sp
from sympy import Symbol, expand, simplify
n = 3
Gfree = {(i,j,l): Symbol(f"G{i}{j}{l}", commutative=True) for i in range(n) for j in range(n) for l in range(n) if j < l}
def G(i,j,l):
    if j==l: return 0
    if j<l: return Gfree[(i,j,l)]
    return -Gfree[(i,l,j)]
def c(i,j,l): return G(i,j,l)-G(j,i,l)

def K(j,a,b):
    r = -G(j,a,b) + G(a,b,j) - c(j,b,a)
    if j == a: r = r + sum(G(i,i,b) for i in range(n))
    if j == b: r = r - sum(G(i,i,a) for i in range(n))
    return r

def LHS(j,p):
    return expand(sum(K(j,a,b)*G(a,b,p) for a in range(n) for b in range(n))
                  + sum(-G(i,k,j)*G(i,k,p) + G(i,i,k)*G(k,j,p) for i in range(n) for k in range(n)))

def RHS(j,p):
    return expand(
        sum(G(j,p,m)*G(i,m,i) for i in range(n) for m in range(n))
        - sum(G(i,p,m)*G(j,m,i) for i in range(n) for m in range(n))
        - sum((G(i,j,m)-G(j,i,m))*G(m,p,i) for i in range(n) for m in range(n)))

print("LHS == RHS (c expanded, K*gamma form):",
      all(simplify(LHS(j,p) - RHS(j,p)) == 0 for j in range(n) for p in range(n)))

res = expand(LHS(0,1) - RHS(0,1))
print("residual for (j,p)=(0,1):", simplify(res))
# split the LHS into its natural pieces and see how they pair with RHS pieces:
def piece(tag, j, p):
    if tag == "K1":   # -G(j,a,b)*G(a,b,p)
        return sum(-G(j,a,b)*G(a,b,p) for a in range(n) for b in range(n))
    if tag == "K2":   # +G(a,b,j)*G(a,b,p)
        return sum(G(a,b,j)*G(a,b,p) for a in range(n) for b in range(n))
    if tag == "K3":   # -c(j,b,a)*G(a,b,p)
        return sum(-(G(j,b,a)-G(b,j,a))*G(a,b,p) for a in range(n) for b in range(n))
    if tag == "K4":   # +sum_i G(i,i,b)*G(j,b,p)
        return sum(G(i,i,b)*G(j,b,p) for i in range(n) for b in range(n))
    if tag == "K5":   # -sum_i G(i,i,a)*G(a,j,p)
        return sum(-G(i,i,a)*G(a,j,p) for i in range(n) for a in range(n))
    if tag == "U1":   # -G(i,k,j)*G(i,k,p)
        return sum(-G(i,k,j)*G(i,k,p) for i in range(n) for k in range(n))
    if tag == "U2":   # +G(i,i,k)*G(k,j,p)
        return sum(G(i,i,k)*G(k,j,p) for i in range(n) for k in range(n))
    if tag == "R1":   # +G(j,p,m)*G(i,m,i)
        return sum(G(j,p,m)*G(i,m,i) for i in range(n) for m in range(n))
    if tag == "R2":   # -G(i,p,m)*G(j,m,i)
        return sum(-G(i,p,m)*G(j,m,i) for i in range(n) for m in range(n))
    if tag == "R3":   # -c(i,j,m)*G(m,p,i)
        return sum(-(G(i,j,m)-G(j,i,m))*G(m,p,i) for i in range(n) for m in range(n))

print("\nK5 + U2 =", simplify(piece("K5",0,1) + piece("U2",0,1)))
print("K2 =", simplify(piece("K2",0,1)), "  U1 =", simplify(piece("U1",0,1)))
print("K2 + U1 =", simplify(piece("K2",0,1) + piece("U1",0,1)))
print("K1 + K4 =", simplify(piece("K1",0,1) + piece("K4",0,1)))
print("R1 =", simplify(piece("R1",0,1)))
print("K3 =", simplify(piece("K3",0,1)), "  R3 =", simplify(piece("R3",0,1)))
print("K3 - R3 =", simplify(piece("K3",0,1) - piece("R3",0,1)))
print("(K2+U1) - R2 =", simplify(piece("K2",0,1) + piece("U1",0,1) - piece("R2",0,1)))
print("(K1+K4) - R1 =", simplify(piece("K1",0,1) + piece("K4",0,1) - piece("R1",0,1)))
