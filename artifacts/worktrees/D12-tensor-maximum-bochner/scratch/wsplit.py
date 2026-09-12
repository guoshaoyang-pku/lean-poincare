#!/usr/bin/env python3
"""Find minimal intermediate forms for the Lean W-half proof (H-formulation), v3.

Mirrors verify_bochner.py's move order:
  commuteDiag: DDU[X,X,j] -> DDU[X,j,X] + sum_m c(X,j,m) DU[X,m]   (all X,j)
  canon:       DDU[j,i,k] -> DDU[i,j,k] + sum_m c(j,i,m) DU[m,k]   (only j > i)
  canonDU:     DU[j,i]    -> DU[i,j]    - sum_m c(i,j,m) U[m]      (only j > i)
All coeff extractions on expanded expressions.
"""
import sympy as sp
from sympy import Symbol, expand, simplify

n = 3
Gfree = {}
for i in range(n):
    for j in range(n):
        for l in range(n):
            if j < l:
                Gfree[(i, j, l)] = Symbol(f"G{i}{j}{l}", commutative=True)

def G(i, j, l):
    if j == l:
        return 0
    if j < l:
        return Gfree[(i, j, l)]
    return -Gfree[(i, l, j)]

def c(i, j, l):
    return G(i, j, l) - G(j, i, l)

U = [Symbol(f"U{j}", commutative=True) for j in range(n)]
DU = {(i, j): Symbol(f"DU{i}{j}", commutative=True) for i in range(n) for j in range(n)}
DDU = {(i, j, k): Symbol(f"DDU{i}{j}{k}", commutative=True)
       for i in range(n) for j in range(n) for k in range(n)}

def H(i, j):
    return DU[(i, j)] - sum(G(i, j, l) * U[l] for l in range(n))

S = expand(sum(U[j] * (DDU[(i, i, j)] - DDU[(j, i, i)]
                       - sum(G(i, j, l) * DU[(i, l)] for l in range(n))
                       + sum(G(i, i, l) * DU[(j, l)] for l in range(n)))
               for j in range(n) for i in range(n)))
F = expand(sum(U[j] * G(i, k, j) * H(i, k) for j in range(n) for i in range(n) for k in range(n))
           - sum(U[j] * G(i, i, l) * H(l, j) for j in range(n) for i in range(n) for l in range(n)))

def commuteDiag(expr):
    new = expand(expr)
    for X in range(n):
        for j in range(n):
            new = new.subs({DDU[(X, X, j)]: DDU[(X, j, X)] + sum(c(X, j, m) * DU[(X, m)] for m in range(n))})
            new = expand(new)
    return new

def canon(expr):
    new = expand(expr)
    for j in range(n):
        for i in range(j):
            for k in range(n):
                new = new.subs({DDU[(j, i, k)]: DDU[(i, j, k)] + sum(c(j, i, m) * DU[(m, k)] for m in range(n))})
                new = expand(new)
    return new

def canonDU(expr):
    new = expand(expr)
    for j in range(n):
        for i in range(j):
            new = new.subs({DU[(j, i)]: DU[(i, j)] - sum(c(i, j, m) * U[m] for m in range(n))})
            new = expand(new)
    return new

Wfull = expand(S + F)
W1 = canon(commuteDiag(Wfull))
W2 = canonDU(W1)

def coeff_of(expr, atom):
    return expand(expand(expr).coeff(atom))

ddu_resid1 = {k: coeff_of(W1, k) for k in DDU.values() if coeff_of(W1, k) != 0}
print("DDU residual after commuteDiag+canon:", ddu_resid1)
du_resid = {k: simplify(coeff_of(W2, k)) for k in DU.values() if coeff_of(W2, k) != 0}
print("DU residual after canonDU:", du_resid)

uu = W2
for k in list(DU.values()) + list(DDU.values()):
    uu = expand(uu - coeff_of(uu, k) * k)
print("\nUU coefficients vs Ric(j,p):")
ok = True
for j in range(n):
    for p in range(n):
        coeff = simplify(uu.coeff(U[j] * U[p]))
        r = expand(sum(
            sum(G(j, p, m) * G(i, m, i) for m in range(n))
            - sum(G(i, p, m) * G(j, m, i) for m in range(n))
            - sum(c(i, j, m) * G(m, p, i) for m in range(n))
            for i in range(n)))
        if simplify(coeff - r) != 0:
            ok = False
            print(f"  MISMATCH U{j}*U{p}: coeff={coeff}  Ric={simplify(r)}")
print("ALL UU coefficients equal Ric(j,p)?:", ok)

# also show the DU-part of W1 (what canonDU consumes) in a clean grouped form
T2 = W1
for k in DDU.values():
    T2 = expand(T2 - coeff_of(T2, k) * k)
print("\nDU part of W1, grouped by U[j]*DU[a,b]:")
from collections import defaultdict
groups = defaultdict(list)
for j in range(n):
    for a in range(n):
        for b in range(n):
            cc = simplify(T2.coeff(U[j] * DU[(a, b)]))
            if cc != 0:
                groups[(a, b)].append((j, cc))
for (a, b), lst in sorted(groups.items()):
    print(f"  DU[{a},{b}]: " + "  ".join(f"U{j}->{cc}" for j, cc in lst))
