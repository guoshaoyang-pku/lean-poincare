#!/usr/bin/env python3
"""Symbolic verification of the abstract algebraic Bochner identity chain (v2).

Structural relations enforced from the start:
  (I2) G[i][j][l] = -G[i][l][j]  AND  G[X][i][i] = 0  (metric compatibility, ON frame)
  (I3) c[i][j][l] := G[i][j][l] - G[j][i][l]           (torsion-free)
  (I1) commutator relations for first and second derivatives.
"""
import itertools
import random
import sympy as sp
from sympy import symbols, Symbol, expand, simplify

n = 3

def idx():
    return itertools.product(range(n), repeat=3)

# free G variables: G[i][j][l] for j < l; diagonal G[X][i][i] = 0.
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
DDUs = {(j, i, k): Symbol(f"DDUs{j}{i}{k}", commutative=True)
        for i in range(n) for j in range(n) for k in range(n)}

def H(i, j):
    return DU[(i, j)] - sum(G(i, j, l) * U[l] for l in range(n))

LapU = sum(H(k, k) for k in range(n))
gradSq = sum(U[j] ** 2 for j in range(n))
hessSq = sum(H(i, j) ** 2 for i in range(n) for j in range(n))

def gradX_gu(X, j):
    return DU[(X, j)] + sum(G(X, k, j) * U[k] for k in range(n))

def gradX_gradX_gu(X, j):
    Dx_inner = DDUs[(X, X, j)] + sum(G(X, k, j) * DU[(X, k)] for k in range(n))
    return Dx_inner + sum(G(X, k, j) * gradX_gu(X, k) for k in range(n))

def LapVecGu(j):
    return sum(gradX_gradX_gu(X, j) - sum(G(X, X, l) * gradX_gu(l, j) for l in range(n))
               for X in range(n))

def R(i, j, k, l):
    return (sum(G(j, k, m) * G(i, m, l) for m in range(n))
            - sum(G(i, k, m) * G(j, m, l) for m in range(n))
            - sum(c(i, j, m) * G(m, k, l) for m in range(n)))

def Ric(j, k):
    return sum(R(i, j, k, i) for i in range(n))

def RicUU():
    return sum(U[j] * U[k] * Ric(j, k) for j in range(n) for k in range(n))

LapGradSq = sum(
    2 * sum(DU[(X, j)] ** 2 + U[j] * DDUs[(X, X, j)] for j in range(n))
    - 2 * sum(G(X, X, l) * U[j] * DU[(l, j)] for l in range(n) for j in range(n))
    for X in range(n))

inner_gu_LapVec = sum(U[j] * LapVecGu(j) for j in range(n))
diffB = expand(LapGradSq - (2 * hessSq + 2 * inner_gu_LapVec))
print("(B) raw diff zero?:", sp.simplify(diffB) == 0)

inner_gu_gLap = sum(U[j] * (sum(DDUs[(j, k, k)] - sum(G(k, k, l) * DU[(j, l)] for l in range(n))
                                for k in range(n)))
                    for j in range(n))
diffW = expand(inner_gu_LapVec - inner_gu_gLap - RicUU())

def commuteDiag(expr):
    # D_X D_X u_j = D_X D_j u_X + D_X D_[e_X,e_j] u
    #            = DDUs[X][j][X] + sum_m c[X][j][m] DU[X][m]
    new = expr
    for X in range(n):
        for j in range(n):
            new = new.subs({DDUs[(X, X, j)]: DDUs[(X, j, X)] + sum(c(X, j, m) * DU[(X, m)] for m in range(n))})
    return new

def canon(expr):
    # canonicalize all second derivatives DDUs[j][i][k] to i <= j
    new = expr
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(n):
                # D_j D_i = D_i D_j + D_[e_j,e_i]  =>  D_j D_i u_k = D_i D_j u_k + sum_m c[j][i][m] D_m u_k
                new = new.subs({DDUs[(j, i, k)]: DDUs[(i, j, k)] + sum(c(j, i, m) * DU[(m, k)] for m in range(n))})
    return new

def canonDU(expr):
    # DU[i][j] - DU[j][i] = sum_m c[i][j][m] U[m]; canonicalize i > j:
    # DU[j][i] = DU[i][j] - sum_m c[i][j][m] U[m]
    new = expr
    for i in range(n):
        for j in range(i + 1, n):
            new = new.subs({DU[(j, i)]: DU[(i, j)] - sum(c(i, j, m) * U[m] for m in range(n))})
    return new

diffWc = expand(canonDU(canon(commuteDiag(diffW))))
print("(W) diff after canonicalization zero?:", sp.simplify(diffWc) == 0)
if sp.simplify(diffWc) != 0:
    print("(W) residual:", diffWc)

# --- numeric sanity of the full Bochner identity with consistent data ---
random.seed(7)
subsG = {v: random.randint(-3, 3) for v in Gfree.values()}
subsU = {U[j]: random.randint(-3, 3) for j in range(n)}
subsDU = {}
for i in range(n):
    for j in range(i, n):
        v = random.randint(-3, 3)
        subsDU[DU[(i, j)]] = v
        subsDU[DU[(j, i)]] = v - sum(sp.sympify(c(i, j, m)).subs(subsG) * subsU[U[m]] for m in range(n))
subsDDU = {}
for k in range(n):
    for i in range(n):
        for j in range(i, n):
            v = random.randint(-3, 3)
            subsDDU[DDUs[(i, j, k)]] = v
            subsDDU[DDUs[(j, i, k)]] = v + sum(sp.sympify(c(j, i, m)).subs(subsG) * subsDU[DU[(m, k)]] for m in range(n))
alld = dict(subsG)
alld.update(subsU)
alld.update(subsDU)
alld.update(subsDDU)
# enforce D_X D_X u_j = D_X D_j u_X + sum_m c[X][j][m] DU[X][m]
for X in range(n):
    for j in range(n):
        alld[DDUs[(X, X, j)]] = (subsDDU[DDUs[(X, j, X)]]
                                 + sum(sp.sympify(c(X, j, m)).subs(subsG) * subsDU[DU[(X, m)]] for m in range(n)))
lhs = LapGradSq.subs(alld)
rhs = (2 * hessSq + 2 * inner_gu_gLap + 2 * RicUU()).subs(alld)
print("numeric Bochner LHS:", expand(lhs))
print("numeric Bochner RHS:", expand(rhs))
print("numeric Bochner ok?:", sp.simplify(lhs - rhs) == 0)

# repeat over several random seeds for confidence
ok = True
for seed in range(20):
    random.seed(seed)
    subsG = {v: random.randint(-4, 4) for v in Gfree.values()}
    subsU = {U[j]: random.randint(-4, 4) for j in range(n)}
    subsDU = {}
    for i in range(n):
        for j in range(i, n):
            v = random.randint(-4, 4)
            subsDU[DU[(i, j)]] = v
            subsDU[DU[(j, i)]] = v - sum(sp.sympify(c(i, j, m)).subs(subsG) * subsU[U[m]] for m in range(n))
    subsDDU = {}
    for k in range(n):
        for i in range(n):
            for j in range(i, n):
                v = random.randint(-4, 4)
                subsDDU[DDUs[(i, j, k)]] = v
                subsDDU[DDUs[(j, i, k)]] = v + sum(sp.sympify(c(j, i, m)).subs(subsG) * subsDU[DU[(m, k)]] for m in range(n))
    alld = dict(subsG)
    alld.update(subsU)
    alld.update(subsDU)
    alld.update(subsDDU)
    for X in range(n):
        for j in range(n):
            alld[DDUs[(X, X, j)]] = (subsDDU[DDUs[(X, j, X)]]
                                     + sum(sp.sympify(c(X, j, m)).subs(subsG) * subsDU[DU[(X, m)]] for m in range(n)))
    lhs = LapGradSq.subs(alld)
    rhs = (2 * hessSq + 2 * inner_gu_gLap + 2 * RicUU()).subs(alld)
    if sp.simplify(lhs - rhs) != 0:
        ok = False
        print("seed", seed, "FAILED")
print("20 random numeric instances ok?:", ok)
