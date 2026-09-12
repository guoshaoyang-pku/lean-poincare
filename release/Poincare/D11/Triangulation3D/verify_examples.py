#!/usr/bin/env python3
"""Independent cross-check of the six D11 example triangulations.

This script re-enters the *same* face-pairing tables that are hard-coded in
`Models.lean`, but runs them through the independent Python model checker
`search.py` (a different implementation of the same combinatorial definitions),
and additionally computes the first homology `H_1` of each example by Smith
normal form of the face-relation matrix (an invariant the Lean layer does not
compute).

It is corroborating evidence only: the Lean `decide` proofs in `Models.lean`
are the source of truth.  Run from this directory:

    python3 verify_examples.py
"""
from itertools import product

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form

import search as S

ID = S.IDENTITY
sw01 = S.swap(0, 1)
sw02 = S.swap(0, 2)
sw03 = S.swap(0, 3)
sw12 = S.swap(1, 2)
sw13 = S.swap(1, 3)
sw21 = S.swap(2, 1)
sw23 = S.swap(2, 3)
sw32 = S.swap(3, 2)


def double(n):
    return {(t, i): (1 - t, ID) for t in range(n) for i in range(4)}


def s3_simplex():
    tbl = {
        (0, 0): (1, ID), (0, 1): (2, sw01), (0, 2): (3, S.compose(sw01, sw12)),
        (0, 3): (4, S.compose(S.compose(sw01, sw12), sw23)),
        (1, 0): (0, ID), (1, 1): (2, ID), (1, 2): (3, sw12),
        (1, 3): (4, S.compose(sw12, sw23)),
        (2, 0): (0, sw01), (2, 1): (1, ID), (2, 2): (3, ID), (2, 3): (4, sw23),
        (3, 0): (0, S.compose(sw02, sw21)), (3, 1): (1, sw12), (3, 2): (2, ID),
        (3, 3): (4, ID),
        (4, 0): (0, S.compose(S.compose(sw03, sw32), sw21)), (4, 1): (1, S.compose(sw13, sw32)),
        (4, 2): (2, sw23), (4, 3): (3, ID),
    }
    return tbl


def solid_torus3():
    return {
        (0, 2): (1, sw23), (0, 3): (2, sw03),
        (1, 1): (2, sw12), (1, 3): (0, sw23),
        (2, 0): (0, sw03), (2, 2): (1, sw12),
    }


def lens_bipyramid(p, q):
    """The bipyramid over a p-gon with the q-step twist (same table as lensPQ)."""
    g = {}
    for t in range(p):
        g[(t, 0)] = ((t + p - q) % p, sw01)
        g[(t, 1)] = ((t + q) % p, sw01)
        g[(t, 2)] = ((t + 1) % p, sw23)
        g[(t, 3)] = ((t + p - 1) % p, sw23)
    return g


def lens31():
    return lens_bipyramid(3, 1)


def lens21():
    cycA = S.compose(sw12, sw23)
    cycB = S.compose(sw12, sw13)
    tbl = {}
    tbl[(0, 2)] = (1, sw23); tbl[(0, 3)] = (1, sw23)
    tbl[(0, 1)] = (3, ID);   tbl[(0, 0)] = (3, cycA)
    tbl[(1, 2)] = (0, sw23); tbl[(1, 3)] = (0, sw23)
    tbl[(1, 1)] = (2, ID);   tbl[(1, 0)] = (2, cycB)
    tbl[(2, 2)] = (3, sw23); tbl[(2, 3)] = (3, sw23)
    tbl[(2, 1)] = (1, ID);   tbl[(2, 0)] = (1, cycA)
    tbl[(3, 2)] = (2, sw23); tbl[(3, 3)] = (2, sw23)
    tbl[(3, 1)] = (0, ID);   tbl[(3, 0)] = (0, cycB)
    return tbl


def h1(glue, n):
    """H_1 of the quotient, as (torsion invariants, free rank)."""
    tri = S.Tri(n, glue)
    vcls = tri.corner_classes()
    ecls = tri.edge_classes()
    fcls = tri.face_classes()
    vmap = {c: i for i, C in enumerate(vcls) for c in C}
    emap = {e: i for i, E in enumerate(ecls) for e in E}
    V, E = len(vcls), len(ecls)
    parent = list(range(V))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    tree = set()
    for idx, Ec in enumerate(ecls):
        t, a, b = Ec[0]
        ra, rb = find(vmap[(t, a)]), find(vmap[(t, b)])
        if ra != rb:
            parent[ra] = rb
            tree.add(idx)
    nontree = [e for e in range(E) if e not in tree]
    nti = {e: i for i, e in enumerate(nontree)}

    rels = []
    for fcl in fcls:
        t, i = sorted(fcl)[0]
        word = []
        fc = sorted(S.face_corners(i))
        for a, b in [(fc[0], fc[1]), (fc[1], fc[2]), (fc[2], fc[0])]:
            key = (t, min(a, b), max(a, b))
            e = emap[key]
            if e not in tree:
                word.append((e, 1 if a < b else -1))
        rels.append(word)

    M = sp.zeros(len(rels), len(nontree))
    for r, w in enumerate(rels):
        for e, sg in w:
            M[r, nti[e]] += sg
    sm = smith_normal_form(M)
    diag = [sm[i, i] for i in range(min(sm.shape))]
    torsion = [int(d) for d in diag if d > 1]
    rank = sum(1 for d in diag if d != 0)
    return torsion, len(nontree) - rank


def boundary_chi(tri):
    """Euler characteristic of the boundary surface."""
    bfs = tri.boundary_faces()
    if not bfs:
        return None
    vcls = tri.corner_classes()
    ecls = tri.edge_classes()
    vset, eset = set(), set()
    for (t, i) in bfs:
        for j in range(4):
            if j != i:
                for idx, C in enumerate(vcls):
                    if (t, j) in C:
                        vset.add(idx)
        for a in range(4):
            for b in range(a + 1, 4):
                if a != i and b != i:
                    for idx, E in enumerate(ecls):
                        if (t, a, b) in E:
                            eset.add(idx)
    return len(vset) - len(eset) + len(bfs)


EXAMPLES = [
    ("ball3", 1, {}, False),
    ("s3Double", 2, double(2), False),
    ("s3Simplex", 5, s3_simplex(), False),
    ("solidTorus3", 3, solid_torus3(), True),
    ("lens31 = L(3,1)", 3, lens31(), False),
    ("lens21 = RP3", 4, lens21(), False),
]

print(f"{'example':18} {'consistent':10} {'orient':8} {'closed':7} {'f-vector':16} "
      f"{'chi':4} {'manifold':9} {'boundary':9} {'H1'}")
for name, n, glue, with_boundary in EXAMPLES:
    tri = S.Tri(n, glue)
    fv = tri.fvector()
    chi = fv[0] - fv[1] + fv[2] - fv[3]
    man = tri.manifold(with_boundary)
    bchi = None
    if tri.boundary_faces():
        bchi = boundary_chi(tri)
    tor, free = h1(glue, n)
    h1str = "Z" if (not tor and free == 1) else (
        "0" if (not tor and free == 0) else
        f"Z^{free} + " + "+".join(f"Z/{d}" for d in tor) if free else "+".join(f"Z/{d}" for d in tor))
    print(f"{name:18} {str(tri.consistent()):10} {str(tri.orientable()):8} "
          f"{str(tri.closed()):7} {str(fv):16} {chi:<4} {str(man):9} {str(bchi):9} {h1str}")

print()
print("bipyramid family L(p,q) (p tetrahedra):")
for p, q in [(2, 1), (3, 1), (4, 1), (5, 1), (5, 2)]:
    tri = S.Tri(p, lens_bipyramid(p, q))
    fv = tri.fvector()
    tor, free = h1(lens_bipyramid(p, q), p)
    print(f"  L({p},{q}): f-vector {fv} chi {fv[0]-fv[1]+fv[2]-fv[3]} "
          f"closed {tri.closed()} manifold {tri.manifold(False)} "
          f"H1 {tor} + Z^{free}")
