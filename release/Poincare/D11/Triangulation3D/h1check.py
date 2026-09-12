import search as S
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form
from itertools import product

def h1_correct(glue, n, use_rp2=False):
    tri = S.Tri(n, glue)
    vcls = tri.corner_classes()
    ecls = tri.edge_classes()
    fcls = tri.face_classes()
    vmap = {tuple(sorted(c)): i for i, c in enumerate(vcls)}
    emap = {tuple(sorted(c)): i for i, c in enumerate(ecls)}
    V = len(vcls); E = len(ecls)
    def endpoints(ec):
        (t, a, b) = ec[0]
        va = vb = None
        for c in vcls:
            if (t, a) in c: va = vmap[tuple(sorted(c))]
            if (t, b) in c: vb = vmap[tuple(sorted(c))]
        return va, vb
    # spanning tree (edges connecting vertex classes)
    parent = list(range(V))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb: parent[ra] = rb
    tree = set()
    for e in range(E):
        va, vb = endpoints(ecls[e])
        if find(va) != find(vb):
            union(va, vb)
            tree.add(e)
    nontree = [e for e in range(E) if e not in tree]
    # sigma for RP2 detection
    sigma = [1] * n
    for sig in product([1, -1], repeat=n):
        ok = True
        for t in range(n):
            for i in range(4):
                g = glue.get((t, i))
                if g is None: continue
                t2, perm = g
                c = ((-1) ** (i + perm[i] + 1)) * S.face_perm_sign(i, perm)
                if sig[t] * sig[t2] != c:
                    ok = False; break
            if not ok: break
        if ok:
            sigma = list(sig); break
    # relations: for each face class: the boundary walk word of the first rep, tree edges deleted
    rels = []
    for fcl in fcls:
        reps = sorted(fcl)
        (t, i) = reps[0]
        word = []
        fc = sorted(S.face_corners(i))
        j0, j1, j2 = fc
        for (a, b) in [(j0, j1), (j1, j2), (j2, j0)]:
            ab = (t, min(a, b), max(a, b))
            for c in ecls:
                if ab in c:
                    e = emap[tuple(sorted(c))]
                    sgn = 1 if a < b else -1
                    if e not in tree:
                        word.append((e, sgn))
        rels.append(word)
        if use_rp2:
            # RP2 detection: union is S2 iff gluing orientation-reversing in sigma sense
            (t2, i2) = reps[1]
            g = glue.get((t, i))
            if g is not None and g[0] == t2:
                perm = g[1]
            else:
                perm = S.invert(glue.get((t2, i2))[1])
            s = S.face_perm_sign(i, perm)
            sphere = (s * ((-1) ** i) * sigma[t] == -((-1) ** (i2)) * sigma[t2])
            if not sphere:
                rels.append([(e, 2 * sg) for (e, sg) in word])
    M = sp.zeros(len(rels), len(nontree))
    nti = {e: idx for idx, e in enumerate(nontree)}
    for r, w in enumerate(rels):
        for (e, sg) in w:
            M[r, nti[e]] += sg
    sm = smith_normal_form(M)
    diag = [sm[i, i] for i in range(min(sm.shape))]
    rank = sum(1 for d in diag if d != 0)
    torsion = [d for d in diag if d > 1]
    free = len(nontree) - rank
    return torsion, free

def build(tm, sm, bm):
    g = {}
    g[(0,2)] = (1, sm); g[(1,3)] = (0, S.invert(sm))
    g[(0,3)] = (1, sm); g[(1,2)] = (0, S.invert(sm))
    g[(2,2)] = (3, sm); g[(3,3)] = (2, S.invert(sm))
    g[(2,3)] = (3, sm); g[(3,2)] = (2, S.invert(sm))
    g[(0,1)] = (3, tm); g[(3,1)] = (0, S.invert(tm))
    g[(1,1)] = (2, tm); g[(2,1)] = (1, S.invert(tm))
    g[(0,0)] = (3, bm); g[(3,0)] = (0, S.invert(bm))
    g[(1,0)] = (2, bm); g[(2,0)] = (1, S.invert(bm))
    return g

sw23 = S.swap(2,3)
# sanity
gd = {}
for t in range(2):
    for i in range(4):
        gd[(t, i)] = (1 - t, S.IDENTITY)
print("double: H1 =", h1_correct(gd, 2), " (expect [], 0)")

side_map = S.swap(2, 3)
top_map = S.swap(0, 1)
p, q = 3, 1
g3 = {}
for i in range(p):
    g3[(i, 2)] = ((i + 1) % p, side_map)
    g3[((i + 1) % p, 3)] = (i, S.invert(side_map))
    g3[(i, 1)] = ((i + q) % p, top_map)
    g3[((i + q) % p, 0)] = (i, S.invert(top_map))
print("L(3,1) bipyramid: H1 =", h1_correct(g3, 3), " (expect [3], 0)")

for name, tm, sm, bm in [
    ("cand1 all sw23", sw23, sw23, sw23),
    ("cand2 sides flip", sw23, S.compose(S.swap(0,1), sw23), sw23),
]:
    g = build(tm, sm, bm)
    tri = S.Tri(4, g)
    print(name, "f-vector", tri.fvector(), "manifold", tri.manifold(False))
    print("   H1 (w=1):", h1_correct(g, 4))
    print("   H1 (w=1 + RP2 sq):", h1_correct(g, 4, True))
