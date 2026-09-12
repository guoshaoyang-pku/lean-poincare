import search as S
import h1check as H
from itertools import product

# 4-tet "2-gon bipyramid" family: fixed pairing, all corner bijections.
# tets: t0=[N,c,w0,w1] (0,1,2,3), t1=[N,c,w1,w0] (0,1,2,3),
#       t2=[S,c,w0,w1] (0,1,2,3), t3=[S,c,w1,w0] (0,1,2,3)
# pairs: (0,2)-(1,3), (0,3)-(1,2), (2,2)-(3,3), (2,3)-(3,2),
#        (0,1)-(3,1), (1,1)-(2,1), (0,0)-(3,0), (1,0)-(2,0)
PAIRS = [((0,2),(1,3)), ((0,3),(1,2)), ((2,2),(3,3)), ((2,3),(3,2)),
         ((0,1),(3,1)), ((1,1),(2,1)), ((0,0),(3,0)), ((1,0),(2,0))]

def bijections(i1, i2):
    out = []
    for perm in S.permutations(range(4)):
        if perm[i1] == i2:
            out.append(perm)
    return out

choices = []
for (f1, f2) in PAIRS:
    choices.append(bijections(f1[1], f2[1]))
print("choices per pair:", [len(c) for c in choices], "total:", end=" ")
tot = 1
for c in choices:
    tot *= len(c)
print(tot)

results = []
count = 0
for pick in product(*choices):
    glue = {}
    for ((f1, f2), g) in zip(PAIRS, pick):
        glue[f1] = (f2[0], g)
        glue[f2] = (f1[0], S.invert(g))
    tri = S.Tri(4, glue)
    count += 1
    if not tri.orientable():
        continue
    if not tri.manifold(False):
        continue
    fv = tri.fvector()
    torsion, free = H.h1_correct(glue, 4)
    results.append((glue, fv, torsion, free))
    print("FOUND", fv, "H1:", torsion, free)
    if torsion == [2]:
        print("=== RP3 CANDIDATE ===")
        for k in sorted(glue):
            print("   glue", k, "->", glue[k][0], "perm", glue[k][1])
print("searched:", count, "found:", len(results))
