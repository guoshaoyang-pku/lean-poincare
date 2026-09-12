#!/usr/bin/env python3
"""Generate the explicit face-pairing table of the boundary of the 4-simplex.

Tet `i` is the facet of Delta^4 opposite vertex `i`; its corner `j` carries the
vertex label `facetVertex i j` (the j-th vertex of that facet in increasing order).
The face of tet `i` opposite corner `j` is glued to the facet opposite the missing
vertex `facetVertex i j`; corner `k` of the glued face is sent to the position of
`facetVertex i k` in the partner facet.

Outputs a Lean `match` table plus a machine-checkable summary.
"""

def facet_vertex(i, j):
    return j if j < i else j + 1

def position_in_facet(i, v):
    """position of vertex v != i in the increasing list of the facet opposite i"""
    assert v != i
    return v if v < i else v - 1

def glue(i, j):
    """(partner tet, corner permutation) for the face of tet i opposite corner j"""
    i2 = facet_vertex(i, j)
    perm = []
    for k in range(4):
        if k == j:
            v = i
        else:
            v = facet_vertex(i, k)
        perm.append(position_in_facet(i2, v))
    return i2, tuple(perm)

def compose(p, q):
    return tuple(p[q[i]] for i in range(4))

def cycle_decomp(p):
    seen = [False]*4
    cycles = []
    for s in range(4):
        if not seen[s]:
            cyc = []
            x = s
            while not seen[x]:
                seen[x] = True
                cyc.append(x)
                x = p[x]
            if len(cyc) > 1:
                cycles.append(cyc)
    return cycles

def to_swaps_expr(p):
    """Lean expression for the permutation p as a product of Equiv.swap"""
    cycles = cycle_decomp(p)
    if not cycles:
        return "(1 : Equiv.Perm (Fin 4))"
    factors = []
    for cyc in cycles:
        # (a b c d) = swap a b * swap b c * swap c d
        for a, b in zip(cyc, cyc[1:]):
            factors.append(f"Equiv.swap {a} {b}")
    return " * ".join(factors) if len(factors) > 1 else f"({factors[0]})"

def eval_swaps(p):
    """simulate the Lean product convention f * g = fun x => f (g x)"""
    cycles = cycle_decomp(p)
    # build the product from the emitted factor list, evaluated right to left
    factors = []
    for cyc in cycles:
        for a, b in zip(cyc, cyc[1:]):
            s = list(range(4)); s[a], s[b] = s[b], s[a]
            factors.append(tuple(s))
    acc = (0, 1, 2, 3)
    for f in reversed(factors):   # f1 * f2 * ... * fn  = f1 o f2 o ... o fn
        acc = compose(f, acc)
    return acc

table = {}
for i in range(5):
    for j in range(4):
        table[(i, j)] = glue(i, j)

# consistency: glue(i,j) = (i2, p) requires glue(i2, p[j]) = (i, p^-1)
ok = True
for (i, j), (i2, p) in table.items():
    j2 = p[j]
    i3, q = table[(i2, j2)]
    pinv = [0]*4
    for a, b in enumerate(p):
        pinv[b] = a
    if (i3, q) != (i, tuple(pinv)):
        ok = False
        print("INCONSISTENT", i, j, (i2, p), (i3, q), tuple(pinv))
print("consistent:", ok)

# every gluing is orientation reversing?  sign(pi) = (-1)^(i + i' + 1)
def sign(seq):
    inv = 0
    for a in range(len(seq)):
        for b in range(a+1, len(seq)):
            if seq[a] > seq[b]:
                inv += 1
    return 1 if inv % 2 == 0 else -1

orient_ok = True
for (i, j), (i2, p) in table.items():
    # induced map on the increasing orders of the two faces
    fc = sorted(k for k in range(4) if k != j)
    fc2 = sorted(k for k in range(4) if k != p[j])
    perm_of_indices = tuple(fc2.index(p[k]) for k in fc)
    s = sign(perm_of_swap := perm_of_indices)
    expected = (-1)**(j + p[j] + 1)
    if s != expected:
        orient_ok = False
        print("NOT ORIENT-REV", i, j, s, expected)
print("orientation reversing (identity orientation):", orient_ok)

print("swap expressions:")
for i in range(5):
    for j in range(4):
        i2, p = table[(i, j)]
        e = to_swaps_expr(p)
        assert eval_swaps(p) == p, (p, e, eval_swaps(p))
        print(f"  | {i}, {j} => some (⟨{i2}, by decide⟩, {e})")
