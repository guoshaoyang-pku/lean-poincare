#!/usr/bin/env python3
"""Prototype checker for D11 face-pairing triangulations of 3-manifolds.

Data model: N tetrahedra, corners (t, j) with t in [0,N), j in {0,1,2,3}.
A face is (t, i) = the triangle opposite corner i. A gluing is
  glue[(t,i)] = (t', perm)  where perm : Fin4 -> Fin4 is a bijection with perm[i] = i'
  (the image of corner j of face (t,i) is corner perm[j] of face (t', i')).
None = boundary (unpaired) face.

Checks (mirroring what will be formalised in Lean):
  1. consistency: partial involution, no face glued to itself, perms valid bijections
  2. orientation-reversing: sign(pi) = (-1)^(i + i' + 1), pi = permutation of the
     increasing orders of the two face vertex sets
  3. Euler characteristic via connected components (union-find)
  4. closedness; boundary surface conditions (closed surface, orientable, chi=0)
  5. vertex links (S^2 for interior, D^2 for boundary vertices), edge links (cycles)
  6. H_1 via Smith normal form (to identify the manifold)
"""
import itertools, json, sys
from fractions import Fraction

def sign(perm):
    """sign of a permutation given as a list perm[a] = image of position a."""
    n = len(perm)
    # number of inversions
    inv = 0
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                inv += 1
    return 1 if inv % 2 == 0 else -1

def face_corners(i):
    return [j for j in range(4) if j != i]

def perm_sign_on_face(i, perm):
    """sign of the induced permutation of the increasing orders of the face corners."""
    i2 = perm[i]
    src = face_corners(i)
    tgt = face_corners(i2)
    # map position k of source increasing order -> position of perm[src[k]] in target increasing order
    p = [tgt.index(perm[src[k]]) for k in range(3)]
    return sign(p)

class Tri:
    def __init__(self, N, glue):
        self.N = N
        self.glue = glue  # dict (t,i) -> (t', perm) or None

    # ---------- 1. consistency ----------
    def consistent(self):
        for t in range(self.N):
            for i in range(4):
                g = self.glue.get((t,i))
                if g is None: continue
                t2, perm = g
                i2 = perm[i]
                if not (0 <= t2 < self.N): return False, f"bad tet {(t,i)}"
                if set(perm) != set(range(4)): return False, f"not a bijection {(t,i)}"
                if perm[i] != i2: return False, f"perm[i] mismatch {(t,i)}"
                if (t2, i2) == (t, i): return False, f"self-glued face {(t,i)}"
                # partner's gluing must be the inverse
                g2 = self.glue.get((t2, i2))
                if g2 is None: return False, f"partner not glued {(t,i)}"
                t3, perm2 = g2
                if t3 != t: return False, f"partner wrong tet {(t,i)}"
                if [perm2[perm[j]] for j in range(4)] != list(range(4)):
                    return False, f"partner not inverse {(t,i)}"
                if perm2[i2] != i: return False, f"partner omits wrong corner {(t,i)}"
        return True, ""

    # ---------- 2. orientation ----------
    def orientation_reversing(self):
        for t in range(self.N):
            for i in range(4):
                g = self.glue.get((t,i))
                if g is None: continue
                t2, perm = g
                i2 = perm[i]
                s = perm_sign_on_face(i, perm)
                want = 1 if (i + i2 + 1) % 2 == 0 else -1
                if s != want:
                    return False, f"orientation {(t,i)}->{(t2,i2)} sign {s} want {want}"
        return True, ""

    # ---------- components ----------
    def components(self, pairs, seed=None):
        parent = {}
        if seed is not None:
            for a in seed: parent.setdefault(a, a)
        def find(a):
            parent.setdefault(a, a)
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a
        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb: parent[ra] = rb
        for a, b in pairs: union(a, b)
        classes = {}
        for a in list(parent):
            classes.setdefault(find(a), []).append(a)
        return classes

    def corner_classes(self):
        pairs = []
        for t in range(self.N):
            for i in range(4):
                g = self.glue.get((t,i))
                if g is None: continue
                t2, perm = g
                for j in face_corners(i):
                    pairs.append(((t,j),(t2,perm[j])))
        return self.components(pairs, seed=[(t,j) for t in range(self.N) for j in range(4)])

    def edge_classes(self):
        edges = {}
        for t in range(self.N):
            for a, b in itertools.combinations(range(4), 2):
                edges[(t,a,b)] = frozenset([(t,a),(t,b)])
        pairs = []
        for t in range(self.N):
            for i in range(4):
                g = self.glue.get((t,i))
                if g is None: continue
                t2, perm = g
                for a, b in itertools.combinations(face_corners(i), 2):
                    pa, pb = sorted([perm[a], perm[b]])
                    pairs.append((edges[(t,a,b)], edges[(t2,pa,pb)]))
        return self.components(pairs, seed=list(edges.values()))

    def face_classes(self):
        pairs = []
        for t in range(self.N):
            for i in range(4):
                g = self.glue.get((t,i))
                if g is None: continue
                t2, perm = g
                pairs.append(((t,i),(t2,perm[i])))
        return self.components(pairs, seed=[(t,i) for t in range(self.N) for i in range(4)])

    def euler(self):
        V = len(self.corner_classes())
        E = len(self.edge_classes())
        F = len(self.face_classes())
        T = self.N
        return V - E + F - T, dict(V=V, E=E, F=F, T=T)

    def closed(self):
        for t in range(self.N):
            for i in range(4):
                if self.glue.get((t,i)) is None: return False
        return True

    # ---------- links ----------
    def all_corner_sets(self):
        return {(t,j) for t in range(self.N) for j in range(4)}

    def vertex_link_data(self):
        vclasses = self.corner_classes()
        eclasses = self.edge_classes()
        fclasses = self.face_classes()
        # edge class lookup
        eclass_of = {}
        for rep, mem in eclasses.items():
            for e in mem: eclass_of[frozenset(e)] = rep
        fclass_of = {}
        for rep, mem in fclasses.items():
            for f in mem: fclass_of[f] = rep
        # boundary faces
        boundary_faces = set()
        for t in range(self.N):
            for i in range(4):
                if self.glue.get((t,i)) is None:
                    boundary_faces.add(fclass_of[(t,i)])
        res = []
        for vrep, vmem in vclasses.items():
            vset = set(vmem)
            # faces through the class
            faces_through = []
            for t in range(self.N):
                for i in range(4):
                    corners = {(t,j) for j in face_corners(i)}
                    if corners & vset:
                        faces_through.append((t,i))
            # edges through the class (edges with >= 1 corner in vset)
            # condition checks
            ok = True
            notes = []
            for (t,i) in faces_through:
                corners = [(t,j) for j in face_corners(i)]
                k = len(set(corners) & vset)
                if k != 1:
                    ok = False; notes.append(f"face {(t,i)} has {k} corners in class")
            for (t,a,b) in [(t,a,b) for t in range(self.N) for a,b in itertools.combinations(range(4),2)]:
                eset = {(t,a),(t,b)}
                k = len(eset & vset)
                if k == 2:
                    ok = False; notes.append(f"edge {(t,a,b)} has both corners in class")
            # link triangles: for each face class through the vertex class, the set of 3 edge classes
            link_triangles = []
            seen_fc = set()
            for (t,i) in faces_through:
                fc = fclass_of[(t,i)]
                if fc in seen_fc: continue
                seen_fc.add(fc)
                tri = []
                for a,b in itertools.combinations(face_corners(i), 2):
                    tri.append(eclass_of[frozenset([(t,a),(t,b)])])
                link_triangles.append(frozenset(tri))
            # link vertices: edge classes appearing
            link_vertices = set()
            for tri in link_triangles: link_vertices |= set(tri)
            # link edges: pairs appearing in triangles
            edge_count = {}
            for tri in link_triangles:
                for a,b in itertools.combinations(sorted(tri), 2):
                    edge_count[(a,b)] = edge_count.get((a,b),0) + 1
            res.append(dict(vertex=vrep, faces_through=len(faces_through),
                            link_vertices=len(link_vertices),
                            link_edges=len(edge_count),
                            link_triangles=len(link_triangles),
                            edge_multiplicities=sorted(set(edge_count.values())),
                            ok=ok, notes=notes))
        return res, boundary_faces

    def full_report(self):
        ok, msg = self.consistent()
        r = dict(N=self.N, consistent=ok, consistent_msg=msg)
        ok2, msg2 = self.orientation_reversing()
        r['orientation_reversing'] = ok2; r['orientation_msg'] = msg2
        r['euler'] = self.euler()
        r['closed'] = self.closed()
        vld, bf = self.vertex_link_data()
        r['vertex_links'] = vld
        r['boundary_faces'] = sorted(bf)
        return r

# ---------------- constructions ----------------

def face_perm_from_map(i, i2, src_face_verts, img):
    """build perm: Fin4 -> Fin4 where the face (t,i) vertices src_face_verts (list) map to img."""
    perm = [None]*4
    for j in face_corners(i):
        # src face corner j = src_face_verts[position]
        # image = img[position]
        perm[j] = img[face_corners(i).index(j)]
    perm[i] = i2
    return perm

def bipyramid_lens(p, q):
    """L(p,q) via the bipyramid: p tets (N,S,v_i,v_{i+1}), side identity gluings,
    top_i ~ bottom_{i+q} via N|->S, v_j |-> v_{j+q}."""
    N = p
    glue = {}
    # tet t = [N=0, S=1, v_t=2, v_{t+1}=3]
    def tet(t): return (t,)
    for t in range(p):
        # side faces: face (t,2) = {N,S,v_{t+1}}, face (t,3) = {N,S,v_t}
        # face (t,2) of tet t glues to face (t+1,3) of tet t+1 by identity
        t2 = (t+1) % p
        # identity on corners 0,1,2 (the face {0,1,3}? careful)
        # tet t face (t,2) = corners {0,1,3}; tet t+1 face (t2,3) = corners {0,1,2}
        # identity: corner 0->0, 1->1, 3->2
        perm = [0,1,3,2]  # maps corner j of tet t to corner perm[j] of tet t2
        glue[(t,2)] = (t2, perm)
        # inverse for tet t2 face (t2,3): corner 0->0,1->1,2->3
        perm_inv = [0,1,3,2]
        glue[(t2,3)] = (t, perm_inv)
        # top face (t,1) = {N, v_t, v_{t+1}} = corners {0,2,3} glues to bottom face (t+q, 0) = {S, v, v} of tet t+q
        s = (t+q) % p
        # map: 0->1 (N->S), 2->2+(s-t) mod p ... in terms of the corners of tet s: S=1, v_s=2, v_{s+1}=3
        # v_t -> v_s, v_{t+1} -> v_{s+1}: corner 2 -> 2, corner 3 -> 3; corner 0 -> 1
        perm = [1,0,2,3]
        glue[(t,1)] = (s, perm)
        # bottom face (s,0) = corners {1,2,3} glues back to top (t,1) = corners {0,2,3}
        # inverse: 1->0, 2->2, 3->3, 0->1
        perm_inv = [1,0,2,3]
        glue[(s,0)] = (t, perm_inv)
    return Tri(p, glue)

def two_tet_sphere():
    """S^3 as the double of the tetrahedron: face (0,i) ~ (1,i) by an odd permutation
    (swap the two smallest corners)."""
    glue = {}
    for i in range(4):
        fc = face_corners(i)
        # odd permutation of the face: swap the first two corners of the increasing order
        perm = [None]*4
        fc_sorted = sorted(fc)
        img = {}
        img[fc_sorted[0]] = fc_sorted[1]
        img[fc_sorted[1]] = fc_sorted[0]
        img[fc_sorted[2]] = fc_sorted[2]
        for j in fc: perm[j] = img[j]
        perm[i] = i
        glue[(0,i)] = (1, perm)
        glue[(1,i)] = (0, perm)
    return Tri(2, glue)

def boundary_four_simplex():
    """∂Δ^4 as face pairings of its 5 facets; facet = 4-subset of {0..4};
    gluing = identity on the shared triangle."""
    facets = [tuple(sorted(set(range(5))-{k})) for k in range(5)]
    N = 5
    glue = {}
    # corner j of facet t corresponds to facets[t][j] in {0..4}
    for t in range(N):
        for u in range(N):
            if t == u: continue
            # shared triangle: facets[t] minus one element = facets[u] minus one element
            st, su = set(facets[t]), set(facets[u])
            common = st & su
            if len(common) != 3: continue
            # face of tet t opposite the corner NOT in common
            i = facets[t].index((st - common).pop())
            i2 = facets[u].index((su - common).pop())
            perm = [None]*4
            for j in range(4):
                if j == i:
                    perm[j] = i2
                else:
                    perm[j] = facets[u].index(facets[t][j])
            glue[(t,i)] = (u, perm)
    return Tri(N, glue)

def single_tet_ball():
    """The 3-ball as one tetrahedron, no gluings (all boundary)."""
    return Tri(1, {})

def layering_data():
    """known 2-tet solid torus? to be searched instead."""
    pass

# ---------------- homology ----------
def smith_normal_form(M):
    """integer Smith normal form of a matrix (list of rows), returns (d1,...,dk) diagonal entries."""
    rows = [r[:] for r in M]
    if not rows: return []
    n = len(rows); m = len(rows[0])
    # work with Fraction-free-ish: just do Gaussian over Q then compute invariant factors via gcd... 
    # simpler: compute over Q the rank and then use the standard algorithm over Z.
    # Implement the classic integer SNF by row/column operations (bounded loop).
    import math
    A = [r[:] for r in rows]
    diag = []
    r, c = 0, 0
    while r < n and c < m:
        # find pivot: nonzero entry
        found = False
        while not found:
            # find nonzero in submatrix
            piv = None
            for i in range(r, n):
                for j in range(c, m):
                    if A[i][j] != 0:
                        piv = (i, j); break
                if piv: break
            if piv is None:
                break
            i0, j0 = piv
            # move to (r,c)
            A[r], A[i0] = A[i0], A[r]
            for i in range(n):
                A[i][c], A[i][j0] = A[i][j0], A[i][c]
            # reduce the row and column using Euclidean algorithm
            changed = True
            while changed:
                changed = False
                for i in range(r+1, n):
                    if A[i][c] != 0:
                        q = A[i][c] // A[r][c]
                        if A[i][c] % A[r][c] == 0:
                            for j in range(c, m):
                                A[i][j] -= q*A[r][j]
                        else:
                            A[r], A[i] = A[i], A[r]
                        changed = True
                        break
                if changed: continue
                for j in range(c+1, m):
                    if A[r][j] != 0:
                        q = A[r][j] // A[r][c]
                        if A[r][j] % A[r][c] == 0:
                            for i in range(r, n):
                                A[i][j] -= q*A[i][c]
                        else:
                            for i in range(n):
                                A[i][c], A[i][j] = A[i][j], A[i][c]
                        changed = True
                        break
            found = True
        if A[r][c] == 0:
            break
        diag.append(abs(A[r][c]))
        r += 1; c += 1
    return diag

def homology(tri):
    """H_1 = ker d1 / im d2 via SNF. Uses oriented incidence:
    d1: edge class -> head - tail (vertex classes); d2: face class -> boundary (alternating)."""
    vc = tri.corner_classes(); ec = tri.edge_classes(); fc = tri.face_classes()
    vclass_of = {}
    for rep, mem in vc.items():
        for x in mem: vclass_of[x] = rep
    # edges: canonical representative with an orientation (ordered pair)
    edges = []
    eclass_of = {}
    for rep, mem in ec.items():
        e = sorted(mem)[0]
        e = tuple(sorted(e))
        edges.append((e[0], e[1]))
        eid = len(edges)-1
        for m in mem:
            eclass_of[frozenset(m)] = eid
    # faces: canonical representative triangle with orientation given by increasing corner order
    faces = []
    fclass_of = {}
    for rep, mem in fc.items():
        f = sorted(mem)[0]
        corners = sorted([(f[0],j) for j in face_corners(f[1])])
        faces.append((f, corners))
        fclass_of[rep] = len(faces)-1
    # d1: rows = vertices, cols = edges
    vids = {rep:i for i, rep in enumerate(vc)}
    d1 = [[0]*len(edges) for _ in range(len(vc))]
    for k, (a, b) in enumerate(edges):
        d1[vids[vclass_of[a]]][k] += 1
        d1[vids[vclass_of[b]]][k] -= 1
    # d2: rows = edges, cols = faces
    d2 = [[0]*len(faces) for _ in range(len(edges))]
    for k, (f, corners) in enumerate(faces):
        # boundary of the triangle (v0,v1,v2): v0v1 + v1v2 + v2v0
        for idx in range(3):
            a = corners[idx]; b = corners[(idx+1)%3]
            e = tuple(sorted([a,b]))
            eid = eclass_of[frozenset([a,b])]
            # sign: +1 if the ordered pair (a,b) equals the representative orientation
            e0 = edges[eid]
            sgn = 1 if (a,b) == e0 else -1
            d2[eid][k] += sgn
    # H1 = ker d1 / im d2: SNF of [d1; d2] gives nothing direct; do: 
    # ker d1 via SNF of d1: elementary divisors of d1 give Z^rank structure of image; 
    # then restrict. Simpler: compute SNF of d2 to get im d2 structure, SNF of d1 for image d1,
    # H1 = ker(d1)/im(d2): use the exact SNF of the combined map [d2 -> ker d1]: 
    # We do: SNF(d1) -> U d1 V = D. ker d1 corresponds to the zero columns. 
    # Restrict d2 to ker d1 and take SNF.
    import math
    # We'll do a quick and dirty: compute over QQ the quotient dimension and torsion via SNF of d2 restricted to ker d1.
    # Get ker d1 basis over Q.
    n_edges = len(edges)
    # solve d1 x = 0 over Q using rational Gaussian elimination
    def rref_over_q(M):
        M = [[Fraction(x) for x in row] for row in M]
        rows = len(M); cols = len(M[0]) if rows else 0
        piv = []
        r = 0
        for c in range(cols):
            pr = None
            for i in range(r, rows):
                if M[i][c] != 0: pr = i; break
            if pr is None: continue
            M[r], M[pr] = M[pr], M[r]
            pv = M[r][c]
            for j in range(c, cols): M[r][j] /= pv
            for i in range(rows):
                if i != r and M[i][c] != 0:
                    f = M[i][c]
                    for j in range(c, cols): M[i][j] -= f*M[r][j]
            piv.append(c); r += 1
        return M, piv
    M, piv = rref_over_q(d1)
    rows = len(d1); cols = len(edges)
    # basis of kernel: for each free column, vector with -M[i][c] at pivot rows and 1 at c
    ker_basis = []
    pivset = set(piv)
    for c in range(cols):
        if c not in pivset:
            v = [Fraction(0)]*cols
            v[c] = 1
            for ri, pc in enumerate(piv):
                v[pc] = -M[ri][c]
            ker_basis.append(v)
    # restrict d2 to ker: columns of d2 expressed in the kernel basis
    # d2_ker[k] = coordinates of d2 column k in the kernel basis
    d2k = []
    for k in range(len(faces)):
        col = [Fraction(d2[i][k]) for i in range(len(edges))]
        coords = []
        for v in ker_basis:
            # find coordinates of col in basis (basis is orthonormal-ish: free cols have 1)
            coords.append(col[[c for c in range(cols) if c not in pivset][ker_basis.index(v)]])
        d2k.append(coords)
    # integer matrix: multiply by LCM of denominators
    lcm = 1
    for row in d2k:
        for x in row:
            lcm = lcm * x.denominator // math.gcd(lcm, x.denominator)
    M2 = [[int(x*lcm) for x in row] for row in d2k]
    d2 = [[0]*len(d2k) for _ in range(len(d2k))]
    # transpose: we want columns = faces, rows = ker basis
    for i, row in enumerate(d2k):
        for j, x in enumerate(row):
            d2[j][i] = int(x*lcm)
    if len(ker_basis) == 0:
        snf = []
    else:
        snf = smith_normal_form(d2)
    rank_free = len([d for d in snf if d == 1])
    # H1 = Z^free + sum Z/d for d > 1
    free_rank = len(snf) - len([d for d in snf if d > 1])
    torsion = [d for d in snf if d > 1]
    return dict(free_rank=free_rank, torsion=torsion, snf=snf)

if __name__ == "__main__":
    import json as _json
    checks = {}
    checks['tetrahedron_ball'] = single_tet_ball().full_report()
    checks['two_tet_sphere'] = two_tet_sphere().full_report()
    checks['boundary_four_simplex'] = boundary_four_simplex().full_report()
    for (p,q) in [(2,1),(3,1),(5,2)]:
        tr = bipyramid_lens(p,q)
        rep = tr.full_report()
        rep['homology'] = homology(tr)
        checks[f'bipyramid_L{p}_{q}'] = rep
    print(_json.dumps(checks, indent=1, default=str))
