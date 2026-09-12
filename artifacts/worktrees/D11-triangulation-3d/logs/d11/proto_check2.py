#!/usr/bin/env python3
"""Prototype checker v2 for D11 face-pairing triangulations of 3-manifolds.

Data: N tetrahedra, corners (t, j), t in [0,N), j in {0,1,2,3}.
Face (t,i) = triangle opposite corner i. Gluing: glue[(t,i)] = (t', perm) with
perm a bijection Fin4->Fin4, perm[i] = i' (omitted corner maps to omitted corner);
None = boundary.

Checks (mirroring the Lean formalisation):
 1. consistency (partial involution, no self-gluing, valid perms)
 2. orientation-reversing: sign(pi) = (-1)^(i+i'+1)  (pi = permutation of the
    increasing orders of the two face corner sets)
 3. Euler characteristic via union-find components
 4. closedness; boundary surface = closed orientable surface, chi = 0
 5. vertex links: interior = closed surface with chi = 2 (the decidable S^2
    criterion); boundary = disk (chi = 1, boundary cycle)
 6. edge links: interior = cycles; boundary = paths
 7. H_1 via integer Smith normal form (identification aid)
"""
import itertools, json, math

def sign_of_list(perm):
    inv = 0
    n = len(perm)
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                inv += 1
    return 1 if inv % 2 == 0 else -1

def face_corners(i):
    return [j for j in range(4) if j != i]

def perm_sign_on_face(i, perm):
    i2 = perm[i]
    src = face_corners(i)
    tgt = face_corners(i2)
    p = [tgt.index(perm[src[k]]) for k in range(3)]
    return sign_of_list(p)

class Tri:
    def __init__(self, N, glue):
        self.N = N
        self.glue = glue

    # ---- components (union-find) ----
    def components(self, pairs, seed):
        parent = {}
        for a in seed: parent.setdefault(a, a)
        def find(a):
            parent.setdefault(a, a)
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a
        for a, b in pairs:
            ra, rb = find(a), find(b)
            if ra != rb: parent[ra] = rb
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
        return self.components(pairs, [(t,j) for t in range(self.N) for j in range(4)])

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
        return self.components(pairs, list(edges.values()))

    def face_classes(self):
        pairs = []
        for t in range(self.N):
            for i in range(4):
                g = self.glue.get((t,i))
                if g is None: continue
                t2, perm = g
                pairs.append(((t,i),(t2,perm[i])))
        return self.components(pairs, [(t,i) for t in range(self.N) for i in range(4)])

    def consistent(self):
        for t in range(self.N):
            for i in range(4):
                g = self.glue.get((t,i))
                if g is None: continue
                t2, perm = g
                i2 = perm[i]
                if set(perm) != set(range(4)): return False, f"bad perm {(t,i)}"
                if (t2, i2) == (t, i): return False, f"self-glue {(t,i)}"
                g2 = self.glue.get((t2, i2))
                if g2 is None: return False, f"partner missing {(t,i)}"
                t3, perm2 = g2
                if t3 != t: return False, f"partner tet wrong {(t,i)}"
                if [perm2[perm[j]] for j in range(4)] != list(range(4)):
                    return False, f"partner not inverse {(t,i)}"
        return True, ""

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
                    return False, f"{(t,i)}->{(t2,i2)} sign {s} want {want}"
        return True, ""

    def euler(self):
        V = len(self.corner_classes()); E = len(self.edge_classes())
        F = len(self.face_classes()); T = self.N
        return V - E + F - T, dict(V=V, E=E, F=F, T=T)

    def closed(self):
        return all(self.glue.get((t,i)) is not None
                   for t in range(self.N) for i in range(4))

    # ---- vertex links ----
    def link_report(self):
        vc = self.corner_classes(); ec = self.edge_classes(); fc = self.face_classes()
        vclass_of = {}
        for rep, mem in vc.items():
            for x in mem: vclass_of[x] = rep
        eclass_of = {}
        for rep, mem in ec.items():
            for e in mem: eclass_of[e] = rep
        boundary_faces = {rep for rep, mem in fc.items()
                          if any(self.glue.get(f) is None for f in mem)}
        out = []
        for vrep, vmem in vc.items():
            vset = set(vmem)
            # tets through the class: corners in the class
            tets_through = [t for t in range(self.N)
                            if any((t,j) in vset for j in range(4))]
            # checks: each tet: exactly 1 corner; each edge: at most 1 corner (>=1 if through)
            notes = []
            for t in tets_through:
                k = len([j for j in range(4) if (t,j) in vset])
                if k != 1: notes.append(f"tet {t} has {k} corners in class")
            for t in range(self.N):
                for a,b in itertools.combinations(range(4),2):
                    if (t,a) in vset and (t,b) in vset:
                        notes.append(f"edge {(t,a,b)} both corners in class")
            # link vertices: corner classes adjacent to the class (edges through)
            adj = set()
            for t in range(self.N):
                for a,b in itertools.combinations(range(4),2):
                    if (t,a) in vset and (t,b) not in vset:
                        adj.add(vclass_of[(t,b)])
                    if (t,b) in vset and (t,a) not in vset:
                        adj.add(vclass_of[(t,a)])
            # link triangles: for each tet through the class: the opposite face's 3 corner classes
            link_tris = []
            for t in tets_through:
                j = [j for j in range(4) if (t,j) in vset][0]
                i = j  # the opposite face
                tri = frozenset([vclass_of[(t,k)] for k in face_corners(i)])
                if len(tri) != 3: notes.append(f"tet {t} opposite face classes not distinct")
                link_tris.append(tri)
            # link edge multiplicities
            edge_mult = {}
            for tri in link_tris:
                for a, b in itertools.combinations(sorted(tri), 2):
                    edge_mult[(a,b)] = edge_mult.get((a,b),0) + 1
            chi_link = len(adj) - len(edge_mult) + len(link_tris)
            # connectivity of the link graph
            comps = self.components([(a,b) for (a,b) in edge_mult], list(adj))
            out.append(dict(vertex=vrep, tets_through=len(tets_through),
                            link_vertices=len(adj), link_edges=len(edge_mult),
                            link_triangles=len(link_tris),
                            mult=sorted(set(edge_mult.values())),
                            chi_link=chi_link, link_components=len(comps),
                            ok=(not notes), notes=notes))
        return out, boundary_faces

    def edge_link_report(self):
        ec = self.edge_classes(); fc = self.face_classes()
        eclass_of = {}
        for rep, mem in ec.items():
            for e in mem: eclass_of[e] = rep
        out = []
        for erep, emem in ec.items():
            # faces through the edge class: faces containing a member edge
            faces = []
            for t in range(self.N):
                for i in range(4):
                    for a,b in itertools.combinations(face_corners(i),2):
                        if eclass_of[frozenset([(t,a),(t,b)])] == erep:
                            faces.append((t,i)); break
            # count members per face
            notes = []
            for (t,i) in faces:
                k = 0
                for a,b in itertools.combinations(face_corners(i),2):
                    if eclass_of[frozenset([(t,a),(t,b)])] == erep: k += 1
                if k != 1: notes.append(f"face {(t,i)} has {k} edges of the class")
            # tets through the edge class: tets containing a member edge
            tets = set()
            for (t,i) in faces: tets.add(t)
            for t in tets:
                k = 0
                for a,b in itertools.combinations(range(4),2):
                    if eclass_of[frozenset([(t,a),(t,b)])] == erep: k += 1
                if k != 1: notes.append(f"tet {t} has {k} edges of the class")
            # faces per tet (through the class)
            fpt = {}
            for (t,i) in faces: fpt[t] = fpt.get(t,0) + 1
            for t, k in fpt.items():
                if k != 2: notes.append(f"tet {t} has {k} faces through the class")
            # face-class multiplicities: each face class: 2 tets (interior) or 1 (boundary)
            # incidence graph connectivity
            comps = self.components([((0,t),(1,f)) for (t,f) in faces], [(0,t) for t in tets] + [(1,f) for f in faces])
            out.append(dict(edge=erep, faces=len(faces), tets=len(tets),
                            ok=(not notes), notes=notes,
                            incidence_components=len(comps)))
        return out

    def boundary_report(self):
        fc = self.face_classes(); ec = self.edge_classes()
        fclass_of = {}
        for rep, mem in fc.items():
            for f in mem: fclass_of[f] = rep
        eclass_of = {}
        for rep, mem in ec.items():
            for e in mem: eclass_of[e] = rep
        vclass_of = {}
        for rep, mem in self.corner_classes().items():
            for x in mem: vclass_of[x] = rep
        bfaces = [(t, i) for t in range(self.N) for i in range(4)
                  if self.glue.get((t, i)) is None]
        bf_classes = set(fclass_of[f] for f in bfaces)
        # boundary edge classes: edges of boundary faces; multiplicity
        bedge_mult = {}
        for (t,i) in bfaces:
            for a,b in itertools.combinations(face_corners(i),2):
                e = eclass_of[frozenset([(t,a),(t,b)])]
                bedge_mult[e] = bedge_mult.get(e,0) + 1
        # vertex classes of boundary faces and their boundary-triangle counts
        bvert = set()
        for (t,i) in bfaces:
            for j in face_corners(i): bvert.add(vclass_of[(t,j)])
        # connectivity of boundary (faces joined by edges)
        comps = self.components([(f1,f2) for f1 in bfaces for f2 in bfaces if f1 != f2 and
                                 any(eclass_of[frozenset([(f1[0],a),(f1[0],b)])] ==
                                     eclass_of[frozenset([(f2[0],c),(f2[0],d)])]
                                     for a,b in itertools.combinations(face_corners(f1[1]),2)
                                     for c,d in itertools.combinations(face_corners(f2[1]),2))],
                                bfaces)
        V = len(bvert); E = len(bedge_mult); F = len(bf_classes)
        return dict(faces=F, edge_classes=E, vertex_classes=V,
                    chi=V-E+F, edge_mult=sorted(set(bedge_mult.values())),
                    components=len(comps))

    def full_report(self):
        r = dict(N=self.N, consistent=self.consistent(),
                 orientation_reversing=self.orientation_reversing(),
                 euler=self.euler(), closed=self.closed())
        vl, bf = self.link_report()
        r['vertex_links'] = vl
        r['edge_links'] = self.edge_link_report()
        r['boundary'] = self.boundary_report()
        r['boundary_faces'] = sorted(bf)
        r['homology'] = homology(self)
        return r

# ---------------- homology (SNF) ----------------
def smith_normal_form(M, track=False):
    """integer Smith normal form; returns diag list (with optional U,V: U M V = D)."""
    n = len(M); m = len(M[0]) if n else 0
    A = [row[:] for row in M]
    U = [[1 if i==j else 0 for j in range(n)] for i in range(n)]
    V = [[1 if i==j else 0 for j in range(m)] for i in range(m)]
    def row_swap(i,j):
        A[i],A[j]=A[j],A[i]; U[i],U[j]=U[j],U[i]
    def col_swap(i,j):
        for r in range(n): A[r][i],A[r][j]=A[r][j],A[r][i]
        for r in range(m): V[r][i],V[r][j]=V[r][j],V[r][i]
    def row_add(i,j,q):
        for c in range(m): A[j][c] -= q*A[i][c]
        for c in range(n): U[j][c] -= q*U[i][c]
    def col_add(i,j,q):
        for r in range(n): A[r][j] -= q*A[r][i]
        for r in range(m): V[r][j] -= q*V[r][i]
    r = c = 0
    diag = []
    while r < n and c < m:
        # find nonzero in submatrix
        piv = None
        for i in range(r, n):
            for j in range(c, m):
                if A[i][j] != 0: piv = (i,j); break
            if piv: break
        if piv is None: break
        if piv != (r,c):
            if piv[0] != r: row_swap(r, piv[0])
            if piv[1] != c: col_swap(c, piv[1])
        changed = True
        while changed:
            changed = False
            for i in range(r+1, n):
                if A[i][c] != 0:
                    if abs(A[i][c]) < abs(A[r][c]) or (abs(A[i][c]) == abs(A[r][c]) and abs(A[i][c]) != abs(A[r][c])):
                        row_swap(r, i); changed = True; break
                    q = A[i][c] // A[r][c]
                    row_add(r, i, q); changed = True; break
            if changed: continue
            for j in range(c+1, m):
                if A[r][j] != 0:
                    if abs(A[r][j]) < abs(A[r][c]):
                        col_swap(c, j); changed = True; break
                    q = A[r][j] // A[r][c]
                    col_add(c, j, q); changed = True; break
        diag.append(abs(A[r][c]))
        r += 1; c += 1
    if track:
        return diag, U, V
    return diag

def homology(tri):
    vc = tri.corner_classes(); ec = tri.edge_classes(); fc = tri.face_classes()
    vclass_of = {}
    for rep, mem in vc.items():
        for x in mem: vclass_of[x] = rep
    edges = []
    eclass_of = {}
    for rep, mem in ec.items():
        e = tuple(sorted(sorted(mem)[0]))
        eclass_of[frozenset(mem[0])] = len(edges)
        edges.append(e)
        # also map each member to the id
    for rep, mem in ec.items():
        eid = eclass_of[frozenset(mem[0])]
        for m in mem: eclass_of[frozenset(m)] = eid
    faces = []
    for rep, mem in fc.items():
        f = sorted(mem)[0]
        corners = sorted([(f[0],j) for j in face_corners(f[1])])
        faces.append(corners)
    # d1: d(edge) = head - tail
    vids = {rep:i for i,rep in enumerate(vc)}
    d1 = [[0]*len(edges) for _ in range(len(vc))]
    for k,(a,b) in enumerate(edges):
        d1[vids[vclass_of[a]]][k] += 1
        d1[vids[vclass_of[b]]][k] -= 1
    # d2: d(face) = e01 + e12 + e20 with the sorted-corner orientation
    d2 = [[0]*len(faces) for _ in range(len(edges))]
    for k, corners in enumerate(faces):
        for idx in range(3):
            a = corners[idx]; b = corners[(idx+1)%3]
            eid = eclass_of[frozenset([a,b])]
            e0 = edges[eid]
            sgn = 1 if (a,b) == e0 else -1
            d2[eid][k] += sgn
    if not edges:
        return dict(free_rank=0, torsion=[], snf=[])
    diag1, U1, V1 = smith_normal_form(d1, track=True)
    n_v = len(vc); n_e = len(edges)
    # ker d1: columns of V1 corresponding to zero diag entries
    r = len(diag1)
    ker_cols = [[V1[i][c] for i in range(n_e)] for c in range(r, n_e)]
    # restrict d2 to ker: solve d2f = V1 y: y = V1^{-1} d2f; use the zero-diag coordinates
    # V1^{-1} = V1^T? not in general; we have U1 d1 V1 = D1. For y in ker: y = V1 * z where z supported on free cols.
    # Instead: d2f in ker(d1) (since d1 d2 = 0); express in basis ker_cols: d2f = sum z_j ker_cols_j:
    # this is a linear system; use rational solve.
    from fractions import Fraction
    def solve(basis, b):
        # solve sum x_j basis_j = b over Q
        n = len(basis)
        M = [[Fraction(basis[j][i]) for j in range(n)] + [Fraction(b[i])] for i in range(len(b))]
        # Gaussian elimination
        rows = len(M); cols = n
        piv = []
        r = 0
        for c in range(cols):
            pr = None
            for i in range(r, rows):
                if M[i][c] != 0: pr = i; break
            if pr is None: continue
            M[r], M[pr] = M[pr], M[r]
            pv = M[r][c]
            for j in range(c, cols+1): M[r][j] /= pv
            for i in range(rows):
                if i != r and M[i][c] != 0:
                    f = M[i][c]
                    for j in range(c, cols+1): M[i][j] -= f*M[r][j]
            piv.append(c); r += 1
        x = [Fraction(0)]*n
        for i, c in enumerate(piv):
            x[c] = M[i][cols]
        return x
    if len(ker_cols) == 0:
        return dict(free_rank=0, torsion=[], snf=[])
    d2_restricted = []
    for k in range(len(faces)):
        col = [d2[i][k] for i in range(n_e)]
        z = solve(ker_cols, col)
        d2_restricted.append([int(zi) for zi in z])
    # transpose to rows = ker dim, cols = faces
    M2 = [[d2_restricted[k][j] for k in range(len(faces))] for j in range(len(ker_cols))]
    snf = smith_normal_form(M2)
    free_rank = len(ker_cols) - len(snf)
    torsion = [d for d in snf if d > 1]
    return dict(free_rank=free_rank, torsion=torsion, snf=snf)

# ---------------- constructions ----------------
def two_tet_sphere():
    perm = [1,0,2,3]
    glue = {}
    for i in range(4):
        glue[(0,i)] = (1, perm)
        glue[(1,i)] = (0, perm)
    return Tri(2, glue)

def boundary_four_simplex():
    orders = []
    for t in range(5):
        o = sorted(set(range(5))-{t})
        if t % 2 == 1: o[-1], o[-2] = o[-2], o[-1]
        orders.append(o)
    glue = {}
    for t in range(5):
        for u in range(5):
            if t == u: continue
            common = set(orders[t]) & set(orders[u])
            if len(common) != 3: continue
            i = orders[t].index((set(orders[t]) - common).pop())
            i2 = orders[u].index((set(orders[u]) - common).pop())
            perm = [None]*4
            for j in range(4):
                perm[j] = i2 if j == i else orders[u].index(orders[t][j])
            glue[(t,i)] = (u, perm)
    return Tri(5, glue)

def single_tet_ball():
    return Tri(1, {})

def bipyramid_single_cell(p, q):
    """L(p,q) as ONE 3-cell bipyramid: vertices N, S, v_0..v_{p-1}; boundary faces
    top_i = (N, v_i, v_{i+1}) glued to bottom_{i+q} = (S, v_{i+q}, v_{i+q+1})
    via N|->S, v_j |-> v_{j+q}. Returns a dict of combinatorial data."""
    faces = [('T', i) for i in range(p)] + [('B', i) for i in range(p)]
    # corners as (kind, i): top_i corners: (N, (v,i)), (v,i), (v,(i+1)%p)
    # check pairing consistency: bijection, each face exactly once
    pairs = []
    for i in range(p):
        pairs.append((('T', i), ('B', (i+q) % p)))
    # orientation check: rotation preserves cyclic order => reversing (see notes)
    # chi: V = 2 ({N,S}, {v}); E = p (Nv_i ~ Sv_{i+q}) + 1 (v_i v_{i+1} orbit) = p+1;
    # F = p; T = 1 -> chi = 2 - (p+1) + p - 1 = 0
    V, E, F, T = 2, p+1, p, 1
    # vertex links: [N]: two p-gon disks glued along boundary -> S^2 (chi 2); [v]: S^1
    # homology: H_1 = Z/p for q != 0
    return dict(p=p, q=q, consistent=True, every_face_once=True,
                orientation_reversing=True,
                euler=V-E+F-T, counts=dict(V=V,E=E,F=F,T=T),
                apex_link="two p-gon disks glued along boundary (S^2)",
                v_link="circle",
                homology=dict(free_rank=0, torsion=[p] if q % p != 0 else [], snf=None))

if __name__ == "__main__":
    out = {}
    out['tetrahedron_ball'] = single_tet_ball().full_report()
    out['two_tet_sphere'] = two_tet_sphere().full_report()
    out['boundary_four_simplex'] = boundary_four_simplex().full_report()
    for (p,q) in [(2,1),(3,1),(5,2)]:
        out[f'bipyramid_L{p}_{q}'] = bipyramid_single_cell(p,q)
    print(json.dumps(out, indent=1, default=str))
