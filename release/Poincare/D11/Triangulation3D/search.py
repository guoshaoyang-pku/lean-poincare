#!/usr/bin/env python3
"""Search for valid generalized triangulations of 3-manifolds.

Mirrors the Lean checker in DeltaComplex.lean (pair-based links).
Used only to discover gluing data; Lean `decide` is the source of truth.
"""
from itertools import permutations, combinations, product

def swap(a, b):
    p = list(range(4))
    p[a], p[b] = p[b], p[a]
    return tuple(p)

def compose(p, q):
    return tuple(p[q[i]] for i in range(4))

def invert(p):
    r = [0]*4
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)

IDENTITY = (0, 1, 2, 3)

def sign3(seq):
    # sign of permutation of a 3-element list of distinct Fin4 values, by inversions
    inv = 0
    for i in range(3):
        for j in range(i+1, 3):
            if seq[i] > seq[j]:
                inv += 1
    return 1 if inv % 2 == 0 else -1

def face_corners(i):
    return [j for j in range(4) if j != i]

def position_in_face(i, c):
    # position of corner c (c != i) in increasing list of corners of face opposite i
    return sorted(face_corners(i)).index(c)

def face_perm_sign(i, g):
    # sign of permutation induced by g on face opposite i, mapped into face opposite g(i)
    target = g[i]
    positions = [position_in_face(target, g[j]) for j in sorted(face_corners(i))]
    return sign3(positions)

def is_orientation_reversing(i, g):
    return face_perm_sign(i, g) == ((-1) ** (i + g[i] + 1))

class Tri:
    def __init__(self, n, glue):
        # glue: dict (t, i) -> (t', g) or None
        self.n = n
        self.glue = glue

    def consistent(self):
        for t in range(self.n):
            for i in range(4):
                g = self.glue.get((t, i))
                if g is None:
                    continue
                t2, perm = g
                if self.glue.get((t2, perm[i])) != (t, invert(perm)):
                    return False
                if (t2, perm[i]) == (t, i):
                    return False
        return True

    def orientation_reversing(self):
        for t in range(self.n):
            for i in range(4):
                g = self.glue.get((t, i))
                if g is None:
                    continue
                t2, perm = g
                if not is_orientation_reversing(i, perm):
                    return False
        return True

    def orientable(self):
        # exists sigma : tets -> {+-1} with sigma_t sigma_t' = (-1)^(i+i'+1) sign(pi)
        import itertools
        n = self.n
        for sigma in itertools.product([1, -1], repeat=n):
            ok = True
            for t in range(n):
                for i in range(4):
                    g = self.glue.get((t, i))
                    if g is None:
                        continue
                    t2, perm = g
                    c = ((-1) ** (i + perm[i] + 1)) * face_perm_sign(i, perm)
                    if sigma[t] * sigma[t2] != c:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                return True
        return False

    def closed(self):
        return all(self.glue.get((t, i)) is not None for t in range(self.n) for i in range(4))

    def _uf_classes(self, seed, pairs):
        parent = {}
        def find(x):
            parent.setdefault(x, x)
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        def union(x, y):
            rx, ry = find(x), find(y)
            if rx != ry:
                parent[rx] = ry
        seedset = set(seed)
        for s in seed:
            parent.setdefault(s, s)
        for a, b in pairs:
            if a in seedset and b in seedset:
                parent.setdefault(a, a)
                parent.setdefault(b, b)
                union(a, b)
        classes = {}
        for x in seedset:
            classes.setdefault(find(x), []).append(x)
        return [tuple(sorted(c)) for c in classes.values()]

    def corner_classes(self):
        seed = [(t, j) for t in range(self.n) for j in range(4)]
        pairs = []
        for t in range(self.n):
            for i in range(4):
                g = self.glue.get((t, i))
                if g is None:
                    continue
                t2, perm = g
                for j in range(4):
                    if j != i:
                        pairs.append(((t, j), (t2, perm[j])))
        return self._uf_classes(seed, pairs)

    def edge_classes(self):
        seed = []
        for t in range(self.n):
            for a in range(4):
                for b in range(a+1, 4):
                    seed.append((t, a, b))
        pairs = []
        for t in range(self.n):
            for i in range(4):
                g = self.glue.get((t, i))
                if g is None:
                    continue
                t2, perm = g
                for a in range(4):
                    for b in range(a+1, 4):
                        if a != i and b != i:
                            x = (t, a, b)
                            pa, pb = perm[a], perm[b]
                            y = (t2, min(pa, pb), max(pa, pb))
                            pairs.append((x, y))
        return self._uf_classes(seed, pairs)

    def face_classes(self):
        seed = [(t, i) for t in range(self.n) for i in range(4)]
        pairs = []
        for t in range(self.n):
            for i in range(4):
                g = self.glue.get((t, i))
                if g is None:
                    continue
                t2, perm = g
                pairs.append(((t, i), (t2, perm[i])))
        return self._uf_classes(seed, pairs)

    def fvector(self):
        return (len(self.corner_classes()), len(self.edge_classes()),
                len(self.face_classes()), self.n)

    def boundary_faces(self):
        return [(t, i) for t in range(self.n) for i in range(4)
                if self.glue.get((t, i)) is None]

    # ---------- pair-based vertex links ----------

    def _vlink_vtx_seed(self, C):
        # (corner c, edge endpoint k) pairs with c in C, k != c.j
        out = []
        for t in range(self.n):
            for j in range(4):
                if (t, j) not in C:
                    continue
                for k in range(4):
                    if k != j:
                        out.append((t, j, k))
        return out

    def _vlink_vtx_pairs(self):
        pairs = []
        for t in range(self.n):
            for i in range(4):
                g = self.glue.get((t, i))
                if g is None:
                    continue
                t2, perm = g
                for j in range(4):
                    if j == i:
                        continue
                    for k in range(4):
                        if k == i or k == j:
                            continue
                        pairs.append(((t, j, k), (t2, perm[j], perm[k])))
        return pairs

    def _vlink_edge_seed(self, C):
        # (face (t,i), corner j of face) with corner (t,j) in C
        out = []
        for t in range(self.n):
            for i in range(4):
                for j in range(4):
                    if j != i and (t, j) in C:
                        out.append((t, i, j))
        return out

    def _vlink_edge_pairs(self):
        pairs = []
        for t in range(self.n):
            for i in range(4):
                g = self.glue.get((t, i))
                if g is None:
                    continue
                t2, perm = g
                for j in range(4):
                    if j != i:
                        pairs.append(((t, i, j), (t2, perm[i], perm[j])))
        return pairs

    def vertex_link(self, C):
        """Return (vtx_classes, edge_classes, faces) of the link of vertex class C."""
        vseed = self._vlink_vtx_seed(C)
        vpairs = self._vlink_vtx_pairs()
        vcls = {tuple(sorted(c)): i for i, c in enumerate(self._uf_classes(vseed, vpairs))}
        def vclass(x):
            for c in self._uf_classes(vseed, vpairs):
                if x in c:
                    return tuple(sorted(c))
        eseed = self._vlink_edge_seed(C)
        epairs = self._vlink_edge_pairs()
        ecls_raw = self._uf_classes(eseed, epairs)
        def eclass(x):
            for c in ecls_raw:
                if x in c:
                    return tuple(sorted(c))
        faces = [ (t, j) for t in range(self.n) for j in range(4) if (t, j) in C ]
        return vcls, ecls_raw, faces, eclass

    def vertex_link_ok(self, C, want):
        """want: 'sphere' or 'disk'"""
        vseed = self._vlink_vtx_seed(C)
        vpairs = self._vlink_vtx_pairs()
        vcls, ecls, faces, eclass = self.vertex_link(C)
        # each face: 3 distinct edge classes and 3 distinct vertex classes
        for (t, j) in faces:
            e3 = [eclass((t, i, j)) for i in range(4) if i != j]
            if len(set(e3)) != 3:
                return False
            # recompute vertex classes of the 3 corners' edges
            v3 = []
            for k in range(4):
                if k != j:
                    for c in self._uf_classes(vseed, vpairs):
                        if (t, j, k) in c:
                            v3.append(tuple(sorted(c)))
            if len(set(v3)) != 3:
                return False
        # incidence of each edge class: number of faces adjacent
        for ec in ecls:
            inc = 0
            for (t, j) in faces:
                for i in range(4):
                    if i != j and eclass((t, i, j)) == ec:
                        inc += 1
            if want == 'sphere' and inc != 2:
                return False
            if want == 'disk' and inc > 2:
                return False
        chi = len(vcls) - len(ecls) + len(faces)
        if want == 'sphere':
            if chi != 2:
                return False
        else:
            if chi != 1:
                return False
        # connectivity via shared edge classes
        # union-find on faces with pairs sharing an edge class
        fseed = faces
        fpairs = []
        for a in faces:
            for b in faces:
                if a == b:
                    continue
                for ea in [eclass((a[0], i, a[1])) for i in range(4) if i != a[1]]:
                    for eb in [eclass((b[0], i, b[1])) for i in range(4) if i != b[1]]:
                        if ea == eb:
                            fpairs.append((a, b))
        comps = self._uf_classes(fseed, fpairs)
        if len(comps) != 1:
            return False
        if want == 'disk':
            # boundary cycle: edge classes with incidence 1 form a single cycle:
            ones = []
            for ec in ecls:
                inc = 0
                for (t, j) in faces:
                    for i in range(4):
                        if i != j and eclass((t, i, j)) == ec:
                            inc += 1
                if inc == 1:
                    ones.append(ec)
            if not ones:
                return False
            # endpoints of each one-edge: its single occurrence (t,i,j) -> vertex classes of (t,j,k1),(t,j,k2)
            def vclass_of(x):
                for c in self._uf_classes(vseed, vpairs):
                    if x in c:
                        return tuple(sorted(c))
            epairs_ones = []
            vused = set()
            for ec in ones:
                occ = None
                for (t, j) in faces:
                    for i in range(4):
                        if i != j and eclass((t, i, j)) == ec:
                            occ = (t, i, j)
                (t, i, j) = occ
                ks = [k for k in range(4) if k != i and k != j]
                v1 = vclass_of((t, j, ks[0]))
                v2 = vclass_of((t, j, ks[1]))
                epairs_ones.append((v1, v2))
                vused.add(v1)
                vused.add(v2)
            # each boundary vertex class has exactly 2 one-edge endpoints
            deg = {}
            for v1, v2 in epairs_ones:
                deg[v1] = deg.get(v1, 0) + 1
                deg[v2] = deg.get(v2, 0) + 1
            for v, d in deg.items():
                if d != 2:
                    return False
            # boundary cycle connected
            comps2 = self._uf_classes(list(vused), epairs_ones)
            if len(comps2) != 1:
                return False
        return True

    # ---------- pair-based edge links ----------

    def _face_occ_seed(self, E):
        out = []
        for t in range(self.n):
            for a in range(4):
                for b in range(a+1, 4):
                    if (t, a, b) not in E:
                        continue
                    for i in range(4):
                        if i != a and i != b:
                            out.append((t, i, a, b))
        return out

    def _face_occ_pairs(self):
        pairs = []
        for t in range(self.n):
            for i in range(4):
                g = self.glue.get((t, i))
                if g is None:
                    continue
                t2, perm = g
                for a in range(4):
                    for b in range(a+1, 4):
                        if a != i and b != i:
                            pa, pb = perm[a], perm[b]
                            x = (t, i, a, b)
                            y = (t2, perm[i], min(pa, pb), max(pa, pb))
                            pairs.append((x, y))
        return pairs

    def _arc_seed(self, E):
        out = []
        for t in range(self.n):
            for a in range(4):
                for b in range(a+1, 4):
                    if (t, a, b) in E:
                        out.append((t, a, b))
        return out

    def _arc_pairs(self):
        pairs = []
        for t in range(self.n):
            for i in range(4):
                g = self.glue.get((t, i))
                if g is None:
                    continue
                t2, perm = g
                for a in range(4):
                    for b in range(a+1, 4):
                        if a != i and b != i:
                            pa, pb = perm[a], perm[b]
                            pairs.append(((t, a, b), (t2, min(pa, pb), max(pa, pb))))
        return pairs

    def edge_link(self, E, want):
        fseed = self._face_occ_seed(E)
        fpairs = self._face_occ_pairs()
        fcls = self._uf_classes(fseed, fpairs)
        def fclass(x):
            for c in fcls:
                if x in c:
                    return tuple(sorted(c))
        occs = self._arc_seed(E)  # each occurrence = one edge of the link graph
        # degree of each face class = number of half-edges (occurrence, adjacent face-occ)
        deg = {}
        for f in fcls:
            deg[tuple(sorted(f))] = 0
        for (t, a, b) in occs:
            for i in range(4):
                if i != a and i != b:
                    fc = fclass((t, i, a, b))
                    deg[fc] = deg.get(fc, 0) + 1
        if set(fcls) != set(deg.keys()):
            return False
        if want == 'cycle':
            if any(d != 2 for d in deg.values()):
                return False
            if len(fcls) - len(occs) != 0:
                return False
        else:
            ones = [f for f, d in deg.items() if d == 1]
            if len(ones) != 2:
                return False
            if any(d not in (1, 2) for d in deg.values()):
                return False
            if len(fcls) - len(occs) != 1:
                return False
        # connected: edges = occurrences connecting their 2 endpoint face classes
        pairs = []
        for (t, a, b) in occs:
            ks = [i for i in range(4) if i != a and i != b]
            f1 = fclass((t, ks[0], a, b))
            f2 = fclass((t, ks[1], a, b))
            pairs.append((f1, f2))
        comps = self._uf_classes(list(fcls), pairs)
        return len(comps) == 1

    def boundary_edge_class(self, E):
        bfs = self.boundary_faces()
        for (t, i) in bfs:
            for a in range(4):
                for b in range(a+1, 4):
                    if a != i and b != i and (t, a, b) in E:
                        return True
        return False

    def manifold(self, with_boundary=True):
        if not self.consistent() or not self.orientable():
            return False
        if not with_boundary:
            if not self.closed():
                return False
        vcls = self.corner_classes()
        ecls = self.edge_classes()
        for C in vcls:
            is_bd = any((t, j) in C and (t, i) in self.boundary_faces()
                        for (t, j) in C for i in range(4) if i != j
                        for _ in [0] if (t, i) in self.boundary_faces())
            # simpler: corner (t,j) in C is on a boundary face (t,i), i != j
            is_bd = False
            bfs = self.boundary_faces()
            for (t, j) in C:
                for (t2, i) in bfs:
                    if t2 == t and i != j:
                        is_bd = True
            if with_boundary:
                want = 'disk' if is_bd else 'sphere'
                if not self.vertex_link_ok(C, want):
                    return False
            else:
                if not self.vertex_link_ok(C, 'sphere'):
                    return False
        for E in ecls:
            bd = self.boundary_edge_class(E)
            want = 'path' if bd else 'cycle'
            if not self.edge_link(E, want):
                return False
        return True

    def euler(self):
        v, e, f, t = self.fvector()
        return v - e + f - t

    def report(self):
        print("  f-vector:", self.fvector(), " chi =", self.euler())
        print("  consistent:", self.consistent(),
              " orient-rev:", self.orientation_reversing(),
              " closed:", self.closed())
        print("  manifold-with-bdry:", self.manifold(True))
        if self.closed():
            print("  closed manifold:", self.manifold(False))


# ---------------- enumeration helpers ----------------

def all_bijections_fixing(i, i2, orient_rev_only=True):
    """All corner bijections g with g[i]=i2 (optionally orientation-reversing)."""
    out = []
    for perm in permutations(range(4)):
        if perm[i] != i2:
            continue
        if orient_rev_only and not is_orientation_reversing(i, perm):
            continue
        out.append(perm)
    return out


def search_two_tet():
    faces = [(t, i) for t in range(2) for i in range(4)]
    results = []
    # perfect matchings of 8 faces
    def matchings(rem):
        if not rem:
            yield []
            return
        f = rem[0]
        for idx in range(1, len(rem)):
            f2 = rem[idx]
            rest = rem[1:idx] + rem[idx+1:]
            for m in matchings(rest):
                yield [(f, f2)] + m
    count = 0
    for m in matchings(faces):
        # choose orientation-reversing bijections for each pair
        choices = []
        for (t1, i1), (t2, i2) in m:
            opts = all_bijections_fixing(i1, i2, False)
            if not opts:
                choices = None
                break
            choices.append(opts)
        if choices is None:
            continue
        for pick in product(*choices):
            glue = {}
            for ((t1, i1), (t2, i2)), g in zip(m, pick):
                glue[(t1, i1)] = (t2, g)
                glue[(t2, i2)] = (t1, invert(g))
            tri = Tri(2, glue)
            count += 1
            if tri.consistent() and tri.orientable() and tri.manifold(False):
                results.append((glue, tri.fvector()))
    print("2-tet search: cases checked:", count)
    seen = set()
    for glue, fv in results:
        if fv in seen:
            continue
        seen.add(fv)
        print("FOUND 2-tet closed manifold with f-vector", fv)
        for k in sorted(glue):
            if glue[k] is not None:
                t2, g = glue[k]
                print("   glue", k, "->", t2, "perm", g)


def search_one_tet():
    faces = [(0, i) for i in range(4)]
    results = []
    def matchings(rem):
        if not rem:
            yield []
            return
        f = rem[0]
        for idx in range(1, len(rem)):
            f2 = rem[idx]
            rest = rem[1:idx] + rem[idx+1:]
            for m in matchings(rest):
                yield [(f, f2)] + m
    for m in matchings(faces):
        choices = []
        for (t1, i1), (t2, i2) in m:
            opts = all_bijections_fixing(i1, i2, False)
            if not opts:
                choices = None
                break
            choices.append(opts)
        if choices is None:
            continue
        for pick in product(*choices):
            glue = {}
            for ((t1, i1), (t2, i2)), g in zip(m, pick):
                glue[(t1, i1)] = (t2, g)
                glue[(t2, i2)] = (t1, invert(g))
            tri = Tri(1, glue)
            if tri.consistent() and tri.orientable() and tri.manifold(False):
                results.append((glue, tri.fvector()))
    print("1-tet search done; found", len(results), "manifolds")
    for glue, fv in results:
        print("FOUND 1-tet closed manifold with f-vector", fv)
        for k in sorted(glue):
            t2, g = glue[k]
            print("   glue", k, "->", t2, "perm", g)


def search_bipyramid(p, q):
    """p tets t_i = [N,S,w_i,w_{i+1}] (corners N=0,S=1,w_i=2,w_{i+1}=3).
    side faces: (t_i,2)=(N,S,w_{i+1}) ~ (t_{i+1},3); tops: (t_i,1) ~ (t_{i+q},0)."""
    results = []
    side_maps = [swap(2, 3), compose(swap(0, 1), swap(2, 3))]
    top_maps = []
    # top: face 1 of t_i -> face 0 of t_{i+q}: g[1]=0; options: g = swap01 or swap01*swap23
    top_maps.append(swap(0, 1))
    top_maps.append(compose(swap(0, 1), swap(2, 3)))
    for side_map in side_maps:
        for top_map in top_maps:
            for bot_map in top_maps:
                glue = {}
                for i in range(p):
                    glue[(i, 2)] = ((i + 1) % p, side_map)
                    glue[((i + 1) % p, 3)] = (i, invert(side_map))
                    glue[(i, 1)] = ((i + q) % p, top_map)
                    glue[((i + q) % p, 0)] = (i, invert(top_map))
                tri = Tri(p, glue)
                if tri.consistent() and tri.orientable() and tri.manifold(False):
                    results.append((glue, tri.fvector()))
    print(f"bipyramid p={p} q={q}: found {len(results)} manifolds")
    for glue, fv in results:
        print("FOUND with f-vector", fv)
        for k in sorted(glue):
            t2, g = glue[k]
            print("   glue", k, "->", t2, "perm", g)


def check_solid_torus():
    # tets: t0=[a,b,c,c'], t1=[a,b,c',b'], t2=[a,c',a',b']  corners 0,1,2,3 in that order
    glue = {}
    glue[(0, 2)] = (1, swap(2, 3))   # t0.(a,b,c') ~ t1.(a,b,c')
    glue[(1, 3)] = (0, swap(2, 3))
    glue[(0, 3)] = (2, swap(0, 3))   # t0.(a,b,c) ~ t2.(a',b',c')
    glue[(2, 0)] = (0, swap(0, 3))
    glue[(1, 1)] = (2, swap(1, 2))   # t1.(a,c',b') ~ t2.(a,c',b')
    glue[(2, 2)] = (1, swap(1, 2))
    tri = Tri(3, glue)
    tri.report()
    # boundary chi
    bfs = tri.boundary_faces()
    print("  boundary faces:", bfs)
    v = set()
    e = set()
    for (t, i) in bfs:
        for a in range(4):
            if a != i:
                for c in tri.corner_classes():
                    if (t, a) in c:
                        v.add(c)
        for a in range(4):
            for b in range(a+1, 4):
                if a != i and b != i:
                    for c in tri.edge_classes():
                        if (t, a, b) in c:
                            e.add(c)
    print("  boundary chi =", len(v) - len(e) + len(bfs))


def check_ball():
    tri = Tri(1, {})
    tri.report()


if __name__ == "__main__":
    import sys
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("all", "ball"):
        print("== ball (1 tet, no gluings) ==")
        check_ball()
    if which in ("all", "1tet"):
        print("== 1-tet closed search ==")
        search_one_tet()
    if which in ("all", "2tet"):
        print("== 2-tet closed search ==")
        search_two_tet()
    if which in ("all", "bipyr"):
        for p, q in [(2, 1), (3, 1), (3, 2)]:
            search_bipyramid(p, q)
    if which in ("all", "torus"):
        print("== solid torus (3 tet) ==")
        check_solid_torus()
