#!/usr/bin/env python3
"""Pruned search for 3-tet manifolds-with-boundary satisfying all D11 checks.
Finds candidates whose boundary is a closed orientable surface with chi=0 and
computes H_1 to identify the solid torus."""
import itertools, json, sys
sys.path.insert(0, 'logs/d11')
from proto_check2 import Tri, face_corners, perm_sign_on_face, homology

def odd_perms(face, i2):
    out = []
    omitted = [j for j in range(4) if j not in face][0]
    tgt = face_corners(i2)
    for p in itertools.permutations(tgt):
        pi = [tgt.index(p[k]) for k in range(3)]
        s = sum(1 for i in range(3) for j in range(i+1,3) if pi[i] > pi[j])
        if s % 2 == 1:
            perm = [None]*4
            for k, c in enumerate(face): perm[c] = p[k]
            perm[omitted] = i2
            out.append(perm)
    return out

def relaxed_link_check(tr):
    vc = tr.corner_classes(); ec = tr.edge_classes()
    eclass_of = {}
    for rep, mem in ec.items():
        for e in mem: eclass_of[e] = rep
    out = []
    for vrep, vmem in vc.items():
        vset = set(vmem)
        tris = []
        notes = []
        for t in range(tr.N):
            for j in range(4):
                if (t,j) in vset:
                    i = j
                    tri = set()
                    for a,b in itertools.combinations(face_corners(i),2):
                        tri.add(eclass_of[frozenset([(t,a),(t,b)])])
                    if len(tri) != 3: notes.append(f"c{(t,j)}")
                    tris.append(frozenset(tri))
        edge_mult = {}
        for tri in tris:
            for a,b in itertools.combinations(sorted(tri),2):
                edge_mult[(a,b)] = edge_mult.get((a,b),0) + 1
        verts = set()
        for tri in tris: verts |= set(tri)
        chi = len(verts) - len(edge_mult) + len(tris)
        m = sorted(set(edge_mult.values()))
        out.append((vrep, dict(verts=len(verts), edges=len(edge_mult), tris=len(tris),
                               mult=m, chi=chi, ok=(not notes), notes=notes)))
    return out

def distinct_boundary_edges(tr):
    ec = tr.edge_classes()
    eclass_of = {}
    for rep, mem in ec.items():
        for e in mem: eclass_of[e] = rep
    for t in range(tr.N):
        for i in range(4):
            if tr.glue.get((t,i)) is None:
                cls = {eclass_of[frozenset([(t,a),(t,b)])] for a,b in itertools.combinations(face_corners(i),2)}
                if len(cls) != 3: return False
    return True

def boundary_orientable(tr):
    """induced orientations of boundary triangles agree oppositely along each boundary edge."""
    ec = tr.edge_classes()
    eclass_of = {}
    for rep, mem in ec.items():
        for e in mem: eclass_of[e] = rep
    # for each boundary face: the ordered corners (increasing) with sign (-1)^(i)
    # for each boundary edge {a,b}: check the two incident triangles induce opposite orientations
    edge_sgn = {}
    for t in range(tr.N):
        for i in range(4):
            if tr.glue.get((t,i)) is None:
                sgn = 1 if i % 2 == 0 else -1
                corners = sorted(face_corners(i))
                for k in range(3):
                    a = corners[k]; b = corners[(k+1)%3]
                    e = eclass_of[frozenset([(t,a),(t,b)])]
                    o = sgn if (a < b) else -sgn
                    edge_sgn.setdefault(e, []).append(o)
    for e, signs in edge_sgn.items():
        if len(signs) != 2 or signs[0] != -signs[1]:
            return False
    return True

def check_candidate(pairs, N=3):
    glue = {}
    for (t,i),(t2,i2),perm in pairs:
        glue[(t,i)] = (t2, perm)
        inv = [0]*4
        for j in range(4): inv[perm[j]] = j
        glue[(t2,i2)] = (t, inv)
    tr = Tri(N, glue)
    r = tr.full_report()
    if not r['consistent'][0] or r['euler'][0] != 0: return None
    b = r['boundary']
    if b['faces'] == 0 or b['chi'] != 0 or b['edge_mult'] != [2] or b['components'] != 1: return None
    if not distinct_boundary_edges(tr) or not boundary_orientable(tr): return None
    links = relaxed_link_check(tr)
    return (r, b, links, tr)

def enumerate_pairings(N, k_pairs):
    """yield pair-specs [(a,b),...] (face pairs, a<b lexicographically) with parity filters."""
    faces = [(t,i) for t in range(N) for i in range(4)]
    n_boundary = 4*N - 2*k_pairs
    idx = {f:i for i,f in enumerate(faces)}
    # case A: (0,0) boundary
    for bf2 in faces[1:]:
        rest = [f for f in faces if f != (0,0) and f != bf2]
        yield from matchings(rest)
    # case B: (0,0) glued to f > (0,0)
    for f in faces[1:]:
        rest = [g for g in faces if g != (0,0) and g != f]
        for m in matchings(rest):
            yield [((0,0), f)] + m

def matchings(lst):
    if not lst: yield []
    else:
        a = lst[0]
        for k in range(1, len(lst)):
            b = lst[k]
            rem = lst[1:k] + lst[k+1:]
            for m in matchings(rem): yield [(a,b)] + m

def search(N=3, k_pairs=5, max_hits=8):
    hits = []
    count = 0
    t0 = __import__('time').time()
    for spec in enumerate_pairings(N, k_pairs):
        # parity: for each pair (a,b): a[1] + b[1] must be even
        if any((a[1]+b[1]) % 2 == 1 for a,b in spec): continue
        perm_lists = [odd_perms(face_corners(a[1]), b[1]) for a,b in spec]
        for perms in itertools.product(*perm_lists):
            pairs = [(a,b,p) for (a,b),p in zip(spec, perms)]
            count += 1
            res = check_candidate(pairs, N)
            if res is not None:
                r, b, links, tr = res
                h = homology(tr)
                hits.append((pairs, r, b, links, h))
                print(json.dumps(dict(hit=len(hits), count=count,
                      euler=r['euler'][1], boundary=b, H1=h,
                      links=[(l[1]['mult'], l[1]['chi'], l[1]['tris'], l[1]['ok']) for l in links],
                      pairs=[f'({t},{i})~({t2},{i2}) {p}' for (t,i),(t2,i2),p in pairs])), flush=True)
                if len(hits) >= max_hits: return hits
        if count % 100000 == 0:
            print(f'... {count} checked, {__import__("time").time()-t0:.0f}s', flush=True)
    print('done', count, flush=True)
    return hits

if __name__ == '__main__':
    hits = search(3, 5, max_hits=6)
    with open('logs/d11/st_search_results.json', 'w') as fh:
        json.dump([dict(pairs=h[0], euler=h[1]['euler'][1], boundary=h[2], H1=h[4]) for h in hits], fh, indent=1, default=str)
