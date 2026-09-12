#!/usr/bin/env python3
"""Search for solid-torus triangulations (2 or 3 tets) with the manifold-with-boundary
conditions, and report the gluing data of the first (canonical) hit with H_1 = Z."""
import itertools, json, sys
sys.path.insert(0, 'logs/d11')
from proto_check2 import Tri, face_corners, perm_sign_on_face, homology

def odd_perms(face):
    """all odd permutations of the 3 face corners, returned as perm lists [Fin4 -> Fin4]
    (the omitted corner i maps to i)."""
    out = []
    for p in itertools.permutations(face):
        # sign of p as permutation of positions
        s = 0
        for i in range(3):
            for j in range(i+1,3):
                if p[i] > p[j]: s += 1
        if s % 2 == 1:
            perm = [None]*4
            for k, c in enumerate(face):
                perm[c] = p[k]
            out.append(perm)
    return out

def valid_glue(N, pairs):
    """pairs: list of (f1, f2, perm): build glue dict; check consistency."""
    glue = {}
    for (t,i),(t2,i2),perm in pairs:
        glue[(t,i)] = (t2, perm)
        inv = [0]*4
        for j in range(4): inv[perm[j]] = j
        glue[(t2,i2)] = (t, inv)
    tr = Tri(N, glue)
    return tr

def manifold_ok(tr, verbose=False):
    r = tr.full_report()
    if not r['consistent'][0]: return False, 'consistency'
    if not r['orientation_reversing'][0]: return False, 'orientation'
    if r['euler'][0] != 0: return False, 'euler'
    # vertex links
    for vl in r['vertex_links']:
        if not vl['ok']: return False, 'vlink-injectivity'
        if vl['mult'] == [2] and vl['chi_link'] == 2 and vl['link_components'] == 1:
            pass  # sphere
        elif vl['mult'] == [1,2] and vl['chi_link'] == 1 and vl['link_components'] == 1:
            pass  # disk (boundary vertex)
        else:
            return False, f"vlink {vl['mult']} chi {vl['chi_link']} comps {vl['link_components']}"
    # edge links: cycles (interior) or paths (boundary)
    for el in r['edge_links']:
        if not el['ok']: return False, 'elink-injectivity'
        if el['incidence_components'] != 1: return False, 'elink-components'
    # boundary: closed surface chi=0
    b = r['boundary']
    if b['faces'] == 0: return False, 'no-boundary'
    if b['chi'] != 0: return False, f"boundary chi {b['chi']}"
    if b['edge_mult'] != [2]: return False, f"boundary edge mult {b['edge_mult']}"
    if b['components'] != 1: return False, 'boundary components'
    return True, ''

def search(N):
    faces = [(t,i) for t in range(N) for i in range(4)]
    hits = []
    # choose 2 boundary faces
    for bf in itertools.combinations(faces, 2):
        rest = [f for f in faces if f not in bf]
        # matchings of rest into pairs
        def matchings(lst):
            if not lst: yield []
            else:
                a = lst[0]
                for k in range(1, len(lst)):
                    b = lst[k]
                    rem = lst[1:k] + lst[k+1:]
                    for m in matchings(rem):
                        yield [(a,b)] + m
        for m in matchings(rest):
            for perms in itertools.product(*[odd_perms(face_corners(a[1])) for a,_ in m]):
                pairs = []
                bad = False
                for (a,b), perm in zip(m, perms):
                    # orientation-reversing requirement: sign(pi) = (-1)^(i + perm[i] + 1)
                    i = a[1]; i2 = perm[i]
                    if b[1] != i2: bad = True; break
                    want = 1 if (i + i2 + 1) % 2 == 0 else -1
                    s = perm_sign_on_face(i, perm)
                    if s != want: bad = True; break
                    pairs.append((a, b, perm))
                if bad: continue
                tr = valid_glue(N, pairs)
                ok, why = manifold_ok(tr)
                if ok:
                    h = homology(tr)
                    if h['free_rank'] == 1 and h['torsion'] == []:
                        hits.append((pairs, tr, h))
                        return hits  # first hit
    return hits

if __name__ == '__main__':
    for N in (2, 3):
        hits = search(N)
        print(f'=== {N} tets ===')
        if not hits:
            print('no hit')
            continue
        pairs, tr, h = hits[0]
        r = tr.full_report()
        print('pairs:')
        for (t,i),(t2,i2),perm in pairs:
            print(f'  ({t},{i}) ~ ({t2},{i2})  perm={perm}')
        print('euler', r['euler'], 'homology', h)
        print('boundary', r['boundary'])
        print('vlinks:')
        for vl in r['vertex_links']:
            print('  ', vl['vertex'], 'vv/ve/vt', vl['link_vertices'], vl['link_edges'], vl['link_triangles'], 'mult', vl['mult'], 'chi', vl['chi_link'])
        print('elinks:', [(el['faces'], el['tets']) for el in r['edge_links']])
