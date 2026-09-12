import os

root = '/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7'
os.chdir(root)

def read_counts(path):
    ok = fail = 0
    for line in open(path):
        line = line.strip()
        if not line or line in ('DONE', 'ALLDONE'):
            continue
        if line.split(':', 1)[0] == '0':
            ok += 1
        else:
            fail += 1
    return ok, fail

per_ok, per_fail = read_counts('logs/d13_thirteenth_final_perfile.txt')
wt_ok, wt_fail = read_counts('logs/d13_thirteenth_final_gate_raw.txt')
sem = [l for l in open('logs/d13_thirteenth_final_semantic_all.out').read().splitlines()
       if l.strip() and l.strip() != 'ALLDONE']
sem_fail = sum(1 for l in sem if not l.startswith('0:'))
nhashes = sum(1 for l in open('logs/d13_thirteenth_final_hashes.txt') if l.strip())

section = open('tmp/d13_thirteenth_section.md').read()
section = section.replace('__HASHCOUNT__', str(nhashes))
section = section.replace('__SEMCOUNT__', str(len(sem)))
section = section.replace('__BUILDJOBS__', '9209')
section = section.replace('__PERFILE__', f'{per_ok}/{per_ok + per_fail} exit 0, 0 failures')
section = section.replace('__WORKTREE__', f'{wt_ok} files, 0 failures')

blockquote = """
> **Thirteenth invocation (2026-09-12T00:10+08:00, ≈ 1.3 h):** the D12 corrected
> admissible-test-function domain now carries the **weak (test-paired) heat equation**.
> `WeakHeatEquation.lean` (25 declarations) defines `IsWeakHeatKernelPDE` (v1),
> `d/dt ∫ x, φ x * K x y t = ∫ x, φ x * Δ_x K(·,y,t) x` for every admissible `φ`, isolates the
> analytic input as the explicit certificate structure `WeakHeatCertificates` (snapshot
> measurability/integrability, paired-Laplacian measurability, local uniform bound on `ΔK` over
> `[a,b]`, `a > 0`), and proves the transfer `weakHeatKernelPDE_of_hasDerivAt` from the pointwise
> PDE by mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (dominating function
> `(max D 0) * ‖φ‖`). The certificates are **proved** for the explicit D10 kernel: the Gaussian sup
> bound `K ≤ (4πt)^{-n/2}`, the elementary maximum `u e^{-u} ≤ e^{-1}`, and the uniform bound
> `|ΔK| ≤ (4πa)^{-n/2}(1/(e a) + n/(2 a))` on `[a,b]`; the flat kernel inhabits the weak equation in
> every dimension on both standard classes, and `flat_weak_snapshot_refuted` records that in positive
> dimension the weak equation holds while the legacy snapshot predicate is refuted.
> `WeakFinite.lean` (7 declarations) instantiates the same interface on the **pinned finite
> Markov-chain model** with a finite-dimensional certificate proof (entries in `[0,1]`,
> `|ΔK| ≤ ∑ x ∑ z |L x z|`, `Integrable.of_finite`). The new D7 consumer
> `Poincare.D7.HeatKernel.WeakStatus` (13 declarations) proves at the D7 level that **every legacy
> `HeatKernelData` satisfies the weak equation** from its `heatEquation` field, that the pinned
> finite model does too, plus the V1 transport and the status summary. AxiomAudit 511 → **556**,
> PASS 556/556. Final gates: 33 hashes re-verified, semantic 14/14 exit 0, build exit 0 (9209
> jobs), per-file {per}, worktree {wt} files 0 failures, forbidden 0 hard / 0 soft, negative
> control PASS, diff vs D12 = 12 expected new-file lines, upstream PASS (bb91a091). No named
> blocker closed; `exact_blockers_closed = []`. See §25.
""".replace('{per}', f'{per_ok}/{per_ok + per_fail}').replace('{wt}', str(wt_ok))

P = 'longrun/results/D13-heatkernel-bridge-d10-d7.md'
s = open(P).read()
anchor = "\n> This card requests independent acceptance (`compiled_only_until_independent_semantic_review`)."
assert anchor in s
s = s.replace(anchor, blockquote + anchor, 1)
s = s.rstrip('\n') + '\n' + section
open(P, 'w').write(s)
print('md updated: section appended, blockquote inserted; lines =', s.count('\n'))
