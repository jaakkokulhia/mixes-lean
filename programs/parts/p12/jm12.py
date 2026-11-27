"""Verification program for the note 'An Explicit Joint Mix for Distributions with Monotone Densities'.

The construction (functions base, tri, uni, slab_split, leaf, pipage, pieces, assemble) works with Fractions
(exact) or with floats (simulation).
Part 1  exact check of Proposition 1 (three coordinates) on a grid, in both orders of the uniform lengths.
Part 2  exact check of identities used in the proofs at random rational points, of Lemmas 2-3 (uniform
        distributions), of Proposition 2 (slab split) and of random leaves with up to eight coordinates.
Part 3  exact end-to-end check of Theorem 1 for random finite slab laws (with and without atoms at 0, tight cases,
        and pairs (1-p) delta_0 + p U[0,b] as in Blotto games).
Part 4  Monte Carlo test of Algorithm 1 (floats) for tuples of different continuous densities.
Results are written to data/jm12.json; the log goes to stdout.
Environment: GRID (default 12), NRAND (default 2000), NSTEP (default 600), NBLOTTO (default 300), MC (default 50000),
SEED (default 2026)."""
import itertools, json, math, os, random, sys, time
from fractions import Fraction as Fr
import numpy as np

GRID = int(os.environ.get('GRID', 12)); NRAND = int(os.environ.get('NRAND', 2000))
NSTEP = int(os.environ.get('NSTEP', 600)); NBLOTTO = int(os.environ.get('NBLOTTO', 300))
MC = int(os.environ.get('MC', 50000)); SEED = int(os.environ.get('SEED', 2026))
UNI_K = (3, 9); LEAF_N = (3, 8); STEP_N = (3, 7); STEP_KMAX = {3: 4, 4: 3, 5: 3, 6: 2, 7: 2}; BLOTTO_N = (3, 10)

def base(c1, c2, a, b, x):
    """Joint mix of (U[0,c1], U[0,c2], g) where g = two-step density with slabs a < b and slab mean x (mean x/2),
    a < x < b <= s = (c1+c2+x)/2 and c1, c2 <= s. Returns (case, [(P, Q, w)]) with points in R^3 summing to s."""
    if c1 < c2:
        case, segs = base(c2, c1, a, b, x)
        return case + "'", [((P[1], P[0], P[2]), (Q[1], Q[0], Q[2]), w) for P, Q, w in segs]
    s = (c1 + c2 + x) / 2
    y1, y2, sig = s - c1, s - c2, s - x
    A = lambda l: (0 * s, s - l, l)
    Ap = lambda l: (s - l, 0 * s, l)
    Dp = lambda l: (c1, y1 - l, l)
    D = lambda l: (y2 - l, c2, l)
    B = (y2, c2, 0 * s); C = (c1, 0 * s, y1); F = (0 * s, c2, y2)
    if a >= y2:                                        # case I
        p, q = (b - x) / (b - a), (x - a) / (b - a)
        segs, t = [], 0
        for l, pl in ((a, p), (b, q)):
            K = sig * l + y1 * y2
            segs.append((A(l), B, pl * (l - y1) * (l - y2) / K))
            segs.append((A(l), C, pl * (s - l) * (l - y1) / K))
            t += pl * (s - l) / K
        segs.append((B, C, y1 * t))
        case = 'I'
    elif y1 == 0:                                      # case II, first coordinate of length s
        de = y2 - a; ep = sig + a; al = (s - b) * de / (b - y2)
        segs = [(A(b), C, al), (A(b), D(a), de), (D(a), C, ep)]
        case = 'II0'
    elif a >= y1:                                      # case II
        P_ = (b - y1) * (b - y2); Q_ = (y2 - a) * (a - y1)
        N = (s - b) * Q_ + (sig + a) * P_
        Kb = sig * b + y1 * y2
        be = y1 * y2 * N; ga = sig * y1 * N
        de = (b - x) * Kb * Q_; ep = (b - x) * Kb * (a - y1) * (sig + a)
        al = (s - b) * (be + de) / (b - y2)
        segs = [(A(b), C, al), (A(b), B, be), (B, C, ga), (A(b), D(a), de), (D(a), C, ep)]
        case = 'II'
    elif b >= c2:                                      # case IIIa
        N2 = sig * (y1 - a) + (sig + a) * (b - y1)
        N4 = (sig + a) * (b - y1) * (b - y2) - (s - b) * (y1 - a) * (y2 - a)
        k2 = sig * N4; k4 = (s - b) * (y2 - a) * N2
        k3 = (b - c2) * N4; k5 = (s - b) * (b - y2) * N2
        k1 = (y1 - a) * (k2 + k4) / (sig + a)
        segs = [(Dp(a), Ap(b), k1), (Dp(a), B, k2), (Ap(b), B, k3), (Dp(a), F, k4), (Ap(b), F, k5)]
        case = 'IIIa'
    else:                                              # case IIIb
        N2 = sig * (y1 - a) + (sig + a) * (b - y1)
        R = sig * b + a * y2
        l1 = sig * (sig + a) * (b * (b - x) + a * y2)
        l2 = y2 * (b - y2) * N2; l3 = y2 * (c1 - b + a) * N2
        l4 = (c2 - b) * (y1 - a) * R; l5 = (b - y1) * (y1 - a) * R
        segs = [(B, Dp(a), l1), (B, A(b), l2), (Dp(a), A(b), l3), (B, Ap(b), l4), (Dp(a), Ap(b), l5)]
        case = 'IIIb'
    tot = sum(w for _, _, w in segs)
    return case, [(P, Q, w / tot) for P, Q, w in segs if w != 0]

def tri(c1, c2, c3):
    """Joint mix of three uniform distributions U[0,cj] with max cj <= s = (c1+c2+c3)/2 (segments of a triangle)."""
    s = (c1 + c2 + c3) / 2
    t1, t2, t3 = s - c1, s - c2, s - c3
    A = (0 * s, t3, c3); B = (t2, c2, 0 * s); C = (c1, 0 * s, t1)
    K = t1 * t2 + t2 * t3 + t1 * t3
    return [sg for sg in [(A, B, t1 * t2 / K), (A, C, t2 * t3 / K), (B, C, t1 * t3 / K)] if sg[2] != 0]

def expand(segs, mapping, n, zero=0):
    """mapping[r] = list of (original index, factor): original coordinate = factor * reduced coordinate r;
    coordinates not mentioned are set to zero."""
    def ex(P):
        X = [zero] * n
        for r, lst in enumerate(mapping):
            for j, f in lst:
                X[j] = f * P[r]
        return tuple(X)
    return [(ex(P), ex(Q), w) for P, Q, w in segs]

def uni(L):
    """Joint mix of U[0,L_j], j = 1..k (k >= 2), with max L_j <= s = sum(L)/2: merge the two shortest
    comonotonically until three remain, then the triangle (k = 2 requires L_1 = L_2)."""
    nz = [j for j in range(len(L)) if L[j] != 0]
    if len(nz) < len(L):
        return expand(uni([L[j] for j in nz]), [[(j, 1)] for j in nz], len(L), zero=L[0] * 0 if L else 0)
    k = len(L)
    if k == 2:
        assert L[0] == L[1] or abs(L[0] - L[1]) < 1e-9
        return [((0 * L[0], L[1]), (L[0], 0 * L[0]), 1)]
    if k == 3:
        return tri(*L)
    order = sorted(range(k), key=lambda j: L[j])
    i, j = order[0], order[1]
    rest = [m for m in range(k) if m not in (i, j)]
    T = L[i] + L[j]
    segs = uni([L[m] for m in rest] + [T])
    mapping = [[(m, 1)] for m in rest] + [[(i, L[i] / T), (j, L[j] / T)]]
    return expand(segs, mapping, k)

def slab_split(C, a, b, x):
    """Joint mix of (U[0,C1], U[0,C2], U[0,C3], g) for max C_i <= s - x (g as in base). Returns (info, segs)."""
    s = (sum(C) + x) / 2
    p, q = (b - x) / (b - a), (x - a) / (b - a)
    kap = [q * c for c in C]; kind = ['low'] * 3
    D = 2 * s - b - sum(kap)
    for i in range(3):
        if D <= 0: break
        r = p * C[i]
        if D >= r:
            kap[i] = C[i]; kind[i] = 'full'; D -= r
        else:
            kap[i] = kap[i] + D; kind[i] = 'part'; D = 0 * D
    M = uni(kap + [b])                                  # four uniform distributions, sum s
    sL = s - x + a
    unis = [i for i in range(3) if kind[i] != 'part']
    part = [i for i in range(3) if kind[i] == 'part']
    lam = {i: (p * C[i] if kind[i] == 'low' else C[i]) for i in unis}
    i0 = unis[0]
    if a == 0:
        if part:
            j = part[0]; i1 = unis[1]
            xj = 2 * C[j] - (C[j] - q * kap[j]) / p
            case, segs = base(lam[i0], lam[i1], C[j] - kap[j], C[j], xj)
            Ls = expand(segs, [[(i0, 1)], [(i1, 1)], [(j, 1)]], 4, zero=a)
            info = 'split/' + case
        else:
            Ls = expand(uni([lam[0], lam[1], lam[2]]), [[(0, 1)], [(1, 1)], [(2, 1)]], 4, zero=a)
            info = 'split/U'
    elif part:
        j = part[0]; i1 = unis[1]
        xj = 2 * C[j] - (C[j] - q * kap[j]) / p        # slab mean of the reflected piece of coordinate j
        case, segs = base(lam[i0] + a, lam[i1], C[j] - kap[j], C[j], xj)
        T = lam[i0] + a
        Ls = expand(segs, [[(i0, lam[i0] / T), (3, a / T)], [(i1, 1)], [(j, 1)]], 4)
        info = 'split/' + case
    else:
        Ls = uni([lam[0], lam[1], lam[2], a])
        info = 'split/U'
    refl = lambda P: (C[0] - P[0], C[1] - P[1], C[2] - P[2], a - P[3])
    segs = [(P, Q, q * w) for P, Q, w in M] + [(refl(P), refl(Q), p * w) for P, Q, w in Ls]
    return info, segs, dict(kap=kap, kind=kind, sL=sL)

def leaf(ells, k, a, b, x):
    """Joint mix of the leaf: U[0, ells[j]] for j != k and the two-step density (a, b; slab mean x) at k."""
    n = len(ells)
    if k is None:
        return 'U', uni(list(ells))
    s = (sum(ells[j] for j in range(n) if j != k) + x) / 2
    groups = [[j] for j in range(n) if j != k and ells[j] != 0]
    tot = lambda g: sum(ells[j] for j in g)
    while len(groups) >= 3:
        groups.sort(key=tot)
        if tot(groups[0]) + tot(groups[1]) <= s:
            groups = [groups[0] + groups[1]] + groups[2:]
        else:
            break
    Cs = [tot(g) for g in groups]
    mapping = [[(j, ells[j] / Cs[r]) for j in g] for r, g in enumerate(groups)] + [[(k, 1)]]
    if len(groups) == 2:
        case, segs = base(Cs[0], Cs[1], a, b, x)
        info = 'base/' + case
    else:
        assert len(groups) == 3, groups
        info, segs, _ = slab_split(Cs, a, b, x)
    return info, expand(segs, mapping, n, zero=0 * s)

def pipage(lo, hi, m):
    """Decompose m in the box prod[lo_j, hi_j] into points of the box with the same coordinate sum and at most one
    coordinate strictly inside its interval. Returns [(vertex, weight, index of that coordinate or None)]."""
    out = []
    one = (m[0] - m[0]) + 1
    stack = [(list(m), one)]
    while stack:
        xv, w = stack.pop()
        Fi = [j for j in range(len(xv)) if lo[j] < xv[j] < hi[j]]
        if len(Fi) <= 1:
            out.append((xv, w, Fi[0] if Fi else None)); continue
        i, k = Fi[0], Fi[1]
        tp = min(hi[i] - xv[i], xv[k] - lo[k]); tm = min(xv[i] - lo[i], hi[k] - xv[k])
        xp = list(xv); xm = list(xv)
        if hi[i] - xv[i] <= xv[k] - lo[k]:
            xp[i] = hi[i]; xp[k] = xv[k] - tp
        else:
            xp[k] = lo[k]; xp[i] = xv[i] + tp
        if xv[i] - lo[i] <= hi[k] - xv[k]:
            xm[i] = lo[i]; xm[k] = xv[k] + tm
        else:
            xm[k] = hi[k]; xm[i] = xv[i] - tm
        stack.append((xp, w * tm / (tp + tm)))
        stack.append((xm, w * tp / (tp + tm)))
    return out

def pieces(pi, m):
    """Pairing of a finite slab law pi (dict length -> probability) with mean m into two-step pieces.
    Returns [((a, b), weight)], with a = b = m for the uniform piece U[0, m]."""
    out = []
    if m in pi:
        out.append(((m, m), pi[m]))
    lo = {l: w for l, w in pi.items() if l < m}; hi = {l: w for l, w in pi.items() if l > m}
    Dl = sum((m - l) * w for l, w in lo.items())
    for l1, w1 in lo.items():
        for l2, w2 in hi.items():
            out.append(((l1, l2), (l2 - l1) * w1 * w2 / Dl))
    return out

def assemble(pis):
    """Full construction for finite slab laws pi_1..pi_n (exact). Returns s, segments, statistics."""
    n = len(pis)
    ms = [sum(l * w for l, w in pi.items()) for pi in pis]
    s = sum(ms) / 2
    pcs = [pieces(pi, m) for pi, m in zip(pis, ms)]
    segs, stats = [], {}
    ntuple = 0; maxleaf = 0
    for combo in itertools.product(*pcs):
        wt = 1
        for _, w in combo: wt *= w
        lo = [ab[0] for ab, _ in combo]; hi = [ab[1] for ab, _ in combo]
        ntuple += 1
        for xv, wv, k in pipage(lo, hi, ms):
            if k is None:
                info, sg = 'U', uni(xv)
            else:
                info, sg = leaf(xv, k, lo[k], hi[k], xv[k])
            stats[info] = stats.get(info, 0) + 1
            maxleaf = max(maxleaf, len(sg))
            segs += [(P, Q, wt * wv * w) for P, Q, w in sg]
    return s, segs, dict(stats=stats, tuples=ntuple, max_leaf_segments=maxleaf)

# ------------------------------------------------------------------ exact checking of segment mixtures
def marginal_check(proj, target):
    """proj: [(u, v, mass)] projections of the segments on one coordinate (u = v gives an atom).
    target = (breakpoints, dens(u, v), atoms). Checks the density on every cell and the atoms exactly."""
    bps, dens_f, atoms_t = target
    ev, atoms = {}, {}
    for u, v, w in proj:
        lo, hi = min(u, v), max(u, v)
        if lo == hi:
            atoms[lo] = atoms.get(lo, 0) + w; continue
        d = w / (hi - lo)
        ev[lo] = ev.get(lo, 0) + d; ev[hi] = ev.get(hi, 0) - d
    assert atoms == {t: m for t, m in atoms_t.items() if m != 0}, (atoms, atoms_t)
    for t in bps:
        ev.setdefault(t, 0)
    pts = sorted(ev)
    dens = 0; cells = 0
    for u, v in zip(pts[:-1], pts[1:]):
        dens += ev[u]
        assert dens == dens_f(u, v), (u, v, dens, dens_f(u, v))
        cells += 1
    assert dens + ev[pts[-1]] == 0
    return cells

def check_mixture(segs, s, targets):
    """Exact checks: positive weights summing to 1, endpoints on the hyperplane sum = s, marginals equal to the
    targets (densities on every cell, atoms)."""
    n = len(targets)
    assert sum(w for _, _, w in segs) == 1
    for P, Q, w in segs:
        assert w > 0 and sum(P) == s and sum(Q) == s and P != Q
    cells = 0
    for j in range(n):
        cells += marginal_check([(P[j], Q[j], w) for P, Q, w in segs], targets[j])
    return cells

def uniform_target(c):
    return ([0 * c, c], lambda u, v, c=c: (1 / c) if (0 <= u and v <= c) else 0, {})

def twostep_target(a, b, x):
    p, q = (b - x) / (b - a), (x - a) / (b - a)
    h1 = (p / a + q / b) if a > 0 else 0
    h2 = q / b
    def d(u, v):
        if u >= 0 and v <= a: return h1
        if u >= a and v <= b: return h2
        return 0
    return ([0 * a, a, b], d, ({0 * a: p} if a == 0 else {}))

def slab_target(pi):
    ls = sorted(pi)
    def d(u, v):
        if u < 0: return 0
        return sum((w / l for l, w in pi.items() if l >= v and l > 0), 0)
    z = [l for l in ls if l == 0]
    return ([0 * ls[-1]] + [l for l in ls if l > 0], d, ({z[0]: pi[z[0]]} if z else {}))

# ------------------------------------------------------------------ Part 1: the base case on a grid
def base_target(c1, c2, a, b, x):
    return [uniform_target(c1), uniform_target(c2), twostep_target(a, b, x)]

def part1():
    t0 = time.time(); G = GRID
    cases, bnd = {}, {}
    checks = cells = 0; maxseg = 0
    for i in range(1, G):
        x = Fr(i, G); s = Fr(1)
        for j in range(G + 1):
            y1 = j * x / (2 * G); y2 = x - y1; c1, c2 = s - y1, s - y2
            for k in range(G):
                a = k * x / G
                for l in range(1, G + 1):
                    b = x + l * (1 - x) / G
                    tags = [t for t, cond in (('y1=0', y1 == 0), ('a=0', a == 0), ('a=y1', a == y1 and a > 0),
                                              ('a=y2', a == y2), ('b=s', b == s), ('b=c2', b == c2),
                                              ('c1=c2', c1 == c2)) if cond]
                    for t in tags: bnd[t] = bnd.get(t, 0) + 1
                    for cc1, cc2 in ((c1, c2), (c2, c1)):
                        case, segs = base(cc1, cc2, a, b, x)
                        cases[case] = cases.get(case, 0) + 1
                        cells += check_mixture(segs, s, base_target(cc1, cc2, a, b, x))
                        maxseg = max(maxseg, len(segs)); checks += 1
    out = dict(checks=checks, points=checks // 2, cells=cells, cases=cases, boundary=bnd, max_segments=maxseg,
               seconds=round(time.time() - t0, 1))
    print('Part 1:', out, flush=True)
    return out

# ------------------------------------------------------------------ Part 2: identities, uniform tuples, slab split, leaves
def rnd(rng, lo, hi, D=10007):
    return lo + (hi - lo) * Fr(rng.randint(1, D - 1), D)

def part2():
    t0 = time.time(); rng = random.Random(SEED + 2)
    nid = 0
    for t in range(NRAND):
        s = Fr(1); x = rnd(rng, 0, 1); mu2 = x                       # mu2 = 2 mu
        y1 = rnd(rng, 0, x); y2 = x - y1; sig = s - x
        a = rnd(rng, 0, x); b = rnd(rng, x, 1); l = rnd(rng, 0, 1)
        K = lambda l: sig * l + y1 * y2
        assert sig * (l - y1) * (l - y2) - (s - l) * y1 * y2 == (l - mu2) * K(l)                 # (A)
        assert (l - y1) * (l - y2) + (s - l) * (l - y1) + y1 * (s - l) == K(l)                   # (B)
        assert (b - y1) * (b - y2) - (y1 - a) * (y2 - a) == (b - a) * (b + a - mu2)              # (C)
        assert (sig + a) - (s - b) == a + b - mu2                                                # (D)
        N2 = sig * (y1 - a) + (sig + a) * (b - y1); R = sig * b + a * y2
        N4 = (sig + a) * (b - y1) * (b - y2) - (s - b) * (y1 - a) * (y2 - a)
        assert N4 == (a + b - mu2) * (b - y1) * (b - y2) + (s - b) * (b - a) * (b + a - mu2)    # (E)
        assert (b - y2) * N2 == (sig + a) * (b * (b - mu2) + a * y2) + (y1 - a) * R               # (F)
        assert (b - y1) * R == sig * (b * (b - mu2) + a * y2) + y2 * N2                           # (G)
        assert (b - y2) * N2 * (sig + a) * (b - y1) == (y1 - a) * (sig * N4 + (s - b) * (y2 - a) * N2) + (sig + a) * (b - y1) * N4  # (H)
        p, q = (b - mu2) / (b - a), (mu2 - a) / (b - a)
        assert p * a + q * b == mu2 and p + q == 1
        assert b * b - 2 * s * b + mu2 * (2 * s - mu2) == (b - mu2) * (b - 2 * s + mu2)          # (I)
        nid += 1
    # uniform tuples (Lemmas 2 and 3)
    nuni = 0; tight = 0
    for t in range(NRAND):
        k = rng.randint(*UNI_K)
        while True:
            L = [rnd(rng, 0, 1) for _ in range(k)]
            if rng.random() < 0.25:
                L[-1] = sum(L[:-1]) / 2 + rnd(rng, 0, 1) * (max(L[:-1]) - sum(L[:-1]) / 2) if 2 * max(L[:-1]) > sum(L[:-1]) else sum(L[:-1])
            if 2 * max(L) <= sum(L): break
        tight += (2 * max(L) == sum(L))
        check_mixture(uni(L), sum(L) / 2, [uniform_target(c) for c in L]); nuni += 1
    # slab split (Proposition 2) at random inputs with max C <= s - 2 mu
    split = {}; nsplit = 0; split_a0 = split_bs = 0
    while nsplit < NRAND:
        s = Fr(1); x = rnd(rng, 0, Fr(1, 2))
        C1 = rnd(rng, 0, 1 - x); C2 = rnd(rng, 0, 1 - x); C3 = 2 - x - C1 - C2
        if not (0 < C3 <= 1 - x): continue
        a = Fr(0) if rng.random() < 0.2 else rnd(rng, 0, x); b = s if rng.random() < 0.1 else rnd(rng, x, 1)
        info, segs, aux = slab_split([C1, C2, C3], a, b, x)
        key = info + '/' + ','.join(sorted(aux['kind']))
        split[key] = split.get(key, 0) + 1
        check_mixture(segs, s, [uniform_target(C1), uniform_target(C2), uniform_target(C3), twostep_target(a, b, x)])
        nsplit += 1; split_a0 += (a == 0); split_bs += (b == s)
    # random leaves with n - 1 uniform coordinates and one with two steps, n = 3..8
    leaves = {}; nleaf = 0; maxseg = 0; leaf_a0 = leaf_bs = leaf_zero = 0
    while nleaf < NRAND:
        n = rng.randint(*LEAF_N)
        x = rnd(rng, 0, 1); b = rnd(rng, x, 1); a = Fr(0) if rng.random() < 0.15 else rnd(rng, 0, x)
        ells = [Fr(0) if (a == 0 and rng.random() < 0.15) else rnd(rng, 0, 1) for _ in range(n - 1)]
        s = (sum(ells) + x) / 2
        if rng.random() < 0.1: b = s
        if max(ells + [b]) > s or b <= x: continue
        k = rng.randrange(n); ells = ells[:k] + [x] + ells[k:]
        info, segs = leaf(ells, k, a, b, x)
        key = info.split('/')[0]; leaves[key] = leaves.get(key, 0) + 1
        tg = [twostep_target(a, b, x) if j == k else (uniform_target(ells[j]) if ells[j] != 0 else
              ([Fr(0)], lambda u, v: 0, {Fr(0): Fr(1)})) for j in range(n)]
        check_mixture(segs, s, tg); nleaf += 1; maxseg = max(maxseg, len(segs))
        leaf_a0 += (a == 0); leaf_bs += (b == s); leaf_zero += any(ells[j] == 0 for j in range(n) if j != k)
    out = dict(identities=nid, uniform_tuples=nuni, uniform_tight=tight, split=nsplit, split_kinds=split,
               split_a0=split_a0, split_bs=split_bs, leaves=nleaf, leaf_kinds=leaves, leaf_a0=leaf_a0,
               leaf_bs=leaf_bs, leaf_zero=leaf_zero, max_segments_leaf=maxseg, uni_k=UNI_K, leaf_n=LEAF_N, seconds=round(time.time() - t0, 1))
    print('Part 2:', out, flush=True)
    return out

# ------------------------------------------------------------------ Part 3: exact end-to-end
def random_slab_law(rng, R, kmax, zero):
    k = rng.randint(1, kmax)
    pts = sorted(set(Fr(rng.randint(1, 60), 60) * R for _ in range(k)))
    if zero: pts = [Fr(0)] + pts
    wts = [Fr(rng.randint(1, 9)) for _ in pts]; t = sum(wts)
    return {p: w / t for p, w in zip(pts, wts)}

def part3():
    t0 = time.time(); rng = random.Random(SEED + 3)
    kinds = {}; done = tried = tight = withzero = 0; nseg = 0; ntup = 0; maxseg = 0; nmax = 0; maxleaf = 0
    while done < NSTEP:
        n = rng.randint(*STEP_N)
        kmax = STEP_KMAX[n]
        pis = [random_slab_law(rng, Fr(rng.randint(20, 60), 60), kmax, rng.random() < 0.2) for _ in range(n)]
        tried += 1
        ms = [sum(l * w for l, w in pi.items()) for pi in pis]
        if rng.random() < 0.3:                                     # rescale one law so that max B = s
            j = rng.randrange(n); Bj = max(pis[j]); s0 = sum(ms) / 2
            t = (s0 - ms[j] / 2) / (Bj - ms[j] / 2)
            if t > 0:
                pis[j] = {l * t: w for l, w in pis[j].items()}; ms[j] *= t
        s = sum(ms) / 2
        if max(max(pi) for pi in pis) > s: continue
        istight = max(max(pi) for pi in pis) == s
        s2, segs, st = assemble(pis)
        for kk, v in st['stats'].items():
            key = kk.split('/')[0]; kinds[key] = kinds.get(key, 0) + v
        check_mixture(segs, s, [slab_target(pi) for pi in pis])
        done += 1; tight += istight; withzero += any(Fr(0) in pi for pi in pis)
        nseg += len(segs); ntup += st['tuples']; maxseg = max(maxseg, len(segs)); nmax = max(nmax, n)
        maxleaf = max(maxleaf, st['max_leaf_segments'])
    # Blotto-type marginals (1 - p_i) delta_0 + p_i U[0, b_i]
    bl = {}; bdone = 0; bseg = 0; bnmax = 0
    while bdone < NBLOTTO:
        n = rng.randint(*BLOTTO_N)
        bs = [rnd(rng, 0, 1, 101) for _ in range(n)]
        ps = [rnd(rng, 0, 1, 101) if rng.random() < 0.7 else Fr(1) for _ in range(n)]
        s = sum(p * b for p, b in zip(ps, bs)) / 2
        if max(bs) > s: continue
        pis = [({Fr(0): 1 - p, b: p} if p < 1 else {b: Fr(1)}) for p, b in zip(ps, bs)]
        s2, segs, st = assemble(pis)
        for kk, v in st['stats'].items():
            key = kk.split('/')[0]; bl[key] = bl.get(key, 0) + v
        check_mixture(segs, s, [slab_target(pi) for pi in pis])
        bdone += 1; bseg += len(segs); bnmax = max(bnmax, n); maxleaf = max(maxleaf, st['max_leaf_segments'])
    out = dict(laws=done, tried=tried, tight=tight, with_zero_atom=withzero, tuples=ntup, segments=nseg,
               max_segments=maxseg, n_max=nmax, leaf_kinds=kinds, blotto=bdone, blotto_segments=bseg,
               blotto_n_max=bnmax, blotto_leaf_kinds=bl, max_leaf_segments=maxleaf, step_n=STEP_N,
               step_kmax=max(STEP_KMAX.values()), blotto_n=BLOTTO_N, seconds=round(time.time() - t0, 1))
    print('Part 3:', out, flush=True)
    return out

# ------------------------------------------------------------------ Part 4: Monte Carlo of Algorithm 1
def law_uniform(B):
    return dict(name=f'uniform on [0,{B:g}]', B=B, mu=B / 2, draw=lambda rng: B, cdf=lambda x: np.clip(x / B, 0, 1))

def law_power(p, B):
    return dict(name=f'power {p:g} on [0,{B:g}]', B=B, mu=B / (p + 2), draw=lambda rng: B * rng.beta(2, p),
                cdf=lambda x: 1 - (1 - np.clip(x / B, 0, 1)) ** (p + 1))

def law_trexp(lam, B):
    Z = -math.expm1(-lam * B); fB = lam * math.exp(-lam * B) / Z
    def draw(rng):
        X = -math.log1p(-rng.random() * Z) / lam
        Y = rng.random() * lam * math.exp(-lam * X) / Z
        return B if Y <= fB else min(B, -math.log(Y * Z / lam) / lam)
    return dict(name=f'exponential {lam:g} on [0,{B:g}]', B=B, mu=1 / lam - B * math.exp(-lam * B) / Z, draw=draw,
                cdf=lambda x: -np.expm1(-lam * np.clip(x, 0, B)) / Z)

def law_invsqrt(B):
    return dict(name=f'inverse square root on (0,{B:g}]', B=B, mu=B / 3,
                draw=lambda rng: B if rng.random() < 0.5 else B * rng.random() ** 2, cdf=lambda x: np.sqrt(np.clip(x, 0, B) / B))

def law_step(atoms):
    ls = list(atoms); ws = [atoms[l] for l in ls]
    return dict(name='step ' + ', '.join(f'{w:g}@{l:g}' for l, w in atoms.items()), B=max(ls),
                mu=sum(l * w for l, w in atoms.items()) / 2, draw=lambda rng: ls[rng.choice(len(ls), p=ws)],
                cdf=lambda x: sum(w * np.minimum(np.clip(x, 0, None) / l, 1.0) for l, w in zip(ls, ws)))

def sample_algorithm(laws, size, rng):
    n = len(laws); m = [2 * L['mu'] for L in laws]
    out = np.empty((size, n)); kinds = {}
    def partner(L, mj, above):
        while True:
            l = L['draw'](rng)
            if above and l > mj and rng.random() * (L['B'] - mj) <= l - mj: return l
            if not above and l < mj and rng.random() * mj <= mj - l: return l
    for t in range(size):
        lo, hi = [], []
        for L, mj in zip(laws, m):
            l = L['draw'](rng)
            if l == mj: lo.append(mj); hi.append(mj)
            elif l < mj: lo.append(l); hi.append(partner(L, mj, True))
            else: hi.append(l); lo.append(partner(L, mj, False))
        xv = list(m)
        while True:                                                # randomised splitting (one path of the tree)
            Fi = [j for j in range(n) if lo[j] < xv[j] < hi[j]]
            if len(Fi) <= 1: break
            i, k = Fi[0], Fi[1]
            tp = min(hi[i] - xv[i], xv[k] - lo[k]); tm = min(xv[i] - lo[i], hi[k] - xv[k])
            if rng.random() < tm / (tp + tm):
                if hi[i] - xv[i] <= xv[k] - lo[k]: xv[i], xv[k] = hi[i], xv[k] - tp
                else: xv[i], xv[k] = xv[i] + tp, lo[k]
            else:
                if xv[i] - lo[i] <= hi[k] - xv[k]: xv[i], xv[k] = lo[i], xv[k] + tm
                else: xv[i], xv[k] = xv[i] - tm, hi[k]
        k = Fi[0] if Fi else None
        info, segs = ('U', uni(xv)) if k is None else leaf(xv, k, lo[k], hi[k], xv[k])
        key = info.split('/')[0]; kinds[key] = kinds.get(key, 0) + 1
        w = np.array([max(sg[2], 0.0) for sg in segs]); e = rng.choice(len(segs), p=w / w.sum())
        P, Q, _ = segs[e]; v = rng.random()
        out[t] = [P[j] + v * (Q[j] - P[j]) for j in range(n)]
    return out, kinds

def ks(sample, cdf):
    x = np.sort(sample); m = len(x); F = cdf(x)
    return float(max(np.max(np.arange(1, m + 1) / m - F), np.max(F - np.arange(m) / m)))

def ks_pvalue(d, m):
    lam = math.sqrt(m) * d
    if lam < 0.3: return 1.0
    return float(min(1.0, 2 * sum((-1) ** (k - 1) * math.exp(-2 * k * k * lam * lam) for k in range(1, 101))))

def part4():
    t0 = time.time(); rng = np.random.default_rng(SEED + 4); res = []
    tests = [
        [law_uniform(2.0), law_power(0.25, 2.2), law_trexp(0.3, 2.1)],
        [law_uniform(2.0), law_uniform(2.0), law_power(1.0, 3.0)],
        [law_power(1.0, 3.0), law_invsqrt(3.0), law_trexp(0.6, 3.2), law_step({0.4: 0.5, 1.6: 0.3, 2.8: 0.2})],
        [law_power(3.0, 3.0), law_power(0.5, 1.5), law_uniform(1.0), law_invsqrt(2.4), law_trexp(1.0, 2.5)],
        [law_power(p, B) for p, B in ((0.2, 1.2), (0.7, 1.6), (1.5, 2.0), (2.5, 2.4), (4.0, 2.8), (6.0, 3.0))],
    ]
    for laws in tests:
        s = sum(L['mu'] for L in laws); Bmax = max(L['B'] for L in laws)
        assert Bmax <= s + 1e-12
        X, kinds = sample_algorithm(laws, MC, rng)
        d = [ks(X[:, j], L['cdf']) for j, L in enumerate(laws)]
        r = dict(n=len(laws), s=s, Bmax=Bmax, samples=MC, laws=[L['name'] for L in laws],
                 max_sum_error=float(np.abs(X.sum(1) - s).max()), min_coord=float(X.min()),
                 ks=d, ks_max=max(d), p_min=min(ks_pvalue(x, MC) for x in d), kinds=kinds,
                 ks_threshold=1.358 / math.sqrt(MC))
        print('Part 4:', r, flush=True); res.append(r)
    return dict(tests=res, seconds=round(time.time() - t0, 1))

if __name__ == '__main__':
    t0 = time.time()
    out = dict(part1=part1(), part2=part2(), part3=part3(), part4=part4())
    out['seconds'] = round(time.time() - t0, 1)
    out['env'] = dict(GRID=GRID, NRAND=NRAND, NSTEP=NSTEP, NBLOTTO=NBLOTTO, MC=MC, SEED=SEED)
    os.makedirs('data', exist_ok=True)
    json.dump(out, open('data/jm12.json', 'w'), indent=1, default=str)
    print('all checks passed in', out['seconds'], 's')
