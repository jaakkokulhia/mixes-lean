"""Verification program for the note 'An Explicit Complete Mix for Distributions with Monotone Densities'.

Part 1  exact (rational) check of Theorem 1 on a grid of (n, a, b): weights, midpoint sums, positive lengths,
        polygon inequalities, supports, and equality of the symmetrised marginal with g_{a,b} on every cell.
Part 2  exact check of the identities used in the proofs at random rational points.
Part 3  exact end-to-end check of Theorem 2 for random rational step densities: the pair law of Lemma 4
        combined with the tuples of Theorem 1 reproduces f exactly.
Part 4  Monte Carlo test of Algorithm 1 (float) for several densities: sums and Kolmogorov-Smirnov distances.
Results are written to data/mono11.json; the log goes to stdout.
Environment: NMAX (default 20), GRID (default 20), NSTEP (default 400), MC (default 50000), SEED (2026)."""
import json, os, sys, time, math, itertools
from fractions import Fraction as Fr
import numpy as np

NMAX = int(os.environ.get('NMAX', 20)); GRID = int(os.environ.get('GRID', 20))
NSTEP = int(os.environ.get('NSTEP', 400)); MC = int(os.environ.get('MC', 50000)); SEED = int(os.environ.get('SEED', 2026))

# ---------------------------------------------------------------- Theorem 1 (exact)
def h12(a, b):
    return (a + b - 2) / (a * b), (2 - a) / (b * (b - a))

def u_beta(n, a, b, beta):
    return 2 * n - n * a - beta * (b - a)

def tuples_small_a(n, a, b):
    """Theorem 1 for 0 < a <= 1 < 2 < b <= n: returns (case, list of (weight, intervals))."""
    def SF(beta):
        u = u_beta(n, a, b, beta)
        p1 = [(0, a)] * (n - 1 - beta) + [(0, b)] * (beta - 1) + [(a, b), (0, u)]
        p2 = [(0, a)] * (n - beta) + [(0, b)] * (beta - 1) + [(u, b)]
        return [(u / b, p1), (1 - u / b, p2)]
    u1, u2 = u_beta(n, a, b, 1), u_beta(n, a, b, 2)
    if u1 <= b:
        return 'A', SF(1)
    if n >= 4 and u_beta(n, a, b, 3) >= 0:
        beta = max(bt for bt in range(3, n) if u_beta(n, a, b, bt) >= 0)
        return 'B', SF(beta)
    if u2 <= (n - 2) * a:
        return 'C', SF(2)
    x = u2 / 2
    p2 = [(0, a)] * (n - 2) + [(x, b)] * 2
    p3 = [(0, a)] * (n - 3) + [(0, x), (a, b), (x, b)]
    return 'D', [(1 - u2 / b, p2), (u2 / b, p3)]

def tuples(n, a, b):
    """Theorem 1 for 0 < a < 2 < b <= n (reflection for a > 1). Returns (case, [(weight, intervals)])."""
    if a <= 1:
        return tuples_small_a(n, a, b)
    theta = 2 * (a - 1) * (b - 2) / (a * (b - a))
    case, t = tuples_small_a(n, 2 - a, b)
    return 'R' + case, [(theta, [(2 - a, a)] * n)] + [((1 - theta) * w, iv) for w, iv in t]

def check_tuples(n, a, b, parts, target):
    """exact checks; target(m) = density at m. Returns number of tuples with positive weight."""
    W = sum(w for w, _ in parts)
    assert W == 1, 'weights do not sum to 1'
    used = 0
    for w, ivs in parts:
        assert w >= 0, 'negative weight'
        if w == 0: continue
        used += 1
        assert len(ivs) == n
        assert sum(l + r for l, r in ivs) == 2 * n, 'midpoint sum'
        L = [r - l for l, r in ivs]
        assert min(L) > 0, 'zero length'
        assert 2 * max(L) <= sum(L), 'polygon inequality'
        assert all(0 <= l and r <= b for l, r in ivs), 'support'
    bps = sorted(set([Fr(0), b] + [e for w, ivs in parts if w for iv in ivs for e in iv] + extra_bps(a)))
    for lo, hi in zip(bps[:-1], bps[1:]):
        m = (lo + hi) / 2
        dens = sum(w * sum(Fr(1, n) / (r - l) for l, r in ivs if l < m < r) for w, ivs in parts if w)
        assert dens == target(m), ('marginal', lo, hi)
    return used

def extra_bps(a):
    return [a] if isinstance(a, Fr) else []

def part1():
    t0 = time.time()
    cases = {}; N = 0; maxtuples = 0; per_n = {}
    for n in range(3, NMAX + 1):
        cnt = 0
        for i in range(1, 2 * GRID):
            a = Fr(i, GRID)                          # 0 < a < 2
            for j in range(1, 2 * GRID + 1):
                b = 2 + (n - 2) * Fr(j, 2 * GRID)    # 2 < b <= n
                case, parts = tuples(n, a, b)
                h1, h2 = h12(a, b)
                used = check_tuples(n, a, b, parts, lambda m: h1 if m < a else h2)
                maxtuples = max(maxtuples, used)
                cases[case] = cases.get(case, 0) + 1; N += 1; cnt += 1
        per_n[n] = cnt
    # boundary cases: b = n (tight), a = 1, and the case thresholds hit exactly
    nb = 0
    for n in range(3, NMAX + 1):
        for a in [Fr(1), Fr(1, 2), Fr(1, 3), Fr(3, 2)]:
            cands = {Fr(n), n - (n - 1) * a / 2, (2 * n - (n - 3) * a) / 3, n - (n - 2) * a}
            for b in cands:
                if 2 < b <= n:
                    case, parts = tuples(n, a, b); h1, h2 = h12(a, b)
                    check_tuples(n, a, b, parts, lambda m: h1 if m < a else h2); nb += 1
    out = dict(cases_checked=N, boundary_checked=nb, case_counts=cases, max_tuples=maxtuples,
               nmax=NMAX, grid=GRID, seconds=round(time.time() - t0, 1))
    print('Part 1:', out, flush=True)
    return out

# ---------------------------------------------------------------- Part 2: algebraic identities
def part2():
    """the rational-function identities used in the proofs, checked exactly at random rational points"""
    rng = np.random.default_rng(SEED + 7)
    res = {k: 0 for k in ('SF_sums', 'D_sums', 'mass', 'mean', 'jump', 'reflection', 'thresholds', 'pair', 'split')}
    for _ in range(2000):
        n = int(rng.integers(3, 60)); beta = int(rng.integers(1, n))
        a = Fr(int(rng.integers(1, 2000)), 1000)                 # 0 < a < 2
        b = 2 + Fr(int(rng.integers(1, 1000)), 1000) * (n - 2)   # 2 < b <= n
        u = u_beta(n, a, b, beta)
        assert (n - 1 - beta) * a + (beta - 1) * b + (a + b) + u == 2 * n
        assert (n - beta) * a + (beta - 1) * b + (u + b) == 2 * n
        res['SF_sums'] += 1
        u2 = u_beta(n, a, b, 2); x = u2 / 2
        assert (n - 2) * a + 2 * (x + b) == 2 * n and (n - 3) * a + x + (a + b) + (x + b) == 2 * n
        res['D_sums'] += 1
        h1, h2 = h12(a, b)
        assert h1 * a + h2 * (b - a) == 1; res['mass'] += 1
        assert h1 * a * a / 2 + h2 * (b * b - a * a) / 2 == 1; res['mean'] += 1
        assert h1 - h2 == (b - 2) / (a * (b - a)); res['jump'] += 1
        if a > 1:
            theta = 2 * (a - 1) * (b - 2) / (a * (b - a)); H1, H2 = h12(2 - a, b)
            assert h1 == (1 - theta) * H1 and h2 == (1 - theta) * H2
            assert h1 - theta / (2 * a - 2) == (1 - theta) * H2 and 0 < theta < 1
            res['reflection'] += 1
        assert (u_beta(n, a, b, 1) <= b) == (b >= n - (n - 1) * a / 2)
        assert (u_beta(n, a, b, 3) >= 0) == (b <= (2 * n - (n - 3) * a) / 3)
        assert (u2 <= (n - 2) * a) == (b >= n - (n - 2) * a)
        res['thresholds'] += 1
        l1, l2 = a, b                                            # pair law: two-step with slab atoms l1 < 2 < l2
        G1 = ((l2 - 2) / l1 + (2 - l1) / l2) / (l2 - l1); G2 = ((2 - l1) / l2) / (l2 - l1)
        assert (G1, G2) == h12(l1, l2); res['pair'] += 1
        uu = b * Fr(int(rng.integers(0, 1001)), 1000)            # splitting identity
        if 0 < uu < b:
            assert (uu / b) / uu == (1 - uu / b) / (b - uu) == 1 / b; res['split'] += 1
    print('Part 2:', res, flush=True)
    return res

# ---------------------------------------------------------------- Part 3: exact end-to-end for step densities
def random_step_density(rng, n):
    """random decreasing step density with mean 1 and support [0,B], B <= n, as a finite slab law pi."""
    while True:
        k = int(rng.integers(1, 6))
        pts = sorted(set(Fr(int(rng.integers(1, 40 * n)), 40) for _ in range(k)))
        pts = [p for p in pts if p <= n]
        if not pts: continue
        wts = [Fr(int(rng.integers(1, 9))) for _ in pts]
        m1 = sum(w * p for w, p in zip(wts, pts)) / sum(wts)     # mean of pi (unnormalised weights)
        # add an atom so that the mean of pi is exactly 2 (mean of f = 1)
        tot = sum(wts)
        if m1 < 2:
            hi = Fr(int(rng.integers(81, 40 * n + 1)), 40)       # atom above 2, hi <= n
            if hi <= 2 or hi > n: continue
            w = tot * (2 - m1) / (hi - 2); pts.append(hi); wts.append(w)
        elif m1 > 2:
            lo = Fr(int(rng.integers(1, 80)), 40)
            w = tot * (m1 - 2) / (2 - lo); pts.append(lo); wts.append(w)
        tot = sum(wts)
        pi = {}
        for p, w in zip(pts, wts): pi[p] = pi.get(p, 0) + w / tot
        assert sum(pi.values()) == 1 and sum(p * w for p, w in pi.items()) == 2
        if max(pi) <= n: return pi

def density_from_pi(pi):
    return lambda x: sum(w / l for l, w in pi.items() if x < l)

def part3():
    t0 = time.time()
    rng = np.random.default_rng(SEED)
    done = 0; pairs = 0; maxk = 0
    for trial in range(NSTEP):
        n = int(rng.integers(3, 9))
        pi = random_step_density(rng, n)
        f = density_from_pi(pi)
        lo = {l: w for l, w in pi.items() if l < 2}; hi = {l: w for l, w in pi.items() if l > 2}
        p0 = pi.get(Fr(2), Fr(0)); Delta = sum((2 - l) * w for l, w in lo.items())
        assert Delta == sum((l - 2) * w for l, w in hi.items())
        parts = []
        if p0: parts.append((p0, [(Fr(0), Fr(2))] * n))
        for l1, w1 in lo.items():
            for l2, w2 in hi.items():
                P = (l2 - l1) * w1 * w2 / Delta              # pair law of Lemma 4
                case, t = tuples(n, l1, l2)
                parts += [(P * w, iv) for w, iv in t if w > 0]; pairs += 1
        B = max(pi)
        # exact marginal check against f on all cells
        W = sum(w for w, _ in parts); assert W == 1
        for w, ivs in parts:
            assert w >= 0 and sum(l + r for l, r in ivs) == 2 * n
            L = [r - l for l, r in ivs]; assert min(L) > 0 and 2 * max(L) <= sum(L)
        bps = sorted(set([Fr(0), B] + [e for w, ivs in parts for iv in ivs for e in iv] + list(pi)))
        for a_, b_ in zip(bps[:-1], bps[1:]):
            m = (a_ + b_) / 2
            dens = sum(w * sum(Fr(1, n) / (r - l) for l, r in ivs if l < m < r) for w, ivs in parts)
            assert dens == f(m)
        done += 1; maxk = max(maxk, len(pi))
    out = dict(step_densities=done, pairs=pairs, max_steps=maxk, seconds=round(time.time() - t0, 1))
    print('Part 3:', out, flush=True)
    return out

# ---------------------------------------------------------------- Part 4: Monte Carlo of Algorithm 1
def tuples_float(n, a, b):
    case, parts = tuples(n, Fr(a).limit_denominator(10 ** 12), Fr(b).limit_denominator(10 ** 12))
    return [(float(w), [(float(l), float(r)) for l, r in iv]) for w, iv in parts if w > 0]

def project(ivs, rng):
    l = np.array([x for x, _ in ivs]); r = np.array([y for _, y in ivs])
    L = r - l; c = (l + r) / 2; n = len(L)
    i0 = int(np.argmax(L)); others = [j for j in range(n) if j != i0]
    pref = np.concatenate([[0.0], np.cumsum(L[others])]); tot = pref[-1]
    m = int(np.argmin(np.abs(2 * pref - tot)))
    G, H = others[:m], others[m:]; S, T = pref[m], tot - pref[m]; Ls = L[i0]
    x = (Ls ** 2 + T ** 2 - S ** 2) / (2 * Ls); y = math.sqrt(max(T ** 2 - x ** 2, 0.0))
    E0 = np.array([Ls, 0.0, 0.0]); P2 = np.array([x, y, 0.0]); ES = P2 - E0; ET = -P2
    xi = rng.standard_normal(3); xi /= np.linalg.norm(xi)
    X = c.copy(); X[i0] += E0 @ xi / 2
    for j in G: X[j] += L[j] / S * (ES @ xi) / 2
    for j in H: X[j] += L[j] / T * (ET @ xi) / 2
    return X

def algorithm1(n, draw_pi, size, rng, B):
    """draw_pi(rng) samples the slab law pi (mean 2). Returns size x n samples of a complete mix (mean 1)."""
    out = np.empty((size, n))
    def draw_below():
        while True:
            l = draw_pi(rng)
            if l < 2 and rng.random() * 2 <= 2 - l: return l
    def draw_above():
        while True:
            l = draw_pi(rng)
            if l > 2 and rng.random() * (B - 2) <= l - 2: return l
    for s in range(size):
        L = draw_pi(rng)
        if L == 2:
            ivs = [(0.0, 2.0)] * n
        else:
            a, b = (L, draw_above()) if L < 2 else (draw_below(), L)
            parts = tuples_float(n, a, b)
            w = np.array([p[0] for p in parts]); ivs = parts[rng.choice(len(parts), p=w / w.sum())][1]
        out[s] = rng.permutation(project(ivs, rng))
    return out

def ks(sample, cdf):
    x = np.sort(sample); m = len(x); F = cdf(x)
    return float(max(np.max(np.arange(1, m + 1) / m - F), np.max(F - np.arange(m) / m)))

def ks_pvalue(d, m):
    """asymptotic Kolmogorov tail probability P(sqrt(m) D > sqrt(m) d)"""
    lam = math.sqrt(m) * d
    if lam < 0.3: return 1.0
    return float(min(1.0, 2 * sum((-1) ** (k - 1) * math.exp(-2 * k * k * lam * lam) for k in range(1, 101))))

def part4():
    t0 = time.time(); rng = np.random.default_rng(SEED + 1); res = []
    tests = []
    for p, n in [(0.5, 3), (1.0, 3), (3.0, 6)]:                 # power densities, B = p + 2
        B = p + 2
        tests.append((f'power p={p}', n, B, (lambda rng, B=B, p=p: B * rng.beta(2, p)),
                      (lambda x, B=B, p=p: 1 - np.clip(1 - x / B, 0, 1) ** (p + 1))))
    # f(x) = x^{-1/2} / (2 sqrt 3) on (0, 3]: pi = (1/2) delta_3 + (1/2) law(3 U^2)
    tests.append(('inverse square root', 3, 3.0, (lambda rng: 3.0 if rng.random() < 0.5 else 3.0 * rng.random() ** 2),
                  (lambda x: np.sqrt(np.clip(x, 0, 3) / 3))))
    # truncated exponential with mean 1 on [0, 3.5], n = 4
    B = 3.5
    lam = 0.5
    for _ in range(200):                                        # solve 1/lam - B/(e^{lam B} - 1) = 1
        g = 1 / lam - B / math.expm1(lam * B) - 1
        dg = -1 / lam ** 2 + B * B * math.exp(lam * B) / math.expm1(lam * B) ** 2
        lam -= g / dg
    Z = -math.expm1(-lam * B)
    grid = np.linspace(0, B, 400001)[1:]
    dens = grid * lam * lam * np.exp(-lam * grid) / Z
    cont = np.concatenate([[0.0], np.cumsum((dens[1:] + dens[:-1]) / 2 * np.diff(grid))])
    atom = B * lam * math.exp(-lam * B) / Z
    cont_mass = cont[-1]
    def draw_exp(rng, grid=grid, cont=cont, atom=atom, cm=cont_mass):
        u = rng.random() * (cm + atom)
        return float(B) if u >= cm else float(np.interp(u, cont, grid))
    tests.append(('truncated exponential', 4, B, draw_exp,
                  (lambda x, lam=lam, Z=Z: -np.expm1(-lam * np.clip(x, 0, B)) / Z)))
    # a decreasing step density with mean 1 on [0, 4.5], n = 5: slab atoms (lengths : probabilities)
    atoms = {0.5: 0.4, 1.5: 0.2, 3.0: 0.2, 4.5: 0.2}
    assert abs(sum(l * w for l, w in atoms.items()) - 2) < 1e-12
    ls = np.array(list(atoms)); ws = np.array(list(atoms.values()))
    def cdf_step(x, ls=ls, ws=ws):
        x = np.clip(x, 0, None)
        return sum(w * np.minimum(x / l, 1.0) for l, w in zip(ls, ws))
    tests.append(('step density', 5, 4.5, (lambda rng, ls=ls, ws=ws: float(ls[rng.choice(len(ls), p=ws)])), cdf_step))
    for name, n, B, draw, cdf in tests:
        X = algorithm1(n, draw, MC, rng, B)
        d = ks(X[:, 0], cdf)
        r = dict(name=name, n=n, B=B, samples=MC, max_sum_error=float(np.abs(X.sum(1) - n).max()),
                 ks_coordinate=d, ks_pvalue=ks_pvalue(d, MC), ks_threshold=1.358 / math.sqrt(MC))
        print('Part 4:', r, flush=True); res.append(r)
    return dict(tests=res, seconds=round(time.time() - t0, 1))

if __name__ == '__main__':
    t0 = time.time()
    out = dict(part1=part1(), part2=part2(), part3=part3(), part4=part4())
    out['seconds'] = round(time.time() - t0, 1)
    out['env'] = dict(NMAX=NMAX, GRID=GRID, NSTEP=NSTEP, MC=MC, SEED=SEED)
    json.dump(out, open('data/mono11.json', 'w'), indent=1, default=str)
    print('all checks passed in', out['seconds'], 's')
