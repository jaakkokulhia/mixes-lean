"""Cones, simplices and pyramids: checks of the section on cones in Part IV of the merged paper.

Part A  exact (rational) check of the slicing of a simplex: the moments E[z^alpha] of the recursive construction
        (level S with density k s^(k-1) on [0,1], fibre a scaled (k-1)-simplex) are computed through the
        recursion alone and compared with the moments k! alpha_1! ... alpha_k! / (k + |alpha|)! of the uniform
        distribution on the standard k-simplex.
Part B  exact check of the joint mixes of Part II (module jm12) in the setting of the cone theorem: for random
        rational scales lambda_1..lambda_n with (k+1) max lambda <= sum lambda, a share of them with equality, the
        level distributions G_i are replaced by step distributions with the same right end lambda_i and the same
        mean lambda_i/(k+1); the joint mix of Part II is built in exact arithmetic and its weights, its sum and its
        marginals are checked exactly, as in jm12.part3.
Part C  simulation (floating point): complete mixes of the uniform distribution on d-simplices (d = 2..5,
        n = d+1..d+3) by the recursive construction, on pyramids over cubes (d = 3, 4), and on the tetrahedron by
        the construction between two opposite edges (n = 4..7); sums, membership and Kolmogorov-Smirnov tests.
Writes data/cones16.json.
Environment: KMOM (default 6), DEGMOM (6), NLEVEL (400), MC (40000), MCT (200000), SEED (2026).
"""
import itertools, json, math, os, random, sys, time
from fractions import Fraction as Fr
import numpy as np
from scipy.stats import kstest, beta as Beta

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "p12"))
sys.path.insert(0, os.path.join(HERE, "..", "p14"))
import jm12
from concave14 import arch_mix

KMOM = int(os.environ.get("KMOM", 6)); DEGMOM = int(os.environ.get("DEGMOM", 6))
NLEVEL = int(os.environ.get("NLEVEL", 400)); MC = int(os.environ.get("MC", 40000))
MCT = int(os.environ.get("MCT", 200000)); SEED = int(os.environ.get("SEED", 2026))
LEVEL_KMAX = 4; LEVEL_EXTRA = 2


# ------------------------------------------------------------------ Part A: moments of the slicing
def compositions(total, parts):
    if parts == 0:
        if total == 0:
            yield ()
        return
    if parts == 1:
        yield (total,); return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest

def multinomial(total, parts):
    r = math.factorial(total)
    for p in parts:
        r //= math.factorial(p)
    return r

def moment_closed(alpha):
    k = len(alpha)
    num = math.factorial(k)
    for a in alpha:
        num *= math.factorial(a)
    return Fr(num, math.factorial(k + sum(alpha)))

MEMO = {(): Fr(1)}
def moment_rec(alpha):
    """E[z^alpha] for z = S (V, 1 - sum V), S with density k s^(k-1) on [0,1] and V the construction for the
    (k-1)-simplex, independent of S; uses only this recursion."""
    alpha = tuple(alpha)
    if alpha in MEMO:
        return MEMO[alpha]
    k = len(alpha); head, a = alpha[:-1], alpha[-1]
    tot = Fr(0)
    for j in range(a + 1):
        cj = math.comb(a, j) * (-1) ** j
        for beta in compositions(j, k - 1):
            tot += cj * multinomial(j, beta) * moment_rec(tuple(h + b for h, b in zip(head, beta)))
    val = Fr(k, k + sum(alpha)) * tot
    MEMO[alpha] = val
    return val

def partA():
    t0 = time.time(); count = 0
    for k in range(1, KMOM + 1):
        for deg in range(DEGMOM + 1):
            for alpha in compositions(deg, k):
                assert moment_rec(alpha) == moment_closed(alpha), (k, alpha)
                count += 1
    out = dict(k_max=KMOM, degree_max=DEGMOM, moments=count, seconds=round(time.time() - t0, 2))
    print("Part A:", out, flush=True)
    return out


# ------------------------------------------------------------------ Part B: joint mixes of the level laws
def step_law(lam, k, rng):
    """Finite slab law (length -> probability) of a step distribution with right end lam and mean lam/(k+1)."""
    if k == 1:
        return {lam: Fr(1)}                               # G is uniform on [0, lam]
    target = Fr(2, k + 1)                                # mean slab length divided by lam
    J = 2 if rng.random() < 1 / 3 else 1
    rs = sorted(set(Fr(rng.randint(1, 59), 60) * target for _ in range(J)))
    ws = [Fr(rng.randint(1, 9)) for _ in rs]
    tot = sum(ws); ws = [w / tot for w in ws]
    rbar = sum(r * w for r, w in zip(rs, ws))
    wt = (target - rbar) / (1 - rbar)                    # weight of the top atom; 0 < wt < 1 as rbar < target < 1
    law = {lam * r: (1 - wt) * w for r, w in zip(rs, ws)}
    law[lam] = law.get(lam, 0) + wt
    return law

def scales(k, n, rng):
    """Random rational scales with (k+1) max <= sum: all equal (n = k+1), one tight, or generic."""
    mode = rng.random()
    if n == k + 1 and mode < 0.25:
        return [Fr(1)] * n, "equal"
    while True:
        lams = [Fr(rng.randint(1, 40), 40) for _ in range(n)]
        if mode < 0.55:
            others = lams[:-1]
            top = sum(others) / k
            if top >= max(others):
                lams[-1] = top
                return lams, "tight"
            continue
        if (k + 1) * max(lams) <= sum(lams):
            return lams, ("tight" if (k + 1) * max(lams) == sum(lams) else "generic")

def partB():
    t0 = time.time(); rng = random.Random(SEED + 2)
    done = 0; modes = {}; nseg = 0; ntup = 0; kinds = {}; cells = 0; nmax = 0
    while done < NLEVEL:
        k = rng.randint(1, LEVEL_KMAX)
        n = rng.randint(max(3, k + 1), k + 1 + LEVEL_EXTRA)
        lams, mode = scales(k, n, rng)
        pis = [step_law(l, k, rng) for l in lams]
        s, segs, st = jm12.assemble(pis)
        assert s == sum(lams) / (k + 1)
        assert max(max(pi) for pi in pis) == max(lams) <= s
        cells += jm12.check_mixture(segs, s, [jm12.slab_target(pi) for pi in pis])
        for kk, v in st["stats"].items():
            key = kk.split("/")[0]; kinds[key] = kinds.get(key, 0) + v
        done += 1; modes[mode] = modes.get(mode, 0) + 1
        nseg += len(segs); ntup += st["tuples"]; nmax = max(nmax, n)
    out = dict(cases=done, modes=modes, k_max=LEVEL_KMAX, extra=LEVEL_EXTRA, n_max=nmax, tuples=ntup,
               segments=nseg, cells=cells, leaf_kinds=kinds, seconds=round(time.time() - t0, 1))
    print("Part B:", out, flush=True)
    return out


# ------------------------------------------------------------------ Part C: simulation
def level_mix(lams, k, rng):
    """Joint mix of the levels S_i (density k s^(k-1) lam_i^(-k) on [0, lam_i]) via T_i = lam_i - S_i."""
    laws = [jm12.law_uniform(l) if k == 1 else jm12.law_power(k - 1, l) for l in lams]
    T, _ = jm12.sample_algorithm(laws, 1, rng)
    return np.asarray(lams, float) - T[0]

def simplex_mix(lams, k, rng):
    """Joint mix of the uniform distributions on lam_i * Delta_k, Delta_k = {z >= 0, sum z <= 1} in R^k."""
    lams = np.asarray(lams, float); n = len(lams)
    if k == 0:
        return np.zeros((n, 0))
    S = level_mix(lams, k, rng)
    w = simplex_mix(S, k - 1, rng)
    return np.concatenate([w, (S - w.sum(1))[:, None]], 1)

def ks_tests(samples_and_cdfs):
    ps = [kstest(x, cdf).pvalue for x, cdf in samples_and_cdfs]
    return len(ps), float(min(ps))

def sim_simplex(d, n, N, rng):
    Z = np.array([simplex_mix(np.ones(n), d, rng) for _ in range(N)])          # (N, n, d)
    target = n / (d + 1)
    bary = np.concatenate([Z, 1 - Z.sum(2, keepdims=True)], 2)                    # (N, n, d+1), Dirichlet(1,..,1)
    tests = [(bary[:, i, j], Beta(1, d).cdf) for i in range(n) for j in range(d + 1)]
    tests += [(bary[:, i, 0] + bary[:, i, 1], Beta(2, d - 1).cdf) for i in range(n)]
    m, pmin = ks_tests(tests)
    return dict(body="simplex", d=d, n=n, samples=N, max_sum_dev=float(np.abs(Z.sum(1) - target).max()),
                min_coord=float(bary.min()), tests=m, min_p=pmin)

def sim_pyramid(d, n, N, rng):
    """Pyramid {(x, s): 0 <= x_j <= s <= 1} over the cube [0,1]^(d-1) at level 1, apex 0."""
    S = np.array([level_mix(np.ones(n), d, rng) for _ in range(N)])               # (N, n), density d s^(d-1)
    X = np.stack([arch_mix(np.zeros_like(S), S, rng) for _ in range(d - 1)], 2)   # (N, n, d-1)
    sums = np.concatenate([X.sum(1), S.sum(1)[:, None]], 1)
    target = np.array([n * d / (2 * (d + 1))] * (d - 1) + [n * d / (d + 1)])
    U = X / S[:, :, None]
    tests = [(S[:, i], Beta(d, 1).cdf) for i in range(n)]
    tests += [(U[:, i, j], lambda t: np.clip(t, 0, 1)) for i in range(n) for j in range(d - 1)]
    m, pmin = ks_tests(tests)
    slack = min(float(X.min()), float((S[:, :, None] - X).min()), float((1 - S).min()))
    return dict(body="pyramid", d=d, n=n, samples=N, max_sum_dev=float(np.abs(sums - target).max()),
                min_coord=slack, tests=m, min_p=pmin)

def sim_tetra(n, N, rng):
    """Tetrahedron {0 <= x <= 1, 0 <= y <= 1-x, 0 <= z <= x}, sliced between the edges at x = 0 and x = 1."""
    X0 = rng.beta(2, 2, N); Y0 = rng.random(N) * 6 * X0 * (1 - X0)
    w = np.sqrt(np.clip(0.25 - Y0 / 6, 0, None))                                    # horizontal slab of 6x(1-x)
    X = arch_mix(np.repeat((0.5 - w)[:, None], n, 1), np.repeat((0.5 + w)[:, None], n, 1), rng)
    Y = arch_mix(np.zeros_like(X), 1 - X, rng)
    Z = arch_mix(np.zeros_like(X), X, rng)
    sums = np.stack([X.sum(1), Y.sum(1), Z.sum(1)], 1)
    target = np.array([n / 2, n / 4, n / 4])
    bary = np.stack([1 - X - Y, Y, X - Z, Z], -1)                                   # vertices (0,0,0),(0,1,0),(1,0,0),(1,0,1)
    tests = [(bary[:, i, j], Beta(1, 3).cdf) for i in range(n) for j in range(4)]
    tests += [(bary[:, i, 0] + bary[:, i, 1], Beta(2, 2).cdf) for i in range(n)]
    m, pmin = ks_tests(tests)
    return dict(body="tetrahedron", d=3, n=n, samples=N, max_sum_dev=float(np.abs(sums - target).max()),
                min_coord=float(bary.min()), tests=m, min_p=pmin)

def partC():
    t0 = time.time(); rng = np.random.default_rng(SEED + 3); rows = []
    for d in (2, 3, 4, 5):
        for n in range(d + 1, d + 4):
            r = sim_simplex(d, n, MC, rng); rows.append(r); print("Part C:", r, flush=True)
    for d, ns in ((3, (4, 5, 6)), (4, (5, 6))):
        for n in ns:
            r = sim_pyramid(d, n, MC, rng); rows.append(r); print("Part C:", r, flush=True)
    for n in (4, 5, 6, 7):
        r = sim_tetra(n, MCT, rng); rows.append(r); print("Part C:", r, flush=True)
    m = sum(r["tests"] for r in rows); pmin = min(r["min_p"] for r in rows)
    out = dict(rows=rows, tests=m, min_p=pmin, chance_min_p=1 - (1 - pmin) ** m, seconds=round(time.time() - t0, 1))
    print("Part C: tests", m, "smallest p", pmin, flush=True)
    return out


if __name__ == "__main__":
    t0 = time.time()
    OUT = dict(partA=partA(), partB=partB(), partC=partC())
    OUT["seconds"] = round(time.time() - t0, 1)
    OUT["settings"] = dict(KMOM=KMOM, DEGMOM=DEGMOM, NLEVEL=NLEVEL, MC=MC, MCT=MCT, SEED=SEED)
    os.makedirs(os.path.join(HERE, "data"), exist_ok=True)
    with open(os.path.join(HERE, "data", "cones16.json"), "w") as fh:
        json.dump(OUT, fh, indent=1, default=str)
    print("all checks passed in %.0f s" % OUT["seconds"])
