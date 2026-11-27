"""Verification program for the section on scaled copies, sections that are products, and a wider coupling of
the levels (Section 20).

Part A  exact (rational) checks: the joint mixes of Theorem 27 for the scaled pieces of Theorem 73,
        (1 - 2/beta) delta_0 + (2/beta) U[0, lam_i beta] with beta max lam <= sum lam; Lemma 76 for random
        piecewise-linear concave g; the inequality of Corollary 77 for random affine profiles; conditions (P_h)
        and (F_h) of Theorem 83 for the double frusta and the chamfered bodies of Corollary 84 at rational
        parameters.
Part B  floating point: the levels of Lemma 82 (sign and mass of alpha, the identity alpha + 2b = 3 nu,
        the slacks of (P_h) and (F_h)) for examples; the table of regular 2m-gons; constants quoted in the text.
Part C  Monte Carlo: joint mixes of scaled copies (Theorem 73); bodies with product sections (Theorem 75,
        Corollaries 77 and 80); the complete mixes of Theorem 83.
Results go to data/gen20.json; the log goes to stdout.
Environment: NA (default 400), NLEM (default 300), MC (default 20000), SEED (default 2026).
"""
import itertools, json, math, os, random, sys, time
from fractions import Fraction as Fr
import numpy as np
from scipy.integrate import quad
from scipy.stats import kstest, kstwo, beta as Beta

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "p12"))
sys.path.insert(0, os.path.join(HERE, "..", "p14"))
sys.path.insert(0, os.path.join(HERE, "..", "pB"))
sys.path.insert(0, os.path.join(HERE, "..", "pO"))
import jm12                                                          # noqa: E402
from concave14 import PLDensity, solve, arch_mix                    # noqa: E402
from bodies17 import ball_fibres                                    # noqa: E402
from open18 import simplex_projection_density, tabulated            # noqa: E402

NA = int(os.environ.get("NA", 400)); NLEM = int(os.environ.get("NLEM", 300))
MC = int(os.environ.get("MC", 20000)); SEED = int(os.environ.get("SEED", 2026))


# ===================================================================== Part A: exact checks
def partA1():
    """Theorem 73: the joint mix of Theorem 27 of the scaled pieces, exactly."""
    t0 = time.time(); rng = random.Random(SEED + 1)
    done = tight = zero = equal = beta2 = 0; segs_total = 0; kinds = {}; nmax = 0
    while done < NA:
        n = rng.randint(3, 8)
        mode = rng.random()
        if mode < 0.1:
            beta = Fr(2)
        else:
            beta = Fr(2) + Fr(rng.randint(1, 50), 10)                 # 2.1 .. 7
        lam = [Fr(rng.randint(1, 40), 20) for _ in range(n)]
        if rng.random() < 0.2:
            lam[rng.randrange(n)] = Fr(0)
        if rng.random() < 0.1:
            lam = [Fr(1)] * n
        if all(l == 0 for l in lam):
            continue
        if rng.random() < 0.3:                                          # make the condition tight
            j = max(range(n), key=lambda i: lam[i]); rest = sum(lam) - lam[j]
            if beta > 1 and rest > 0:
                lam[j] = rest / (beta - 1)                              # beta lam_j = sum lam
                if max(lam) != lam[j]:
                    continue
        if beta * max(lam) > sum(lam):
            continue
        pis = [({Fr(0): 1 - 2 / beta, l * beta: 2 / beta} if (l > 0 and beta > 2) else ({2 * l: Fr(1)} if l > 0 else {Fr(0): Fr(1)}))
               for l in lam]
        s, segs, st = jm12.assemble(pis)
        assert s == sum(lam)
        jm12.check_mixture(segs, s, [jm12.slab_target(pi) for pi in pis])
        done += 1; tight += beta * max(lam) == sum(lam); zero += any(l == 0 for l in lam)
        equal += len(set(lam)) == 1; beta2 += beta == 2; segs_total += len(segs); nmax = max(nmax, n)
        for k, v in st["stats"].items():
            key = k.split("/")[0]; kinds[key] = kinds.get(key, 0) + v
    out = dict(cases=done, tight=tight, with_zero=zero, equal=equal, beta_two=beta2, segments=segs_total,
               n_max=nmax, leaf_kinds=kinds, seconds=round(time.time() - t0, 1))
    print("Part A1:", out, flush=True)
    return out


# polynomials with Fraction coefficients, lists of coefficients in increasing powers
def pmul(p, q):
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def ppow(p, e):
    r = [Fr(1)]
    for _ in range(e):
        r = pmul(r, p)
    return r


def pint(p, lo, hi):
    return sum(c * (hi ** (i + 1) - lo ** (i + 1)) / (i + 1) for i, c in enumerate(p))


def random_concave_pl(rng):
    """random concave piecewise-linear g >= 0 on [0,1] with rational nodes: (nodes, values)."""
    k = rng.randint(0, 4)
    xs = sorted({Fr(0), Fr(1)} | {Fr(rng.randint(1, 59), 60) for _ in range(k)})
    sl = sorted([Fr(rng.randint(-40, 40), 10) for _ in range(len(xs) - 1)], reverse=True)
    ys = [Fr(0)]
    for i in range(len(xs) - 1):
        ys.append(ys[-1] + sl[i] * (xs[i + 1] - xs[i]))
    m = min(ys); lift = Fr(rng.randint(0, 3), 4) * rng.randint(0, 1)
    ys = [y - m + lift for y in ys]
    if all(y == 0 for y in ys):
        ys = [y + 1 for y in ys]
    return xs, ys


def partA2():
    """Lemma 76: w(s_bar) >= (k+1)/(k+gamma+2) for w = 1 - c s and density proportional to w^k g^gamma."""
    t0 = time.time(); rng = random.Random(SEED + 2)
    worst = None; done = 0; eq_cases = 0
    while done < NLEM:
        c = Fr(rng.randint(0, 20), 20); k = rng.randint(0, 6); gam = rng.randint(0, 6)
        xs, ys = random_concave_pl(rng)
        num = den = Fr(0)
        w = [Fr(1), -c]
        for i in range(len(xs) - 1):
            a, b = xs[i], xs[i + 1]
            sl = (ys[i + 1] - ys[i]) / (b - a)
            g = [ys[i] - sl * a, sl]
            P = pmul(ppow(w, k), ppow(g, gam))
            den += pint(P, a, b); num += pint(pmul(P, [Fr(0), Fr(1)]), a, b)
        if den == 0:
            continue
        sbar = num / den
        slack = (1 - c * sbar) - Fr(k + 1, k + gam + 2)
        assert slack >= 0, (c, k, gam, xs, ys, slack)
        worst = slack if worst is None else min(worst, slack)
        done += 1
    # the equality case c = 1, g(s) = s
    for k in range(0, 7):
        for gam in range(0, 7):
            P = pmul(ppow([Fr(1), Fr(-1)], k), ppow([Fr(0), Fr(1)], gam))
            sbar = pint(pmul(P, [Fr(0), Fr(1)]), Fr(0), Fr(1)) / pint(P, Fr(0), Fr(1))
            assert 1 - sbar == Fr(k + 1, k + gam + 2); eq_cases += 1
    out = dict(cases=done, min_slack=float(worst), equality_cases=eq_cases, seconds=round(time.time() - t0, 2))
    print("Part A2:", out, flush=True)
    return out


def partA3():
    """Corollary 77: r_j(s_bar) / max r_j >= (k_j + 1)/(d + 1) for affine profiles r_j = (1-s) a_j + s b_j."""
    t0 = time.time(); rng = random.Random(SEED + 3)
    done = 0; worst = None; joins = 0
    while done < NLEM:
        J = rng.randint(1, 4); ks = [rng.randint(1, 3) for _ in range(J)]; d = 1 + sum(ks)
        a = [Fr(rng.randint(0, 10), 10) for _ in range(J)]; b = [Fr(rng.randint(0, 10), 10) for _ in range(J)]
        if rng.random() < 0.2 and J >= 2:                                 # a join
            a = [Fr(1), Fr(0)] + a[2:]; b = [Fr(0), Fr(1)] + b[2:]
        if any(x + y == 0 for x, y in zip(a, b)):
            continue
        P = [Fr(1)]
        for kj, aj, bj in zip(ks, a, b):
            P = pmul(P, ppow([aj, bj - aj], kj))
        sbar = pint(pmul(P, [Fr(0), Fr(1)]), Fr(0), Fr(1)) / pint(P, Fr(0), Fr(1))
        for kj, aj, bj in zip(ks, a, b):
            rs = aj + (bj - aj) * sbar
            slack = rs / max(aj, bj) - Fr(kj + 1, d + 1)
            assert slack >= 0, (ks, a, b, slack)
            worst = slack if worst is None else min(worst, slack)
        joins += (J == 2 and a == [1, 0] and b == [0, 1])
        done += 1
    out = dict(cases=done, min_slack=float(worst), joins=joins, seconds=round(time.time() - t0, 2))
    print("Part A3:", out, flush=True)
    return out


def pl_rational(zs, rs):
    """piecewise-linear function with rational nodes; returns evaluator."""
    def r(z):
        z = abs(z)
        for i in range(len(zs) - 1):
            if zs[i] <= z <= zs[i + 1]:
                return rs[i] + (rs[i + 1] - rs[i]) * (z - zs[i]) / (zs[i + 1] - zs[i])
        raise ValueError(z)
    return r


def F_slack_exact(zs, rs, h):
    r = pl_rational(zs, rs)
    cs = {Fr(0), 1 - h} | {c for z in zs for c in (z, z - h) if 0 <= c <= 1 - h}
    return min(r(h) + r(h + c) - r(c) for c in cs)


def P_slack_affine_tail(sigma, h, k):
    """(P_h) when r(a) = sigma (2h - a) on [h, 1]: r(h)^(k-1) - 2 sigma^(k-1) int_h^1 (2h-a)^(k-2) da (exact)."""
    if k == 2:
        integral = 1 - h
    else:
        integral = (h ** (k - 1) - (2 * h - 1) ** (k - 1)) / (k - 1)
    return (sigma * h) ** (k - 1) - 2 * sigma ** (k - 1) * integral


def partA4():
    """Corollary 84 (d), (e): (P_h) and (F_h) exactly at rational parameters."""
    t0 = time.time(); rows = {}
    for k in range(2, 7):
        # double frusta r = 1 - (1 - rho) z, h = 1/(2(1 - rho)), rho in [0, 1/2)
        lo = Fr(1, 4) if k == 2 else Fr(0)
        rhos = [lo + (Fr(1, 2) - lo) * Fr(i, 40) for i in range(40)]
        wP = wF = None
        for rho in rhos:
            h = 1 / (2 * (1 - rho))
            if h == Fr(1, 2) and k == 2:
                continue
            p = P_slack_affine_tail(1 - rho, h, k); f = F_slack_exact([Fr(0), Fr(1)], [Fr(1), rho], h)
            assert p >= 0 and f >= 0, (k, rho, p, f)
            wP = p if wP is None else min(wP, p); wF = f if wF is None else min(wF, f)
        # below the threshold for k = 2: (P_h) fails at the h of (d)
        fails = None
        if k == 2:
            fails = all(P_slack_affine_tail(1 - rho, 1 / (2 * (1 - rho)), 2) < 0 for rho in [Fr(i, 100) for i in range(1, 25)])
        rows["double frusta k=%d" % k] = dict(cases=len(rhos), min_P=float(wP), min_F=float(wF), below_quarter_fails=fails)
        # chamfered r = min(1, 2 - e - z), h = (2 - e)/2, e in (0, 1) (k >= 3) or (0, 2/3] (k = 2)
        es = [Fr(i, 60) for i in range(1, 41 if k == 2 else 60)]
        wP = wF = None
        for e in es:
            h = (2 - e) / 2
            p = P_slack_affine_tail(Fr(1), h, k); f = F_slack_exact([Fr(0), 1 - e, Fr(1)], [Fr(1), Fr(1), 1 - e], h)
            assert p >= 0 and f >= 0, (k, e, p, f)
            wP = p if wP is None else min(wP, p); wF = f if wF is None else min(wF, f)
        rows["chamfered k=%d" % k] = dict(cases=len(es), min_P=float(wP), min_F=float(wF))
    print("Part A4:", rows, flush=True)
    return dict(rows=rows, seconds=round(time.time() - t0, 2))


# ===================================================================== Part B: levels of Lemma 82
class Profile:
    """even concave profile on [-1, 1] given on [0, 1] by a function, its derivative and breakpoints."""
    def __init__(self, name, f, df, bps):
        self.name, self.f, self.df, self.bps = name, f, df, sorted(set([0.0, 1.0] + list(bps)))

    def __call__(self, z):
        return self.f(np.abs(np.asarray(z, float)))


def pl_profile(name, zs, rs):
    zs = np.asarray(zs, float); rs = np.asarray(rs, float)
    sl = np.diff(rs) / np.diff(zs)
    f = lambda z: np.interp(z, zs, rs)
    df = lambda z: sl[np.clip(np.searchsorted(zs, z, side="right") - 1, 0, len(sl) - 1)]
    return Profile(name, f, df, zs)


def regular_polygon(m):
    """regular 2m-gon with inradius 1, flat sides at z = +-1: half-width r(z) on [0, 1]."""
    R = 1 / math.cos(math.pi / (2 * m))
    angs = [math.pi / 2 - math.pi / (2 * m) - j * math.pi / m for j in range(m + 1)]
    pts = sorted([(R * math.cos(t), R * math.sin(t)) for t in angs if math.cos(t) >= -1e-12 and math.sin(t) >= -1e-12],
                 key=lambda p: p[1])
    zs = [p[1] for p in pts]; xs = [p[0] for p in pts]
    if zs[0] > 1e-12:
        zs = [0.0] + zs; xs = [xs[0]] + xs
    zs[-1] = 1.0
    return pl_profile("regular %d-gon" % (2 * m), zs, xs)


def stadium(hp):
    R = 1 - hp
    f = lambda z: np.where(z <= hp, R, np.sqrt(np.clip(R * R - (z - hp) ** 2, 0, None)))
    df = lambda z: np.where(z <= hp, 0.0, -(z - hp) / np.sqrt(np.clip(R * R - (z - hp) ** 2, 1e-300, None)))
    return Profile("stadium h'=%g" % hp, f, df, [hp])


def integral(fun, a, b, bps):
    pts = sorted({a, b} | {p for p in bps if a < p < b})
    return sum(quad(fun, x0, x1, limit=400, epsabs=1e-14, epsrel=1e-12)[0] for x0, x1 in zip(pts[:-1], pts[1:]))


def P_slack(r, k, h):
    return float(r(h)) ** (k - 1) - 2 * integral(lambda a: float(r(a)) ** (k - 1) / (2 * h - a), h, 1.0, r.bps)


def F_slack(r, h):
    cs = {0.0, 1 - h} | {c for z in r.bps for c in (z, z - h) if 0 <= c <= 1 - h}
    if not all(isinstance(z, float) for z in r.bps) or r.name.startswith("stadium"):
        cs |= set(np.linspace(0, 1 - h, 2001).tolist())                 # curved profile: a fine grid as well
    return min(float(r(h) + r(h + c) - r(c)) for c in cs)


class LevelsH:
    """the 3-complete mix of the levels of Lemma 82 for nu proportional to r^(k-1) and partner bound h."""
    def __init__(self, r, k, h, ngrid=1500):
        self.r, self.k, self.h = r, k, h
        Z = integral(lambda a: float(r(a)) ** (k - 1), 0.0, 1.0, r.bps)
        self.nu = lambda a: r(a) ** (k - 1) / Z
        dnu = lambda a: ((k - 1) * r(a) ** (k - 2) * r.df(np.abs(np.asarray(a, float))) / Z) if k > 1 else 0.0 * a
        self.dnu = dnu
        tail = integral(lambda a: float(self.nu(a)) / (2 * h - a), h, 1.0, r.bps)
        self.alpha0 = 3 * float(self.nu(h)) - 6 * tail
        assert self.alpha0 >= -1e-12, "condition (P_h) fails"
        g = lambda t: (-3 * float(dnu(t)) + (6 * float(self.nu(t + h)) / (h - t) if t < 1 - h else 0.0)) / t ** 2
        brk = {h, 1 - h} | {float(z) for z in r.bps if 0 < z < h} | {float(z - h) for z in r.bps if 0 < z - h < h}
        pts = np.unique(np.concatenate([np.geomspace(1e-6, 1e-2, 120), np.linspace(1e-2, h, ngrid), sorted(brk)]))
        pts = pts[(pts > 0) & (pts <= h)]
        F = np.zeros_like(pts)
        for i in range(len(pts) - 2, -1, -1):
            F[i] = F[i + 1] + quad(g, pts[i], pts[i + 1], limit=100, epsabs=1e-13, epsrel=1e-12)[0]
        al = pts ** 2 * (self.alpha0 / h ** 2 + F)
        xr = np.linspace(h, 1.0, 3001)[1:]
        self.x = np.concatenate([[0.0], pts, xr]); self.al = np.concatenate([[0.0], al, 3 * self.nu(xr)])
        self.min_alpha_over_x = float(np.min(al / pts))
        self.mass = quad(self.alpha, 0, h, limit=400, points=sorted(brk - {h}), epsabs=1e-12)[0] \
            + integral(lambda a: 3 * float(self.nu(a)), h, 1.0, r.bps)
        cdf = np.concatenate([[0.0], np.cumsum(0.5 * (self.al[1:] + self.al[:-1]) * np.diff(self.x))])
        self.cdf = cdf / cdf[-1]

    def alpha(self, x):
        return float(np.interp(x, self.x, self.al))

    def b(self, x):
        h = self.h
        i1 = integral(lambda a: self.alpha(a) / a, x, h, list(self.r.bps) + [1 - h]) if x < h else 0.0
        hi = min(1.0, x + h)
        i2 = integral(lambda a: 3 * float(self.nu(a)) / (2 * h - a), h, hi, self.r.bps) if hi > h else 0.0
        return i1 + i2

    def sample(self, N, rng):
        A = np.interp(rng.random(N), self.cdf, self.x)
        delta = np.minimum(A, 2 * self.h - A) / 2
        D = (2 * rng.random(N) - 1) * delta
        B, C = A / 2 + D, A / 2 - D
        eps = np.where(rng.random(N) < 0.5, 1.0, -1.0)
        Zs = np.stack([eps * A, -eps * B, -eps * C], 1)
        perm = np.argsort(rng.random((N, 3)), axis=1)
        return np.take_along_axis(Zs, perm, axis=1)

    def level_cdf(self):
        grid = np.linspace(0, 1, 40001); dens = self.nu(grid)
        c = np.concatenate([[0.0], np.cumsum(0.5 * (dens[1:] + dens[:-1]) * np.diff(grid))]); c /= c[-1]
        return lambda z: np.where(np.asarray(z) >= 0, 0.5 + 0.5 * np.interp(np.abs(z), grid, c),
                                  0.5 - 0.5 * np.interp(np.abs(z), grid, c))


def level_examples():
    s2 = math.sqrt(2)
    return [
        ("regular octagon", pl_profile("regular octagon", [0, s2 - 1, 1], [1, 1, s2 - 1]), 2, 1 / s2),
        ("regular decagon", regular_polygon(5), 2, 0.7),
        ("regular 14-gon", regular_polygon(7), 2, None),
        ("regular 16-gon", regular_polygon(8), 2, None),
        ("hexagon rho=0.3", pl_profile("hexagon", [0, 1], [1, 0.3]), 2, 1 / 1.4),
        ("chamfered square e=0.6", pl_profile("chamfered", [0, 0.4, 1], [1, 1, 0.4]), 2, 0.7),
        ("stadium h'=0.75", stadium(0.75), 2, 0.75),
        ("elongated octahedron h'=0.75", pl_profile("elongated", [0, 0.75, 1], [1, 1, 0]), 3, 0.75),
        ("double frustum k=3 rho=0.1", pl_profile("double frustum", [0, 1], [1, 0.1]), 3, 1 / 1.8),
    ]


HSTEP = 0.0005


def best_h(r, k):
    hs = np.round(0.5 + HSTEP * np.arange(1, int(round(0.5 / HSTEP))), 10)     # grid of h in (1/2, 1)
    good = [(h, P_slack(r, k, h), F_slack(r, h)) for h in hs]
    good = [g for g in good if g[1] >= 0 and g[2] >= 0]
    if not good:
        return None
    hbest = max(good, key=lambda g: min(g[1], g[2]))
    return dict(h_lo=float(good[0][0]), h_hi=float(good[-1][0]), h=float(hbest[0]), P=float(hbest[1]), F=float(hbest[2]))


def partB():
    t0 = time.time(); rows = []; polys = []
    for m in range(3, 31):
        r = regular_polygon(m)
        res = best_h(r, 2)
        row = dict(n_sides=2 * m, ratio=float(r(1.0) / r(0.0)), ok=res is not None)
        if res:
            row.update(res)
        polys.append(row); print("Part B polygon:", row, flush=True)
    chosen = {p["n_sides"]: p["h"] for p in polys if p["ok"]}
    for name, r, k, h in level_examples():
        if h is None:
            h = chosen[int(name.split()[1].split("-")[0])]
        L = LevelsH(r, k, h)
        xi = np.linspace(0.01, h, 40)
        ident = max(abs(L.alpha(x) + 2 * L.b(x) - 3 * float(L.nu(x))) for x in xi)
        row = dict(body=name, k=k, h=h, P_slack=P_slack(r, k, h), F_slack=F_slack(r, h), alpha0=L.alpha0,
                   min_alpha_over_x=L.min_alpha_over_x, mass_err=abs(L.mass - 1), identity_err=ident)
        rows.append(row); print("Part B levels:", row, flush=True)
    dec = regular_polygon(5)
    consts = dict(plateau_bound=math.exp(0.5) / (2 * math.exp(0.5) - 1),
                  dec_r0=float(dec(0.0)), dec_rsum=float(dec(0.7) + dec(1.0)), dec_r0_formula=1 / math.cos(math.pi / 10))
    # regular pentagon: 2 max r / l(s_bar) against (5 + 3 sqrt 5)/2
    c5 = math.cos(math.pi / 5)
    th = 2 * math.pi / 5
    V = np.array([[math.cos(math.pi / 2 + j * th), math.sin(math.pi / 2 + j * th)] for j in range(5)])
    ybot, ytop = V[:, 1].min(), V[:, 1].max()
    def half_width(y):
        xs = []
        for j in range(5):
            p, q = V[j], V[(j + 1) % 5]
            if (p[1] - y) * (q[1] - y) <= 0 and p[1] != q[1]:
                t = (y - p[1]) / (q[1] - p[1]); xs.append(p[0] + t * (q[0] - p[0]))
        return (max(xs) - min(xs)) / 2
    rr = np.array([half_width(y) for y in V[:, 1]])                     # the widest chords pass through vertices
    sb = quad(lambda s: s * half_width(ybot + s * (ytop - ybot)), 0, 1, points=[0.618], limit=200)[0] / \
        quad(lambda s: half_width(ybot + s * (ytop - ybot)), 0, 1, points=[0.618], limit=200)[0]
    ratio = 2 * rr.max() / (half_width(ybot + 1e-12) * (1 - sb))
    consts.update(pentagon_sbar=sb, pentagon_sbar_formula=c5 / (1 + c5), pentagon_ratio=ratio,
                  pentagon_formula=(5 + 3 * math.sqrt(5)) / 2)
    print("Part B constants:", consts, flush=True)
    return dict(polygons=polys, levels=rows, constants=consts, hstep=HSTEP, seconds=round(time.time() - t0, 1))


# ===================================================================== Part C: simulations
def blotto_joint(beta, lam, rng):
    """one draw of the joint mix of Theorem 27 of (1 - 2/beta) delta_0 + (2/beta) U[0, lam_i beta]."""
    n = len(lam)
    beta = min(beta, sum(lam) / max(lam))                  # the computed beta may exceed the bound by rounding
    if beta <= 2 + 1e-14:
        lo = [2 * l for l in lam]; hi = list(lo)
    else:
        lo = [0.0] * n; hi = [l * beta for l in lam]
    xv = [2 * l for l in lam]; tol = 1e-12 * max(hi)
    while True:
        for j in range(n):                                  # snap to the ends what rounding left just inside
            if abs(xv[j] - lo[j]) <= tol: xv[j] = lo[j]
            elif abs(xv[j] - hi[j]) <= tol: xv[j] = hi[j]
        Fi = [j for j in range(n) if lo[j] < xv[j] < hi[j]]
        if len(Fi) <= 1:
            break
        i, k = Fi[0], Fi[1]
        tp = min(hi[i] - xv[i], xv[k] - lo[k]); tm = min(xv[i] - lo[i], hi[k] - xv[k])
        if rng.random() < tm / (tp + tm):
            if hi[i] - xv[i] <= xv[k] - lo[k]: xv[i], xv[k] = hi[i], xv[k] - tp
            else: xv[i], xv[k] = xv[i] + tp, lo[k]
        else:
            if xv[i] - lo[i] <= hi[k] - xv[k]: xv[i], xv[k] = lo[i], xv[k] + tm
            else: xv[i], xv[k] = xv[i] - tm, hi[k]
    k = Fi[0] if Fi else None
    info, segs = ("U", jm12.uni(xv)) if k is None else jm12.leaf(xv, k, lo[k], hi[k], xv[k])
    w = np.array([max(sg[2], 0.0) for sg in segs]); e = rng.choice(len(segs), p=w / w.sum())
    P, Q, _ = segs[e]; v = rng.random()
    return np.array([P[j] + v * (Q[j] - P[j]) for j in range(n)]), info.split("/")[0]


def scaled_mix(P, S, lam, N, rng):
    """Theorem 73 for the piecewise-linear density P (on [0,1]) with peeling S: returns (N, n), rows summing to
    mu * sum(lam)."""
    U, l, r = S["U"], S["l"], S["r"]
    W = (l + r) ** 2 / (2 * np.minimum(l, r))
    cw = np.concatenate([[0.0], np.cumsum(0.5 * (W[1:] + W[:-1]) * np.diff(U))])
    Us = np.interp(rng.random(N) * cw[-1], cw, U)
    ls, rs = np.interp(Us, U, l), np.interp(Us, U, r)
    beta = (ls + rs) / np.minimum(ls, rs)
    lam = np.asarray(lam, float); out = np.empty((N, len(lam))); kinds = {}
    pos = lam > 0
    for t in range(N):
        V = np.zeros(len(lam))
        V[pos], kd = blotto_joint(beta[t], list(lam[pos]), rng); kinds[kd] = kinds.get(kd, 0) + 1
        out[t] = lam * (P.mu - ls[t]) + ls[t] * V if ls[t] <= rs[t] else lam * (P.mu + rs[t]) - rs[t] * V
    return out, kinds


def pvalue(x, cdf):
    return float(kstwo.sf(kstest(x, cdf).statistic, len(x)))


def sim_scaled(name, dens, lam, N, rng, p=None):
    """joint mix of lam_i X for a density on [0,1] given as a function (tabulated at 4001 points)."""
    x = np.linspace(0, 1, 4001)
    P = PLDensity(x, dens(x), name); S = solve(P, n=3000)
    bstar = float(S["beta"].max())
    lam = np.asarray(lam, float)
    X, kinds = scaled_mix(P, S, lam, N, rng)
    tests = [pvalue(X[:, i] / lam[i], P.cdf) for i in range(len(lam)) if lam[i] > 0]
    return dict(kind="scaled copies", body=name, n=len(lam), samples=N, beta_star=bstar,
                ratio=float(lam.sum() / lam.max()), p_bound=p, max_sum_dev=float(np.abs(X.sum(1) - P.mu * lam.sum()).max()),
                tests=len(tests), min_p=float(min(tests)), kinds=kinds)


def level_mix(nu, lam, N, rng, ngrid=4001):
    """levels of Theorem 75: joint mix of lam_i S, S with the density nu on [0,1] (tabulated)."""
    x = np.linspace(0, 1, ngrid)
    P = PLDensity(x, nu(x)); S = solve(P, n=3000)
    L, _ = scaled_mix(P, S, lam, N, rng)
    return L, P, float(S["beta"].max())


def segment_fibres(sig, rng):
    """joint mix of U([-sig_i, sig_i]) by Lemma 1 (rows of sig with 2 max <= sum)."""
    return arch_mix(-sig, sig, rng)


def sim_product_body(name, d, blocks, nu, lam, N, rng, t=None):
    """Theorem 75 with c = 0 and blocks [(kind, k_j, r_j)], kind in {'seg', 'disc'}; scales lam."""
    lam = np.asarray(lam, float); n = len(lam)
    L, P, bstar = level_mix(nu, lam, N, rng)
    S = L / lam[None, :]
    tests = [pvalue(S[:, i], P.cdf) for i in range(n)]
    sums = [float(np.abs(L.sum(1) - P.mu * lam.sum()).max())]
    outside = 0.0; fibre_min = np.inf
    for kind, kj, rf in blocks:
        rr = rf(S)
        sig = lam[None, :] * rr
        fibre_min = min(fibre_min, float((sig.sum(1) - 2 * sig.max(1)).min()))
        if kind == "seg":
            W = segment_fibres(sig, rng)
            rel = W / np.where(sig > 0, sig, 1)
            tests += [pvalue((rel[:, i] + 1) / 2, lambda u: np.clip(u, 0, 1)) for i in range(n)]
            sums.append(float(np.abs(W.sum(1)).max())); outside = max(outside, float((np.abs(rel) - 1).max()))
        else:
            W = ball_fibres(sig, 2, rng)
            rad = np.linalg.norm(W, axis=2) / np.where(sig > 0, sig, 1)
            ang = (np.arctan2(W[:, :, 1], W[:, :, 0]) / (2 * np.pi)) % 1.0
            tests += [pvalue(rad[:, i] ** 2, lambda u: np.clip(u, 0, 1)) for i in range(n)]
            tests += [pvalue(ang[:, i], lambda u: np.clip(u, 0, 1)) for i in range(n)]
            sums.append(float(np.abs(W.sum(1)).max())); outside = max(outside, float((rad - 1).max()))
    return dict(kind="product sections", body=name, d=d, n=n, samples=N, beta_star=bstar,
                ratio=float(lam.sum() / lam.max()), max_sum_dev=max(sums), fibre_slack=fibre_min,
                outside=outside, tests=len(tests), min_p=float(min(tests)))


def sim_flat(name, r, k, h, fibre, n, N, rng):
    """Theorem 83: the 3-complete mix (and for n = 5 the 3-complete mix and a pair (Y, -Y))."""
    L = LevelsH(r, k, h)
    Z3 = L.sample(N, rng); r3 = r(np.abs(Z3))
    fib = float((r3.sum(1) - 2 * r3.max(1)).min())
    two_central = float(np.sort(np.abs(Z3), axis=1)[:, 1].max())
    W3 = fibre(r3, rng)
    Fz = L.level_cdf()
    if n == 3:
        Zs, W = Z3, W3
    else:
        grid = np.linspace(-1, 1, 40001); z = np.interp(rng.random(N), Fz(grid), grid)
        rz = r(np.abs(z)); w = fibre(np.stack([rz, rz], 1), rng)[:, 0]
        Zs = np.concatenate([Z3, z[:, None], -z[:, None]], 1)
        W = np.concatenate([W3, w[:, None], -w[:, None]], 1)
    perm = np.argsort(rng.random((N, n)), axis=1)
    Zs = np.take_along_axis(Zs, perm, axis=1); W = np.take_along_axis(W, perm[:, :, None], axis=1)
    rr = r(np.abs(Zs))
    tests = []
    for i in range(n):
        tests.append(pvalue(Zs[:, i], Fz))
        rel = W[:, i] / np.where(rr[:, i] > 0, rr[:, i], 1)[:, None]
        for c in range(rel.shape[1]):
            tests.append(pvalue((rel[:, c] + 1) / 2, lambda u: np.clip(u, 0, 1)))
    outside = float((np.abs(W).max(axis=2) - rr).max())
    return dict(kind="flat ends", body=name, k=k, h=h, n=n, samples=N, max_sum_dev=float(max(np.abs(Zs.sum(1)).max(), np.abs(W.sum(1)).max())),
                fibre_slack=fib, two_central_max=two_central, outside=outside, tests=len(tests), min_p=float(min(tests)))


def pentagon_profile_fn():
    th = 2 * np.pi / 5
    V = np.array([[np.cos(np.pi / 2 + j * th), np.sin(np.pi / 2 + j * th)] for j in range(5)])
    ybot, ytop = V[:, 1].min(), V[:, 1].max()
    zs = np.array([0.0, (V[1, 1] - ybot) / (ytop - ybot), 1.0])
    rs = np.array([abs(V[2, 0]), abs(V[1, 0]), 0.0])
    return lambda s: np.interp(s, zs, rs)


def partC():
    t0 = time.time(); rng = np.random.default_rng(SEED + 7); rows = []
    # Theorem 73: scaled copies
    tet = simplex_projection_density(np.array([0.0, 0.13, 0.55, 1.0]))
    cases = [
        ("(p+1)(1-x)^p, p=2", lambda x: 3 * (1 - x) ** 2, [1, 1, 1, 1], 2),
        ("(p+1)(1-x)^p, p=3", lambda x: 4 * (1 - x) ** 3, [1, 1, 1, 0.8, 0.7, 0.5], 3),
        ("polygon Q", lambda x: np.interp(x, [0, 0.2, 0.6, 1], [0, 2, 3, 1]), [1, 0.8, 0.7, 0.5], 1),
        ("projection of a tetrahedron", lambda x: tet(x), [1, 1, 0.9, 0.6, 0.5], 2),
        ("Beta(2,4)", lambda x: x * (1 - x) ** 3, [1, 0.9, 0.7, 0.6, 0.2], 4),
    ]
    for name, dens, lam, p in cases:
        row = sim_scaled(name, dens, lam, MC, rng, p)
        assert row["ratio"] >= row["beta_star"] - 1e-6, row
        rows.append(row); print("Part C:", row, flush=True)
    # Theorem 75 and Corollary 77: affine profiles
    hip = [("seg", 1, lambda S: 1 - S), ("seg", 1, lambda S: 1 - S / 2)]
    nu_hip = lambda x: (1 - x) * (1 - x / 2)
    for lam in ([1, 1, 1, 1], [1, 1, 0.8, 0.7, 0.5]):
        row = sim_product_body("hip roof, beta = 1/2", 3, hip, nu_hip, lam, MC, rng); rows.append(row); print("Part C:", row, flush=True)
    fr = [("seg", 1, lambda S: 1 - 0.75 * S), ("seg", 1, lambda S: 1 - 0.4 * S)]
    row = sim_product_body("frustum, ratios 1/4 and 3/5", 3, fr, lambda x: (1 - 0.75 * x) * (1 - 0.4 * x), [1] * 4, MC, rng)
    rows.append(row); print("Part C:", row, flush=True)
    jn = [("seg", 1, lambda S: 1 - S), ("disc", 2, lambda S: S)]
    row = sim_product_body("join of a segment and a disc", 4, jn, lambda x: (1 - x) * x ** 2, [1] * 5, MC, rng)
    rows.append(row); print("Part C:", row, flush=True)
    # Corollary 80: the half-ball (scaled copies) and the regular pentagon
    hb = [("disc", 2, lambda S: np.sqrt(np.clip(1 - S ** 2, 0, None)))]
    row = sim_product_body("half-ball", 3, hb, lambda x: 1 - x ** 2, [1, 1, 0.9, 0.6, 0.5], MC, rng)
    rows.append(row); print("Part C:", row, flush=True)
    pent = pentagon_profile_fn()
    for n in (6, 7):
        row = sim_product_body("regular pentagon", 2, [("seg", 1, pent)], pent, [1] * n, MC, rng)
        rows.append(row); print("Part C:", row, flush=True)
    # Theorem 83
    s2 = math.sqrt(2)
    octa = pl_profile("regular octagon", [0, s2 - 1, 1], [1, 1, s2 - 1])
    seg = lambda rr, rng: segment_fibres(rr, rng)[:, :, None]
    diamond = lambda rr, rng: np.stack([arch_mix(-rr, rr, rng) for _ in range(2)], axis=2)
    flat_cases = (("regular octagon", octa, 2, 1 / s2, seg, 3), ("regular octagon", octa, 2, 1 / s2, seg, 5),
                  ("regular decagon", regular_polygon(5), 2, 0.7, seg, 3),
                  ("hexagon rho=0.3", pl_profile("hexagon", [0, 1], [1, 0.3]), 2, 1 / 1.4, seg, 3),
                  ("stadium h'=0.75", stadium(0.75), 2, 0.75, seg, 3),
                  ("elongated octahedron h'=0.75", pl_profile("elongated", [0, 0.75, 1], [1, 1, 0]), 3, 0.75, diamond, 3))
    for args in flat_cases:
        row = sim_flat(*args, MC, rng)
        rows.append(row); print("Part C:", row, flush=True)
    m = sum(r["tests"] for r in rows); pmin = min(r["min_p"] for r in rows)
    # follow-up: the case with the smallest p-value, four further runs with four times as many samples
    worst = min(range(len(rows)), key=lambda i: rows[i]["min_p"]); follow = None
    if rows[worst]["kind"] == "flat ends":
        args = [a for a in flat_cases if a[0] == rows[worst]["body"] and a[5] == rows[worst]["n"]][0]
        follow = dict(body=args[0], n=args[5], samples=4 * MC,
                      min_p=[sim_flat(*args, 4 * MC, np.random.default_rng(SEED + 100 + rep))["min_p"] for rep in range(4)])
        print("Part C follow-up:", follow, flush=True)
    return dict(rows=rows, tests=m, min_p=pmin, chance_min_p=1 - (1 - pmin) ** m, follow=follow,
                seconds=round(time.time() - t0, 1))


if __name__ == "__main__":
    t0 = time.time()
    OUT = dict(partA1=partA1(), partA2=partA2(), partA3=partA3(), partA4=partA4())
    OUT["partB"] = partB()
    OUT["partC"] = partC()
    OUT["seconds"] = round(time.time() - t0, 1)
    OUT["settings"] = dict(NA=NA, NLEM=NLEM, MC=MC, SEED=SEED)
    os.makedirs(os.path.join(HERE, "data"), exist_ok=True)
    with open(os.path.join(HERE, "data", "gen20.json"), "w") as fh:
        json.dump(OUT, fh, indent=1, default=str)
    print("all checks passed in", OUT["seconds"], "s")
