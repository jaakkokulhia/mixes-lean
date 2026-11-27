"""Verification program for the note 'Explicit Complete Mixes for Concave and Unimodal Densities'.

Part 1  exact (rational) check of Proposition 3, the complete mix of P_beta, on a grid of (n, beta).
Part 2  the peeling process of Theorem 1 for test densities: phases, largest ratio beta, monotonicity of
        the ends, integral form of the differential equation, and the decomposition f = int pi_U dU;
        statistics over random piecewise-linear concave densities.
Part 3  Monte Carlo test of Algorithm 1: sums and Kolmogorov-Smirnov distances of the first coordinate.
Part 4  the largest ratio beta* for some unimodal densities that are not concave.
Results are written to data/concave14.json; the log goes to stdout.
Environment: NMAX (default 20), GRID (40), NLEV (4000), NRAND (1000), MC (100000), NBETA (200), SEED (2026).
"""
import json, os, time, math
from fractions import Fraction as Fr
import numpy as np
from scipy.stats import kstwo
from scipy.special import betaln

NMAX = int(os.environ.get("NMAX", 20)); GRID = int(os.environ.get("GRID", 40))
NLEV = int(os.environ.get("NLEV", 4000)); NRAND = int(os.environ.get("NRAND", 1000))
MC = int(os.environ.get("MC", 100000)); SEED = int(os.environ.get("SEED", 2026))
NBETA = int(os.environ.get("NBETA", 200))
OUT = {}


# ===================================================================== Proposition 3 (pieces)
def piece_mixture(n, beta):
    """complete mix of P_beta = (1 - 2/beta) delta_0 + (2/beta) U[0, beta], 2 <= beta <= n, as a list of
    (weight, tuple of n intervals); works with Fractions and with floats."""
    if n >= 4 and 3 * beta <= 2 * n:                      # case B
        k = min(n - 1, int((2 * n) // beta))
        u = 2 * n - k * beta
        t1 = [(0, 0)] * (n - 1 - k) + [(0, beta)] * k + [(0, u)]
        t2 = [(0, 0)] * (n - k) + [(0, beta)] * (k - 1) + [(u, beta)]
        parts, case = [(u / beta, t1), (1 - u / beta, t2)], "B"
    else:                                                  # case D
        x = n - beta
        t1 = [(0, 0)] * (n - 2) + [(x, beta)] * 2
        t2 = [(0, 0)] * (n - 3) + [(0, x), (0, beta), (x, beta)]
        parts, case = [(1 - 2 * x / beta, t1), (2 * x / beta, t2)], "D"
    return case, [(w, t) for w, t in parts if w != 0]


def check_piece(n, beta):
    case, parts = piece_mixture(n, beta)
    assert sum(w for w, _ in parts) == 1, "weights"
    for w, ivs in parts:
        assert 0 < w <= 1, "weight range"
        assert len(ivs) == n
        assert sum(l + r for l, r in ivs) == 2 * n, "midpoint sum"
        L = [r - l for l, r in ivs]
        assert min(L) >= 0 and 2 * max(L) <= sum(L), "polygon inequality"
        assert all(0 <= l <= r <= beta for l, r in ivs), "support"
    atom = sum(w * Fr(sum(1 for l, r in ivs if r == l == 0), n) for w, ivs in parts)
    assert atom == 1 - 2 / beta, "atom at 0"
    assert all(not (l == r and l != 0) for w, ivs in parts for l, r in ivs), "atom elsewhere"
    bps = sorted(set([Fr(0), beta] + [e for w, ivs in parts for iv in ivs for e in iv]))
    for lo, hi in zip(bps[:-1], bps[1:]):
        m = (lo + hi) / 2
        dens = sum(w * sum(Fr(1, n) / (r - l) for l, r in ivs if l < m < r) for w, ivs in parts)
        assert dens == 2 / beta ** 2, ("density", n, beta, lo, hi)
    return case, len(parts)


def part1():
    t0 = time.time()
    cnt = {"B": 0, "D": 0}; ncases = 0; nbound = 0; maxparts = 0
    for n in range(3, NMAX + 1):
        betas = set(Fr(2) + Fr(n - 2) * Fr(j, GRID) for j in range(GRID + 1))
        bound = set([Fr(2 * n, 3)] if n >= 3 else []) | set(Fr(2 * n, k) for k in range(3, n)) | {Fr(2), Fr(n)}
        bound = set(b for b in bound if 2 <= b <= n) - betas
        for beta in sorted(betas) + sorted(bound):
            case, k = check_piece(n, beta)
            cnt[case] += 1; maxparts = max(maxparts, k)
            if beta in bound:
                nbound += 1
            else:
                ncases += 1
    res = dict(nmax=NMAX, grid=GRID, cases=ncases, boundary=nbound, caseB=cnt["B"], caseD=cnt["D"],
               maxparts=maxparts, seconds=time.time() - t0)
    print("Part 1:", res, flush=True)
    OUT["part1"] = res


# ===================================================================== densities and the peeling
class PLDensity:
    """continuous piecewise-linear unimodal density on [0, 1]; positions are measured from the mean,
    l = mu - x and r = x - mu, and levels by d = f(mu) - U."""

    def __init__(self, xs, ys, name=""):
        xs = np.asarray(xs, float); ys = np.asarray(ys, float)
        xs = (xs - xs[0]) / (xs[-1] - xs[0])
        ys = ys / np.sum(0.5 * (ys[1:] + ys[:-1]) * np.diff(xs))
        h = np.diff(xs)
        mu = float(np.sum(h * (xs[:-1] * (2 * ys[:-1] + ys[1:]) + xs[1:] * (ys[:-1] + 2 * ys[1:])) / 6.0))
        self.name = name
        self.mu = mu
        k = int(np.searchsorted(xs, mu))
        if k > 0 and mu - xs[k - 1] < 1e-13:              # mean within rounding of a node: use the node
            k -= 1
        if k < len(xs) and xs[k] != mu and xs[k] - mu < 1e-13:
            mu = float(xs[k]); self.mu = mu
        if xs[k] != mu:
            fm = float(np.interp(mu, xs, ys))
            xs = np.insert(xs, k, mu); ys = np.insert(ys, k, fm)
        self.xs, self.ys, self.fmu = xs, ys, float(ys[k])
        dy = np.diff(ys); imax = int(np.argmax(ys))
        self.unimodal = bool(np.all(dy[:imax] >= 0) and np.all(dy[imax:] <= 0))
        sl = dy / np.diff(xs)
        self.concave = bool(np.all(np.diff(sl) <= 1e-9 * max(1.0, np.abs(sl).max())))
        self.vL, self.gL = mu - xs[k::-1], ys[k::-1] - self.fmu
        self.vR, self.gR = xs[k:] - mu, ys[k:] - self.fmu
        self.QL, self.QR = self._cum(self.vL, self.gL), self._cum(self.vR, self.gR)
        self.P0 = np.concatenate([[0.0], np.cumsum(0.5 * (ys[1:] + ys[:-1]) * np.diff(xs))])

    @staticmethod
    def _seg(v1, g1, s, W):          # int_0^W (v1 + w)(g1 + s w) dw
        return v1 * g1 * W + (g1 + s * v1) * W * W / 2.0 + s * W ** 3 / 3.0

    def _cum(self, v, g):
        s = np.diff(g) / np.diff(v)
        return np.concatenate([[0.0], np.cumsum(self._seg(v[:-1], g[:-1], s, np.diff(v)))])

    def _Q(self, v, g, Qc, t):
        i = np.clip(np.searchsorted(v, t, side="right") - 1, 0, len(v) - 2)
        s = (g[i + 1] - g[i]) / (v[i + 1] - v[i])
        return Qc[i] + self._seg(v[i], g[i], s, t - v[i])

    def DL(self, l, d):              # int_{mu-l}^{mu} (mu - t)(f(t) - U) dt with U = f(mu) - d
        return 0.5 * d * l * l + self._Q(self.vL, self.gL, self.QL, l)

    def DR(self, r, d):
        return 0.5 * d * r * r + self._Q(self.vR, self.gR, self.QR, r)

    @staticmethod
    def _reach(v, g, d):             # largest v with g(v) >= -d, computed from the inner node
        j = int(np.argmax(g)); vt, gt = v[j:], g[j:]
        i = np.clip(np.searchsorted(-gt, d, side="right") - 1, 0, len(vt) - 1)
        ii = np.minimum(i, len(vt) - 2)
        with np.errstate(divide="ignore", invalid="ignore"):
            out = vt[ii] + (gt[ii] + d) / (gt[ii] - gt[ii + 1]) * (vt[ii + 1] - vt[ii])
        return np.where(i >= len(vt) - 1, vt[-1], out)

    def lmax(self, d):
        return self._reach(self.vL, self.gL, np.asarray(d, float))

    def rmax(self, d):
        return self._reach(self.vR, self.gR, np.asarray(d, float))

    def _inv(self, Dfun, m, d, top):
        lo = np.zeros_like(top); hi = top.copy()
        bad = Dfun(hi, d) < m * (1 - 1e-12)
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            big = Dfun(mid, d) > m
            hi = np.where(big, mid, hi); lo = np.where(big, lo, mid)
            if np.all(hi - lo <= 4e-16 * np.maximum(hi, 1e-300)):
                break
        return np.where(bad, top, 0.5 * (lo + hi)), bad

    def inv_L(self, m, d):
        return self._inv(self.DL, m, d, self.lmax(d) + 0.0 * m)

    def inv_R(self, m, d):
        return self._inv(self.DR, m, d, self.rmax(d) + 0.0 * m)

    def cdf(self, x):
        x = np.clip(np.asarray(x, float), 0.0, 1.0)
        i = np.clip(np.searchsorted(self.xs, x, side="right") - 1, 0, len(self.xs) - 2)
        return self.P0[i] + 0.5 * (self.ys[i] + np.interp(x, self.xs, self.ys)) * (x - self.xs[i])


def phase_state(P, side, l0, r0, d):
    d = np.asarray(d, float)
    if side == "L":                  # left end cut; right end frozen or on the level set
        r = np.minimum(r0, P.rmax(d)); m = P.DR(r, d); l, bad = P.inv_L(m, d)
    else:
        l = np.minimum(l0, P.lmax(d)); m = P.DL(l, d); r, bad = P.inv_R(m, d)
    return l, r, m, bad


def solve(P, n=NLEV, nend=20, tol=1e-9):
    """phase solution on a grid of d = f(mu) - U (decreasing); switch levels are located by bisection."""
    s = np.linspace(0.0, 1.0, n + 1)[:-1]
    grid = P.fmu * (1.0 - s) ** 2 * (1.0 + 2.0 * s)      # U / f(mu) = 3 s^2 - 2 s^3
    grid = np.concatenate([grid, grid[-1] * 0.5 ** np.arange(1, nend)])
    side = "L" if P.mu < 0.5 else "R"
    l0, r0 = P.mu, 1.0 - P.mu
    if P.mu == 0.5:
        l, r, _, _ = phase_state(P, "L", l0, r0, grid[1:2])
        side = "L" if r[0] >= l[0] else "R"
    sw, chunks, i0 = [], [], 0
    while True:
        dg = grid[i0:]
        l, r, m, bad = phase_state(P, side, l0, r0, dg)
        g = (r - l) if side == "L" else (l - r)
        neg = np.where(g[1:] < -tol * np.maximum(l, r)[1:])[0]
        if len(neg) == 0:
            chunks.append((dg, l, r, m, bad, side)); break
        j = neg[0] + 1
        hi, lo = dg[j - 1], dg[j]
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            lm, rm, _, _ = phase_state(P, side, l0, r0, np.array([mid]))
            if ((rm - lm) if side == "L" else (lm - rm))[0] >= 0:
                hi = mid
            else:
                lo = mid
            if hi - lo <= 4e-16 * hi:
                break
        ls, rs, ms, _ = phase_state(P, side, l0, r0, np.array([hi]))
        chunks.append((np.append(dg[:j], hi), np.append(l[:j], ls), np.append(r[:j], rs),
                       np.append(m[:j], ms), np.append(bad[:j], False), side))
        sw.append(P.fmu - hi)
        side = "R" if side == "L" else "L"
        l0, r0 = float(ls[0]), float(rs[0])
        i0 += j
        grid = np.concatenate([grid[:i0], [hi], grid[i0:]])
        if len(sw) > 100:
            raise RuntimeError("too many switches")
    d = np.concatenate([c[0] for c in chunks]); l = np.concatenate([c[1] for c in chunks])
    r = np.concatenate([c[2] for c in chunks]); m = np.concatenate([c[3] for c in chunks])
    bad = np.concatenate([c[4] for c in chunks])
    keep = np.concatenate([[True], np.diff(d) < 0])
    d, l, r, m, bad = d[keep], l[keep], r[keep], m[keep], bad[keep]
    l[0], r[0] = P.mu, 1.0 - P.mu                       # level 0: the ends of the support (exact)
    U = P.fmu - d
    return dict(U=U, d=d, l=l, r=r, m=m, bad=bad, switches=sw, beta=(l + r) / np.minimum(l, r),
                first=chunks[0][5])


def diagnostics(P, S, nx=1001):
    """monotonicity, moment balance, integral form of the ODE, and the decomposition error."""
    U, l, r, m = S["U"], S["l"], S["r"], S["m"]
    out = {}
    out["mono"] = float(max(np.max(np.diff(l)), np.max(np.diff(r))))      # should be <= 0 (ends move inwards)
    bal = np.abs(P.DL(l, S["d"]) - P.DR(r, S["d"])) / np.maximum(m, 1e-300)
    out["balance"] = float(np.max(bal[1:]))
    rhs = 0.5 * np.maximum(l, r) ** 2
    integ = np.concatenate([[0.0], np.cumsum(0.5 * (rhs[1:] + rhs[:-1]) * np.diff(U))])
    out["ode"] = float(np.max(np.abs(m[0] - integ - m)))
    # decomposition: F_mix(x) = int [ (min(x, B) - A)^+ + w 1{E <= x} ] dU, cells split at crossings of E
    A, B = P.mu - l, P.mu + r
    mn, mx = np.minimum(l, r), np.maximum(l, r)
    w = (mx ** 2 - mn ** 2) / (2 * mn)
    hU = np.diff(U)
    left = (l[:-1] + l[1:]) < (r[:-1] + r[1:])                         # regime of each cell
    E0 = np.where(left, A[:-1], B[:-1]); E1 = np.where(left, A[1:], B[1:])
    w0, w1 = w[:-1], w[1:]
    xs = np.linspace(0.0, 1.0, nx)
    err = 0.0; mass = None
    for x in xs:
        ui = np.clip(np.minimum(x, B) - A, 0.0, None)
        uni = np.sum(0.5 * (ui[1:] + ui[:-1]) * hU)
        in0, in1 = E0 <= x, E1 <= x
        full = in0 & in1
        part = in0 ^ in1
        with np.errstate(divide="ignore", invalid="ignore"):
            th = np.where(part, (x - E0) / (E1 - E0), 0.0)
        wt = w0 + th * (w1 - w0)
        at = np.sum(np.where(full, 0.5 * (w0 + w1) * hU, 0.0))
        at += np.sum(np.where(part & in0, 0.5 * th * hU * (w0 + wt), 0.0))
        at += np.sum(np.where(part & in1, 0.5 * (1 - th) * hU * (wt + w1), 0.0))
        Fm = uni + at
        err = max(err, abs(Fm - float(P.cdf(x))))
        mass = Fm
    out["decomp"] = err
    out["mass"] = float(mass)
    # mean of every piece
    piece_mass = (l + r) + w
    E = np.where(l < r, A, B)
    pm = ((A + B) / 2 * (l + r) + w * E) / piece_mass
    out["piece_mean"] = float(np.max(np.abs(pm - P.mu)))
    return out


def tabulate(fun, N=2000):
    x = np.linspace(0.0, 1.0, N + 1)
    return x, fun(x)


def test_densities():
    D = {}
    D["triangle"] = PLDensity([0, 0.2, 1], [0, 1, 0], "triangle, mode 0.2")
    D["twoswitch"] = PLDensity([0, 0.2, 0.6, 1], [0, 2, 3, 1], "polygon (0,0),(0.2,2),(0.6,3),(1,1)")
    D["linear"] = PLDensity([0, 1], [2, 0], "decreasing linear")
    D["trapezoid"] = PLDensity([0, 0.3, 0.5, 1], [0.2, 1, 1, 0.1], "trapezoid")
    D["semicircle"] = PLDensity(*tabulate(lambda x: np.sqrt(np.clip(x * (1 - x), 0, None))), "semicircle")
    D["parabola"] = PLDensity(*tabulate(lambda x: 1 - ((x - 0.25) / 0.8) ** 2), "1-((x-0.25)/0.8)^2")
    D["power"] = PLDensity(*tabulate(lambda x: np.clip(x, 0, 1) ** 0.3 * np.clip(1 - x, 0, 1) ** 0.6),
                           "x^0.3 (1-x)^0.6")
    D["sqrt"] = PLDensity(*tabulate(lambda x: np.sqrt(np.clip(x, 0, 1))), "sqrt(x)")
    return D


def random_concave(rng):
    k = int(rng.integers(1, 6))
    xs = np.sort(np.concatenate([[0.0, 1.0], rng.uniform(0, 1, k)]))
    sl = np.sort(rng.normal(0, 4, len(xs) - 1))[::-1]
    ys = np.concatenate([[0.0], np.cumsum(sl * np.diff(xs))])
    ys = ys - ys.min() + rng.uniform(0, 1) * rng.integers(0, 2)
    return PLDensity(xs, ys)


def part2():
    t0 = time.time()
    res = {}
    sols = {}
    for key, P in test_densities().items():
        assert P.concave
        S = solve(P)
        dg = diagnostics(P, S)
        dg["ode_half"] = diagnostics(P, solve(P, n=NLEV // 2), nx=3)["ode"]
        res[key] = dict(name=P.name, mu=P.mu, fmu=P.fmu, switches=S["switches"], first=S["first"],
                        beta_max=float(np.max(S["beta"])), beta_end=float(S["beta"][-1]),
                        bad=int(S["bad"].sum()), levels=len(S["U"]), **dg)
        sols[key] = (P, S)
        print("Part 2:", key, {k: (round(v, 12) if isinstance(v, float) else v) for k, v in res[key].items()},
              flush=True)
    # random piecewise-linear concave densities
    rng = np.random.default_rng(SEED)
    nsw = {}; bmax = 0.0; mono = -1.0; badc = 0; ode = 0.0; dec = 0.0; ndec = 0; t1 = time.time()
    for i in range(NRAND):
        P = random_concave(rng)
        S = solve(P, n=2000)
        k = len(S["switches"]); nsw[k] = nsw.get(k, 0) + 1
        bmax = max(bmax, float(np.max(S["beta"])))
        mono = max(mono, float(max(np.max(np.diff(S["l"])), np.max(np.diff(S["r"])))))
        badc += int(S["bad"].sum())
        if i < 100:
            dg = diagnostics(P, S, nx=201)
            ode = max(ode, dg["ode"]); dec = max(dec, dg["decomp"]); ndec += 1
    res["random"] = dict(n=NRAND, switches={str(k): v for k, v in sorted(nsw.items())}, beta_max=bmax,
                         mono=mono, bad=badc, ode=ode, decomp=dec, ndecomp=ndec, seconds=time.time() - t1)
    print("Part 2: random", res["random"], flush=True)
    res["seconds"] = time.time() - t0
    OUT["part2"] = res
    return sols


# ===================================================================== Algorithm 1 (sampling)
def arch_mix(lo, hi, rng):
    """Lemma 1 for tuples given by arrays lo, hi of shape (N, n): returns X of shape (N, n)."""
    N, n = lo.shape
    lam = hi - lo; mid = 0.5 * (lo + hi)
    k = np.argmax(lam, axis=1)
    rows = np.arange(N)
    lk = lam[rows, k]
    others = np.argsort(np.where(np.arange(n)[None, :] == k[:, None], -1, np.arange(n)[None, :]), axis=1)[:, 1:]
    lo_ = lam[rows[:, None], others]                     # other lengths in index order
    pref = np.concatenate([np.zeros((N, 1)), np.cumsum(lo_, axis=1)], axis=1)
    Ltot = pref[:, -1]
    mstar = np.argmin(np.abs(2 * pref - Ltot[:, None]), axis=1)
    S = pref[rows, mstar]; T = Ltot - S
    with np.errstate(divide="ignore", invalid="ignore"):
        xx = np.where(lk > 0, (lk ** 2 + T ** 2 - S ** 2) / (2 * lk), 0.0)
    yy = np.sqrt(np.clip(T ** 2 - xx ** 2, 0.0, None))
    xx = np.where(S == 0, lk, np.where(T == 0, 0.0, xx))   # one side empty: the triangle is a segment
    yy = np.where((S == 0) | (T == 0), 0.0, yy)
    z = rng.normal(size=(N, 3)); z /= np.linalg.norm(z, axis=1, keepdims=True)
    pk = 0.5 * lk * z[:, 0]                              # (1/2) E_k . xi with E_k = (lk, 0, 0)
    pG = (xx - lk) * z[:, 0] + yy * z[:, 1]              # E_G . xi
    pH = -(xx * z[:, 0] + yy * z[:, 1])                  # E_H . xi
    X = mid.copy()
    X[rows, k] += pk
    inG = np.arange(n - 1)[None, :] < mstar[:, None]
    with np.errstate(divide="ignore", invalid="ignore"):
        cG = np.where(S[:, None] > 0, lo_ / (2 * S[:, None]), 0.0) * pG[:, None]
        cH = np.where(T[:, None] > 0, lo_ / (2 * T[:, None]), 0.0) * pH[:, None]
    X[rows[:, None], others] += np.where(inG, cG, cH)
    return X


def sample_pieces(n, beta, rng):
    """n-complete mixes of P_beta for an array of beta values: returns Y of shape (N, n), rows summing to n."""
    N = len(beta)
    Y = np.empty((N, n))
    caseB = (n >= 4) & (3 * beta <= 2 * n)
    k = np.where(caseB, np.minimum(n - 1, np.floor(2 * n / beta + 1e-12)).astype(int), 0)
    groups = [("B", kk) for kk in np.unique(k[caseB])] + [("D", 0)]
    U1 = rng.random(N)
    for case, kk in groups:
        idx = np.where(caseB & (k == kk))[0] if case == "B" else np.where(~caseB)[0]
        if len(idx) == 0:
            continue
        b = beta[idx]; M = len(idx)
        lo = np.zeros((M, n)); hi = np.zeros((M, n))
        if case == "B":
            u = 2 * n - kk * b
            first = U1[idx] < u / b
            # t1: (n-1-k) atoms, k copies of [0,b], [0,u];  t2: (n-k) atoms, (k-1) copies of [0,b], [u,b]
            hi[:, n - 1 - kk:n - 1] = np.where(first[:, None], b[:, None], 0.0)
            hi[:, n - kk:n - 1] = b[:, None]
            lo[:, n - 1] = np.where(first, 0.0, u)
            hi[:, n - 1] = np.where(first, u, b)
        else:
            x = n - b
            first = U1[idx] < 1 - 2 * x / b
            # t1: (n-2) atoms, 2 copies of [x,b];  t2: (n-3) atoms, [0,x], [0,b], [x,b]
            lo[:, n - 2] = np.where(first, x, 0.0); hi[:, n - 2] = b
            lo[:, n - 1] = x; hi[:, n - 1] = b
            lo[:, n - 3] = 0.0; hi[:, n - 3] = np.where(first, 0.0, x)
        Y[idx] = arch_mix(lo, hi, rng)
    perm = np.argsort(rng.random((N, n)), axis=1)
    return np.take_along_axis(Y, perm, axis=1)


def algorithm(P, S, n, N, rng):
    """Algorithm 1: draw the level U with density W(U) = (l + r)^2 / (2 min(l, r)), then a complete mix
    of the piece at U, mapped back by x = mu - l + l y (left) or x = mu + r - r y (right)."""
    U, l, r = S["U"], S["l"], S["r"]
    W = (l + r) ** 2 / (2 * np.minimum(l, r))
    cw = np.concatenate([[0.0], np.cumsum(0.5 * (W[1:] + W[:-1]) * np.diff(U))])
    q = rng.random(N) * cw[-1]
    Us = np.interp(q, cw, U)
    ls, rs = np.interp(Us, U, l), np.interp(Us, U, r)
    beta = (ls + rs) / np.minimum(ls, rs)
    Y = sample_pieces(n, beta, rng)
    left = ls <= rs
    X = np.where(left[:, None], (P.mu - ls)[:, None] + ls[:, None] * Y, (P.mu + rs)[:, None] - rs[:, None] * Y)
    return X, cw[-1]


def part3(sols):
    t0 = time.time()
    rng = np.random.default_rng(SEED + 1)
    rows = []
    for key in ["triangle", "twoswitch", "linear", "semicircle", "power"]:
        P, S = sols[key]
        for n in [3, 4, 5, 8]:
            X, wtot = algorithm(P, S, n, MC, rng)
            sums = np.abs(X.sum(axis=1) - n * P.mu).max()
            x1 = np.sort(X[:, 0])
            Fx = P.cdf(x1)
            i = np.arange(1, MC + 1)
            ks = float(max(np.max(i / MC - Fx), np.max(Fx - (i - 1) / MC)))
            pval = float(kstwo.sf(ks, MC))
            rng_ok = bool(np.all(X >= -1e-12) and np.all(X <= 1 + 1e-12))
            rows.append(dict(density=key, n=n, sumerr=float(sums), ks=ks, p=pval, inrange=rng_ok, wtot=float(wtot)))
            print("Part 3:", rows[-1], flush=True)
    # follow-up of the smallest p-value: four further runs with four times as many samples
    worst = min(rows, key=lambda r: r["p"])
    P, S = sols[worst["density"]]
    follow = []
    for rep in range(4):
        X, _ = algorithm(P, S, worst["n"], 4 * MC, np.random.default_rng(SEED + 10 + rep))
        x1 = np.sort(X[:, 0]); Fx = P.cdf(x1); i = np.arange(1, 4 * MC + 1)
        ks = float(max(np.max(i / (4 * MC) - Fx), np.max(Fx - (i - 1) / (4 * MC))))
        follow.append(dict(ks=ks, p=float(kstwo.sf(ks, 4 * MC)),
                           sumerr=float(np.abs(X.sum(axis=1) - worst["n"] * P.mu).max())))
    print("Part 3: follow-up of", worst["density"], worst["n"], follow, flush=True)
    OUT["part3"] = dict(rows=rows, mc=MC, crit=float(kstwo.isf(0.05, MC)), follow=dict(density=worst["density"],
                        n=worst["n"], runs=follow), seconds=time.time() - t0)


# ===================================================================== unimodal densities
def part4():
    t0 = time.time()
    x = np.linspace(0.0, 1.0, 4001)
    rows = []
    def add(key, P):
        S = solve(P, n=3000)
        b = S["beta"]; i = int(np.argmax(b))
        b0 = 1.0 / min(P.mu, 1 - P.mu)
        rows.append(dict(key=key, mu=P.mu, unimodal=P.unimodal, concave=P.concave, beta0=b0,
                         betastar=float(b[i]), at=float(S["U"][i] / P.fmu), switches=len(S["switches"]),
                         n_mean=math.ceil(b0 - 1e-9), n_peel=max(3, math.ceil(float(b[i]) - 1e-9))))
        print("Part 4:", rows[-1], flush=True)
    lg = lambda z: np.log(np.clip(z, 1e-300, None))
    for a, b in [(1.5, 3), (2, 3), (2, 5), (3, 5), (2, 8), (4, 6), (5, 10)]:
        y = np.exp((a - 1) * lg(x) + (b - 1) * lg(1 - x) - betaln(a, b)); y[0] = y[-1] = 0.0
        add("beta(%g,%g)" % (a, b), PLDensity(x, y))
    for bb in [10, 15, 20, 21.6, 22.6]:
        t = 0.2 + (bb - 0.2) * x
        y = np.exp(-0.5 * (np.log(t) - 2) ** 2) / t
        add("lognormal[0.2,%g]" % bb, PLDensity(t, y))
    y = np.exp(-0.5 * ((x - 1.48) / 0.722) ** 2)
    add("normal(1.48,0.722)[0,1]", PLDensity(x, y))
    # random Beta densities: excess of beta* over max(beta(0), 3)
    rng = np.random.default_rng(SEED + 2)
    xb = np.linspace(0.0, 1.0, 3001)
    exc = []; nb_mean = []; nb_peel = []
    for _ in range(NBETA):
        a, b = rng.uniform(1, 8, 2)
        y = np.exp((a - 1) * lg(xb) + (b - 1) * lg(1 - xb) - betaln(a, b))
        if a > 1: y[0] = 0.0
        if b > 1: y[-1] = 0.0
        P = PLDensity(xb, y)
        S = solve(P, n=2500)
        b0 = 1.0 / min(P.mu, 1 - P.mu)
        exc.append(float(np.max(S["beta"]) / max(b0, 3.0) - 1.0))
        nb_mean.append(max(3, math.ceil(b0 - 1e-9))); nb_peel.append(max(3, math.ceil(float(np.max(S["beta"])) - 1e-9)))
    beta_rand = dict(n=NBETA, max_excess=max(exc), same_n=int(sum(p == q for p, q in zip(nb_mean, nb_peel))))
    # the case with the largest excess, with an interpolation four times finer
    rng = np.random.default_rng(SEED + 2)
    pars = [tuple(rng.uniform(1, 8, 2)) for _ in range(NBETA)]
    a, b = pars[int(np.argmax(exc))]
    def start_excess(npts):
        # largest relative excess of beta over beta(0) on 41 levels U/f(mu) in [1e-12, 1e-2], first phase
        xf = np.linspace(0.0, 1.0, npts)
        y = np.exp((a - 1) * lg(xf) + (b - 1) * lg(1 - xf) - betaln(a, b)); y[0] = 0.0; y[-1] = 0.0
        P = PLDensity(xf, y)
        S = solve(P, n=2500)
        assert not S["switches"] or S["switches"][0] > 1e-2 * P.fmu
        Us = P.fmu * np.logspace(-12, -2, 41)
        l, r, _, _ = phase_state(P, S["first"], P.mu, 1.0 - P.mu, P.fmu - Us)
        return float(np.max((l + r) / np.minimum(l, r)) * min(P.mu, 1 - P.mu) - 1.0)
    beta_rand.update(worst_a=float(a), worst_b=float(b), start_excess=start_excess(3001),
                     start_excess_fine=start_excess(12001))
    print("Part 4: random Beta", beta_rand, flush=True)
    OUT["part4"] = dict(rows=rows, beta_random=beta_rand, seconds=time.time() - t0)


if __name__ == "__main__":
    T0 = time.time()
    part1()
    sols = part2()
    part3(sols)
    part4()
    OUT["seconds"] = time.time() - T0
    OUT["settings"] = dict(NMAX=NMAX, GRID=GRID, NLEV=NLEV, NRAND=NRAND, MC=MC, NBETA=NBETA, SEED=SEED)
    os.makedirs("data", exist_ok=True)
    with open("data/concave14.json", "w") as fh:
        json.dump(OUT, fh, indent=1)
    print("total %.0f s" % OUT["seconds"])
