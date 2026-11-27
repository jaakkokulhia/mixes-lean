"""Verification program for the centrally symmetric bodies of the section on stability (pairs and a core).

Part A  volume ratios behind the corollary on centrally symmetric bodies: |K|/|B_r| for the regular
        dodecahedron, icosahedron, 24-cell, 120-cell and 600-cell from their convex hulls, against the
        closed forms of the proof, and the ratios v_m of the cross-polytopes against their double cones.
Part B  Monte Carlo of the complete mixes of the proposition on orbits and a core: a uniformly random
        permutation of j orbits (P, AP, ..., A^(m-1) P) and an r-complete mix (X1, ..., Xr) of the uniform
        distribution on the core L, with P drawn by the acceptance rule of the proposition; A = -I (pairs,
        r = 3) for the centrally symmetric bodies and the rotation by 120 degrees (r = 2, 4) for the Reuleaux
        triangle.  Cores: the inscribed ball (five regular bodies, the Reuleaux triangle), the double cone over
        a ball (cross-polytopes of R^4 and R^5, with the levels of the lemma on the levels), and an ellipse of
        maximal area (a centrally symmetric hexagon).  Checks: sums, containment, acceptance rate, and
        two-sample Kolmogorov-Smirnov tests of each coordinate against an independent sample of U(K), in
        three fixed directions and for |x|.
Part C  reruns of the two cases of Part B with the smallest p-values, the dodecahedron (n = 5) and the Reuleaux
        triangle (n = 7), with other seeds and RERUN (default 1000000) tuples.
Results go to data/symm25.json; the log goes to stdout.
Environment: MC (default 200000), RERUN (default 1000000), SEED (2026).
"""
import json, math, os, sys, time
import numpy as np
from scipy.optimize import minimize
from scipy.spatial import ConvexHull
from scipy.stats import ks_2samp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "pO"))
from open18 import Levels                                            # noqa: E402

MC = int(os.environ.get("MC", 200000)); SEED = int(os.environ.get("SEED", 2026))
RERUN = int(os.environ.get("RERUN", 1000000))
PHI = (1 + 5 ** 0.5) / 2


# ===================================================================== bodies
def signs(v):
    import itertools
    return {tuple(a * b for a, b in zip(v, s)) for s in itertools.product((1, -1), repeat=len(v))}


def perms(vs):
    import itertools
    return {p for v in vs for p in itertools.permutations(v)}


def even_perms(vs):
    import itertools
    out = set()
    for v in vs:
        for p in itertools.permutations(range(len(v))):
            inv = sum(1 for i in range(len(p)) for j in range(i + 1, len(p)) if p[i] > p[j])
            if inv % 2 == 0:
                out.add(tuple(v[i] for i in p))
    return out


def cyclic(vs):
    return {tuple(np.roll(np.array(v), s)) for v in vs for s in range(3)}


def vertices(name):
    if name == "dodecahedron":
        V = signs((1, 1, 1)) | cyclic(signs((0, 1 / PHI, PHI)))
    elif name == "icosahedron":
        V = cyclic(signs((0, 1, PHI)))
    elif name == "24-cell":
        V = perms(signs((1, 1, 0, 0)))
    elif name in ("600-cell", "120-cell"):
        V = perms(signs((1, 0, 0, 0))) | signs((0.5, 0.5, 0.5, 0.5)) | even_perms(signs((PHI / 2, 0.5, 1 / (2 * PHI), 0)))
        if name == "120-cell":                       # polar body: facet normals divided by the offsets
            h = ConvexHull(np.array(sorted(V)))
            N = h.equations[:, :-1] / (-h.equations[:, -1:])
            return np.unique(np.round(N, 12), axis=0)
    else:
        raise ValueError(name)
    return np.array(sorted(V), float)


class Polytope:
    """Centrally symmetric polytope given by its vertices; H-representation A x <= b from the hull."""

    def __init__(self, V):
        h = ConvexHull(V)
        A = h.equations[:, :-1]; b = -h.equations[:, -1]
        _, idx = np.unique(np.round(np.c_[A, b], 10), axis=0, return_index=True)   # merge coplanar triangles
        self.A, self.b = A[idx], b[idx]
        self.d = V.shape[1]; self.volume = h.volume; self.inradius = float(self.b.min())
        self.R = float(np.linalg.norm(V, axis=1).max()); self.nverts = len(V)

    def inside(self, X, tol=0.0):
        out = np.empty(len(X), bool)
        for s in range(0, len(X), 20000):
            out[s:s + 20000] = (X[s:s + 20000] @ self.A.T - self.b).max(1) <= tol
        return out

    def excess(self, X):
        m = -np.inf
        for s in range(0, len(X), 20000):
            m = max(m, float((X[s:s + 20000] @ self.A.T - self.b).max()))
        return m

    def sample(self, N, rng):
        out = []; got = 0
        while got < N:
            Y = (2 * rng.random((200000, self.d)) - 1) * self.R
            Y = Y[self.inside(Y)]; out.append(Y); got += len(Y)
        return np.concatenate(out)[:N]


class Reuleaux:
    """the Reuleaux triangle of width 1 centred at 0: the intersection of the unit discs about the vertices of an
    equilateral triangle with side 1; area (pi - sqrt 3)/2, inradius 1 - 1/sqrt 3, symmetric under rotation by 120 degrees."""

    def __init__(self):
        a = np.pi / 2 + 2 * np.pi * np.arange(3) / 3
        self.V = np.stack([np.cos(a), np.sin(a)], 1) / 3 ** 0.5
        self.d = 2; self.volume = (np.pi - 3 ** 0.5) / 2; self.inradius = 1 - 1 / 3 ** 0.5; self.R = 1 / 3 ** 0.5

    def excess(self, X):
        return float((np.linalg.norm(X[:, None, :] - self.V[None], axis=2) - 1).max())

    def inside(self, X, tol=0.0):
        return (np.linalg.norm(X[:, None, :] - self.V[None], axis=2) <= 1 + tol).all(1)

    def sample(self, N, rng):
        out = []; got = 0
        while got < N:
            Y = (2 * rng.random((200000, 2)) - 1) * self.R
            Y = Y[self.inside(Y)]; out.append(Y); got += len(Y)
        return np.concatenate(out)[:N]


class CrossPolytope:
    def __init__(self, d):
        self.d = d; self.volume = 2.0 ** d / math.factorial(d); self.inradius = d ** -0.5

    def inside(self, X, tol=0.0):
        return np.abs(X).sum(1) <= 1 + tol

    def excess(self, X):
        return float((np.abs(X).sum(1) - 1).max())

    def sample(self, N, rng):                        # random signs times a uniform point of the simplex
        E = rng.exponential(size=(N, self.d + 1))
        return (E[:, :-1] / E.sum(1, keepdims=True)) * np.where(rng.random((N, self.d)) < 0.5, 1.0, -1.0)


# ===================================================================== 3-complete mixes of the cores
def random_frame(N, j, rng):
    G = rng.standard_normal((N, j, 2))
    g1 = G[:, :, 0] / np.linalg.norm(G[:, :, 0], axis=1, keepdims=True)
    g2 = G[:, :, 1] - (G[:, :, 1] * g1).sum(1, keepdims=True) * g1
    return g1, g2 / np.linalg.norm(g2, axis=1, keepdims=True)


def triangle(l):
    """vectors v_1, v_2, v_3 in the plane with |v_i| = l_i and sum 0, for rows of l (N, 3) with 2 max <= sum."""
    l1, l2, l3 = l[:, 0], l[:, 1], l[:, 2]
    c = np.clip((l3 ** 2 - l1 ** 2 - l2 ** 2) / np.maximum(2 * l1 * l2, 1e-300), -1, 1)
    v1 = np.stack([l1, 0 * l1], 1); v2 = np.stack([l2 * c, l2 * np.sqrt(1 - c * c)], 1)
    return np.stack([v1, v2, -v1 - v2], 1)                                      # (N, 3, 2)


def ball_triple(lengths, j, rng):
    """joint mix of U(l_i B_j), i = 1, 2, 3 (the theorem on balls): R (v_i1 g1 + v_i2 g2), R = V^(1/j)."""
    N = len(lengths); v = triangle(lengths); g1, g2 = random_frame(N, j, rng)
    R = rng.random(N) ** (1.0 / j)
    return R[:, None, None] * (v[:, :, 0, None] * g1[:, None, :] + v[:, :, 1, None] * g2[:, None, :])


def ball_mix(N, r, j, rng):
    """r-complete mix of U(B_j) (the theorem on balls with equal radii): the vertices of a regular r-gon."""
    ang = 2 * np.pi * np.arange(r) / r; g1, g2 = random_frame(N, j, rng)
    R = rng.random(N) ** (1.0 / j)
    return R[:, None, None] * (np.cos(ang)[None, :, None] * g1[:, None, :] + np.sin(ang)[None, :, None] * g2[:, None, :])


class BallCore:
    """the ellipsoid M B_d (M = r I for a ball), 3-completely mixable by the theorem on balls."""

    def __init__(self, M):
        self.M = np.atleast_2d(M); self.d = len(self.M); self.Minv = np.linalg.inv(self.M)
        self.volume = math.pi ** (self.d / 2) / math.gamma(self.d / 2 + 1) * abs(np.linalg.det(self.M))

    def contains(self, X):
        return np.linalg.norm(X @ self.Minv.T, axis=1) <= 1

    def mix(self, N, r, rng):
        return ball_mix(N, r, self.d, rng) @ self.M.T


class DoubleConeCore:
    """L = {(y, z): |z| <= 1, |y| <= rho (1 - |z|)} in R^(d-1) x R, 3-completely mixable by the theorem on
    bipyramids: levels of the lemma on the levels for nu = d (1 - a)^(d - 1), fibres by the theorem on balls."""

    def __init__(self, d, rho):
        self.d, self.rho = d, rho
        self.volume = 2 * math.pi ** ((d - 1) / 2) / math.gamma((d - 1) / 2 + 1) * rho ** (d - 1) / d
        self.levels = Levels(lambda a: d * (1 - a) ** (d - 1), lambda a: -d * (d - 1) * (1 - a) ** (d - 2))
        self.fibre_ok = True

    def contains(self, X):
        return np.linalg.norm(X[:, :-1], axis=1) <= self.rho * (1 - np.abs(X[:, -1]))

    def mix(self, N, r, rng):
        assert r == 3
        Z = self.levels.sample(N, rng)                                          # (N, 3), sums 0
        r = 1 - np.abs(Z)
        self.fibre_ok &= bool(np.all(2 * r.max(1) <= r.sum(1) * (1 + 1e-12) + 1e-15))
        W = ball_triple(self.rho * r, self.d - 1, rng)
        return np.concatenate([W, Z[:, :, None]], 2)


def max_ellipse(P):
    """largest centred ellipse M B_2 in the symmetric polygon P: ||M a_j|| <= b_j; M = [[p, q], [q, s]]."""
    A, b = P.A, P.b
    def mat(x):
        return np.array([[x[0], x[1]], [x[1], x[2]]])
    cons = [{"type": "ineq", "fun": lambda x, j=j: b[j] ** 2 - np.sum((mat(x) @ A[j]) ** 2)} for j in range(len(b))]
    cons.append({"type": "ineq", "fun": lambda x: x[0] * x[2] - x[1] ** 2 - 1e-9})
    r0 = P.inradius * 0.9
    res = minimize(lambda x: -math.log(max(x[0] * x[2] - x[1] ** 2, 1e-300)), [r0, 0.0, r0], constraints=cons,
                   method="SLSQP", options=dict(ftol=1e-14, maxiter=500))
    M = mat(res.x) * (1 - 1e-9)
    assert np.all(np.linalg.norm(A @ M, axis=1) <= b), "ellipse not inside"
    return M


# ===================================================================== Part A: volume ratios
def partA():
    t0 = time.time(); rows = {}
    s5 = 5 ** 0.5
    closed = {
        "dodecahedron": ((15 + 7 * s5) / 4) / (4 * math.pi / 3 * ((250 + 110 * s5) ** 0.5 / 20) ** 3),
        "icosahedron": (5 * (3 + s5) / 12) / (4 * math.pi / 3 * ((3 * 3 ** 0.5 + 15 ** 0.5) / 12) ** 3),
        "24-cell": 16 / math.pi ** 2,
    }
    bound600 = 128 / (47 + 21 * s5)
    for name in ("dodecahedron", "icosahedron", "24-cell", "600-cell", "120-cell"):
        V = vertices(name); P = Polytope(V); d = V.shape[1]
        if name in ("dodecahedron", "icosahedron"):     # scale to edge 1 for the closed forms
            D = np.linalg.norm(V[:, None] - V[None], axis=2); a = D[D > 1e-9].min()
        ratio = P.volume / (math.pi ** (d / 2) / math.gamma(d / 2 + 1) * P.inradius ** d)
        row = dict(d=d, vertices=P.nverts, facets=len(P.b), volume=P.volume, inradius=P.inradius, R=P.R, ratio=ratio)
        if name in closed:
            row["closed"] = closed[name]; row["err"] = abs(ratio - closed[name])
        else:
            row["bound"] = bound600; row["ok"] = bool(ratio <= bound600)
            row["inradius_600"] = ((7 + 3 * s5) / 16) ** 0.5
        row["below_5_3"] = bool(ratio <= 5 / 3)
        rows[name] = row; print("Part A:", name, row, flush=True)
    v = {}
    for m in (2, 3, 4, 5):
        wm = math.pi ** (m / 2) / math.gamma(m / 2 + 1)
        v[m] = 2 ** m * m ** (m / 2) / (math.factorial(m) * wm)
    cross = dict(v3=v[3], v3_closed=3 * 3 ** 0.5 / math.pi, v4=v[4], v4_closed=64 / (3 * math.pi ** 2),
                 three_v3=3 * v[3], three_v4=3 * v[4], v5=v[5], three_v5=3 * v[5],
                 ineq_243=bool(243 < 25 * math.pi ** 2), ineq_64=bool(64 < 7 * math.pi ** 2))
    print("Part A: cross-polytopes", cross, flush=True)
    ball_bounds = {d: 3 * 2 ** d / (math.pi ** (d / 2) / math.gamma(d / 2 + 1)) for d in (2, 3, 4, 5)}
    print("Part A: 3 * 2^d / |B^d|", ball_bounds, flush=True)
    return dict(rows=rows, cross=cross, ball_bounds={str(k): w for k, w in ball_bounds.items()},
                seconds=round(time.time() - t0, 1))


# ===================================================================== Part B: Monte Carlo of the pairs and a core
def simulate(name, K, core, n, N, rng, A=None, m=2, r=3):
    A = -np.eye(K.d) if A is None else A
    assert np.allclose(np.linalg.matrix_power(A, m), np.eye(K.d)) and (n - r) % m == 0 and n - r >= m
    assert np.allclose(sum(np.linalg.matrix_power(A, i) for i in range(m)), 0), "A has the eigenvalue 1"
    ratio = K.volume / core.volume
    assert n * core.volume >= r * K.volume, "n |L| < r |K|"
    q = 1 - r * K.volume / (n * core.volume)            # acceptance probability inside the core
    P = []; got = 0; drawn = 0
    while got < N:
        Y = K.sample(N, rng); drawn += len(Y)
        keep = ~core.contains(Y) | (rng.random(len(Y)) < q)
        P.append(Y[keep]); got += int(keep.sum())
    P = np.concatenate(P)[:N]; accept = got / drawn
    Xr = core.mix(N, r, rng)                                                    # (N, r, d)
    j = (n - r) // m
    orbit = [P @ np.linalg.matrix_power(A, i).T for i in range(m)]
    T = np.concatenate([np.stack(orbit * j, 1), Xr], 1)                         # (N, n, d)
    perm = np.argsort(rng.random((N, n)), axis=1)
    T = np.take_along_axis(T, perm[:, :, None], axis=1)
    max_sum = float(np.abs(T.sum(1)).max())
    excess = max(K.excess(T[:, i]) for i in range(n))
    ref = K.sample(N, rng)
    U = rng.standard_normal((3, K.d)); U /= np.linalg.norm(U, axis=1, keepdims=True)
    feats = [lambda X, u=u: X @ u for u in U] + [lambda X: np.linalg.norm(X, axis=1)]
    pv = [float(ks_2samp(f(T[:, i]), f(ref)).pvalue) for i in range(n) for f in feats]
    row = dict(body=name, d=K.d, n=n, m=m, r=r, core=type(core).__name__, ratio=ratio, threshold=r * ratio,
               samples=N, max_sum=max_sum, excess=excess, accept=accept, accept_expected=1 - r / n, tests=len(pv),
               min_p=min(pv))
    if isinstance(core, DoubleConeCore):
        row["fibre_ok"] = core.fibre_ok; row["alpha_min"] = core.levels.min_alpha
        row["alpha_mass_err"] = abs(core.levels.mass - 1)
    return row


def hexagon():
    V = np.array([[1.0, 0.0], [0.62, 0.81], [-0.45, 0.93]]); V = np.concatenate([V, -V])
    P = Polytope(V); assert P.nverts == 6 and len(P.b) == 6, "not a hexagon"
    P.V = V
    return P


def partB():
    t0 = time.time(); rng = np.random.default_rng(SEED + 25); rows = []
    cases = []
    for name in ("dodecahedron", "icosahedron", "24-cell", "120-cell", "600-cell"):
        P = Polytope(vertices(name)); cases.append((name, P, BallCore(P.inradius * np.eye(P.d) * (1 - 1e-12)), 5))
    for d, n in ((4, 5), (5, 7)):
        cases.append(("cross-polytope", CrossPolytope(d), DoubleConeCore(d, (d - 1) ** -0.5), n))
    H = hexagon(); M = max_ellipse(H)
    cases.append(("hexagon", H, BallCore(M), 5))
    for name, K, core, n in cases:
        row = simulate(name, K, core, n, MC, rng); rows.append(row); print("Part B:", row, flush=True)
    Rt = Reuleaux(); c, s_ = math.cos(2 * math.pi / 3), math.sin(2 * math.pi / 3)
    A3 = np.array([[c, -s_], [s_, c]]); disc = BallCore(Rt.inradius * np.eye(2) * (1 - 1e-12))
    assert np.allclose(Rt.V @ A3.T, Rt.V[[1, 2, 0]])                            # A maps the body onto itself
    for n, r in ((5, 2), (7, 4)):
        row = simulate("Reuleaux triangle", Rt, disc, n, MC, rng, A=A3, m=3, r=r); rows.append(row)
        print("Part B:", row, flush=True)
    m = sum(r["tests"] for r in rows); pmin = min(r["min_p"] for r in rows)
    hexa = dict(vertices=H.V[:3].tolist(), ratio=H.volume / (math.pi * abs(np.linalg.det(M))), area=H.volume,
                ellipse=M.tolist())
    return dict(rows=rows, tests=m, min_p=pmin, chance_min_p=1 - (1 - pmin) ** m, hexagon=hexa,
                seconds=round(time.time() - t0, 1))


def partC():
    t0 = time.time(); rows = []
    P = Polytope(vertices("dodecahedron")); ball = BallCore(P.inradius * np.eye(3) * (1 - 1e-12))
    Rt = Reuleaux(); c, s_ = math.cos(2 * math.pi / 3), math.sin(2 * math.pi / 3)
    A3 = np.array([[c, -s_], [s_, c]]); disc = BallCore(Rt.inradius * np.eye(2) * (1 - 1e-12))
    for k in (1, 2):
        row = simulate("dodecahedron", P, ball, 5, RERUN, np.random.default_rng(SEED + 100 + k))
        rows.append(dict(body="dodecahedron", n=5, seed=SEED + 100 + k, tests=row["tests"], min_p=row["min_p"],
                         max_sum=row["max_sum"], excess=row["excess"])); print("Part C:", rows[-1], flush=True)
    for k in (3, 4, 5):
        row = simulate("Reuleaux triangle", Rt, disc, 7, RERUN, np.random.default_rng(SEED + 100 + k), A=A3, m=3, r=4)
        rows.append(dict(body="Reuleaux triangle", n=7, seed=SEED + 100 + k, tests=row["tests"], min_p=row["min_p"],
                         max_sum=row["max_sum"], excess=row["excess"])); print("Part C:", rows[-1], flush=True)
    return dict(rows=rows, samples=RERUN, seconds=round(time.time() - t0, 1))


if __name__ == "__main__":
    t0 = time.time()
    out = dict(MC=MC, SEED=SEED, RERUN=RERUN, partA=partA(), partB=partB(), partC=partC())
    out["seconds"] = round(time.time() - t0, 1)
    os.makedirs(os.path.join(HERE, "data"), exist_ok=True)
    with open(os.path.join(HERE, "data", "symm25.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("done in %.1f s" % out["seconds"], flush=True)
