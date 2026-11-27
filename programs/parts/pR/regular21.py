"""Checks for the regular polygons of Section 21 (Theorem 95 and Corollary 96).

B is the unit disc, lens(d) = |B cap (B + d e_1)| = 2 arccos(d/2) - (d/2) sqrt(4 - d^2), lam_m the m-fold convolution
power of the indicator of B, c_m = lam_m(0) and a_n(rho) = lam_{n-1}(rho e_1), so that a_3 = lens, c_1 = 1, c_2 = pi and
c_3 = pi^2 - 3 sqrt(3) pi / 4.  For the regular k-gon P_k with inradius 1, R = sec(pi/k), |P_k| = k tan(pi/k), the
sufficient condition of Theorem 95 reads

    n W / (a_n(1) - (n-1) c_{n-2} / k)  <=  (1/|P_k| - N) / c_{n-1},
    W = 2 (n-1) c_{n-2} tan(pi/k) sigma / (pi k^2 a_n(R)),     N = (n-1) c_{n-2} (|P_k| - pi) / (|P_k| a_n(R)),

with sigma = sum over j >= 1 with n not dividing jk of j^-2 (at most pi^2/6).

Part A evaluates the condition: in closed form for n = 3, and for n = 4, 5 with lower bounds for a_4, a_5 and an
upper bound for c_4 from Riemann sums over cells in polar coordinates, where the monotonicity of lens gives the
extreme value of each integrand on each cell; these sums are evaluated in floating point. For the heptagon and n = 3
it also bounds the partner density more sharply, through the largest area of the corners in a unit disc (Part A2).
Part B carries out the construction for n = 3 and k = 8, 20 numerically: the Fourier coefficients of the partner
density, the correction phi on each mode by a Nystrom discretisation, and its size compared with t.
Part C simulates the complete mix for n = 3 and k = 20 and tests the marginals.
Writes data/regular21.json.
"""
import json, math, time
import numpy as np
from scipy import integrate, stats

t0 = time.time()
PI = math.pi
ZETA2 = PI * PI / 6


def lens(d):
    d = np.clip(np.asarray(d, float), 0.0, 2.0)
    return 2 * np.arccos(d / 2) - (d / 2) * np.sqrt(np.maximum(4 - d * d, 0.0))


C1, C2 = 1.0, PI
C3 = PI * PI - 3 * math.sqrt(3) * PI / 4                      # closed form of 2 pi int_0^1 s lens(s) ds
LENS1 = 2 * PI / 3 - math.sqrt(3) / 2                          # a_3(1)


# ---------------------------------------------------------------- Part A: certified-style bounds
def polar_cells(smax, ns, nth):
    s = np.linspace(0.0, smax, ns + 1); th = np.linspace(0.0, PI, nth + 1)
    S0, T0 = np.meshgrid(s[:-1], th[:-1], indexing="ij"); S1, T1 = np.meshgrid(s[1:], th[1:], indexing="ij")
    area = (S1 ** 2 - S0 ** 2) / 2 * (T1 - T0)
    return S0, S1, T0, T1, area


def dist_range(rho, S0, S1, T0, T1):
    """min and max of |rho e_1 - s e^{i th}| over the cell [S0,S1] x [T0,T1] with 0 <= th <= pi"""
    f = lambda s, t: rho * rho + s * s - 2 * rho * s * np.cos(t)
    dmax2 = np.maximum(f(S0, T1), f(S1, T1))                   # increasing in th; convex in s
    smin = np.clip(rho * np.cos(T0), S0, S1)                   # the minimum over s of f(s, T0)
    dmin2 = f(smin, T0)
    return np.sqrt(np.maximum(dmin2, 0)), np.sqrt(np.maximum(dmax2, 0))


def a4_bounds(rho, ns=1500, nth=1500):
    S0, S1, T0, T1, area = polar_cells(1.0, ns, nth)
    dmin, dmax = dist_range(rho, S0, S1, T0, T1)
    return 2 * float((area * lens(dmax)).sum()), 2 * float((area * lens(dmin)).sum())


def a5_bounds(rho, ns=2000, nth=1500):
    S0, S1, T0, T1, area = polar_cells(2.0, ns, nth)
    dmin, dmax = dist_range(rho, S0, S1, T0, T1)
    lo = 2 * float((area * lens(S1) * lens(dmax)).sum()); hi = 2 * float((area * lens(S0) * lens(dmin)).sum())
    return lo, hi


def c4_bounds(ns=200000):
    s = np.linspace(0.0, 2.0, ns + 1); ring = PI * (s[1:] ** 2 - s[:-1] ** 2)
    return float((ring * lens(s[1:]) ** 2).sum()), float((ring * lens(s[:-1]) ** 2).sum())


def a4_quad(rho):
    f = lambda th, s: s * float(lens(math.sqrt(max(rho * rho + s * s - 2 * rho * s * math.cos(th), 0.0))))
    return 2 * integrate.dblquad(f, 0, 1, 0, PI, epsabs=1e-11, epsrel=1e-11)[0]


def a5_quad(rho):
    f = lambda th, s: s * float(lens(s)) * float(lens(math.sqrt(max(rho * rho + s * s - 2 * rho * s * math.cos(th), 0.0))))
    return 2 * integrate.dblquad(f, 0, 2, 0, PI, epsabs=1e-11, epsrel=1e-11)[0]


def sigma(n, k, J=10 ** 6):
    j = np.arange(1, J + 1, dtype=float); keep = (np.arange(1, J + 1) * k) % n != 0
    return float((1 / j[keep] ** 2).sum()) + 1.0 / J            # tail bound for j > J


def condition(n, k, aR, a1, cm2, cm1, sig):
    """returns (left side, right side) of the condition of Theorem 95"""
    t = math.tan(PI / k); area = k * t
    W = 2 * (n - 1) * cm2 * t * sig / (PI * k * k * aR)
    N = (n - 1) * cm2 * (area - PI) / (area * aR)
    den = a1 - (n - 1) * cm2 / k
    lhs = n * W / den if den > 0 else float("inf")
    return lhs, (1 / area - N) / cm1, W, N


def partA():
    out = {"c3": C3, "lens1": LENS1}
    # c3 against quadrature
    out["c3_quad"] = 2 * PI * integrate.quad(lambda s: s * float(lens(s)), 0, 1, epsabs=1e-14, epsrel=1e-14)[0]
    c4lo, c4hi = c4_bounds(); out.update(c4_lo=c4lo, c4_hi=c4hi,
                                        c4_quad=2 * PI * integrate.quad(lambda s: s * float(lens(s)) ** 2, 0, 2, epsabs=1e-14, epsrel=1e-14)[0])
    R = lambda k: 1 / math.cos(PI / k)
    rows = {}
    a4_1 = a4_bounds(1.0); a5_1 = a5_bounds(1.0)
    out.update(a4_1=a4_1, a5_1=a5_1, a4_1_quad=a4_quad(1.0), a5_1_quad=a5_quad(1.0))
    for k in range(5, 21):
        a4R = a4_bounds(R(k)); a5R = a5_bounds(R(k))
        row = dict(k=k, R=R(k), lensR=float(lens(R(k))), a4R=a4R, a5R=a5R)
        # n = 3 in closed form, n = 4 and 5 with the lower bounds of a_n and the upper bound of c_4
        for n, aR, a1, cm2, cm1 in ((3, float(lens(R(k))), LENS1, C1, C2), (4, a4R[0], a4_1[0], C2, C3), (5, a5R[0], a5_1[0], C3, c4hi)):
            lhs, rhs, W, N = condition(n, k, aR, a1, cm2, cm1, sigma(n, k))
            lhsz, rhsz, _, _ = condition(n, k, aR, a1, cm2, cm1, ZETA2)
            row["n%d" % n] = dict(lhs=lhs, rhs=rhs, W=W, N=N, ok=lhs <= rhs, lhs_zeta=lhsz, ok_zeta=lhsz <= rhsz)
        rows[k] = row
        print("k=%2d  n=3 %.5f/%.5f  n=4 %.5f/%.5f  n=5 %.5f/%.5f" % (
            k, row["n3"]["lhs"], row["n3"]["rhs"], row["n4"]["lhs"], row["n4"]["rhs"], row["n5"]["lhs"], row["n5"]["rhs"]), flush=True)
    out["rows"] = rows
    # the monotone argument needs the condition with sigma = pi^2/6 at the first k
    out["k0"] = {"3": 8, "4": 9, "5": 9}
    out["k0_ok"] = {str(n): rows[k]["n%d" % n]["ok_zeta"] for n, k in ((3, 8), (4, 9), (5, 9))}
    out["quad_a4R9"] = a4_quad(R(9)); out["quad_a5R9"] = a5_quad(R(9))
    # Corollary 80(b) for the heptagon: 2 max r / l(sbar) along an axis of symmetry
    k = 7; Rc = 1 / math.cos(PI / k); half_side = math.tan(PI / k)
    angs = [2 * PI * j / k for j in range(k)]                     # vertices measured from the top vertex
    maxr = max(Rc * abs(math.sin(a)) for a in angs)
    sbar = 1 / (1 + Rc); ell = half_side * (1 - sbar)
    out["heptagon_ratio"] = 2 * maxr / ell
    return out


# ---------------------------------------------------------------- Part A2: a sharper bound for the heptagon, n = 3
def clip_halfplane(poly, a, b, c0):
    out = []; m = len(poly)
    for i in range(m):
        P, Q = poly[i], poly[(i + 1) % m]
        fP = a * P[0] + b * P[1] - c0; fQ = a * Q[0] + b * Q[1] - c0
        if fP <= 0: out.append(P)
        if (fP < 0 < fQ) or (fQ < 0 < fP):
            t = fP / (fP - fQ); out.append((P[0] + t * (Q[0] - P[0]), P[1] + t * (Q[1] - P[1])))
    return out


def poly_area(poly):
    if len(poly) < 3: return 0.0
    P = np.asarray(poly); x, y = P[:, 0], P[:, 1]
    return 0.5 * abs(float((x * np.roll(y, -1) - np.roll(x, -1) * y).sum()))


def corner_cap_bound(k, nr=60, nth=20, M=1024):
    """an upper bound for sup over c in B of |(P_k minus B) cap (c + B)|: on a grid of the fundamental domain
    0 <= |c| <= 1, 0 <= arg c <= pi/k, |P_k cap (c + B)| is bounded by the area of P_k cut from a regular M-gon
    circumscribed about c + B, lens(|c|) = |B cap (c + B)| is subtracted, and 2h is added for the distance h of any
    point of the domain from the grid, since the function is 2-Lipschitz (pi - lens(d) <= 2d)."""
    normals = [2 * PI * i / k + PI / k for i in range(k)]
    Rm = 1 / math.cos(PI / M); ang = 2 * PI * np.arange(M) / M
    best = 0.0
    for r in np.linspace(0, 1, nr + 1):
        for th in np.linspace(0, PI / k, nth + 1):
            cx, cy = r * math.cos(th), r * math.sin(th)
            poly = list(zip(cx + Rm * np.cos(ang), cy + Rm * np.sin(ang)))
            for a in normals:
                poly = clip_halfplane(poly, math.cos(a), math.sin(a), 1.0)
            best = max(best, poly_area(poly) - float(lens(r)))
    h = math.hypot(0.5 / nr, 0.5 * (PI / k) / nth)
    return best, best + 2 * h, h


def partA2(k=7):
    area = k * math.tan(PI / k); R = 1 / math.cos(PI / k)
    grid_max, cap, h = corner_cap_bound(k)
    N = 2 * cap / (area * float(lens(R)))
    lhs, rhs_crude, W, N_crude = condition(3, k, float(lens(R)), LENS1, C1, C2, sigma(3, k))
    rhs = (1 / area - N) / C2
    print("heptagon n=3: cap <= %.5f (grid %.5f, h %.4f), N <= %.4f (crude %.4f), %.5f <= %.5f" % (cap, grid_max, h, N, N_crude, lhs, rhs), flush=True)
    return dict(k=k, cap_grid=grid_max, cap_bound=cap, h=h, N=N, N_crude=N_crude, corners=area - PI, lhs=lhs, rhs=rhs,
                rhs_crude=rhs_crude, ok=lhs <= rhs)


# ---------------------------------------------------------------- Part B: the construction for n = 3
def w_arc(r, s):
    """half-width of the arc of angles psi with |r + s e^{i psi}| <= 1 around psi = pi"""
    with np.errstate(divide="ignore", invalid="ignore"):
        c = (1 - r * r - s * s) / (2 * r * s)
    c = np.where((r == 0) | (s == 0), np.where(r + s <= 1, 1.0, -1.0), c)
    return np.arccos(np.clip(-c, -1.0, 1.0))


def construction(k, J=60, nr=500):
    """Fourier coefficients nu_kappa(r) of the partner density on [0,1] (kappa = j k, 3 not dividing j), the
    correction f_kappa = -G_kappa^{-1} nu_kappa, the radial mean nu_0, and the sizes compared with t."""
    R = 1 / math.cos(PI / k); area = k * math.tan(PI / k)
    xg, wg = np.polynomial.legendre.leggauss(nr); r = (xg + 1) / 2; wr = wg / 2          # nodes on [0, 1]
    xq, wq = np.polynomial.legendre.leggauss(200); rho = 1 + (R - 1) * (xq + 1) / 2; wrho = wq * (R - 1) / 2
    phimax = PI / k - np.arccos(1 / rho)
    W = w_arc(r[:, None], rho[None, :])                                                  # r x rho
    base = rho / lens(rho) * wrho
    nu0 = (2 / area) / (2 * PI) * ((2 * W) * (2 * k * phimax * base)[None, :]).sum(1)      # radial mean
    modes = [j * k for j in range(1, J + 1) if j % 3 != 0]
    nus, fs = {}, {}
    Wrs = w_arc(r[:, None], r[None, :])
    for kap in modes:
        nu = ((-1) ** kap * 4 * k / (PI * area * kap * kap)) * (np.sin(kap * W) * (np.sin(kap * phimax) * base)[None, :]).sum(1)
        T = ((-1) ** kap * 2 / kap) * np.sin(kap * Wrs) * (r * wr)[None, :]               # Nystrom matrix of T_kappa
        G = (np.diag(lens(r)) + 2 * T) / 3
        f = np.linalg.solve(G, -nu)
        nus[kap], fs[kap] = nu, f
    # sizes: phi = sum over +-kappa of f e^{i kappa theta}, so |phi| <= 2 sum |f_kappa|
    phi_bound_num = 2 * sum(np.abs(fs[kp]).max() for kp in modes)
    # sup of nu: radial mean plus the modes divisible by 3 (sym) and not (osc)
    nu_osc_W = 2 * sum(np.abs(nus[kp]).max() for kp in modes)
    sym_modes = [j * k for j in range(1, J + 1) if j % 3 == 0]
    nusym = {}
    for kap in sym_modes:
        nusym[kap] = ((-1) ** kap * 4 * k / (PI * area * kap * kap)) * (np.sin(kap * W) * (np.sin(kap * phimax) * base)[None, :]).sum(1)
    nu_sup = float((nu0 + 2 * sum(np.abs(nusym[kp]) for kp in sym_modes) + 2 * sum(np.abs(nus[kp]) for kp in modes)).max())
    t = (1 / area - nu_sup) / PI
    lhs, rhs, Wb, Nb = condition(3, k, float(lens(R)), LENS1, C1, C2, sigma(3, k))
    return dict(k=k, modes=len(modes), phi_sup_numeric=float(phi_bound_num), nu_osc_wiener=float(nu_osc_W),
                nu_sup_numeric=nu_sup, t_numeric=float(t), bound_phi=lhs, bound_t=rhs, bound_W=Wb, bound_N=Nb,
                nu_mass=float(2 * PI * (wr * r * nu0).sum()), nu_mass_exact=2 * (area - PI) / area,
                _r=r, _nu0=nu0, _modes=modes, _f=fs, _sym=sym_modes, _nusym=nusym)


def partB():
    res = {}
    for k in (8, 20):
        c = construction(k)
        res[k] = {key: v for key, v in c.items() if not key.startswith("_")}
        print("construction k=%d: |phi| <= %.2e (bound %.2e), t = %.4f (bound %.4f), sup nu = %.4f (bound %.4f)" % (
            k, c["phi_sup_numeric"], c["bound_phi"], c["t_numeric"], c["bound_t"], c["nu_sup_numeric"], c["bound_N"]), flush=True)
    return res


# ---------------------------------------------------------------- Part C: simulation for n = 3, k = 20
def in_polygon(X, k):
    ang = 2 * PI * np.arange(k) / k + PI / k                 # outer normals of the sides; a vertex lies on the x-axis
    return (X @ np.stack([np.cos(ang), np.sin(ang)]) <= 1 + 1e-12).all(1)


def sample_polygon(m, k, rng):
    R = 1 / math.cos(PI / k); out = np.empty((0, 2))
    while len(out) < m:
        X = rng.uniform(-R, R, size=(2 * m, 2)); out = np.vstack([out, X[in_polygon(X, k)]])
    return out[:m]


def sample_disc(m, rng):
    out = np.empty((0, 2))
    while len(out) < m:
        X = rng.uniform(-1, 1, size=(2 * m, 2)); out = np.vstack([out, X[(X ** 2).sum(1) <= 1]])
    return out[:m]


def partC(k=20, N=300000, seed=2026):
    rng = np.random.default_rng(seed)
    c = construction(k)
    R = 1 / math.cos(PI / k); area = k * math.tan(PI / k); Cc = area - PI
    t = c["t_numeric"]; r = c["_r"]
    phi_inf = c["phi_sup_numeric"]

    def radial(vals, q):
        return np.interp(np.sqrt((q ** 2).sum(1)), r, vals)

    def phi(q):
        rad = np.sqrt((q ** 2).sum(1)); th = np.arctan2(q[:, 1], q[:, 0]); out = np.zeros(len(q))
        for kap in c["_modes"]:
            out += 2 * np.interp(rad, r, c["_f"][kap]) * np.cos(kap * th)
        return out

    def nu_sym(q):
        rad = np.sqrt((q ** 2).sum(1)); th = np.arctan2(q[:, 1], q[:, 0]); out = np.interp(rad, r, c["_nu0"])
        for kap in c["_sym"]:
            out += 2 * np.interp(rad, r, c["_nusym"][kap]) * np.cos(kap * th)
        return out

    m_C = 3 * Cc / area; m_L = t * C3; m_R = 1 - m_C - m_L
    counts = rng.multinomial(N, [m_C, m_L, m_R])
    tuples = []
    # corners with partners uniform on the lens
    P = np.empty((0, 2))
    while len(P) < counts[0]:
        Y = sample_polygon(2 * counts[0] + 100, k, rng); P = np.vstack([P, Y[(Y ** 2).sum(1) > 1]])
    P = P[:counts[0]]
    Yp = np.empty((0, 2)); idx = np.empty(0, int); todo = np.arange(len(P))
    while len(todo):
        Y = sample_disc(len(todo), rng); ok = ((P[todo] + Y) ** 2).sum(1) <= 1
        Yp = np.vstack([Yp, Y[ok]]); idx = np.concatenate([idx, todo[ok]]); todo = todo[~ok]
    order = np.argsort(idx); Yp = Yp[order]
    tuples.append(np.stack([P, Yp, -P - Yp], 1))
    # the density t + (phi(x)+phi(y)+phi(z))/3 on the triples in the disc
    got = []
    need = counts[1]
    while need > 0:
        X = sample_disc(3 * need + 100, rng); Y = sample_disc(3 * need + 100, rng); Z = -X - Y
        ok = (Z ** 2).sum(1) <= 1; X, Y, Z = X[ok], Y[ok], Z[ok]
        dens = t + (phi(X) + phi(Y) + phi(Z)) / 3
        assert dens.min() >= 0
        acc = rng.uniform(size=len(X)) * (t + phi_inf) <= dens
        T = np.stack([X[acc], Y[acc], Z[acc]], 1)[:need]; got.append(T); need -= len(T)
    tuples.append(np.concatenate(got))
    # the invariant remainder by the rotation of order 3
    got = []; need = counts[2]
    rot = np.array([[math.cos(2 * PI / 3), -math.sin(2 * PI / 3)], [math.sin(2 * PI / 3), math.cos(2 * PI / 3)]])
    while need > 0:
        X = sample_disc(2 * need + 100, rng)
        dens = 1 / area - nu_sym(X) - t * lens(np.sqrt((X ** 2).sum(1)))
        assert dens.min() >= 0
        X = X[rng.uniform(size=len(X)) * (1 / area) <= dens][:need]
        got.append(np.stack([X, X @ rot.T, X @ rot.T @ rot.T], 1)); need -= len(X)
    tuples.append(np.concatenate(got))
    T = np.concatenate(tuples)
    perm = rng.permuted(np.tile(np.arange(3), (len(T), 1)), axis=1)
    T = np.take_along_axis(T, perm[:, :, None], 1)
    sums = np.abs(T.sum(1)).max()
    inside = all(in_polygon(T[:, i], k).all() for i in range(3))
    # marginal tests against U(P_k): the coordinates and the radius of each point
    ref = sample_polygon(2 * 10 ** 6, k, np.random.default_rng(seed + 1))
    pvals = []
    for i in range(3):
        for f in (lambda X: X[:, 0], lambda X: X[:, 1], lambda X: np.sqrt((X ** 2).sum(1))):
            pvals.append(float(stats.ks_2samp(f(T[:, i]), f(ref)).pvalue))
    return dict(k=k, N=int(len(T)), counts=[int(x) for x in counts], masses=[m_C, m_L, m_R], max_sum=float(sums),
                inside=bool(inside), tests=len(pvals), min_p=min(pvals), pvalues=pvals)


if __name__ == "__main__":
    A = partA(); print("Part A done", round(time.time() - t0, 1), "s", flush=True)
    A["heptagon"] = partA2()
    Bres = partB()
    Cres = partC(); print("Part C:", {k: v for k, v in Cres.items() if k != "pvalues"}, flush=True)
    json.dump(dict(partA=A, partB={str(k): v for k, v in Bres.items()}, partC=Cres, seconds=round(time.time() - t0, 1)),
              open("data/regular21.json", "w"), indent=1)
    print("done in", round(time.time() - t0, 1), "s")
