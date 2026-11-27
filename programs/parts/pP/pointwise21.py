"""Pointwise form of the condition of Theorem 95 for the regular pentagon (n = 3, 4) and heptagon (n = 4, 5).

lam_m is the m-fold convolution power of the indicator of the unit disc B (radial), a_n = lam_{n-1} and
c_m = lam_m(0); P_k is the regular k-gon with inradius 1 and a vertex on the positive x-axis, and C = P_k minus B.
The partner density of the corners is nu(q) = (n-1)/|P_k| int_C lam_{n-2}(|p+q|) 1_B(q) / a_n(|p|) dp, with the
Fourier coefficients
  nu_kap(r) = (n-1)/|P_k| (-1)^kap (k/pi) int_1^R rho/a_n(rho) K_kap(r,rho) sin(kap phimax(rho))/kap drho  (k | kap),
  K_kap(r,s) = int_0^{2pi} lam_{n-2}(sqrt(r^2+s^2-2rs cos psi)) cos(kap psi) dpsi,  phimax = pi/k - arccos(1/rho),
and the correction phi = sum over kap in M of f_kap(|q|) e^{i kap arg q}, M the multiples of k not divisible by n,
f_kap = -G_kap^{-1} nu_kap with G_kap f = (a_n f + (n-1)(-1)^kap int_0^1 K_kap(r,s) f(s) s ds)/n.

Part A computes, at two resolutions, the bound t = 2 sum_{0<kap<=J k, kap in M} max|f_kap| + (tail bound of the
proof for kap > J k) for sup|phi|, and the largest value over B of nu_s + t a_n(|q|) + (tail of nu_s), where nu_s is
the average of nu over the rotations by 2 pi / n; the pointwise condition asks it to be at most 1/|P_k|.  Part B
checks the tables of lam_3 and lam_4 against the bounds of regular21.py, the mass of nu, and the Fourier synthesis
of nu against direct quadrature over the corners.  Part C simulates the complete mixes and tests their marginals.
Writes data/pointwise21.json.
"""
import json, math, sys, time
import numpy as np
from scipy import stats
from scipy.interpolate import CubicSpline

t0 = time.time()


PI = math.pi


def lens(d):
    d = np.clip(np.asarray(d, float), 0.0, 2.0)
    return 2 * np.arccos(d / 2) - (d / 2) * np.sqrt(np.maximum(4 - d * d, 0.0))


def gl(n, a, b):
    x, w = np.polynomial.legendre.leggauss(n)
    return a + (b - a) * (x + 1) / 2, w * (b - a) / 2


class Lam:
    """radial functions lam_1..lam_4 as callables of the distance"""
    def __init__(self, nd=1201, ns=240, npsi=1024):
        self.cache = {1: lambda d: (np.asarray(d, float) <= 1.0).astype(float), 2: lens}
        psi = 2 * PI * np.arange(npsi) / npsi
        for m, smax, inner in ((3, 1.0, lambda s: np.ones_like(s)), (4, 2.0, lambda s: lens(s))):
            dmax = float(m)
            d = np.linspace(0, dmax, nd)
            s, ws = gl(ns, 0.0, smax)
            vals = np.empty(nd)
            for i, di in enumerate(d):
                D = np.sqrt(np.maximum(di * di + s[:, None] ** 2 - 2 * di * s[:, None] * np.cos(psi)[None, :], 0.0))
                vals[i] = float((ws * s * inner(s) * lens(D).mean(1)).sum()) * 2 * PI
            vals = np.maximum(vals, 0.0)
            spl = CubicSpline(d, vals)
            self.cache[m] = (lambda spl, dmax: (lambda x: np.where(np.asarray(x) >= dmax, 0.0,
                                                                   np.maximum(spl(np.clip(x, 0, dmax)), 0.0))))(spl, dmax)

    def __call__(self, m, d):
        return self.cache[m](d)


def kernel_modes(lam, m, r, s, kmax, npsi=4096):
    """K[kap, i, j] = int_0^{2pi} lam_m(|r_i - s_j e^{i psi}|) cos(kap psi) dpsi for kap = 0..kmax (trapezoid + FFT)"""
    psi = 2 * PI * np.arange(npsi) / npsi
    K = np.empty((kmax + 1, len(r), len(s)))
    for i, ri in enumerate(r):
        D = np.sqrt(np.maximum(ri * ri + s[:, None] ** 2 - 2 * ri * s[:, None] * np.cos(psi)[None, :], 0.0))
        F = np.fft.rfft(lam(m, D), axis=1) * (2 * PI / npsi)
        K[:, i, :] = F[:, :kmax + 1].real.T
    return K


def kernel_modes_n3(r, s, kmax):
    """closed form for lam_1: K_kap = 2 sin(kap w)/kap, K_0 = 2w, w the half-width of the arc |r - s e^{i psi}| <= 1"""
    R_, S_ = np.meshgrid(r, s, indexing="ij")
    with np.errstate(divide="ignore", invalid="ignore"):
        c = (R_ * R_ + S_ * S_ - 1) / (2 * R_ * S_)
    c = np.where((R_ == 0) | (S_ == 0), np.where(R_ + S_ <= 1, -1.0, 1.0), c)
    w = np.arccos(np.clip(c, -1.0, 1.0))
    K = np.empty((kmax + 1,) + w.shape)
    K[0] = 2 * w
    for kap in range(1, kmax + 1):
        K[kap] = 2 * np.sin(kap * w) / kap
    return K


def solve(k, n, lam, J=48, nr=320, nu_quad=160, npsi=4096, verbose=True):
    R = 1 / math.cos(PI / k); area = k * math.tan(PI / k)
    kmax = J * k
    r, wr = gl(nr, 0.0, 1.0)
    # rho = sec(u), u in [0, pi/k]: phimax = pi/k - u, drho = sec u tan u du
    u, wu = gl(nu_quad, 0.0, PI / k)
    rho = 1 / np.cos(u); drho = wu * np.tan(u) / np.cos(u); phimax = PI / k - u
    an = lambda x: lam(n - 1, x)
    if n == 3:
        Krr = kernel_modes_n3(r, r, kmax); Krho = kernel_modes_n3(r, rho, kmax)
    else:
        Krr = kernel_modes(lam, n - 2, r, r, kmax, npsi); Krho = kernel_modes(lam, n - 2, r, rho, kmax, npsi)
    pref = (n - 1) / area * k / PI
    base = rho / an(rho) * drho
    nu = {0: pref * (Krho[0] * (base * phimax)[None, :]).sum(1)}
    for kap in range(k, kmax + 1, k):
        nu[kap] = pref * (-1) ** kap * (Krho[kap] * (base * np.sin(kap * phimax) / kap)[None, :]).sum(1)
    a_r = an(r)
    osc = [kap for kap in range(k, kmax + 1, k) if kap % n != 0]
    sym = [kap for kap in range(k, kmax + 1, k) if kap % n == 0]
    f = {}
    for kap in osc:
        G = (np.diag(a_r) + (n - 1) * (-1) ** kap * Krr[kap] * (r * wr)[None, :]) / n
        f[kap] = np.linalg.solve(G, -nu[kap])
    # tail bounds beyond kmax (proof of Theorem 95): |nu_kap| <= Cnu/kap^2, |f_kap| <= n/(a_n(1)-(n-1)c_{n-2}/kap) |nu_kap|
    c_nm2 = float(lam(n - 2, 0.0)); a1 = float(an(1.0)); aR = float(an(R))
    Cnu = (n - 1) * k * c_nm2 * (R * R - 1) / (PI * area * aR)
    jj = np.arange(J + 1, 10 ** 6, dtype=float)
    tail_nu = 2 * Cnu * float((1 / (jj * k) ** 2).sum())
    tail_f = 2 * n / (a1 - (n - 1) * c_nm2 / ((J + 1) * k)) * Cnu * float((1 / (jj * k) ** 2)[(jj * k) % n != 0].sum())
    return dict(k=k, n=n, R=R, area=area, r=r, wr=wr, nu=nu, f=f, osc=osc, sym=sym, a1=a1, aR=aR, c_nm2=c_nm2,
                Cnu=Cnu, tail_nu=tail_nu, tail_f=tail_f, neumann=a1 - (n - 1) * c_nm2 / k)


def check(res, lam, nth=721):
    k, n, r = res["k"], res["n"], res["r"]
    th = np.linspace(0, PI / k, nth)            # reflection-symmetric fundamental domain
    phi = np.zeros((len(r), nth)); nus = np.repeat(res["nu"][0][:, None], nth, 1)
    for kap in res["osc"]:
        phi += 2 * res["f"][kap][:, None] * np.cos(kap * th)[None, :]
    for kap in res["sym"]:
        nus += 2 * res["nu"][kap][:, None] * np.cos(kap * th)[None, :]
    wiener = 2 * sum(np.abs(res["f"][kap]).max() for kap in res["osc"])
    t_grid = np.abs(phi).max()
    t = wiener + res["tail_f"]                         # a bound for sup |phi| over the disc
    an_r = lam(n - 1, r)
    lhs = nus + t * an_r[:, None] + res["tail_nu"]
    out = dict(k=k, n=n, sup_phi_grid=float(t_grid), wiener=float(wiener), tail_f=res["tail_f"], t=float(t), max_nus=float(nus.max()),
               max_lhs=float(lhs.max()), inv_area=1 / res["area"], margin=1 / res["area"] - float(lhs.max()),
               argmax_r=float(r[np.unravel_index(lhs.argmax(), lhs.shape)[0]]), min_nus=float(nus.min()),
               neumann=res["neumann"], tail_nu=res["tail_nu"])
    return out



def nu_direct(k, n, q, nrho=400, nphi=400):
    """partner density at points q (m x 2) by direct quadrature over the corners"""
    R = 1 / math.cos(PI / k); area = k * math.tan(PI / k)
    u, wu = gl(nrho, 0.0, PI / k); rho = 1 / np.cos(u); drho = wu * np.tan(u) / np.cos(u)
    out = np.zeros(len(q))
    for j in range(k):
        for i in range(nrho):
            pm = PI / k - u[i]
            ph, wph = gl(nphi, 2 * PI * j / k - pm, 2 * PI * j / k + pm)
            P = rho[i] * np.stack([np.cos(ph), np.sin(ph)], 1)
            D = np.sqrt(((P[None, :, :] + q[:, None, :]) ** 2).sum(2))
            out += (lam(n - 2, D) * wph[None, :]).sum(1) * rho[i] * drho[i] / float(lam(n - 1, rho[i]))
    return (n - 1) / area * out * ((q ** 2).sum(1) <= 1)



def in_polygon(X, k):
    ang = 2 * PI * np.arange(k) / k + PI / k            # outer normals; a vertex on the positive x-axis
    return (X @ np.stack([np.cos(ang), np.sin(ang)]) <= 1 + 1e-12).all(1)


def sample_polygon(m, k, rng):
    R = 1 / math.cos(PI / k); out = np.empty((0, 2))
    while len(out) < m:
        X = rng.uniform(-R, R, size=(2 * m + 100, 2)); out = np.vstack([out, X[in_polygon(X, k)]])
    return out[:m]


def sample_disc(m, rng):
    out = np.empty((0, 2))
    while len(out) < m:
        X = rng.uniform(-1, 1, size=(2 * m + 100, 2)); out = np.vstack([out, X[(X ** 2).sum(1) <= 1]])
    return out[:m]


def simulate(k, n, lam, Ntot=300000, seed=7):
    rng = np.random.default_rng(seed)
    res = solve(k, n, lam); chk = check(res, lam)
    r = res["r"]; area = res["area"]; t = chk["t"]; C = area - PI
    cn = float(lam(n, 0.0)) if n <= 4 else None
    if cn is None:                                   # c_5 = int_B lam_4 = 2 pi int_0^1 s lam_4(s) ds
        s, ws = gl(2000, 0, 1); cn = 2 * PI * float((ws * s * lam(4, s)).sum())

    def phi(X):
        rad = np.sqrt((X ** 2).sum(-1)); th = np.arctan2(X[..., 1], X[..., 0]); out = np.zeros(rad.shape)
        for kap in res["osc"]:
            out += 2 * np.interp(rad, r, res["f"][kap]) * np.cos(kap * th)
        return out

    def nu_s(X):
        rad = np.sqrt((X ** 2).sum(-1)); th = np.arctan2(X[..., 1], X[..., 0]); out = np.interp(rad, r, res["nu"][0])
        for kap in res["sym"]:
            out += 2 * np.interp(rad, r, res["nu"][kap]) * np.cos(kap * th)
        return out

    mC = n * C / area; mL = t * cn; mR = 1 - mC - mL
    counts = rng.multinomial(Ntot, [mC, mL, mR])
    tuples = []
    # 1. corners with partners uniform on L_p
    P = np.empty((0, 2))
    while len(P) < counts[0]:
        Y = sample_polygon(2 * counts[0] + 100, k, rng); P = np.vstack([P, Y[(Y ** 2).sum(1) > 1]])
    P = P[:counts[0]]
    T = np.empty((len(P), n, 2)); todo = np.arange(len(P))
    while len(todo):
        Xs = np.stack([sample_disc(len(todo), rng) for _ in range(n - 2)], 1)
        last = -P[todo] - Xs.sum(1); ok = (last ** 2).sum(1) <= 1
        T[todo[ok], 0] = P[todo[ok]]; T[todo[ok], 1:n - 1] = Xs[ok]; T[todo[ok], n - 1] = last[ok]
        todo = todo[~ok]
    tuples.append(T)
    # 2. density t + mean phi on the tuples in B
    got, need, minden = [], counts[1], np.inf
    phisup = chk["wiener"]
    while need > 0:
        m = 3 * need + 200
        Xs = np.stack([sample_disc(m, rng) for _ in range(n - 1)], 1); last = -Xs.sum(1)
        ok = (last ** 2).sum(1) <= 1; T = np.concatenate([Xs[ok], last[ok][:, None, :]], 1)
        dens = t + phi(T).mean(1); minden = min(minden, float(dens.min()))
        acc = rng.uniform(size=len(T)) * (t + phisup) <= dens
        T = T[acc][:need]; got.append(T); need -= len(T)
    tuples.append(np.concatenate(got) if got else np.empty((0, n, 2)))
    # 3. the invariant remainder by the rotation of order n
    Q = np.array([[math.cos(2 * PI / n), -math.sin(2 * PI / n)], [math.sin(2 * PI / n), math.cos(2 * PI / n)]])
    got, need, minR = [], counts[2], np.inf
    while need > 0:
        X = sample_disc(2 * need + 200, rng)
        dens = 1 / area - nu_s(X) - t * lam(n - 1, np.sqrt((X ** 2).sum(1))); minR = min(minR, float(dens.min()))
        X = X[rng.uniform(size=len(X)) * (1 / area) <= dens][:need]
        T = np.stack([X @ np.linalg.matrix_power(Q, i).T for i in range(n)], 1); got.append(T); need -= len(X)
    tuples.append(np.concatenate(got))
    T = np.concatenate(tuples)
    perm = rng.permuted(np.tile(np.arange(n), (len(T), 1)), axis=1)
    T = np.take_along_axis(T, perm[:, :, None], 1)
    sums = float(np.abs(T.sum(1)).max()); inside = bool(all(in_polygon(T[:, i], k).all() for i in range(n)))
    ref = sample_polygon(2 * 10 ** 6, k, np.random.default_rng(seed + 1))
    pv = []
    for i in range(n):
        for f in (lambda X: X[:, 0], lambda X: X[:, 1], lambda X: np.sqrt((X ** 2).sum(1)), lambda X: np.arctan2(X[:, 1], X[:, 0])):
            pv.append(float(stats.ks_2samp(f(T[:, i]), f(ref)).pvalue))
    return dict(k=k, n=n, N=len(T), masses=(mC, mL, mR), max_sum=sums, inside=inside, min_density_L=minden,
                min_density_R=minR, tests=len(pv), min_p=min(pv), chance=1 - (1 - min(pv)) ** len(pv))




CASES = ((5, 3), (5, 4), (7, 4), (7, 5))
RES = {"base": dict(tab=dict(nd=1201, ns=240, npsi=1024), solve=dict(J=48, nr=320, nu_quad=160, npsi=4096), nth=721),
       "fine": dict(tab=dict(nd=1801, ns=360, npsi=2048), solve=dict(J=64, nr=480, nu_quad=240, npsi=8192), nth=1441)}


def partA():
    out = {}
    for name, cfg in RES.items():
        lam = Lam(**cfg["tab"]); rows = {}
        for k, n in CASES:
            res = solve(k, n, lam, **cfg["solve"]); chk = check(res, lam, nth=cfg["nth"])
            chk.update(Cnu=res["Cnu"], a1=res["a1"], aR=res["aR"], c_nm2=res["c_nm2"])
            rows["%d,%d" % (k, n)] = chk
            print("%s k=%d n=%d t=%.5f max=%.5f 1/|P|=%.5f margin %.5f" % (name, k, n, chk["t"], chk["max_lhs"], chk["inv_area"], chk["margin"]), flush=True)
        out[name] = dict(rows=rows, c3=float(lam(3, 0.0)), lam3_1=float(lam(3, 1.0)), c4=float(lam(4, 0.0)), lam4_1=float(lam(4, 1.0)))
    return out


def partB(lam):
    rng = np.random.default_rng(1); out = {}
    for k, n in CASES:
        res = solve(k, n, lam)
        r = res["r"]; area = res["area"]
        mass = 2 * PI * float((res["wr"] * r * res["nu"][0]).sum()); exact = (n - 1) * (area - PI) / area
        qr = rng.uniform(0.05, 0.98, 6); qt = rng.uniform(0, 2 * PI, 6)
        q = np.stack([qr * np.cos(qt), qr * np.sin(qt)], 1)
        synth = np.interp(qr, r, res["nu"][0])
        for kap, v in res["nu"].items():
            if kap: synth = synth + 2 * np.interp(qr, r, v) * np.cos(kap * qt)
        direct = nu_direct(k, n, q, nrho=200, nphi=200 if n == 3 else 120)
        out["%d,%d" % (k, n)] = dict(mass=mass, mass_exact=exact, synth_err=float(np.abs(synth - direct).max()),
                                     nu_values=[float(x) for x in direct])
        print("B k=%d n=%d mass %.6f/%.6f synth err %.1e" % (k, n, mass, exact, out["%d,%d" % (k, n)]["synth_err"]), flush=True)
    return out


if __name__ == "__main__":
    A = partA()
    lam = Lam()
    Bres = partB(lam)
    Cres = {}
    for k, n in CASES:
        c = simulate(k, n, lam)
        Cres["%d,%d" % (k, n)] = {a: (list(b) if isinstance(b, tuple) else b) for a, b in c.items()}
        print("C", {a: b for a, b in c.items()}, flush=True)
    json.dump(dict(partA=A, partB=Bres, partC=Cres, seconds=round(time.time() - t0, 1)),
              open("data/pointwise21.json", "w"), indent=1)
    print("done in", round(time.time() - t0, 1), "s")
