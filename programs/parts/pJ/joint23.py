"""Checks for Section 23: conditioned-product joint mixes of densities on different planar convex bodies.

For convex bodies K_1, ..., K_n and probability densities g_j on them whose means add up to 0, Theorem 110 gives,
for large n, densities h_j = g_j e^{phi_j} with small phi_j such that n independent points X_j ~ h_j, conditioned on
X_1 + ... + X_n = 0, form a joint mix of g_1, ..., g_n.  The equations are
    h_j(p) * f_{-j}(-p) = c_j g_j(p)  on K_j,   f_{-j} = convolution of the h_k with k != j.
They are solved here by cyclic iterative proportional fitting, h_j <- g_j / f_{-j}(-.), one coordinate at a time.
The bodies are discretised on the lattice step*Z^2: each pixel carries the area of its intersection with K_j (16 x 16
sub-sampling), times the target density; convolutions are computed by fast Fourier transforms on a grid that holds
the sum of n-1 bodies, with prefix and suffix products, so that lattice sums are exact.  At a fixed point the lattice
conditioned product is a joint mix of the discretised targets.  Where the discrete means do not add up to 0 exactly,
the targets get a common exponential tilt that makes them do so (its size is recorded).

Part A: the "battery community": uniform distributions on the disc D and on the cut discs D with x <= 0.2 and
        D with x >= -0.2 (n = 3, 4, 6, 8).
Part B: complete mixes of a non-uniform density: the density of maximal entropy with mean 0 on D with x <= 0.5, an
        exponentially tilted uniform distribution (n = 4, 5, 8); n >= 3 is necessary, with equality at n = 3.
Part E: n times the range of the correction for that density, n = 4, 5, 8, 16 (step 1/24).
Part F: the same density with n = 3, where the necessary condition n >= 3 holds with equality: range and Lipschitz
        estimate of the correction as the step decreases from 1/24 to 1/96.
Part C: weighted sums: uniform distributions on the images of the square [-1,1]^2 under multiplication by complex
        gains rho_j e^{i theta_j}, i.e. joint mixes of X_j uniform on the square with sum_j gain_j X_j = 0
        (n = 3, 4, 6).
Part D: different shapes: uniform distributions on a triangle, a square, a regular pentagon and a disc, each centred
        at its centroid (n = 3, 4, 5).
Each case is solved at two lattice steps; the change of the correction between them is recorded.
Writes data/joint23.json.
"""
import json, math, time
import numpy as np

t0 = time.time()
PI = math.pi


def polygon(verts):
    def ind(X, Y):
        inside = np.ones(np.broadcast(X, Y).shape, dtype=bool)
        m = len(verts)
        for i in range(m):
            (x0, y0), (x1, y1) = verts[i], verts[(i + 1) % m]
            inside &= (x1 - x0) * (Y - y0) - (y1 - y0) * (X - x0) >= 0
        return inside
    return ind


def regular(k, r=1.0, phase=PI / 2):
    return [(r * math.cos(2 * PI * j / k + phase), r * math.sin(2 * PI * j / k + phase)) for j in range(k)]


def disc(r=1.0):
    return lambda X, Y: X * X + Y * Y <= r * r


def cut_disc(side, a=0.2):
    if side > 0:
        return lambda X, Y: (X * X + Y * Y <= 1) & (X <= a)
    return lambda X, Y: (X * X + Y * Y <= 1) & (X >= -a)


def gain_square(rho, theta_deg):
    """image of [-1,1]^2 under multiplication by rho e^{i theta}"""
    th = math.radians(theta_deg)
    c, s = math.cos(th), math.sin(th)
    verts = [(rho * (c * x - s * y), rho * (s * x + c * y)) for x, y in ((-1, -1), (1, -1), (1, 1), (-1, 1))]
    return polygon(verts)


def area_weights(ind, step, H, shift, sub=16):
    idx = np.arange(-H, H + 1)
    w = np.zeros((len(idx), len(idx)))
    o = (np.arange(sub) + 0.5) / sub - 0.5
    for a in o:
        X = (idx[:, None] + a) * step - shift[0]
        for b in o:
            w += ind(X, (idx[None, :] + b) * step - shift[1])
    return w / sub ** 2


def body_weights(ind, step, H, centre):
    """area weights on the lattice; with centre=True the body is translated (continuously) so that the discrete
    uniform measure has mean 0, as in Section 22"""
    ax = np.arange(-H, H + 1) * step
    X, Y = np.meshgrid(ax, ax, indexing="ij")
    c = np.zeros(2)
    w = area_weights(ind, step, H, c)
    if centre:
        for _ in range(5):
            dc = np.array([(w * X).sum(), (w * Y).sum()]) / w.sum()
            c = c - dc
            w = area_weights(ind, step, H, c)
    return w, X, Y, c


def tilt_to_mean(g, X, Y, target=(0.0, 0.0)):
    """exponential tilt of the measure g whose mean is `target` (Newton)"""
    v = np.zeros(2)
    for _ in range(100):
        e = v[0] * X + v[1] * Y
        q = g * np.exp(e - e[g > 0].max())
        q = q / q.sum()
        mu = np.array([(q * X).sum(), (q * Y).sum()]) - np.array(target)
        if np.abs(mu).max() < 1e-15:
            break
        C = np.array([[(q * X * X).sum(), (q * X * Y).sum()], [(q * X * Y).sum(), (q * Y * Y).sum()]])
        m0 = np.array([(q * X).sum(), (q * Y).sum()])
        C -= np.outer(m0, m0)
        v = v - np.linalg.solve(C, mu)
    return q, v


def balance(G, X, Y):
    """common tilt e^{<w,x>} of all targets that makes the sum of their means 0"""
    w = np.zeros(2)
    for _ in range(100):
        Q, mus, covs = [], [], []
        for g in G:
            e = w[0] * X + w[1] * Y
            q = g * np.exp(e - e[g > 0].max()); q = q / q.sum()
            m0 = np.array([(q * X).sum(), (q * Y).sum()])
            C = np.array([[(q * X * X).sum(), (q * X * Y).sum()], [(q * X * Y).sum(), (q * Y * Y).sum()]]) - np.outer(m0, m0)
            Q.append(q); mus.append(m0); covs.append(C)
        tot = np.sum(mus, 0)
        if np.abs(tot).max() < 1e-15:
            break
        w = w - np.linalg.solve(np.sum(covs, 0), tot)
    return Q, w


def ipf(G, keeps, H, n, tol=1e-10, max_sweeps=4000):
    """cyclic iterative proportional fitting for the conditioned product with marginals G (lattice measures)"""
    L = 2 * H + 1
    size = 1 << int(math.ceil(math.log2((n - 1) * (L - 1) + 1)))
    I = np.arange(-H, H + 1)
    sel = np.ix_(-I + (n - 1) * H, -I + (n - 1) * H)
    h = [g.copy() for g in G]
    hat = [np.fft.rfft2(x, s=(size, size)) for x in h]
    errs = []
    for sweep in range(max_sweeps):
        suf = [None] * (n + 1)
        suf[n] = np.ones_like(hat[0])
        for j in range(n - 1, -1, -1):
            suf[j] = suf[j + 1] * hat[j]
        pre = np.ones_like(hat[0])
        err = 0.0
        for j in range(n):
            f = np.fft.irfft2(pre * suf[j + 1], s=(size, size))[sel]
            fk = f[keeps[j]]
            if fk.min() <= 0:
                return dict(ok=False, reason="no partners", sweep=sweep)
            marg = h[j][keeps[j]] * fk
            marg = marg / marg.sum()
            err = max(err, float(np.abs(marg / G[j][keeps[j]] - 1).max()))
            new = np.zeros_like(h[j])
            new[keeps[j]] = G[j][keeps[j]] / fk
            h[j] = new / new.sum()
            hat[j] = np.fft.rfft2(h[j], s=(size, size))
            pre = pre * hat[j]
        errs.append(err)
        if err < tol:
            break
        if not np.isfinite(err):
            return dict(ok=False, reason="diverged", sweep=sweep)
    ok = errs[-1] < tol
    rate = None
    a = [x for x in errs[-12:] if x > 1e-14]
    if ok and len(a) >= 4:
        rate = float((a[-1] / a[0]) ** (1 / (len(a) - 1)))
    return dict(ok=bool(ok), sweeps=len(errs), err=errs[-1], rate=rate, h=h)


def corrections(h, G, keeps, X, Y, W, step):
    """phi_j = log(h_j/g_j) in the gauge in which the h_j have means adding up to 0; their largest range, a Lipschitz
    estimate over adjacent pixels that lie inside the body, and the largest gradient of their affine parts"""
    # gauge: common tilt making the sum of the means of the h_j zero (it does not change the conditioned product)
    Hc, v = balance(h, X, Y)
    rng, lip, grad = 0.0, 0.0, 0.0
    phis = []
    for j in range(len(h)):
        k = keeps[j]
        phi = np.full(X.shape, np.nan)
        phi[k] = np.log(Hc[j][k] / G[j][k])
        phi[k] -= np.nanmean(phi[k])
        rng = max(rng, float(np.nanmax(phi) - np.nanmin(phi)))
        g = G[j][k]; g = g / g.sum()
        B = np.stack([np.ones(k.sum()), X[k], Y[k]], 1)
        coef = np.linalg.solve(B.T @ (B * g[:, None]), B.T @ (g * phi[k]))
        grad = max(grad, float(math.hypot(coef[1], coef[2])))
        inner = W[j] >= 1 - 1e-12
        for dx, dy in ((1, 0), (0, 1)):
            A = phi[: phi.shape[0] - dx, : phi.shape[1] - dy]
            Bv = phi[dx:, dy:]
            mk = inner[: phi.shape[0] - dx, : phi.shape[1] - dy] & inner[dx:, dy:]
            if mk.any():
                lip = max(lip, float(np.nanmax(np.abs(A[mk] - Bv[mk]))) / step)
        phis.append(phi)
    return dict(range=rng, lip=lip, grad=grad, phis=phis, gauge=float(np.hypot(*v)))


def setup(spec, step):
    """spec: list of (indicator, centre, tilt_to_zero_mean); returns targets on a common lattice"""
    H = int(math.ceil(1.45 / step))
    G, W, keeps, shifts = [], [], [], []
    for ind, centre, tilt in spec:
        w, X, Y, c = body_weights(ind, step, H, centre)
        shifts.append(c)
        g = w / w.sum()
        if tilt:
            g, _ = tilt_to_mean(g, X, Y)
        G.append(g); W.append(w); keeps.append(w > 0)
    tot = np.sum([[(g * X).sum(), (g * Y).sum()] for g in G], 0)
    wb = np.zeros(2)
    if np.abs(tot).max() > 1e-13:
        G, wb = balance(G, X, Y)
    return G, W, keeps, X, Y, H, float(np.hypot(*wb)), shifts


def solve_case(spec, step):
    G, W, keeps, X, Y, H, wb, shifts = setup(spec, step)
    n = len(spec)
    r = ipf(G, keeps, H, n)
    if not r["ok"]:
        return dict(ok=False, reason=r.get("reason"), n=n, step=step)
    c = corrections(r["h"], G, keeps, X, Y, W, step)
    return dict(ok=True, n=n, step=step, sweeps=r["sweeps"], err=r["err"], rate=r["rate"], balance_tilt=wb,
                range=c["range"], lip=c["lip"], grad=c["grad"], gauge=c["gauge"], phis=c["phis"], H=H,
                shifts=shifts, inner=[x >= 1 - 1e-12 for x in W])


def change(a, b):
    """largest change of the corrections between the coarse and the fine lattice: the coarse correction is
    interpolated bilinearly at the body coordinates of the fine lattice points that lie inside the body together with
    their four coarse neighbours; both are compared after removing their means over these points"""
    out = 0.0
    sa, sb = a["step"], b["step"]
    for j, (pa, pb) in enumerate(zip(a["phis"], b["phis"])):
        Ha, Hb = a["H"], b["H"]
        ca, cb = a["shifts"][j], b["shifts"][j]
        inner_a = a["inner"][j]
        ok_a = inner_a & ~np.isnan(pa)
        fi = np.argwhere(b["inner"][j] & ~np.isnan(pb))
        xf = (fi - Hb) * sb                                  # lattice coordinates of fine points
        xc = (xf - cb + ca) / sa + Ha                        # coarse array coordinates of the same body points
        i0 = np.floor(xc).astype(int); t = xc - i0
        good = (i0 >= 0).all(1) & (i0 + 1 < pa.shape[0]).all(1)
        i0, t, fi = i0[good], t[good], fi[good]
        nb = [(0, 0), (1, 0), (0, 1), (1, 1)]
        good = np.ones(len(i0), bool)
        for dx, dy in nb:
            good &= ok_a[i0[:, 0] + dx, i0[:, 1] + dy]
        i0, t, fi = i0[good], t[good], fi[good]
        v = ((1 - t[:, 0]) * (1 - t[:, 1]) * pa[i0[:, 0], i0[:, 1]] + t[:, 0] * (1 - t[:, 1]) * pa[i0[:, 0] + 1, i0[:, 1]]
             + (1 - t[:, 0]) * t[:, 1] * pa[i0[:, 0], i0[:, 1] + 1] + t[:, 0] * t[:, 1] * pa[i0[:, 0] + 1, i0[:, 1] + 1])
        w = pb[fi[:, 0], fi[:, 1]]
        if len(v):
            out = max(out, float(np.abs((v - v.mean()) - (w - w.mean())).max()))
    return out


D, KP, KM, KB = disc(), cut_disc(+1), cut_disc(-1), cut_disc(+1, 0.5)
CASES = {
    "A": {"title": "battery community",
          "rows": {3: [(D, False, False), (KP, False, False), (KM, False, False)],
                   4: [(KP, False, False), (KM, False, False)] * 2,
                   6: [(D, False, False)] * 2 + [(KP, False, False), (KM, False, False)] * 2,
                   8: [(D, False, False)] * 2 + [(KP, False, False), (KM, False, False)] * 3}},
    "B": {"title": "tilted density on the cut disc",
          "rows": {n: [(KB, False, True)] * n for n in (4, 5, 8)}},
    "C": {"title": "weighted sums of squares",
          "rows": {3: [(gain_square(r, t), False, False) for r, t in ((1, 0), (0.8, 25), (0.6, 50))],
                   4: [(gain_square(r, t), False, False) for r, t in ((1, 0), (0.9, 20), (0.7, 40), (0.5, 70))],
                   6: [(gain_square(r, t), False, False) for r, t in ((1, 0), (0.95, 15), (0.85, 30), (0.75, 45),
                                                                        (0.65, 60), (0.55, 75))]}},
    "D": {"title": "different shapes",
          "rows": {3: [(polygon(regular(3, 1.2)), True, False), (polygon([(-0.8, -0.8), (0.8, -0.8), (0.8, 0.8), (-0.8, 0.8)]), True, False),
                       (polygon(regular(5, 1.0)), True, False)],
                   4: [(polygon(regular(3, 1.2)), True, False), (polygon([(-0.8, -0.8), (0.8, -0.8), (0.8, 0.8), (-0.8, 0.8)]), True, False),
                       (polygon(regular(5, 1.0)), True, False), (disc(0.9), True, False)],
                   5: [(polygon(regular(3, 1.2)), True, False)] * 2 + [(polygon([(-0.8, -0.8), (0.8, -0.8), (0.8, 0.8), (-0.8, 0.8)]), True, False),
                       (polygon(regular(5, 1.0)), True, False), (disc(0.9), True, False)]}},
}


def strip(r):
    return {k: v for k, v in r.items() if k not in ("phis", "H", "shifts", "inner")}


if __name__ == "__main__":
    import sys
    only = sys.argv[1:] or ["A", "B", "C", "D", "E", "F"]
    out = {}
    for key in ("A", "B", "C", "D"):
        if key not in only:
            continue
        out[key] = {}
        for n, spec in CASES[key]["rows"].items():
            s1, s2 = (1 / 24, 1 / 48) if n >= 6 else (1 / 32, 1 / 64)
            a = solve_case(spec, s1)
            b = solve_case(spec, s2)
            row = {"coarse": strip(a), "fine": strip(b)}
            if a["ok"] and b["ok"]:
                row["change"] = change(a, b)
            out[key][str(n)] = row
            print(key, n, {"ok": (a["ok"], b["ok"]), "sweeps": b.get("sweeps"), "rate": b.get("rate"),
                           "range": b.get("range"), "lip": b.get("lip"), "grad": b.get("grad"),
                           "change": row.get("change"), "bal": b.get("balance_tilt"),
                           "t": round(time.time() - t0, 1)}, flush=True)
    if "E" in only:
        out["E"] = {}
        for n in (4, 5, 8, 16):
            r = solve_case([(KB, False, True)] * n, 1 / 24)
            out["E"][str(n)] = {"ok": r["ok"], "range": r.get("range"), "n_range": n * r["range"] if r["ok"] else None,
                                "lip": r.get("lip")}
            print("E", n, out["E"][str(n)], round(time.time() - t0, 1), flush=True)
    if "F" in only:
        out["F"] = []
        for den in (24, 32, 48, 64, 96):
            r = solve_case([(KB, False, True)] * 3, 1 / den)
            out["F"].append({"den": den, "ok": r["ok"], "range": r.get("range"), "lip": r.get("lip")})
            print("F", out["F"][-1], round(time.time() - t0, 1), flush=True)
    out["seconds"] = round(time.time() - t0, 1)
    json.dump(out, open("data/joint23.json" if len(sys.argv) == 1 else "data/joint23_partial.json", "w"), indent=1)
    print("done in", out["seconds"], "s")
