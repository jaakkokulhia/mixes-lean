"""Checks for Section 22 (Theorem 101 to Remark 107): conditioned products, the maximal-entropy complete mixes,
of uniform distributions on planar convex bodies.

For a body K with centroid 0 and n >= 3 it solves h(p) h^{*(n-1)}(-p) = exp(affine(p)) on K by iterating the map
Psi of the proof of Theorem 101: psi -> -(F - P F), where h is the tilt of mean 0 of u e^psi, F(p) = log h^{*(n-1)}(-p)
and P is the L^2(u) projection onto the affine functions.  The body is discretised on the lattice step*Z^2: each pixel
carries the area of its intersection with K (by 16 x 16 sub-sampling), the body is translated so that this discrete
measure has centroid 0, and convolution powers are computed by fast Fourier transforms on a grid that holds (n-1)K,
so that the lattice sum of n-1 pixels is exact.  At a fixed point the marginal of the conditioned product is the
discrete uniform measure times exp(affine), with mean 0.

Part A solves for eight bodies and n = 3, 4, 5, 8 at the steps 1/32 and 1/64 (undamped iteration; damped with
weight 1/2 if the undamped one does not converge), and records the ratio max e^psi / min e^psi, a Lipschitz
estimate for psi, the contraction factor of the iteration and the change of psi between the two steps.
Part B follows the triangle with n = 3 as the step decreases.  Part C records n times the range of psi for the
quadrilateral and n = 3, 4, 5, 8, 16.  Part D computes, for the pentagon and n = 3, the total variation between the
lattice conditioned product and its shifts by zero-sum vectors delta, against the bounds of Proposition 106.
Writes data/large22.json.
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


def regular(k):
    return [(math.cos(2 * PI * j / k + PI / 2), math.sin(2 * PI * j / k + PI / 2)) for j in range(k)]


BODIES = {
    "disc": (lambda X, Y: X * X + Y * Y <= 1, [(math.cos(2 * PI * j / 720), math.sin(2 * PI * j / 720)) for j in range(720)]),
    "square": (polygon([(-1, -1), (1, -1), (1, 1), (-1, 1)]), [(-1, -1), (1, -1), (1, 1), (-1, 1)]),
    "pentagon": (polygon(regular(5)), regular(5)),
    "heptagon": (polygon(regular(7)), regular(7)),
    "halfdisc": (lambda X, Y: (X * X + Y * Y <= 1) & (Y >= 0), [(math.cos(PI * j / 360), math.sin(PI * j / 360)) for j in range(361)]),
    "kite": (polygon([(0, 0), (0.3, -1), (1, 0), (0.3, 1)]), [(0, 0), (0.3, -1), (1, 0), (0.3, 1)]),
    "quad": (polygon([(0, 0), (1, 0), (1.2, 0.8), (0.1, 1.0)]), [(0, 0), (1, 0), (1.2, 0.8), (0.1, 1.0)]),
    "triangle": (polygon([(0, 0), (1, 0), (0, 1)]), [(0, 0), (1, 0), (0, 1)]),
}
ORDER = ["disc", "square", "pentagon", "heptagon", "halfdisc", "kite", "quad", "triangle"]


def area_weights(ind, step, half, shift, sub=16):
    idx = np.arange(-half, half + 1)
    w = np.zeros((len(idx), len(idx)))
    o = (np.arange(sub) + 0.5) / sub - 0.5
    for a in o:
        X = (idx[:, None] + a) * step + shift[0]
        for b in o:
            w += ind(X, (idx[None, :] + b) * step + shift[1])
    return w / sub ** 2


def discretise(name, step):
    ind, _ = BODIES[name]
    half = int(math.ceil(1.3 / step))
    ax = np.arange(-half, half + 1) * step
    X, Y = np.meshgrid(ax, ax, indexing="ij")
    c = np.zeros(2)
    for _ in range(4):
        w = area_weights(ind, step, half, c)
        dc = np.array([(w * X).sum(), (w * Y).sum()]) / w.sum()
        c = c + dc
    w = area_weights(ind, step, half, c)
    return w, X, Y, half, c


def centroid(name):
    """exact centroid: shoelace formula for polygons, closed forms for the disc and the half-disc"""
    if name == "disc":
        return np.zeros(2)
    if name == "halfdisc":
        return np.array([0.0, 4 / (3 * PI)])
    P = np.array(BODIES[name][1], float)
    x, y = P[:, 0], P[:, 1]
    cr = x * np.roll(y, -1) - np.roll(x, -1) * y
    a = cr.sum() / 2
    return np.array([((x + np.roll(x, -1)) * cr).sum(), ((y + np.roll(y, -1)) * cr).sum()]) / (6 * a)


def asymmetry(name):
    """Minkowski's measure of asymmetry about the centroid (Remark 85), from the vertices (or boundary points)"""
    ind, pts = BODIES[name]
    P = np.array(pts, float)
    c = centroid(name)
    best = 0.0
    for th in np.linspace(0, 2 * PI, 7200, endpoint=False):
        e = np.array([math.cos(th), math.sin(th)])
        v = (P - c) @ e
        best = max(best, v.max() / (-v.min()))
    return best


def solve(name, n, step, theta=1.0, iters=3000, tol=1e-11, disc=None):
    w, X, Y, half, c = disc if disc is not None else discretise(name, step)
    keep = w > 0
    u = w / w.sum()
    xs, ys, uk = X[keep], Y[keep], u[keep]
    B = np.stack([np.ones(keep.sum()), xs, ys], 1)
    Ginv = np.linalg.inv(B.T @ (B * uk[:, None]))
    L = 2 * half + 1
    m = n - 1
    size = 1 << int(math.ceil(math.log2(m * (L - 1) + 1)))
    I = np.arange(-half, half + 1)
    sel = np.ix_(-I + m * half, -I + m * half)
    psi = np.zeros(keep.sum())
    hist = []
    for it in range(iters):
        g = uk * np.exp(psi - psi.max())
        g /= g.sum()
        v = np.zeros(2)
        for _ in range(60):
            e = np.exp(v[0] * xs + v[1] * ys - (v[0] * xs + v[1] * ys).max())
            q = g * e
            q /= q.sum()
            mu = np.array([(q * xs).sum(), (q * ys).sum()])
            if np.abs(mu).max() < 1e-16:
                break
            C = np.cov(np.stack([xs, ys]), aweights=q, bias=True)
            v = v - np.linalg.solve(C, mu)
        h = np.zeros_like(u)
        h[keep] = q
        S = np.fft.irfft2(np.fft.rfft2(h, s=(size, size)) ** m, s=(size, size))
        Sk = S[sel][keep]
        if Sk.min() <= 0:
            return dict(ok=False, reason="nonpositive", it=it)
        F = np.log(Sk)
        PF = B @ (Ginv @ (B.T @ (uk * F)))
        new = -(F - PF)
        diff = float(np.abs(new - psi).max())
        hist.append(diff)
        psi = (1 - theta) * psi + theta * new
        if diff < tol:
            break
        if not np.isfinite(diff) or np.abs(psi).max() > 60:
            return dict(ok=False, reason="diverged", it=it)
    ok = hist[-1] < tol
    # contraction factor of the iteration from the decay of the differences
    k = min(len(hist) - 1, 12)
    rate = None
    if ok and k >= 4:
        a = [x for x in hist[-k - 1:] if x > 1e-14]
        if len(a) >= 4:
            rate = float((a[-1] / a[0]) ** (1 / (len(a) - 1)))
    # marginal: h(p) h^{*(n-1)}(-p) / h^{*n}(0), relative to u
    Sn0 = float((h[keep] * Sk).sum())
    M = h[keep] * Sk / Sn0
    rel = M / uk
    bcoef = np.linalg.lstsq(B, np.log(rel), rcond=None)[0]
    resid = float(np.abs(np.log(rel) - B @ bcoef).max())
    # Lipschitz estimate of psi over adjacent pixels both well inside K
    full = np.zeros_like(u, dtype=bool)
    full[keep] = True
    P2 = np.full(u.shape, np.nan)
    P2[keep] = psi
    inner = w >= 1 - 1e-12
    lip = 0.0
    for dx, dy in ((1, 0), (0, 1)):
        A = P2[: L - dx, : L - dy]
        Bv = P2[dx:, dy:]
        mk = inner[: L - dx, : L - dy] & inner[dx:, dy:]
        if mk.any():
            lip = max(lip, float(np.nanmax(np.abs(A[mk] - Bv[mk]))) / step)
    return dict(ok=bool(ok), it=it + 1, rate=rate, theta=theta, ratio=float(math.exp(psi.max() - psi.min())),
                lip=lip, tilt=float(math.hypot(bcoef[1], bcoef[2])), resid=resid, psi=psi, keep=keep, half=half,
                h=h, Sk=Sk, xs=xs, ys=ys, uk=uk, u=u)


def run(name, n, step, disc=None):
    r = solve(name, n, step, theta=1.0, iters=800, disc=disc)
    if not r["ok"]:
        r = solve(name, n, step, theta=0.5, iters=3000, disc=disc)
    return r


def partA():
    rows = {}
    for name in ORDER:
        d32 = discretise(name, 1 / 32)
        d64 = discretise(name, 1 / 64)
        rows[name] = {"as": asymmetry(name)}
        for n in (3, 4, 5, 8):
            a = run(name, n, 1 / 32, disc=d32)
            b = run(name, n, 1 / 64, disc=d64)
            change = None
            if a["ok"] and b["ok"]:
                # psi on the coarse lattice versus psi on the fine lattice at the same points (normalisations agree
                # up to the discretisation of P)
                P1 = np.full(a["u"].shape, np.nan); P1[a["keep"]] = a["psi"]
                P2 = np.full(b["u"].shape, np.nan); P2[b["keep"]] = b["psi"]
                sub = P2[::2, ::2][: P1.shape[0], : P1.shape[1]]
                both = ~np.isnan(P1) & ~np.isnan(sub)
                inner1 = d32[0] >= 1 - 1e-12
                both &= inner1
                change = float(np.nanmax(np.abs(P1[both] - sub[both])))
            rows[name]["n%d" % n] = {
                "ok32": a["ok"], "ok64": b["ok"], "it": b.get("it"), "theta": b.get("theta"),
                "rate": b.get("rate"), "ratio32": a.get("ratio"), "ratio": b.get("ratio"), "lip": b.get("lip"),
                "tilt": b.get("tilt"), "resid": b.get("resid"), "change": change}
            print(name, n, {k: (round(v, 4) if isinstance(v, float) else v) for k, v in rows[name]["n%d" % n].items()},
                  flush=True)
    return rows


def partB():
    out = []
    for den in (24, 32, 48, 96, 128):
        r = solve("triangle", 3, 1 / den, theta=0.5, iters=3000, tol=1e-10)
        out.append({"den": den, "ok": r["ok"], "ratio": r.get("ratio"), "reason": r.get("reason")})
        print("triangle n=3 step 1/%d" % den, out[-1], flush=True)
    und = solve("triangle", 3, 1 / 32, theta=1.0, iters=800)
    return {"steps": out, "undamped_ok": und["ok"]}


def partC():
    d = discretise("quad", 1 / 32)
    out = {}
    for n in (3, 4, 5, 8, 16):
        r = run("quad", n, 1 / 32, disc=d)
        rng = math.log(r["ratio"])
        out[str(n)] = {"range": rng, "n_range": n * rng, "lip": r["lip"]}
        print("quad", n, out[str(n)], flush=True)
    return out


def partD(step=1 / 24):
    """lattice conditioned product for the pentagon and n = 3: TV against zero-sum shifts"""
    d = discretise("pentagon", step)
    r = run("pentagon", 3, step, disc=d)
    assert r["ok"]
    h, u, half = r["h"], r["u"], r["half"]
    L = 2 * half + 1
    idx = np.argwhere(h > 0)                       # pixel index pairs (array coordinates)
    hv = h[h > 0]
    # w(i1, i2) = h(i1) h(i2) h(-i1-i2) / Z on pairs; array coordinate a <-> lattice index a - half
    pos = idx - half
    npx = len(pos)
    look = {tuple(p): k for k, p in enumerate(pos)}
    W = np.zeros((npx, npx))
    for k1 in range(npx):
        third = -pos[k1] - pos                        # lattice index of the third point
        a = third + half
        okm = (a >= 0).all(1) & (a < L).all(1)
        vals = np.zeros(npx)
        vals[okm] = h[a[okm, 0], a[okm, 1]]
        W[k1] = hv[k1] * hv * vals
    W /= W.sum()
    marg = W.sum(1)
    marg_err = float(np.abs(marg / (u[h > 0] / u[h > 0].sum()) - 1).max())

    def shifted(d1, d2):
        """W shifted by delta = (d1, d2, -d1-d2) (lattice vectors); returns TV between W and the shift"""
        # W_shift(i1, i2) = W(i1 - d1, i2 - d2)
        map1 = np.array([look.get((p[0] - d1[0], p[1] - d1[1]), -1) for p in pos])
        map2 = np.array([look.get((p[0] - d2[0], p[1] - d2[1]), -1) for p in pos])
        Ws = np.zeros_like(W)
        ok1, ok2 = map1 >= 0, map2 >= 0
        Ws[np.ix_(ok1, ok2)] = W[np.ix_(map1[ok1], map2[ok2])]
        # mass of W that moves to pairs outside the support (third point outside) is accounted for by the total:
        moved_out = 1 - Ws.sum()
        return 0.5 * (np.abs(W - Ws).sum() + moved_out)

    def single(dv):
        U = u / u.sum()
        Us = np.zeros_like(U)
        sx, sy = dv
        src = U[max(0, -sx): L - max(0, sx), max(0, -sy): L - max(0, sy)]
        Us[max(0, sx): L - max(0, -sx), max(0, sy): L - max(0, -sy)] = src
        return 0.5 * np.abs(U - Us).sum()

    lipD = r["lip"]
    res = []
    for t in (1, 2, 4):
        for label, d1, d2 in (("A", (t, 0), (-t, 0)), ("B", (t, 0), (0, t))):
            d3 = (-d1[0] - d2[0], -d1[1] - d2[1])
            tv = shifted(d1, d2)
            singles = [single(dv) for dv in (d1, d2, d3)]
            norm1 = step * sum(math.hypot(*dv) for dv in (d1, d2, d3))
            bound = 0.5 * (math.exp(lipD * norm1) - 1) + sum(singles)
            res.append({"t": t, "dir": label, "tv": float(tv), "max_single": float(max(singles)),
                        "sum_single": float(sum(singles)), "bound": float(bound), "norm1": norm1})
            print("leakage", res[-1], flush=True)
    return {"step": step, "pixels": int(npx), "marg_err": marg_err, "lip": lipD, "rows": res}


if __name__ == "__main__":
    A = partA(); print("A done", round(time.time() - t0, 1), flush=True)
    Bres = partB()
    Cres = partC()
    Dres = partD()
    json.dump(dict(partA=A, partB=Bres, partC=Cres, partD=Dres, seconds=round(time.time() - t0, 1)),
              open("data/large22.json", "w"), indent=1)
    print("done in", round(time.time() - t0, 1), "s")
