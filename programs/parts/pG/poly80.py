"""Recomputes Table 3 (Corollary 84(f)) with 80 significant digits.

For each regular 2m-gon with inradius 1 that Table 3 lists, sliced perpendicular to two opposite sides, the program
evaluates the slacks of the conditions (P_h) and (F_h) of Theorem 83 with k = 2 at the value of h stored in
data/gen20.json:
    (P_h)  r(h) - 2 * int_h^1 r(a) / (2h - a) da,
    (F_h)  min over 0 <= c <= 1-h of r(h) + r(h+c) - r(c).
The half-width r is piecewise linear, so the integral has a closed form on each linear piece, and r(h) + r(h+c) - r(c)
is piecewise linear in c, so its minimum is attained at c = 0, at c = 1-h, or where c or h+c is a breakpoint.
pi, sines and cosines are summed from their series and logarithms come from the decimal module, all with 80 digits,
so rounding errors are far below the slacks. Uses only the standard library. Writes data/poly80.json.
"""
import json, time
from decimal import Decimal as D, getcontext

getcontext().prec = 80
TINY = D(10) ** -85


def atan_inv(x):
    """arctan(1/x) for an integer x > 1, by its alternating series"""
    x = D(x); s = D(0); t = 1 / x; k = 0; x2 = x * x
    while t > TINY:
        s += t / (2 * k + 1) if k % 2 == 0 else -t / (2 * k + 1)
        t /= x2; k += 1
    return s


PI = 16 * atan_inv(5) - 4 * atan_inv(239)          # Machin's formula


def sincos(x):
    s = D(0); term = x; k = 1
    while abs(term) > TINY:
        s += term; term *= -x * x / ((k + 1) * (k + 2)); k += 2
    c = D(0); term = D(1); k = 0
    while abs(term) > TINY:
        c += term; term *= -x * x / ((k + 1) * (k + 2)); k += 2
    return s, c


def profile(m):
    """breakpoints (z, r) of the half-width of the regular 2m-gon with inradius 1 and flat sides at z = +-1,
    for 0 <= z <= 1 in increasing z; the same polygon as regular_polygon(m) in gen20.py"""
    _, c0 = sincos(PI / (2 * m)); R = 1 / c0
    pts = []
    for j in range(m + 1):
        s, c = sincos(PI / 2 - PI / (2 * m) - j * PI / m)
        if abs(s) < D(10) ** -70:
            s = D(0)
        if s >= 0 and c >= 0:
            pts.append((R * s, R * c))
    pts.sort()
    if pts[0][0] > 0:                                 # a vertical side crosses z = 0
        pts.insert(0, (D(0), pts[0][1]))
    pts[-1] = (D(1), pts[-1][1])                      # the flat side is at height 1 exactly
    return pts


def r_of(prof, z):
    for (z0, r0), (z1, r1) in zip(prof, prof[1:]):
        if z0 <= z <= z1:
            return r0 + (r1 - r0) * (z - z0) / (z1 - z0)
    raise ValueError(z)


def P_slack(prof, h):
    tot = D(0)
    for (z0, r0), (z1, r1) in zip(prof, prof[1:]):
        lo, hi = max(z0, h), min(z1, D(1))
        if lo >= hi:
            continue
        beta = (r1 - r0) / (z1 - z0); alpha = r0 - beta * z0      # r(a) = alpha + beta a on this piece
        tot += (alpha + 2 * h * beta) * ((2 * h - lo) / (2 * h - hi)).ln() - beta * (hi - lo)
    return r_of(prof, h) - 2 * tot


def F_slack(prof, h):
    cands = {D(0), 1 - h}
    for z, _ in prof:
        for c in (z, z - h):
            if 0 <= c <= 1 - h:
                cands.add(c)
    return min(r_of(prof, h) + r_of(prof, h + c) - r_of(prof, c) for c in cands)


def main():
    t0 = time.time()
    stored = json.load(open("data/gen20.json"))["partB"]["polygons"]
    rows = []
    for p in stored:
        if not p["ok"]:
            continue
        m = p["n_sides"] // 2; h = D(repr(p["h"]))
        prof = profile(m)
        P, F = P_slack(prof, h), F_slack(prof, h)
        rows.append(dict(n_sides=p["n_sides"], h=str(h), P80=str(+P), F80=str(+F),
                         P_float=p["P"], F_float=p["F"],
                         diff=float(max(abs(P - D(repr(p["P"]))), abs(F - D(repr(p["F"])))))))
        print("%2d-gon  h=%s  P=%.12f  F=%.12f" % (p["n_sides"], h, P, F))
    out = dict(digits=getcontext().prec, rows=rows,
               min_slack=float(min(min(D(r["P80"]), D(r["F80"])) for r in rows)),
               max_diff=max(r["diff"] for r in rows), seconds=round(time.time() - t0, 2))
    json.dump(out, open("data/poly80.json", "w"), indent=1)
    print("smallest slack %.6f, largest difference from the floating-point values %.2e"
          % (out["min_slack"], out["max_diff"]))


if __name__ == "__main__":
    main()
