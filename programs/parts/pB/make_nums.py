"""Writes nums.tex for the sections on balls, products, frusta and bodies with homothetic sections from
data/bodies17.json; the table of thresholds of frusta is computed here from the formula for a_{d,q}."""
import json, math
D = json.load(open("data/bodies17.json"))
A1, A2, A3, A4, B = D["partA1"], D["partA2"], D["partA3"], D["partA4"], D["partB"]
out = []
def m(k, v): out.append("\\newcommand{\\%s}{%s}" % (k, v))
def intc(k): return "{:,}".format(k).replace(",", "{,}")
def dn(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.floor(x * f + 1e-12) / f)
def sci(x):
    if x == 0: return "0"
    e = int(math.floor(math.log10(abs(x)))); mt = x / 10 ** e
    mt = math.ceil(mt * 10 - 1e-9) / 10
    if mt >= 10: mt /= 10; e += 1
    return "%s\\cdot10^{%d}" % (("%.1f" % mt).rstrip("0").rstrip("."), e)

# ---- thresholds of frusta over parallelotopes and balls: least q with a_{d,q} <= n
def a(d, q): return (d + 1) * sum(q ** j for j in range(d)) / sum((j + 1) * q ** j for j in range(d))
def qstar(d, n):
    lo, hi = 0.0, 1.0                                    # a(d, .) decreases from d+1 to 2 on [0, 1)
    if a(d, 0.0) <= n: return 0.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if a(d, mid) <= n: hi = mid
        else: lo = mid
    return hi
for d in range(2, 11):                                   # check the decrease used by the bisection
    vals = [a(d, i / 1000) for i in range(1000)]
    assert all(x > y for x, y in zip(vals, vals[1:]))
assert abs(qstar(3, 3) - (math.sqrt(6) - 1) / 5) < 1e-12
m("FrustumQThree", "%.4f" % ((math.sqrt(6) - 1) / 5))
NMAX = 8
rows = []
for d in range(3, NMAX + 1):
    cells = []
    for n in range(3, NMAX + 1):
        cells.append("%.3f" % qstar(d, n) if n <= d else ("$0$" if n == d + 1 else ""))
    rows.append("%d & %s \\\\" % (d, " & ".join(cells)))
m("FrustumRows", "\n".join(rows))
m("FrustumNMax", NMAX)
# check against the grid of Part A1 (least grid q with a <= n, grid 1/1000)
for d, row in A1["first_q"].items():
    d = int(d)
    for n, qg in zip(range(3, d + 2), row):
        if qg is None: continue
        num, den = (int(x) for x in qg.split("/")) if "/" in qg else (int(qg), 1)
        assert qstar(d, n) <= num / den + 1e-12 and (num == 0 or qstar(d, n) > (num - 1) / den - 1e-12), (d, n, qg)

# ---- Part A
m("BodACases", intc(A1["cases"])); m("BodAKMax", A1["k_max"]); m("BodAGrid", A1["grid"])
m("BodMomCount", intc(A2["moments"])); m("BodMomKMax", A2["k_max"]); m("BodMomDeg", A2["degree_max"])
m("BodMomQs", ",".join((q if "/" not in q else "\\tfrac{%s}{%s}" % tuple(q.split("/"))) for q in A2["q_values"]))
modes = A3["modes"]
m("BodNLevel", intc(A3["cases"])); m("BodLevelKMax", A3["k_max"]); m("BodLevelNMax", A3["n_max"])
m("BodNLevelTight", intc(modes.get("tight", 0) + modes.get("equal", 0))); m("BodNLevelEqual", intc(modes.get("equal", 0)))
m("BodLevelSeg", intc(A3["segments"])); m("BodLevelCells", intc(A3["cells"])); m("BodLevelTuples", intc(A3["tuples"]))
m("BodNConc", intc(A4["cases"]))

# ---- Part B
P = B["polygons"]
m("BodPolyCases", intc(P["cases"])); m("BodPolyErr", sci(P["max_error"]))
names = {"ball": "Ball", "scaled balls": "Five scaled balls",
         "truncated simplex": "Truncated simplex", "scaled truncated simplices": "Five truncated simplices",
         "frustum over a cube": "Frustum over a cube", "frustum over a ball": "Frustum over a ball",
         "triangular prism": "Prism $\\Delta_2\\times[0,1]$", "cylinder": "Cylinder $B_2\\times[0,1]$",
         "half-ball": "Half-ball", "paraboloid": "Paraboloid", "join of two discs": "Join of two discs"}
groups = {}                                              # rows grouped by body, dimension and ratio, in order
for r in B["rows"]:
    groups.setdefault((r["body"], r["d"], r.get("q")), []).append(r)
groups = list(groups.items())
lines = []
for (body, d, q), rs in groups:
    ns = [r["n"] for r in rs]
    nstr = str(ns[0]) if len(ns) == 1 else ("%d, %d" % (ns[0], ns[1]) if len(ns) == 2 else "%d--%d" % (ns[0], ns[-1]))
    qs = "--" if q is None else ("%g" % q)
    dev = max(r["max_sum_dev"] for r in rs)
    lines.append("%s & %d & %s & %s & %s & $%s$ & %d & %s \\\\" % (names[body], d, qs, nstr, intc(rs[0]["samples"]),
                 sci(dev), sum(r["tests"] for r in rs), dn(min(r["min_p"] for r in rs), 3)))
m("BodRows", "\n".join(lines))
for r in B["rows"]:                                      # every point lies in its body
    assert r.get("min_coord", 0) >= 0 and r.get("outside", -1) <= 0, r
m("BodSumDev", sci(max(r["max_sum_dev"] for r in B["rows"])))
m("BodTests", intc(B["tests"])); m("BodPmin", dn(B["min_p"], 4)); m("BodChance", dn(B["chance_min_p"], 2))
m("BodMC", intc(D["settings"]["MC"])); m("BodMCB", intc(D["settings"]["MCB"]))
m("SecsBod", int(math.ceil(D["seconds"])))
open("nums.tex", "w").write("\n".join(out) + "\n")
print("nums.tex written")
