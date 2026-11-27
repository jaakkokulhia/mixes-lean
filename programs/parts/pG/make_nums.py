"""Writes nums.tex for the section on scaled copies, sections that are products and the wider coupling of the
levels (Section 20) from data/gen20.json.  Upper bounds are rounded up, lower bounds down."""
import json, math
D = json.load(open("data/gen20.json"))
A1, A2, A3, A4, B, C = D["partA1"], D["partA2"], D["partA3"], D["partA4"], D["partB"], D["partC"]
out = []
def m(k, v): out.append("\\newcommand{\\%s}{%s}" % (k, v))
def intc(k): return "{:,}".format(k).replace(",", "{,}")
def up(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.ceil(x * f - 1e-12) / f)
def dn(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.floor(x * f + 1e-12) / f)
def sci(x):
    """upper bound with a one-digit mantissa rounded up, as a TeX number"""
    if x <= 0: return "0"
    e = int(math.floor(math.log10(abs(x)))); mt = x / 10 ** e
    mt = math.ceil(mt * 10 - 1e-9) / 10
    if mt >= 10: mt /= 10; e += 1
    return "%s\\cdot10^{%d}" % (("%.1f" % mt).rstrip("0").rstrip("."), e)

# ---- Part A: exact checks
m("GenAOneCases", intc(A1["cases"])); m("GenAOneTight", A1["tight"]); m("GenAOneZero", A1["with_zero"])
m("GenAOneEqual", A1["equal"]); m("GenAOneBetaTwo", A1["beta_two"]); m("GenAOneSegments", intc(A1["segments"]))
m("GenAOneNmax", A1["n_max"])
lk = A1["leaf_kinds"]
m("GenAOneBase", intc(lk.get("base", 0))); m("GenAOneSplit", intc(lk.get("split", 0))); m("GenAOneU", intc(lk.get("U", 0)))
m("GenATwoCases", A2["cases"]); m("GenATwoEq", A2["equality_cases"])
assert A2["min_slack"] >= 0 and A3["min_slack"] >= 0
m("GenAThreeCases", A3["cases"]); m("GenAThreeJoins", A3["joins"])
rows4 = A4["rows"]
assert all(r["min_P"] >= 0 and r["min_F"] >= 0 for r in rows4.values())
assert rows4["double frusta k=2"]["below_quarter_fails"]
m("GenAFourKmax", max(int(k.split("k=")[1]) for k in rows4))
m("GenAFourDF", rows4["double frusta k=2"]["cases"])
m("GenAFourCHtwo", rows4["chamfered k=2"]["cases"]); m("GenAFourCHmore", rows4["chamfered k=3"]["cases"])

# ---- Part B: levels of Lemma 82, regular polygons, constants
c = B["constants"]
m("PlateauBound", dn(c["plateau_bound"], 4))
assert abs(c["dec_r0"] - c["dec_r0_formula"]) < 1e-12 and c["dec_rsum"] > c["dec_r0"]
m("DecRZero", up(c["dec_r0"], 4)); m("DecRSum", dn(c["dec_rsum"], 4))
assert abs(c["pentagon_sbar"] - c["pentagon_sbar_formula"]) < 1e-8
m("GenBPentErr", sci(abs(c["pentagon_ratio"] - c["pentagon_formula"])))
m("PolyHStep", ("%g" % B["hstep"]))
lines = []; none = []
for p in B["polygons"]:
    if p["ok"]:
        lines.append("%d & %s & $[%.4f,\\,%.4f]$ & %.4f & %s & %s \\\\" % (
            p["n_sides"], dn(p["ratio"], 4), p["h_lo"], p["h_hi"], p["h"], dn(p["P"], 4), dn(p["F"], 4)))
        assert p["P"] > 0 and p["F"] > 0
    else:
        none.append(p["n_sides"])
first_none = min(none)
lines.append("%d & %s & none & & & \\\\" % (first_none, dn([p for p in B["polygons"] if p["n_sides"] == first_none][0]["ratio"], 4)))
assert all(p["ok"] for p in B["polygons"] if p["n_sides"] < first_none) and none == list(range(first_none, max(none) + 1, 2))
m("PolyRows", "\n".join(lines))
m("PolyNoneLo", first_none); m("PolyNoneHi", max(none))
m("PolyOkHi", max(p["n_sides"] for p in B["polygons"] if p["ok"]))
lv = B["levels"]
assert all(r["min_alpha_over_x"] > 0 and r["P_slack"] >= -1e-12 and r["F_slack"] >= -1e-12 for r in lv)
m("GenBNbodies", len(lv))
m("GenBIdErr", sci(max(r["identity_err"] for r in lv)))
m("GenBMassErr", sci(max(r["mass_err"] for r in lv)))

# ---- Part C: simulations
names = {"(p+1)(1-x)^p, p=2": "$3(1-x)^2$", "(p+1)(1-x)^p, p=3": "$4(1-x)^3$", "polygon Q": "Polygon $Q$",
         "projection of a tetrahedron": "Projection of a tetrahedron", "Beta(2,4)": "Beta$(2,4)$",
         "hip roof, beta = 1/2": "Hip roof, $\\beta=\\frac12$", "frustum, ratios 1/4 and 3/5": "Frustum, top $[-\\frac14,\\frac14]\\times[-\\frac35,\\frac35]$",
         "join of a segment and a disc": "Join of a segment and a disc", "half-ball": "Half-ball",
         "regular pentagon": "Regular pentagon", "regular octagon": "Regular octagon", "regular decagon": "Regular decagon",
         "hexagon rho=0.3": "Hexagon, $\\rho=0.3$", "stadium h'=0.75": "Stadium, $h'=\\frac34$",
         "elongated octahedron h'=0.75": "Elongated octahedron, $h'=\\frac34$"}
thm = {"scaled copies": "\\ref{g:thm:scaled}", "product sections": "\\ref{g:thm:prod}", "flat ends": "\\ref{g:thm:bipyr}"}
lines = []
for r in C["rows"]:
    dim = 1 if r["kind"] == "scaled copies" else r.get("d", r.get("k"))
    ratio = r.get("ratio", float(r["n"]))
    sc = ("%g" % ratio) if abs(ratio - r["n"]) > 1e-9 else "equal"
    if r["kind"] != "scaled copies":
        assert r["outside"] <= 1e-12 and r["fibre_slack"] >= -1e-12
    else:
        assert ratio >= r["beta_star"] - 1e-6
    lines.append("%s & %s & %d & %d & %s & $%s$ & %d & %s \\\\" % (
        names[r["body"]], thm[r["kind"]], dim, r["n"], sc, sci(r["max_sum_dev"]), r["tests"], dn(r["min_p"], 3 if r["min_p"] >= 0.01 else 4)))
m("GenCRows", "\n".join(lines))
m("GenCTests", C["tests"]); m("GenCPmin", dn(C["min_p"], 4)); m("GenCChance", up(C["chance_min_p"], 2))
m("GenCSumDev", sci(max(r["max_sum_dev"] for r in C["rows"])))
m("GenCSamples", intc(C["rows"][0]["samples"]))
worst = min(C["rows"], key=lambda r: r["min_p"])
m("GenCWorst", names[worst["body"]])
f = C["follow"]
if f:
    m("GenCFollowSamples", intc(f["samples"])); m("GenCFollowLo", dn(min(f["min_p"]), 3)); m("GenCFollowHi", up(max(f["min_p"]), 3))
m("SecsGen", "%d" % math.ceil(D["seconds"]))
# ---- the 80-digit recomputation of Table 3 (poly80.py)
E = json.load(open("data/poly80.json"))
assert E["min_slack"] > 0 and len(E["rows"]) == len([p for p in B["polygons"] if p["ok"]])
m("PolyEightyMin", dn(E["min_slack"], 4)); m("PolyEightyDiff", sci(E["max_diff"])); m("PolyEightyDigits", E["digits"])
open("nums.tex", "w").write("\n".join(out) + "\n")
print("nums.tex written:", len(out), "macros")
