"""Writes nums.tex for the section on one-dimensional projections, bipyramids and the remaining cases of
Open Problem 5 from data/open18.json.  Upper bounds are rounded up, lower bounds down."""
import json, math
D = json.load(open("data/open18.json"))
A, B, C, Dd = D["partA"], D["partB"], D["partC"], D["partD"]
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

# ---- Part A: concave p-th roots
rows = A["rows"]
m("OpnANDet", len(rows))
m("OpnANRand", intc(A["random"]["n"]))
m("OpnARandMax", up(A["random"]["max_ratio"], 4))
assert A["random"]["max_ratio"] < 1
excess = max(r["beta"] - (r["p"] + 2) for r in rows)
m("OpnADetExcess", sci(max(excess, 1e-300)) if excess > 0 else "0")
tight = [r for r in rows if r["key"] == "linear"]
m("OpnATightN", len(tight))
m("OpnATightErr", sci(max(abs(r["beta"] - (r["p"] + 2)) for r in tight)))
m("OpnATightPs", ", ".join("%g" % r["p"] for r in tight))
tet = [r for r in rows if r["key"] == "tetra"]; sym = [r for r in rows if r["key"] in ("cube", "octa")]
m("OpnATetraErr", sci(max(abs(r["beta"] - 3) for r in tet)))
m("OpnASymErr", sci(max(abs(r["beta"] - 2) for r in sym)))
m("OpnANProj", len(tet) + len(sym))
others = [r for r in rows if r["key"] in ("tent", "quartic", "sine", "symmetric")]
m("OpnAOtherMax", up(max(r["ratio"] for r in others), 3))
mc = A["mc"]
m("OpnAMCN", len(mc)); m("OpnAMCSamples", intc(mc[0]["samples"]))
m("OpnAMCSumDev", sci(max(r["sumerr"] for r in mc)))
m("OpnAMCTests", sum(r["tests"] for r in mc))
m("OpnAMCPmin", dn(min(r["min_p"] for r in mc), 3))
assert all(r["inrange"] for r in mc)

# ---- Part B: levels of the bipyramids
m("OpnBKMax", B["rows"][-1]["k"])
m("OpnBIdErr", sci(max(r["identity_err"] for r in B["rows"])))
m("OpnBMassErr", sci(max(r["mass_err"] for r in B["rows"])))
m("OpnBHalfErr", sci(max(abs(r["alpha_half"] - r["alpha_half_formula"]) for r in B["rows"]) or 1e-300)
  if any(abs(r["alpha_half"] - r["alpha_half_formula"]) > 0 for r in B["rows"]) else "0")
m("OpnBClosedErr", sci(B["closed_k3"]))
assert all(r["min_alpha_over_x"] >= 0 for r in B["rows"])
st = B["star"]
assert not st["tent k=2"]["holds"] and st["tent k=3"]["holds"] and not st["ball k=3"]["holds"]

# ---- Part C: Monte Carlo of the bipyramids
names = {"regular octahedron": "Regular octahedron", "double cone over a disc": "Double cone over a disc",
         "bipyramid over a cube": "Bipyramid over a cube", "elongated octahedron": "Elongated octahedron, $h=\\frac12$"}
lines = []
for r in C["rows"]:
    assert r["outside"] <= 1e-12
    lines.append("%s & %d & %d & %s & $%s$ & %d & %s \\\\" % (names[r["body"]], r["k"], r["n"], intc(r["samples"]),
                 sci(r["max_sum_dev"]), r["tests"], dn(r["min_p"], 3)))
m("OpnCRows", "\n".join(lines))
m("OpnCTests", C["tests"]); m("OpnCPmin", dn(C["min_p"], 3)); m("OpnCChance", up(C["chance_min_p"], 2))
m("OpnCSumDev", sci(max(r["max_sum_dev"] for r in C["rows"])))
m("OpnCSamples", intc(C["rows"][0]["samples"]))

# ---- Part D: linear programmes on the levels of planar bodies
by = {}
for r in Dd["rows"]:
    by.setdefault(r["body"], {})[r["J"]] = r
Js = sorted({r["J"] for r in Dd["rows"]})
lines = []
for body in ["half-disc", "regular pentagon", "kite", "triangle", "disc"]:
    c = " & ".join("$%s$" % sci(by[body][J]["constrained"]) for J in Js)
    f = " & ".join("$%s$" % sci(by[body][J]["free"]) for J in Js)
    lines.append("%s & with & %s \\\\" % (body[0].upper() + body[1:], c))
    lines.append(" & without & %s \\\\" % f)
m("OpnDRows", "\n".join(lines))
m("OpnDJs", ", ".join(str(J) for J in Js))
m("OpnDJMax", Js[-1]); m("OpnDJMin", Js[0])
# half-disc and pentagon: largest difference from the second grid on; kite: ratio of consecutive differences
diff = lambda body, J: by[body][J]["constrained"] - by[body][J]["free"]
m("OpnDSymDiff", sci(max(max(abs(diff(b, J)) for J in Js[1:]) for b in ("half-disc", "regular pentagon"))))
kd = [diff("kite", J) for J in Js]
ratios = [kd[i] / kd[i + 1] for i in range(len(kd) - 1)]
m("OpnDKiteRatioLo", dn(min(ratios), 2)); m("OpnDKiteRatioHi", up(max(ratios), 2))
m("OpnDKiteLast", sci(kd[-1]))
ctrl = max(abs(diff(b, J)) for b in ("triangle", "disc") for J in Js)
m("OpnDCtrlDiff", sci(ctrl) if ctrl > 0 else "0")
mo = Dd["more"]
m("OpnDMoreDiff", sci(max(abs(r["constrained"] - r["free"]) for r in mo)) if any(
    abs(r["constrained"] - r["free"]) > 0 for r in mo) else "0")
m("OpnDMoreN", len(mo))
m("SecsOpn", "%d" % math.ceil(D["seconds"]))
open("nums.tex", "w").write("\n".join(out) + "\n")
print("nums.tex written:", len(out), "macros")
