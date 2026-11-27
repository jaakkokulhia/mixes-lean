"""Writes nums.tex for the pointwise check of Corollary 96(c) from data/pointwise21.json and for the centrally
symmetric bodies of Corollary 98 from data/symm25.json.  Upper bounds and left
sides are rounded up, right sides and margins down."""
import json, math
D = json.load(open("data/pointwise21.json"))
R21 = json.load(open("../pR/data/regular21.json"))["partA"]
A, B, C = D["partA"], D["partB"], D["partC"]
out = []
def m(k, v): out.append("\\newcommand{\\%s}{%s}" % (k, v))
def up(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.ceil(x * f - 1e-12) / f)
def dn(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.floor(x * f + 1e-12) / f)
def intc(k): return "{:,}".format(k).replace(",", "{,}")
def sci(x):
    if x <= 0: return "0"
    e = int(math.floor(math.log10(abs(x)))); mt = math.ceil(x / 10 ** e * 10 - 1e-9) / 10
    if mt >= 10: mt /= 10; e += 1
    return "%s\\cdot10^{%d}" % (("%.1f" % mt).rstrip("0").rstrip("."), e)

CASES = ["5,3", "5,4", "7,4", "7,5"]
base, fine = A["base"], A["fine"]
# the tables against the bounds of regular21.py
for res in (base, fine):
    assert abs(res["c3"] - R21["c3"]) < 1e-5
    assert R21["a4_1"][0] <= res["lam3_1"] <= R21["a4_1"][1] and R21["a5_1"][0] <= res["lam4_1"] <= R21["a5_1"][1]
    assert R21["c4_lo"] - 1e-4 <= res["c4"] <= R21["c4_hi"] + 1e-4
m("PwCthreeErr", sci(max(abs(base["c3"] - R21["c3"]), abs(fine["c3"] - R21["c3"]))))
lines, margins, changes = [], [], []
for c in CASES:
    b, f = base["rows"][c], fine["rows"][c]
    assert b["margin"] > 0 and f["margin"] > 0 and b["neumann"] > 0
    k, n = c.split(",")
    lines.append("%s & %s & %s & %s & %s & %s & %s & %s \\\\" % (
        k, n, up(b["t"], 4), up(b["max_nus"], 4), up(b["max_lhs"], 4), dn(b["inv_area"], 4), dn(b["margin"], 4), dn(f["margin"], 4)))
    margins.append(b["margin"]); changes.append(abs(f["margin"] - b["margin"]))
m("PwRows", "\n".join(lines))
m("PwMinMargin", dn(min(margins), 3)); m("PwMaxChange", sci(max(changes)))
m("PwJ", 48); m("PwJfine", 64); m("PwNodes", 320); m("PwNodesFine", 480); m("PwAngles", "4096"); m("PwAnglesFine", "8192")
m("PwPentT", up(base["rows"]["5,3"]["t"], 4))
# consistency checks
mass_err = max(abs(B[c]["mass"] - B[c]["mass_exact"]) for c in CASES); assert mass_err < 1e-6
synth_err = max(B[c]["synth_err"] for c in CASES); assert synth_err < 1e-4
m("PwMassErr", sci(mass_err)); m("PwSynthErr", sci(synth_err))
# the simulations
for c in CASES:
    assert C[c]["inside"] and C[c]["max_sum"] < 1e-12 and C[c]["min_density_L"] > 0 and C[c]["min_density_R"] > 0
tests = sum(C[c]["tests"] for c in CASES); pmin = min(C[c]["min_p"] for c in CASES)
m("PwSimN", intc(C["5,3"]["N"])); m("PwSimTests", tests); m("PwSimP", dn(pmin, 3))
m("PwSimChance", up(1 - (1 - pmin) ** tests, 2)); m("PwSimSum", sci(max(max(C[c]["max_sum"] for c in CASES), 1e-300)))
m("SecsPw", "%d" % math.ceil(D["seconds"]))
# the centrally symmetric bodies (symm25.py)
S = json.load(open("data/symm25.json")); SA, SB = S["partA"], S["partB"]
volerr = max(SA["rows"][k]["err"] for k in ("dodecahedron", "icosahedron", "24-cell")); assert volerr < 1e-12
for k in ("600-cell", "120-cell"):
    assert SA["rows"][k]["ok"] and abs(SA["rows"][k]["inradius_600"] - SA["rows"]["600-cell"]["inradius"]) < 1e-12
assert all(SA["rows"][k]["below_5_3"] for k in SA["rows"])
cr = SA["cross"]; assert cr["ineq_243"] and cr["ineq_64"] and cr["three_v3"] < 5 and cr["three_v4"] < 7
assert abs(cr["v3"] - cr["v3_closed"]) < 1e-12 and abs(cr["v4"] - cr["v4_closed"]) < 1e-12
m("SymmVolErr", sci(max(volerr, 1e-16)))
m("SymmRatioOneTwenty", up(SA["rows"]["120-cell"]["ratio"], 3)); m("SymmRatioSixHundred", up(SA["rows"]["600-cell"]["ratio"], 3))
NAMES = {"dodecahedron": "dodecahedron", "icosahedron": "icosahedron", "24-cell": "$24$-cell", "120-cell": "$120$-cell",
         "600-cell": "$600$-cell", "cross-polytope": "cross-polytope", "hexagon": "hexagon",
         "Reuleaux triangle": "Reuleaux triangle"}
CORES = {"BallCore": "ball", "DoubleConeCore": "double cone"}
lines = []; accerr = 0.0
for r in SB["rows"]:
    assert r["max_sum"] < 1e-12 and r["excess"] <= 1e-12 and r["threshold"] <= r["n"] and r.get("fibre_ok", True)
    core = {"hexagon": "ellipse", "Reuleaux triangle": "disc"}.get(r["body"], CORES[r["core"]])
    accerr = max(accerr, abs(r["accept"] - r["accept_expected"]))
    lines.append("%s & %d & %d & %d & %s & %s & %s & %s & %d & %s \\\\" % (
        NAMES[r["body"]], r["d"], r["n"], r["r"], core, up(r["ratio"], 4), dn(r["accept"], 4),
        dn(r["accept_expected"], 4), r["tests"], dn(r["min_p"], 4)))
assert accerr < 0.01
m("SymmRows", "\n".join(lines)); m("SymmN", intc(SB["rows"][0]["samples"])); m("SymmAccErr", sci(accerr))
m("SymmMaxSum", sci(max(r["max_sum"] for r in SB["rows"]))); m("SymmTests", SB["tests"])
m("SymmMinP", dn(SB["min_p"], 4)); m("SymmChance", up(SB["chance_min_p"], 2))
m("SymmHexRatio", up(SB["hexagon"]["ratio"], 4)); m("SecsSymm", "%d" % math.ceil(S["seconds"]))
SC = S["partC"]
for r in SC["rows"]:
    assert r["max_sum"] < 1e-12 and r["excess"] <= 1e-12
m("SymmRerunN", "10^{%d}" % round(math.log10(SC["samples"])) if SC["samples"] in (10 ** 6, 10 ** 7) else intc(SC["samples"]))
m("SymmRerunRuns", len(SC["rows"])); m("SymmRerunMin", dn(min(r["min_p"] for r in SC["rows"]), 3))
m("SymmRerunMax", up(max(r["min_p"] for r in SC["rows"]), 3))
open("nums.tex", "w").write("\n".join(out) + "\n")
print("nums.tex written:", len(out), "macros")
