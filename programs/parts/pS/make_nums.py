"""Writes nums.tex for the section on cones from data/cones16.json."""
import json, math
D = json.load(open("data/cones16.json"))
A, B, C = D["partA"], D["partB"], D["partC"]
out = []
def m(k, v): out.append("\\newcommand{\\%s}{%s}" % (k, v))
def intc(k): return "{:,}".format(k).replace(",", "{,}")
def up(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.ceil(x * f - 1e-12) / f)
def dn(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.floor(x * f + 1e-12) / f)
def sci(x, mode="up"):
    e = int(math.floor(math.log10(abs(x)))); mt = x / 10 ** e
    mt = (math.ceil(mt * 10 - 1e-9) if mode == "up" else math.floor(mt * 10 + 1e-9)) / 10
    if mt >= 10: mt /= 10; e += 1
    return "%s\\cdot10^{%d}" % (("%.1f" % mt).rstrip("0").rstrip("."), e)

m("MomKMax", A["k_max"]); m("MomDeg", A["degree_max"]); m("MomCount", intc(A["moments"]))
modes = B["modes"]
m("NLevel", intc(B["cases"])); m("LevelKMax", B["k_max"]); m("LevelExtraPlus", B["extra"] + 1)
m("NLevelTight", intc(modes.get("tight", 0) + modes.get("equal", 0))); m("NLevelEqual", intc(modes.get("equal", 0)))
m("NLevelSeg", intc(B["segments"])); m("NLevelTuples", intc(B["tuples"])); m("NLevelCells", intc(B["cells"]))
m("LevelNMax", B["n_max"])
rows = C["rows"]
assert all(r["min_coord"] >= 0 for r in rows)                     # every point lies in its body
names = {"simplex": "Simplex", "pyramid": "Pyramid over a cube", "tetrahedron": "Tetrahedron, Remark~\\ref{s:rem:tetra}"}
lines = []
for r in rows:
    lines.append("%s & %d & %d & %s & $%s$ & %d & %s \\\\" % (names[r["body"]], r["d"], r["n"], intc(r["samples"]),
                 sci(r["max_sum_dev"]), r["tests"], dn(r["min_p"], 3)))
m("ConeRows", "\n".join(lines))
m("ConeMC", intc(max(r["samples"] for r in rows if r["body"] != "tetrahedron")))
m("ConeMCT", intc(max(r["samples"] for r in rows if r["body"] == "tetrahedron")))
m("ConeSumDev", sci(max(r["max_sum_dev"] for r in rows)))
m("ConeTests", intc(C["tests"])); m("ConePmin", dn(C["min_p"], 4)); m("ConeChance", dn(C["chance_min_p"], 2))
m("SecsCone", int(math.ceil(D["seconds"])))
m("SecsConeExact", int(math.ceil(A["seconds"] + B["seconds"])))
open("nums.tex", "w").write("\n".join(out) + "\n")
print("nums.tex written")
