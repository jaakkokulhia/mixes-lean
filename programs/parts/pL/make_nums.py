"""Writes nums.tex for Section 22 from data/large22.json."""
import json, math
D = json.load(open("data/large22.json"))
A, B, C, L = D["partA"], D["partB"], D["partC"], D["partD"]
out = []
def m(k, v): out.append("\\newcommand{\\%s}{%s}" % (k, v))
def up(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.ceil(x * f - 1e-12) / f)
def dn(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.floor(x * f + 1e-12) / f)
def rnd(x, d): return ("%." + str(d) + "f") % x

NAMES = {"disc": "Disc", "square": "Square", "pentagon": "Regular pentagon", "heptagon": "Regular heptagon",
         "halfdisc": "Half-disc", "kite": "Kite", "quad": "Quadrilateral",
         "triangle": "Triangle"}
ORDER = ["disc", "square", "pentagon", "heptagon", "halfdisc", "kite", "quad", "triangle"]
rows = []
tilt = change = 0.0
lip3 = lip8 = 0.0
rate3 = 0.0
for name in ORDER:
    r = A[name]
    cells = []
    for n in (3, 4, 5, 8):
        c = r["n%d" % n]
        if name == "triangle" and n == 3:
            assert not c["ok64"]
            cells.append("---")
            continue
        assert c["ok32"] and c["ok64"] and c["rate"] is not None and c["rate"] < 1
        cells.append("%s (%s)" % (rnd(c["ratio"], 2), rnd(c["rate"], 2)))
        tilt = max(tilt, c["tilt"]); change = max(change, c["change"])
        if n == 3: lip3 = max(lip3, c["lip"]); rate3 = max(rate3, c["rate"])
        if n == 8: lip8 = max(lip8, c["lip"])
    rows.append("%s & %s & %s \\\\" % (NAMES[name], rnd(r["as"], 3), " & ".join(cells)))
m("LgRows", "\n".join(rows))
m("LgTilt", up(tilt, 3)); m("LgChange", up(change, 3)); m("LgLipMax", up(lip3, 1)); m("LgLipMaxEight", up(lip8, 1))
m("LgRateMax", up(rate3, 2))
# the triangle with n = 3
assert all(s["ok"] for s in B["steps"]) and not B["undamped_ok"]
m("LgTriRatios", ", ".join("$%d$" % round(s["ratio"]) for s in B["steps"]))
# 1/n decay for the quadrilateral
m("LgQuadNR", ", ".join(rnd(C[str(n)]["n_range"], 2) for n in (3, 4, 5, 8, 16)))
m("LgQuadNRlo", dn(min(C[str(n)]["n_range"] for n in (4, 5, 8, 16)), 1))
m("LgQuadNRhi", up(max(C[str(n)]["n_range"] for n in (4, 5, 8, 16)), 1))
# leakage
rr = L["rows"]
for x in rr:
    assert x["max_single"] <= x["tv"] + 1e-12 and x["tv"] <= x["bound"] + 1e-12
ratio = max(x["tv"] / x["sum_single"] for x in rr)
m("LgLeakRatio", up(ratio, 2))
m("LgLeakPixels", "{:,}".format(L["pixels"]).replace(",", "{,}"))
ex = [x for x in rr if x["t"] == 2 and x["dir"] == "B"][0]
m("LgLeakEx", "for $t=2$ steps in the second direction the total variation is $%s$, against $%s$ for the largest single coordinate, $%s$ for their sum and $%s$ for the bound" % (
    rnd(ex["tv"], 3), rnd(ex["max_single"], 3), rnd(ex["sum_single"], 3), rnd(ex["bound"], 3)))
m("LgLeakLip", up(L["lip"], 1))
m("SecsLg", "%d" % math.ceil(D["seconds"]))
open("nums.tex", "w").write("\n".join(out) + "\n")
print("nums.tex written:", len(out), "macros")
