"""Writes nums.tex for Section 24 from data/markov24.json."""
import json, math
D = json.load(open("data/markov24.json"))
A, B = D["partA"], D["partB"]
out = []
def m(k, v): out.append("\\newcommand{\\%s}{%s}" % (k, v))
def up(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.ceil(x * f - 1e-12) / f)
def rnd(x, d): return ("%." + str(d) + "f") % x
def sci(x):
    e = math.floor(math.log10(x)); return "%d\\cdot10^{%d}" % (math.ceil(x / 10 ** e - 1e-12), e)
m("MkT", "{:,}".format(A["rows"][0]["T"]).replace(",", "{,}"))
m("MkSumDev", sci(max(r["sum_dev"] for r in A["rows"])))
m("MkTests", "%d" % A["tests"]); m("MkPmin", rnd(A["pmin"], 3)); m("MkChance", rnd(A["chance"], 2))
m("MkCorr", up(max(r["corr_max"] for r in A["rows"]), 3)); m("MkSlope", up(max(r["slope_dev_max"] for r in A["rows"]), 3))
m("MkCases", ", ".join("$\\rho=%g$ with $n=%d$" % (r["rho"], r["n"]) for r in A["rows"]))
rows = []
for r in B:
    rows.append("$%g$ & $%d$ & %s & %s & %s & %s \\\\" % (r["rho"], r["n_min"], rnd(r["mean_sq"], 3),
                rnd(r["lb_0.05"], 3), rnd(r["lb_0.1"], 3), rnd(r["lb_0.2"], 3)))
m("MkRows", "\n".join(rows))
b0 = [r for r in B if r["rho"] == 0][0]; b9 = [r for r in B if r["rho"] == 0.9][0]
m("MkLbZero", rnd(b0["lb_0.05"], 3)); m("MkLbNine", rnd(b9["lb_0.05"], 3))
m("MkRatioNine", rnd(b9["lb_0.05"] / b0["lb_0.05"], 1))
m("SecsMk", "%d" % math.ceil(D["seconds"]))
open("nums.tex", "w").write("\n".join(out) + "\n")
print("nums.tex written:", len(out), "macros")
