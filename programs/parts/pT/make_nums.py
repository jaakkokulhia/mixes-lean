"""Writes nums.tex for the trapezoid section from data/trap15.json."""
import json, math
tr = json.load(open("data/trap15.json")); P = tr["parts"]
out = []
def m(k, v): out.append("\\newcommand{\\%s}{%s}" % (k, v))
def up(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.ceil(x * f - 1e-12) / f)
def dn(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.floor(x * f + 1e-12) / f)
def sci(x, mode="up"):
    e = int(math.floor(math.log10(abs(x)))); mt = x / 10 ** e
    mt = (math.ceil(mt * 10 - 1e-9) if mode == "up" else math.floor(mt * 10 + 1e-9)) / 10
    if mt >= 10: mt /= 10; e += 1
    return "%s\\cdot10^{%d}" % (("%.1f" % mt).rstrip("0").rstrip("."), e)
def intc(k): return "{:,}".format(k).replace(",", "{,}")
m("TrapCasesA", intc(tr["partA"]["cases"])); m("TrapSlackA", "%.1f" % tr["partA"]["min_slack"])
m("TrapMC", intc(P[0]["mc"])); m("TrapRuns", len(P)); m("TrapPvals", 2 * len(P))
m("TrapSumDev", sci(max(max(p["dev_sum_x"], p["dev_sum_y"]) for p in P)))
m("TrapKSx", up(max(p["ks_x"] for p in P), 4)); m("TrapKSv", up(max(p["ks_v"] for p in P), 4))
m("TrapPmin", dn(min(min(p["p_x"], p["p_v"]) for p in P), 3))
m("TrapPminCount", sum((p["p_x"] < 0.05) + (p["p_v"] < 0.05) for p in P))
m("TrapPolySlack", sci(min(p["poly_min_slack"] for p in P), "dn"))
m("SecsTrap", int(math.ceil(tr["seconds"])))
open("nums.tex", "w").write("\n".join(out) + "\n")
