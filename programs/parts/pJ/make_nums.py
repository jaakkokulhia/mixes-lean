"""Writes nums.tex for Section 23 from data/joint23.json."""
import json, math
D = json.load(open("data/joint23.json"))
out = []
def m(k, v): out.append("\\newcommand{\\%s}{%s}" % (k, v))
def up(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.ceil(x * f - 1e-12) / f)
def dn(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.floor(x * f + 1e-12) / f)
def rnd(x, d): return ("%." + str(d) + "f") % x

COMP = {
    ("A", "3"): r"$D,\ D_+,\ D_-$", ("A", "4"): r"$2D_+,\ 2D_-$", ("A", "6"): r"$2D,\ 2D_+,\ 2D_-$",
    ("A", "8"): r"$2D,\ 3D_+,\ 3D_-$",
    ("B", "4"): r"$4g_B$", ("B", "5"): r"$5g_B$", ("B", "8"): r"$8g_B$",
    ("C", "3"): r"$1,\ 0.8\,e^{25^\circ i},\ 0.6\,e^{50^\circ i}$",
    ("C", "4"): r"$1,\ 0.9\,e^{20^\circ i},\ 0.7\,e^{40^\circ i},\ 0.5\,e^{70^\circ i}$",
    ("C", "6"): r"$1,\ 0.95\,e^{15^\circ i},\ \dots,\ 0.55\,e^{75^\circ i}$",
    ("D", "3"): r"$T,\ S,\ P$", ("D", "4"): r"$T,\ S,\ P,\ D'$", ("D", "5"): r"$2T,\ S,\ P,\ D'$",
}
rows = []
errmax = changemax = ratemax = balmax = 0.0
for fam in ("A", "B", "C", "D"):
    for n, r in D[fam].items():
        a, b = r["coarse"], r["fine"]
        assert a["ok"] and b["ok"], (fam, n)
        errmax = max(errmax, a["err"], b["err"]); changemax = max(changemax, r["change"])
        ratemax = max(ratemax, b["rate"]); balmax = max(balmax, a["balance_tilt"], b["balance_tilt"])
        steps = "$\\frac1{%d},\\frac1{%d}$" % (round(1 / a["step"]), round(1 / b["step"]))
        rows.append("%s & $%s$ & %s & %s & %d & %s & %s & %s \\\\" % (
            fam, n, COMP[(fam, n)], steps, b["sweeps"], rnd(b["range"], 2), rnd(b["lip"], 1), up(r["change"], 3)))
m("JlRows", "\n".join(rows))
m("JlErrMax", "10^{%d}" % math.ceil(math.log10(errmax)))
m("JlChangeMax", up(changemax, 3))
m("JlRateMax", up(ratemax, 2))
e = math.floor(math.log10(balmax))
m("JlBalMax", "%d\\cdot10^{%d}" % (math.ceil(balmax / 10 ** e - 1e-12), e))
E = D["E"]
assert all(E[k]["ok"] for k in E)
m("JlNR", ", ".join(rnd(E[k]["n_range"], 2) for k in ("4", "5", "8", "16")))
m("JlNRlo", dn(min(E[k]["n_range"] for k in E), 1)); m("JlNRhi", up(max(E[k]["n_range"] for k in E), 1))
F = D["F"]
assert all(x["ok"] for x in F)
assert all(F[i + 1]["range"] > F[i]["range"] and F[i + 1]["lip"] > F[i]["lip"] for i in range(len(F) - 1))
m("JlBdRanges", ", ".join(rnd(x["range"], 2) for x in F))
m("JlBdLips", ", ".join("%d" % round(x["lip"]) for x in F))
m("JlBdDens", ", ".join("\\frac1{%d}" % x["den"] for x in F))
m("SecsJl", "%d" % math.ceil(D["seconds"]))
open("nums.tex", "w").write("\n".join(out) + "\n")
print("nums.tex written:", len(out), "macros")
