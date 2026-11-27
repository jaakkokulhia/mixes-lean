"""Writes nums.tex, the numbers quoted in the note, from data/concave14.json."""
import json, math

d = json.load(open("data/concave14.json"))
M = {}


def up(x, k):
    """round up to k significant digits, as a LaTeX number."""
    if x <= 0:
        return "0"
    e = math.floor(math.log10(x))
    m = math.ceil(x / 10 ** (e - k + 1) - 1e-9) * 10 ** (e - k + 1)
    e2 = math.floor(math.log10(m))
    mant = m / 10 ** e2
    s = ("%." + str(k - 1) + "f") % mant
    return r"$%s\cdot10^{%d}$" % (s, e2)


def pv(p):
    return ("%.3f" % p) if p < 0.01 else ("%.2f" % p)


def fx(x, k):
    return ("%." + str(k) + "f") % x


p1 = d["part1"]
M["NMaxOne"] = str(p1["nmax"]); M["GridOne"] = str(p1["grid"]); M["NCasesOne"] = str(p1["cases"])
M["NBoundary"] = str(p1["boundary"]); M["NCaseB"] = str(p1["caseB"]); M["NCaseD"] = str(p1["caseD"])
M["MaxParts"] = str(p1["maxparts"])

p2 = d["part2"]
names = {"triangle": "triangle $T$", "twoswitch": "polygon $Q$", "linear": r"$2(1-x)$",
         "trapezoid": "trapezoid $Z$", "semicircle": r"$\sqrt{x(1-x)}$", "parabola": r"$1-((x-0.25)/0.8)^2$",
         "power": r"$x^{0.3}(1-x)^{0.6}$", "sqrt": r"$\sqrt x$"}
rows = []
dec_max = 0.0; ode_max = 0.0; mass_err = 0.0; mono_max = -1.0; bal_max = 0.0
for key in ["triangle", "twoswitch", "linear", "trapezoid", "semicircle", "parabola", "power", "sqrt"]:
    r = p2[key]
    dec_max = max(dec_max, r["decomp"]); ode_max = max(ode_max, r["ode"])
    mass_err = max(mass_err, abs(r["mass"] - 1)); mono_max = max(mono_max, r["mono"]); bal_max = max(bal_max, r["balance"])
    rows.append("%s & %s & %d & %s & %s & %s & %s \\\\" % (
        names[key], fx(r["mu"], 4), len(r["switches"]), fx(r["beta_max"], 4),
        up(r["decomp"], 2), up(r["ode"], 2), up(r["ode_half"], 2)))
M["PeelRows"] = "\n".join(rows)
M["DecompMax"] = up(dec_max, 2); M["OdeMax"] = up(ode_max, 2); M["BalMax"] = up(bal_max, 2)
M["MonoOK"] = "yes" if mono_max <= 0 else "no"
tw = p2["twoswitch"]
M["SwOne"] = fx(tw["switches"][0], 4); M["SwTwo"] = fx(tw["switches"][1], 4)
M["MuTwo"] = fx(tw["mu"], 4); M["FmuTwo"] = fx(tw["fmu"], 4)
M["NSemicircleBad"] = str(p2["semicircle"]["bad"])
M["SemicircleBalance"] = up(p2["semicircle"]["balance"], 1)
M["TrapBetaMax"] = fx(p2["trapezoid"]["beta_max"], 4)
rnd = p2["random"]
M["NRand"] = str(rnd["n"])
sw = rnd["switches"]
M["RandSw"] = ", ".join("%s with %s" % (v, k) for k, v in sorted(sw.items(), key=lambda t: int(t[0])))
M["RandSwZero"] = str(sw.get("0", 0)); M["RandSwOne"] = str(sw.get("1", 0))
M["RandSwTwo"] = str(sw.get("2", 0)); M["RandSwThree"] = str(sw.get("3", 0))
M["RandMaxSw"] = str(max(int(k) for k in sw))
M["RandBetaExcess"] = up(max(rnd["beta_max"] - 3.0, 1e-300), 1)
M["RandOde"] = up(rnd["ode"], 2); M["RandDecomp"] = up(rnd["decomp"], 2); M["NRandDecomp"] = str(rnd["ndecomp"])
M["RandBad"] = str(rnd["bad"]); M["RandMonoOK"] = "yes" if rnd["mono"] <= 0 else "no"
M["NLev"] = str(d["settings"]["NLEV"]); M["NLevHalf"] = str(d["settings"]["NLEV"] // 2)

p3 = d["part3"]
M["NMC"] = "{:,}".format(p3["mc"]).replace(",", "\\,"); M["MCCrit"] = fx(p3["crit"], 4)
M["NMCFollow"] = "{:,}".format(4 * p3["mc"]).replace(",", "\\,")
dn = {"triangle": "triangle $T$", "twoswitch": "polygon $Q$", "linear": "$2(1-x)$",
      "semicircle": "$\\sqrt{x(1-x)}$", "power": "$x^{0.3}(1-x)^{0.6}$"}
by = {}
sumerr = 0.0
for r in p3["rows"]:
    by.setdefault(r["density"], {})[r["n"]] = r
    sumerr = max(sumerr, r["sumerr"])
    assert r["inrange"]
rows = []
for key in ["triangle", "twoswitch", "linear", "semicircle", "power"]:
    cells = ["%s (%s)" % (fx(by[key][n]["ks"], 4), pv(by[key][n]["p"])) for n in [3, 4, 5, 8]]
    rows.append("%s & %s \\\\" % (dn[key], " & ".join(cells)))
M["MCRows"] = "\n".join(rows)
M["MCSumErr"] = up(sumerr, 1)
ps = sorted(r["p"] for r in p3["rows"])
M["MCMinP"] = fx(ps[0], 4); M["MCSecondP"] = fx(ps[1], 3); M["MCMaxP"] = fx(ps[-1], 2)
M["NMCTests"] = str(len(p3["rows"]))
M["MCMinPChance"] = fx(1 - (1 - ps[0]) ** len(p3["rows"]), 3)
f = p3["follow"]
M["FollowDensity"] = dn[f["density"]]; M["FollowN"] = str(f["n"])
fp = sorted(x["p"] for x in f["runs"])
M["FollowMinP"] = fx(fp[0], 2); M["FollowMaxP"] = fx(fp[-1], 2)

p4 = d["part4"]
lab = {}
for r in p4["rows"]:
    k = r["key"]
    if k.startswith("beta"):
        a, b = k[5:-1].split(",")
        lab[k] = r"Beta$(%s,%s)$" % (a, b)
    elif k.startswith("lognormal"):
        lab[k] = r"lognormal, $[0.2,%s]$" % k.split(",")[1].rstrip("]")
    else:
        lab[k] = r"normal$(1.48,0.722^2)$, $[0,1]$"
rows = []
for r in p4["rows"]:
    rows.append("%s & %s & %s & %s & %s & %d & %d \\\\" % (lab[r["key"]], fx(r["mu"], 4), fx(r["beta0"], 4),
                fx(r["betastar"], 4), fx(r["at"], 3), r["n_mean"], r["n_peel"]))
M["UniRows"] = "\n".join(rows)
br = p4["beta_random"]
M["NBeta"] = str(br["n"]); M["BetaMaxExcess"] = up(br["max_excess"], 2); M["BetaSameN"] = str(br["same_n"])
M["BetaWorstA"] = fx(br["worst_a"], 3); M["BetaWorstB"] = fx(br["worst_b"], 3)
M["BetaStartExcess"] = up(br["start_excess"], 2); M["BetaStartExcessFine"] = up(br["start_excess_fine"], 2)
M["NUniTotal"] = str(len(p4["rows"]) + br["n"])
nbt = sum(1 for r in p4["rows"] if r["key"].startswith("beta"))
words = {7: "seven", 8: "eight", 6: "six", 5: "five"}
M["NBetaTable"] = words.get(nbt, str(nbt)); M["NBetaTotal"] = str(nbt + br["n"])
M["NPeelDens"] = words.get(len([k for k in p2 if k not in ("random", "seconds")]), "?")
M["RunSeconds"] = str(int(math.ceil(d["seconds"])))

with open("nums.tex", "w") as fh:
    for k, v in M.items():
        fh.write("\\newcommand{\\%s}{%s}\n" % (k, v))
print(open("nums.tex").read())
