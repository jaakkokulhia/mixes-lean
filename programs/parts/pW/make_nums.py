"""Writes nums.tex for Sections 25 to 28 from data/wang26.json and data/check_binomial.json."""
import json, math
from fractions import Fraction as Fr
D = json.load(open("data/wang26.json"))
out = []
def m(k, v): out.append("\\newcommand{\\%s}{%s}" % (k, v))
def up(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.ceil(x * f - 1e-12) / f)
def down(x, d): f = 10 ** d; return ("%." + str(d) + "f") % (math.floor(x * f + 1e-12) / f)
def rnd(x, d): return ("%." + str(d) + "f") % x
def sci(x):
    e = math.floor(math.log10(x)); c = math.ceil(x / 10 ** e - 1e-12)
    if c == 10: c, e = 1, e + 1
    return "%d\\cdot10^{%d}" % (c, e)
def big(k): return "{:,}".format(k).replace(",", "{,}")
def frac(s):
    f = Fr(s)
    return "%d" % f.numerator if f.denominator == 1 else "\\frac{%d}{%d}" % (f.numerator, f.denominator)
def dec(s):
    """a fraction with a terminating decimal expansion, written as a decimal"""
    f = Fr(s); d = 0
    while (f * 10 ** d).denominator != 1: d += 1
    return ("%." + str(d) + "f") % float(f)

A1, A2, A3, A4, B, C, C2 = D["A1"], D["A2"], D["A3"], D["A4"], D["B"], D["C"], D["C2"]
# ---- Section 25
m("AsMmax", "%d" % A1["mmax"]); m("AsTiltCases", big(A1["cases"] + A1["cases_m3"])); m("AsTiltTuples", "%d" % A1["max_tuples"])
m("AsFamilies", "%d" % A2["families"]); m("AsGrids", "%d" % A2["grids"])
assert A2["worst_ratio"] <= 1 and A2["grid_worst"] <= 1
names = {"gap": "uniform on $[0,\\frac13]\\cup[\\frac23,1]$", "atoms": "$\\frac3{10}\\,\\U[0,1]+\\frac12\\,\\delta_0+\\frac15\\,\\delta_3$",
         "density 1/2 + x": "density $\\frac12+x$ on $[0,1]$"}
rows = []
for r in A3["rows"]:
    assert r["n"] >= r["bound"] - 1e-9 and r["max_tilt"] <= 1 + 1e-9
    rows.append("%s & $%d$ & $%d$ & $%d$ & $%d$ & $%s$ & %s \\\\" % (names[r["name"]], round(r["bound"]), r["n"], r["m"], r["k"],
                sci(max(r["max_sum_error"], 1e-16)), down(r["pmin"], 2)))
m("AsSimRows", "\n".join(rows))
errs = [r["max_sum_error"] for r in A3["rows"]] + [r["max_sum_error"] for r in A3["windows"]] + \
       [r["max_sum_error"] for r in A3["completion"]] + [A3["Lshape"]["max_sum_error"]]
m("AsSumErr", sci(max(errs)))
m("AsTuples", big(A3["rows"][0]["tuples"])); m("AsTuplesSmall", big(A3["completion"][0]["tuples"]))
assert all(r["tuples"] == A3["rows"][0]["tuples"] for r in A3["rows"] + A3["windows"]) and A3["Lshape"]["tuples"] == A3["rows"][0]["tuples"]
osc = max(r["max_osc"] for r in A3["completion"])
m("AsOscExcess", sci(max(osc - 1, 1e-16)))
assert all(r["max_tilt"] <= 1 + 1e-9 for r in A3["completion"]) and A3["Lshape"]["max_tilt"] <= 1 + 1e-9
P = D["pvalues"]
m("AllPtests", "%d" % P["tests"]); m("AllPmin", down(P["pmin"], 3)); m("AllPchance", rnd(P["chance"], 2))
def sci3(x):
    e = math.floor(math.log10(x)); return "%.2f\\cdot10^{%d}" % (x / 10 ** e, e)
rows = []
for r in A4["rows"]:
    rows.append("$%d$ & $%s$ & $%s$ & $%s$ \\\\" % (r["d"], big(r["per_block"]), sci3(r["q"]), big(r["N"])))
m("AsNdRows", "\n".join(rows))
m("AsNtwo", big([r for r in A4["rows"] if r["d"] == 2][0]["N"])); m("AsNthree", big([r for r in A4["rows"] if r["d"] == 3][0]["N"]))
A5 = D["A5"]
rows = []; sums = {"constant": "constant", "two points": "two values", "uniform": "uniform"}
for r in A5["types"]:
    assert r["max_tilt"] <= 1 + 1e-9 and r["half_width"] <= r["rho"] and r["copies"] == [17, 7] and r["uniform"] == [8, 4]
    rows.append("%s & $%d$ & $%d$ & $%d+%d$ & $%s$ & $%s$ & $%s$ & $%s$ & %s \\\\" % (sums[r["name"]], sum(r["copies"]), r["others"],
                r["uniform"][0], r["uniform"][1], frac(Fr(r["rho"]).limit_denominator(1000)),
                "0" if r["name"] == "constant" else dec(Fr(r["half_width"]).limit_denominator(1000)), big(r["tuples"]),
                sci(max(r["max_sum_error"], 1e-16)), down(r["pmin"], 2)))
for r in A5["different"]:
    assert r["max_tilt"] <= 1 + 1e-9 and r["max_shift"] <= 1 + 1e-9 and r["half_width"] <= r["rho"]
    assert r["n"] == r["b"] * (r["m1"] + r["m2"]) and (r["m1"] - 1) * r["H"] >= 4 * (r["ell"] - r["H"])
    assert abs(r["m2"] * r["H"] / 2 - r["ell"] - r["H"] - r["rho"]) < 1e-12
    rows.append("%s & $%d$ & $%d$ & $%d+%d$ & $%s$ & $%s$ & $%s$ & $%s$ & %s \\\\" % ("constant" if r["half_width"] == 0 else "uniform",
                r["n"], r["others"], r["m1"], r["m2"], frac(Fr(r["rho"]).limit_denominator(1000)),
                dec(Fr(r["half_width"]).limit_denominator(1000)), big(r["tuples"]), sci(max(r["max_sum_error"], 1e-16)),
                down(r["pmin"], 3 if r["pmin"] < 0.01 else 2)))
assert A5["different"][0]["max_rest_dev"] <= 1 + 1e-9 and A5["different"][0]["grid"] == 60
m("AsHetRows", "\n".join(rows))
Se = A5["selection"]
assert Se["worst_ratio"] <= 1
m("AsSelConf", "%d" % Se["configurations"]); m("AsSelChoices", big(Se["selections"])); m("AsSelSamples", big(Se["samples"]))
m("AsHetSumErr", sci(max(r["max_sum_error"] for r in A5["types"] + A5["different"])))
m("AsHetShift", up(max(r["max_shift"] for r in A5["different"]) / 2, 2))
m("AsHetTilt", up(max(r["max_tilt"] for r in A5["different"]), 2))
A6 = D["A6"]; Pc = A6["pairs"]
assert Pc["max_tuples"] <= 3
m("AsPairCases", big(Pc["cases"])); m("AsPairBoundary", "%d" % Pc["boundary"])
names3 = {"steps": "density with three steps", "atom": "$\\frac{17}{25}\\,\\delta_{47/100}+\\frac8{25}\\,\\U[0,1]$",
          "gap": names["gap"], "atoms": names["atoms"]}
rows = []
for r in A6["rows"]:
    assert (r["m"] >= 4 and r["m"] * r["H"] >= r["R"] - 1e-12) or (r["m"] == 3 and abs(2 * r["H"] - r["R"]) < 1e-12)
    assert r["n"] < r["bound_window"] and r["max_dev"] > 1e-3
    rows.append("%s & $%d$ & $%d$ & $%d$ & $%d$ & $%s$ & %s \\\\" % (names3[r["name"]], math.ceil(r["bound_window"] - 1e-9), r["n"],
                r["m"], r["k"], sci(max(r["max_sum_error"], 1e-16)), down(r["pmin"], 2)))
m("AsThreeRows", "\n".join(rows))
assert [w["name"] for w in A6["windows"]] == ["m = 3, two points", "m = 3, beta", "m = 4, two points, centred", "m = 4, two points", "m = 8, beta"]
assert A6["completion"]["laws"] == 5 and A6["completion"]["uniforms"] == 3
m("AsThreeSumErr", sci(max([r["max_sum_error"] for r in A6["rows"] + A6["windows"]] + [A6["completion"]["max_sum_error"]])))
m("AsThreeTuples", big(A6["rows"][0]["tuples"])); m("AsThreeTuplesWin", big(A6["windows"][0]["tuples"]))
m("AsThreeTuplesComp", big(A6["completion"]["tuples"]))
# ---- Section 26
m("PjMuE", up(max(r["mu_on_E"] for r in B["rows"]), 3)); m("PjFibres", big(B["fibres"])); m("PjRatio", down(B["min_fibre_ratio"], 3))
assert B["Q_min"] >= 0 and all(abs(r["Q_on_shift"] - 0.1) < 1e-15 for r in B["rows"])
m("PjMassErr", sci(abs(B["Q_mass_over_pi"] - 1)))
assert [r["n"] for r in B["clusters"]] == [3, 4, 5, 6, 7]
# ---- Section 27
r0 = C["rows"][0]
assert r0["n"] == 3
m("NcExP", frac(r0["p"])); m("NcExC", frac(r0["c"])); m("NcExEta", frac(r0["eta"]))
m("NcExDmin", dec(Fr(r0["density_min"]).limit_denominator(10 ** 6))); m("NcExDmax", dec(Fr(r0["density_max"]).limit_denominator(10 ** 6)))
rows = []
for r in C["rows"]:
    assert r["cx_min"] == 0 and r["cx_min_mixture"] == 0 and r["cx_min_convolution"] == 0 and r["Eh_proof"] < 0
    assert r["n_mu"] >= r["sqrt"]
    assert abs(r["miss_lower"] + r["Eh_proof"]) < 1e-15 and 0 < r["miss_lower"] <= r["miss_lower_uniform"]
    rows.append("$%d$ & $%s$ & $%s$ & $%s$ & $%s$ & $%s$ & $%s$ & $%d$ & $%s$ \\\\" % (r["n"], frac(r["p"]), frac(r["c"]), frac(r["eta"]),
                dec(Fr(r["n_mu"]).limit_denominator(10 ** 6)), up(r["sqrt"], 4), down(r["miss_lower"], 4), r["n_sufficient"],
                dec(Fr(r["density_max"]).limit_denominator(10 ** 6))))
m("NcRows", "\n".join(rows))
m("NcControl", "$%s$" % up(C["control_min"], 4))
lp = {(r["N"], r["p"]): r["dist"] for r in C["lps"]}
for N in (300, 600):
    assert lp[(N, "3/10")] < 1e-9 and lp[(N, "1/3")] < 1e-9
m("NcLpA", down(min(lp[(300, "2/5")], lp[(600, "2/5")]), 3)); m("NcLpB", down(min(lp[(300, "1/2")], lp[(600, "1/2")]), 3))
m("NcLpF", down(min(r["dist"] for r in C["lps_f1"]), 3))
assert len(C["sims"]) == 8
def lst(v): return ", ".join("$%s$" % x for x in v[:-1]) + " and $%s$" % v[-1]
Le = C["least"]
assert [r["p"] for r in Le] == ["2/5", "11/20", "7/10", "17/20"] and all(r["c"] == "47/100" for r in Le)
assert all(r["sim"]["n"] == r["n_least"] and r["miss_before"] > 0 for r in Le)
m("NcCxMax", "40"); m("NcLeastList", lst([r["n_least"] for r in Le])); m("NcLeastCor", lst([r["n_corollary"] for r in Le]))
m("NcLeastMiss", lst([down(r["miss_before"], 3) for r in Le]))
Al = C["alln"]
assert Al["n0"] == 6 and Al["p"] == "7/10" and Al["c"] == "23/50" and Al["eta"] == "1/100" and Al["cx_checked_to"] == 40
assert len(Al["miss_bounds"]) == 4 and min(Al["miss_bounds"]) > 0 and Al["sim"]["n"] == Al["n_sufficient"]
assert Al["sim"]["m"] == 3 and Al["sim_next"]["m"] == 3 and Al["sim_next"]["n"] == Al["n_sufficient"] + 1
m("NcAllnMiss", lst([down(v, 3) for v in Al["miss_bounds"]])); m("NcAllnN", "%d" % Al["n_sufficient"])
m("NcSumErr", sci(max([r["max_sum_error"] for r in C["sims"]] + [r["sim"]["max_sum_error"] for r in Le] + [Al["sim"]["max_sum_error"], Al["sim_next"]["max_sum_error"]])))
m("NcCubics", "%d" % C2["densities"]); m("NcCubicsBad", "%d" % C2["beta_over_3"]); m("NcCubicsOk", "%d" % C2["at_3"])
assert C2["below_3"] == 0 and C2["at_3"] + C2["beta_over_3"] == C2["densities"]
m("NcBetaNoise", sci(C2["noise"])); m("NcBetaMinExcess", down(C2["min_excess"], 3))
m("NcBetaMax", up(C2["beta_max"], 2)); m("NcTilt", up(C2["tilt_max"], 3))
assert C2["lp_max_dist"] < 1e-9 and C2["lp_cases"] == 2 * C2["beta_over_3"]
# ---- Section 28
Bi = D["D_binomial"]
assert Bi["agree"] == Bi["cases"]
m("LtNmaxBin", "%d" % Bi["Nmax"]); m("LtNmaxBox", "%d" % Bi["nmax"]); m("LtCases", big(Bi["cases"])); m("LtMixable", big(Bi["mixable"]))
m("LtNonInt", big(Bi["mixable_np_not_integer"])); m("LtMaxVec", "%d" % Bi["max_vectors"])
Ck = json.load(open("data/check_binomial.json"))                      # written by check_binomial.py
assert Ck["mixes"] == Bi["mixable"] and Ck["Nmax"] == Bi["Nmax"] and Ck["nmax"] == Bi["nmax"]
assert Ck["max_vectors"] == Bi["max_vectors"] and Ck["np_not_integer"] == Bi["mixable_np_not_integer"]
m("LtPairs", big(Ck["pairs"]))
assert D["D_three"]["agree"] == D["D_three"]["cases"]
m("LtThree", big(D["D_three"]["cases"]))
assert D["D_three_general"]["agree"] == D["D_three_general"]["cases"] and D["D_three_general"]["xmax"] == 8
m("LtThreeGen", big(D["D_three_general"]["cases"]))
Ne = D["D_necessary"]; ex = Ne["examples"]
assert not ex["A"]["mixable"] and ex["A"]["convex_order"] and ex["A"]["peak"] == [1]
assert not ex["B"]["mixable"] and ex["B"]["convex_order"] and ex["B"]["peak"] is None and ex["B"]["tail"] is False
assert ex["B"]["counting"] == [True, 0, 0, 2]
assert not ex["C"]["mixable"] and ex["C"]["convex_order"] and ex["C"]["peak"] is None and ex["C"]["counting"] is None
assert ex["C"]["tail"] is False and not ex["E"]["mixable"] and ex["E"]["peak"] is None
S4, S5 = Ne["search"]
assert S4["points"] == 4 and S4["denominators"] == [12, 15, 18] and S4["n"] == [3, 4, 5, 6] and S4["without_peak_violation"] == 0
assert S5["points"] == 5 and S5["denominators"] == [10, 12] and S5["n"] == [3, 4, 5] and S5["without_peak_violation"] == 0
m("LtNecFourAdm", big(S4["admissible"])); m("LtNecFourNon", big(S4["not_mixable"])); m("LtNecFourCx", big(S4["convex_order_fails"]))
m("LtNecFiveAdm", big(S5["admissible"])); m("LtNecFiveNon", big(S5["not_mixable"])); m("LtNecFiveCx", big(S5["convex_order_fails"]))
assert Ne["mixable_checked"] == S4["admissible"] - S4["not_mixable"] + S5["admissible"] - S5["not_mixable"]
m("LtNecSane", big(Ne["mixable_checked"]))
L = D["D_large"]
assert L["mixable"] == [n for n in range(2, 41) if n % 2 == 0 or n >= 25]
F4 = D["D_four"]
assert F4["mixable"] == F4["admissible"] == list(range(10, 101, 10))
m("LtFourBound", "%d" % F4["bound"])
m("LtAlloc", "%d" % D["D_alloc"]["cases"]); m("LtOps", "%d" % D["D_ops"]["cases"])
assert D["D_logconcave"]["mixable"] is False
m("SecsW", "%d" % math.ceil(D["seconds"]))
open("nums.tex", "w").write("\n".join(out) + "\n")
print("nums.tex written:", len(out), "macros")
