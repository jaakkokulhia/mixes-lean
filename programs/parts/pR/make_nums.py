"""Writes nums.tex for the regular polygons of Section 21 from data/regular21.json.  Upper bounds and left sides of
the condition are rounded up, lower bounds and right sides down."""
import json, math
D = json.load(open("data/regular21.json"))
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

assert abs(A["c3"] - A["c3_quad"]) < 1e-12
assert A["c4_lo"] <= A["c4_quad"] <= A["c4_hi"] and A["a4_1"][0] <= A["a4_1_quad"] <= A["a4_1"][1]
assert A["a5_1"][0] <= A["a5_1_quad"] <= A["a5_1"][1]
assert A["rows"]["9"]["a4R"][0] <= A["quad_a4R9"] <= A["rows"]["9"]["a4R"][1]
assert A["rows"]["9"]["a5R"][0] <= A["quad_a5R9"] <= A["rows"]["9"]["a5R"][1]
assert all(A["k0_ok"].values())
m("RegCthree", dn(A["c3"], 4)); m("RegLensOne", dn(A["lens1"], 4))
m("RegCfourHi", up(A["c4_hi"], 3)); m("RegAfourOne", dn(A["a4_1"][0], 3)); m("RegAfiveOne", dn(A["a5_1"][0], 3))
r9 = A["rows"]["9"]
m("RegAfourRnine", dn(r9["a4R"][0], 3)); m("RegAfiveRnine", dn(r9["a5R"][0], 3))
r8 = A["rows"]["8"]
m("RegAfourReight", dn(r8["a4R"][0], 3))
assert r8["n3"]["ok_zeta"] and r9["n4"]["ok_zeta"] and r9["n5"]["ok_zeta"] and r8["n4"]["ok"]
m("RegThreeL", up(r8["n3"]["lhs_zeta"], 4)); m("RegThreeR", dn(r8["n3"]["rhs"], 4))
m("RegFourL", up(r9["n4"]["lhs_zeta"], 4)); m("RegFourR", dn(r9["n4"]["rhs"], 4)); m("RegFourEightR", dn(r8["n4"]["rhs"], 4))
m("RegFiveL", up(r9["n5"]["lhs_zeta"], 4)); m("RegFiveR", dn(r9["n5"]["rhs"], 4))
# failures used in the remark
r7, r5 = A["rows"]["7"], A["rows"]["5"]
m("RegSevenFourL", up(r7["n4"]["lhs"], 3)); m("RegSevenFourR", dn(r7["n4"]["rhs"], 3))
m("RegSevenFiveL", up(r7["n5"]["lhs"], 3)); m("RegSevenFiveR", dn(r7["n5"]["rhs"], 3))
m("RegFiveThreeL", up(r5["n3"]["lhs"], 3)); m("RegFiveThreeR", dn(r5["n3"]["rhs"], 3))
# the heptagon, n = 3
H = A["heptagon"]; assert H["ok"]
m("HeptCapGrid", dn(H["cap_grid"], 4)); m("HeptCap", up(H["cap_bound"], 4)); m("HeptCorners", dn(H["corners"], 4))
m("HeptN", up(H["N"], 4)); m("HeptNcrude", dn(H["N_crude"], 4)); m("HeptL", up(H["lhs"], 4)); m("HeptR", dn(H["rhs"], 4))
m("HeptRatio", dn(A["heptagon_ratio"], 2)); m("HeptNmin", int(math.ceil(A["heptagon_ratio"])))
# the table of the condition
lines = []
for k in range(5, 17):
    r = A["rows"][str(k)]; cells = []
    for n in (3, 4, 5):
        x = r["n%d" % n]
        if x["W"] < 1e-5:
            cells.append("\\multicolumn{2}{c}{%s}" % ("trivial" if x["rhs"] >= 0 else "fails"))
        else:
            cells.append("%s & %s%s" % (up(x["lhs"], 4), dn(x["rhs"], 4).replace("-", "$-$"), "" if x["ok"] else "$^*$"))
    lines.append("%d & %s \\\\" % (k, " & ".join(cells)))
m("RegRows", "\n".join(lines))
# the construction for n = 3
for k, name in (("8", "Eight"), ("20", "Twenty")):
    b = B[k]
    m("Reg%sPhi" % name, sci(b["phi_sup_numeric"])); m("Reg%sPhiBound" % name, sci(b["bound_phi"]))
    m("Reg%sT" % name, dn(b["t_numeric"], 4)); m("Reg%sTBound" % name, dn(b["bound_t"], 4))
    m("Reg%sNu" % name, up(b["nu_sup_numeric"], 4)); m("Reg%sNuBound" % name, up(b["bound_N"], 4))
    m("Reg%sModes" % name, b["modes"])
    assert abs(b["nu_mass"] - b["nu_mass_exact"]) < 1e-6
# the simulation
assert C["inside"] and C["max_sum"] < 1e-12
m("RegSimN", intc(C["N"])); m("RegSimSum", sci(C["max_sum"])); m("RegSimTests", C["tests"]); m("RegSimP", dn(C["min_p"], 3))
m("RegSimChance", up(1 - (1 - C["min_p"]) ** C["tests"], 2))
m("SecsReg", "%d" % math.ceil(D["seconds"]))
open("nums.tex", "w").write("\n".join(out) + "\n")
print("nums.tex written:", len(out), "macros")
