"""Writes nums.tex for the merged paper: runs the number script of each part on its stored data and renames
its macros with a suffix (Mon, Jnt, Conc; the macros of the trapezoids, of the cones, of the other bodies and of Section 20
keep their names, as do those of Sections 21 to 24)."""
import os, re, subprocess, sys
here = os.path.dirname(os.path.abspath(__file__))
PARTS = [("p11", "Mon"), ("p12", "Jnt"), ("p14", "Conc"), ("pT", ""), ("pS", ""), ("pB", ""), ("pO", ""), ("pG", ""), ("pR", ""), ("pL", ""), ("pJ", ""), ("pM", ""), ("pP", ""), ("pW", "")]
out = []
for d, suf in PARTS:
    pd = os.path.join(here, "parts", d)
    subprocess.run([sys.executable, "make_nums.py"], cwd=pd, check=True, stdout=subprocess.DEVNULL)
    txt = open(os.path.join(pd, "nums.tex")).read()
    if suf:
        for n in sorted(re.findall(r"\\newcommand\{\\([A-Za-z]+)\}", txt), key=len, reverse=True):
            txt = txt.replace("\\newcommand{\\%s}" % n, "\\newcommand{\\%s%s}" % (n, suf))
    out.append("%% ---- part %s\n" % d + txt)
open(os.path.join(here, "nums.tex"), "w").write("\n".join(out))
print("nums.tex written")
