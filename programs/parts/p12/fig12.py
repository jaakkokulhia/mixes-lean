#!/usr/bin/env python3
"""Writes figcases.tex: TikZ drawings of the joint mix of Proposition 1 in its four cases, computed by jm12.base."""
import os
from fractions import Fraction as Fr
from jm12 import base

here = os.path.dirname(os.path.abspath(__file__))
F = lambda v: Fr(v).limit_denominator(1000)
# example parameters (s = 1): c1, c2, a, b, 2mu
EX = [('I', F('0.75'), F('0.65'), F('0.45'), F('0.9'), F('0.6')),
      ('II', F('0.85'), F('0.55'), F('0.3'), F('0.9'), F('0.6')),
      ('IIIa', F('0.75'), F('0.65'), F('0.1'), F('0.9'), F('0.6')),
      ('IIIb', F('0.85'), F('0.75'), F('0.05'), F('0.6'), F('0.4'))]

def names(c1, c2, a, b, x):
    s = (c1 + c2 + x) / 2; y1, y2 = s - c1, s - c2
    pts = {r'A(a)': (0, s - a, a), r'A(b)': (0, s - b, b), r"A'(b)": (s - b, 0, b), r'B': (y2, c2, 0),
           r'C': (c1, 0, y1), r'D(a)': (y2 - a, c2, a), r"D'(a)": (c1, y1 - a, a), r'E': (0, c2, y2)}
    return {tuple(Fr(v) for v in P): k for k, P in pts.items()}

def f(v): return f'{float(v):.4f}'

out = []
macros = []
for idx, (case, c1, c2, a, b, x) in enumerate(EX):
    got, segs = base(c1, c2, a, b, x)
    assert got == case, (got, case)
    s = (c1 + c2 + x) / 2
    nm = names(c1, c2, a, b, x)
    # region of the plane inside [0,c1]x[0,c2]x[0,b], in coordinates (x1, x2): polygon by clipping
    poly = [(Fr(0), Fr(0)), (c1, Fr(0)), (c1, c2), (Fr(0), c2)]
    def clip(poly, keep, inter):
        res = []
        for i in range(len(poly)):
            P, Q = poly[i], poly[(i + 1) % len(poly)]
            if keep(P): res.append(P)
            if keep(P) != keep(Q): res.append(inter(P, Q))
        return res
    def line_inter(P, Q, t):     # point on PQ with x1 + x2 = t
        lam = (t - P[0] - P[1]) / ((Q[0] - P[0]) + (Q[1] - P[1]))
        return (P[0] + lam * (Q[0] - P[0]), P[1] + lam * (Q[1] - P[1]))
    poly = clip(poly, lambda P: P[0] + P[1] <= s, lambda P, Q: line_inter(P, Q, s))
    poly = clip(poly, lambda P: P[0] + P[1] >= s - b, lambda P, Q: line_inter(P, Q, s - b))
    lines = [r'\begin{tikzpicture}[x=44mm,y=44mm,font=\footnotesize]']
    lines.append(r'\fill[hair!70] ' + ' -- '.join(f'({f(P[0])},{f(P[1])})' for P in poly) + ' -- cycle;')
    lines.append(rf'\draw[ink2,line width=0.3pt] (0,0) rectangle ({f(c1)},{f(c2)});')
    lines.append(rf'\draw[ink2,->,line width=0.3pt] (0,0) -- ({f(c1 + Fr(1, 8))},0) node[below=1pt] {{$x_1$}};')
    lines.append(rf'\draw[ink2,->,line width=0.3pt] (0,0) -- (0,{f(c2 + Fr(1, 8))}) node[left=1pt] {{$x_2$}};')
    used = set()
    for P, Q, w in segs:
        lw = 0.35 + 3.2 * float(w)
        lines.append(rf'\draw[accent,line width={lw:.2f}pt,line cap=round] ({f(P[0])},{f(P[1])}) -- ({f(Q[0])},{f(Q[1])});')
        used.add(P); used.add(Q)
    for P in sorted(used):
        label = nm[tuple(Fr(v) for v in P)]
        if P[0] == 0: anchor = 'left'
        elif P[1] == 0: anchor = 'below'
        elif P[0] == c1: anchor = 'right'
        else: anchor = 'above'
        lines.append(rf'\fill[ink] ({f(P[0])},{f(P[1])}) circle (0.6pt) node[{anchor}=1pt,ink] {{${label}$}};')
    lines.append(r'\end{tikzpicture}')
    out.append('\n'.join(lines))
    tag = 'ABCD'[idx]
    macros.append(rf'\newcommand{{\FigPar{tag}}}{{$c_1={float(c1):g}$, $c_2={float(c2):g}$, $a={float(a):g}$, $b={float(b):g}$, $\mu={float(x/2):g}$}}')
    macros.append(rf'\newcommand{{\FigSeg{tag}}}{{{len(segs)}}}')
with open(os.path.join(here, 'figcases.tex'), 'w') as fh:
    fh.write('% written by fig12.py\n' + '\n'.join(macros) + '\n')
    fh.write(r'\newcommand{\FigCases}{%' + '\n')
    panels = [r'\begin{minipage}[b]{0.48\textwidth}\centering' + '\n' + t + '\n' + r'\par\smallskip(' + c[0] + r')\end{minipage}'
              for t, c in zip(out, EX)]
    fh.write(panels[0] + '\\hfill\n' + panels[1] + '\n\n\\bigskip\n' + panels[2] + '\\hfill\n' + panels[3])
    fh.write('\n}\n')
print(open(os.path.join(here, 'figcases.tex')).read()[:1500])
