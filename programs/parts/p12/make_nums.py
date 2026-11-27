#!/usr/bin/env python3
"""Writes nums.tex, the numbers quoted in the note, from data/jm12.json."""
import json, os, re
here = os.path.dirname(os.path.abspath(__file__))
r = json.load(open(os.path.join(here, 'data', 'jm12.json')))
m = {}
def num(n): return f'{n:,}'.replace(',', '{,}')
def sci(x):
    mant, ex = f'{x:.1e}'.split('e')
    return f'{mant}\\times10^{{{int(ex)}}}'
p1, p2, p3, p4 = r['part1'], r['part2'], r['part3'], r['part4']
m['GridOne'] = str(r['env']['GRID']); m['NPointsOne'] = num(p1['points']); m['NChecksOne'] = num(p1['checks'])
m['NCellsOne'] = num(p1['cells']); m['MaxSegOne'] = str(p1['max_segments'])
cc = p1['cases']
for key, name in (('I', 'NCaseI'), ('II', 'NCaseII'), ('II0', 'NCaseIIz'), ('IIIa', 'NCaseIIIa'), ('IIIb', 'NCaseIIIb')):
    m[name] = num(cc.get(key, 0) + cc.get(key + "'", 0))
bd = p1['boundary']
for key, name in (('y1=0', 'NBdyYz'), ('a=0', 'NBdyAz'), ('a=y1', 'NBdyAyOne'), ('a=y2', 'NBdyAyTwo'),
                  ('b=s', 'NBdyBs'), ('b=c2', 'NBdyBc'), ('c1=c2', 'NBdyCc')):
    m[name] = num(bd.get(key, 0))
m['NRand'] = num(r['env']['NRAND']); m['NIdent'] = num(p2['identities']); m['NUni'] = num(p2['uniform_tuples'])
m['NUniTight'] = num(p2['uniform_tight']); m['NSplit'] = num(p2['split'])
m['NSplitAz'] = num(p2['split_a0']); m['NSplitBs'] = num(p2['split_bs'])
m['NSplitNoPart'] = num(sum(v for k, v in p2['split_kinds'].items() if 'part' not in k))
m['NLeaves'] = num(p2['leaves']); m['NLeafBase'] = num(p2['leaf_kinds'].get('base', 0))
m['NLeafSplit'] = num(p2['leaf_kinds'].get('split', 0)); m['NLeafAz'] = num(p2['leaf_a0']); m['NLeafZero'] = num(p2['leaf_zero']); m['NLeafBs'] = num(p2['leaf_bs'])
m['MaxSegLeaf'] = str(p2['max_segments_leaf'])
m['UniKLo'], m['UniKHi'] = map(str, p2['uni_k']); m['LeafNLo'], m['LeafNHi'] = map(str, p2['leaf_n'])
m['NLaws'] = num(p3['laws']); m['NLawsTight'] = num(p3['tight']); m['NLawsZero'] = num(p3['with_zero_atom'])
m['NTuples'] = num(p3['tuples']); m['NSegments'] = num(p3['segments']); m['NMaxSegments'] = num(p3['max_segments'])
m['NMaxN'] = str(p3['n_max'])
lk = p3['leaf_kinds']
m['NLeafKindU'] = num(lk.get('U', 0)); m['NLeafKindB'] = num(lk.get('base', 0)); m['NLeafKindS'] = num(lk.get('split', 0))
m['NBlotto'] = num(p3['blotto']); m['NBlottoSegments'] = num(p3['blotto_segments']); m['NBlottoMaxN'] = str(p3['blotto_n_max'])
bk = p3['blotto_leaf_kinds']
m['NBlottoU'] = num(bk.get('U', 0)); m['NBlottoB'] = num(bk.get('base', 0)); m['NBlottoS'] = num(bk.get('split', 0))
m['MaxLeafSeg'] = str(p3['max_leaf_segments'])
m['StepNLo'], m['StepNHi'] = map(str, p3['step_n']); m['StepKMax'] = str(p3['step_kmax'])
m['BlottoNLo'], m['BlottoNHi'] = map(str, p3['blotto_n'])
tests = p4['tests']
m['NMC'] = num(tests[0]['samples']); m['NMCTests'] = str(len(tests)); m['NMCCoords'] = str(sum(t['n'] for t in tests))
m['MCThreshold'] = f"{tests[0]['ks_threshold']:.4f}"
m['MCMaxSumErr'] = sci(max(t['max_sum_error'] for t in tests))
m['MCMinP'] = f"{min(t['p_min'] for t in tests):.3f}"; m['MCMaxKS'] = f"{max(t['ks_max'] for t in tests):.4f}"
m['RunSeconds'] = str(int(round(r['seconds'])))

def law_tex(name):
    g = lambda s: s
    mo = re.match(r'uniform on \[0,([\d.]+)\]', name)
    if mo: return f'$\\U[0,{mo.group(1)}]$'
    mo = re.match(r'power ([\d.]+) on \[0,([\d.]+)\]', name)
    if mo:
        e = '' if float(mo.group(1)) == 1 else f'^{{{mo.group(1)}}}'
        base = f'1-x/{mo.group(2)}' if e == '' else f'(1-x/{mo.group(2)})'
        return f'${base}{e}$ on $[0,{mo.group(2)}]$'
    mo = re.match(r'exponential ([\d.]+) on \[0,([\d.]+)\]', name)
    if mo:
        r = '' if float(mo.group(1)) == 1 else mo.group(1)
        return f'$e^{{-{r}x}}$ on $[0,{mo.group(2)}]$'
    mo = re.match(r'inverse square root on \(0,([\d.]+)\]', name)
    if mo: return f'$x^{{-1/2}}$ on $(0,{mo.group(1)}]$'
    mo = re.match(r'step (.*)', name)
    if mo:
        parts = [p.split('@') for p in mo.group(1).split(', ')]
        return ('the step density with slab measure $' + '+'.join(f'{w}\\,\\delta_{{{l}}}' for w, l in parts) + '$')
    raise ValueError(name)
descs = []
for i, t in enumerate(tests):
    descs.append(f"({i + 1}) " + '; '.join(law_tex(n) for n in t['laws']))
m['MCDesc'] = '; '.join(descs)
rows = []
for i, t in enumerate(tests):
    rows.append(f"({i + 1}) & {t['n']} & {t['s']:.4f} & {t['Bmax']:g} & ${sci(t['max_sum_error'])}$ & "
                f"{t['ks_max']:.4f} & {t['p_min']:.3f} & {num(t['kinds'].get('split', 0))} \\\\")
with open(os.path.join(here, 'nums.tex'), 'w') as fh:
    for k, v in m.items():
        fh.write(f'\\newcommand{{\\{k}}}{{{v}}}\n')
    fh.write('\\newcommand{\\MCRows}{%\n' + '\n'.join(rows) + '\n}\n')
print(open(os.path.join(here, 'nums.tex')).read())
