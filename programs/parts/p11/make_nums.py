#!/usr/bin/env python3
"""Writes nums.tex, the numbers quoted in the note, from data/mono11.json."""
import json, os
here = os.path.dirname(os.path.abspath(__file__))
r = json.load(open(os.path.join(here, 'data', 'mono11.json')))
m = {}
def num(n): return f'{n:,}'.replace(',', '{,}')
p1, p2, p3, p4 = r['part1'], r['part2'], r['part3'], r['part4']
m['NCasesOne'] = num(p1['cases_checked']); m['NBoundary'] = num(p1['boundary_checked'])
m['NMaxOne'] = str(p1['nmax']); m['GridOne'] = str(p1['grid']); m['MaxTuples'] = str(p1['max_tuples'])
cc = p1['case_counts']
for k in ('A', 'B', 'C', 'D'):
    m['NCase' + k] = num(cc.get(k, 0)); m['NCaseR' + k] = num(cc.get('R' + k, 0))
m['NIdent'] = num(p2['SF_sums']); m['NIdentRefl'] = num(p2['reflection']); m['NIdentSplit'] = num(p2['split'])
m['NStepDens'] = num(p3['step_densities']); m['NStepPairs'] = num(p3['pairs']); m['MaxSteps'] = str(p3['max_steps'])
tests = p4['tests']
m['NMC'] = num(tests[0]['samples']); m['NMCTests'] = str(len(tests))
m['MCThreshold'] = f"{tests[0]['ks_threshold']:.4f}"
m['MCMaxSumErr'] = f"{max(t['max_sum_error'] for t in tests):.1e}".replace('e-', '\\times10^{-') + '}'
m['MCMinP'] = f"{min(t['ks_pvalue'] for t in tests):.2f}"; m['MCMaxP'] = f"{max(t['ks_pvalue'] for t in tests):.2f}"
m['MCMaxKS'] = f"{max(t['ks_coordinate'] for t in tests):.4f}"
m['RunSeconds'] = str(int(round(r['seconds'])))
names = {'power p=0.5': r'$f\propto(1-x/2.5)^{1/2}$', 'power p=1.0': r'$f\propto 1-x/3$', 'power p=3.0': r'$f\propto(1-x/5)^{3}$',
         'inverse square root': r'$f\propto x^{-1/2}$', 'truncated exponential': r'$f\propto e^{-\lambda x}$',
         'step density': r'step density'}
rows = []
for t in tests:
    e = f"{t['max_sum_error']:.1e}"; mant, ex = e.split('e')
    rows.append(f"{names[t['name']]} & {t['n']} & {t['B']:g} & ${mant}\\times10^{{{int(ex)}}}$ & {t['ks_coordinate']:.4f} & {t['ks_pvalue']:.2f} \\\\")
with open(os.path.join(here, 'nums.tex'), 'w') as fh:
    for k, v in m.items():
        fh.write(f'\\newcommand{{\\{k}}}{{{v}}}\n')
    fh.write('\\newcommand{\\MCRows}{%\n' + '\n'.join(rows) + '\n}\n')
print(open(os.path.join(here, 'nums.tex')).read())
