"""Independent check of the complete mixes of binomial distributions stored in data/binomial_mixes.json
(Proposition 159(c)); standard library only, no code shared with wang26.py.

Each entry is [N, n, M, mix] with p = M/(n N) and mix a list of [count vector k, weight]: k_x of the n variables
take the value x.  The check: every count vector has n coordinates in all and the sum M, the weights are positive
and add up to 1, and the mixture of the vectors k/n is the distribution B(N, p), exactly.  It also checks that the
entries are exactly the triples (N, n, M) with N <= M <= (n-1) N in the range, and counts the pairs (n, p) that
they settle through the least number of trials N_0 = b / gcd(b, n), p = a/b in lowest terms.
Writes data/check_binomial.json."""
import json, math, os
from fractions import Fraction as Fr

here = os.path.dirname(os.path.abspath(__file__))
C = json.load(open(os.path.join(here, "data", "binomial_mixes.json")))
seen = set(); maxvec = 0; nonint = 0
for N, n, M, mix in C:
    p = Fr(M, n * N)
    pmf = [math.comb(N, x) * p ** x * (1 - p) ** (N - x) for x in range(N + 1)]
    total = Fr(0); marg = [Fr(0)] * (N + 1)
    for k, w in mix:
        w = Fr(w)
        assert w > 0 and len(k) == N + 1 and all(type(v) is int and v >= 0 for v in k)
        assert sum(k) == n and sum(x * v for x, v in enumerate(k)) == M
        total += w
        for x in range(N + 1):
            marg[x] += w * Fr(k[x], n)
    assert total == 1 and marg == pmf
    assert (N, n, M) not in seen
    seen.add((N, n, M)); maxvec = max(maxvec, len(mix))
    nonint += (n * p).denominator != 1
Nmax = max(c[0] for c in C); nmax = max(c[1] for c in C)
assert seen == {(N, n, M) for N in range(1, Nmax + 1) for n in range(2, nmax + 1) for M in range(N, (n - 1) * N + 1)}
# the pairs (n, p) with 1/n <= p <= 1 - 1/n whose least number of trials N_0 is at most Nmax
pairs = set()
for (N, n, M) in seen:
    p = Fr(M, n * N); b = p.denominator
    if b // math.gcd(b, n) == N:
        pairs.add((n, p))
for n in range(2, nmax + 1):                                           # every such pair is among them
    for N0 in range(1, Nmax + 1):
        for M in range(N0, (n - 1) * N0 + 1):
            p = Fr(M, n * N0)
            if p.denominator // math.gcd(p.denominator, n) == N0:
                assert (n, p) in pairs
out = dict(mixes=len(C), Nmax=Nmax, nmax=nmax, max_vectors=maxvec, np_not_integer=nonint, pairs=len(pairs))
json.dump(out, open(os.path.join(here, "data", "check_binomial.json"), "w"), indent=1)
print(out)
