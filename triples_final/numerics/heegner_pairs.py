"""Illustration of Lemma 8.4 and Remark 13.1 of triples_final.pdf: pairs of Heegner points at bounded distance.

For N = E*H_d (Proposition 3.2) let Q_N be the positive definite integral symmetric matrices
g = (a b; b c) of determinant N, with attached point w = (b + i sqrt N)/c, and let Lambda_N be the reduced
ones (|2b| <= c <= a).  We count
    P(N)   = #{(z, w): z in Lambda_N, w in Q_N, u(w, z) <= 1},      u(w,z) = |w - z|^2 / (4 Im w Im z),
which is the quantity bounded by N^{1+eps} in Lemma 8.4 (it bounds the pair count P there), and
    P_d(N) = the number of those pairs for which some (c0 : d0) in P^1(F_d) is a common zero modulo d of the
             binary forms of z and w (the pairs that can contribute when the level-d congruence is kept).
Equidistribution of Heegner points predicts P(N) ~ 12 (#Lambda_N)^2: the disc u <= 1 has hyperbolic area
4 pi and a fundamental domain for SL_2(Z) has area pi/3.
Run: python3 heegner_pairs.py"""
import math
import numpy as np
from seedsA import setup

def reduced(N):
    out = []
    for c in range(1, math.isqrt(4 * N // 3) + 2):
        for b in range(-(c // 2), c // 2 + 1):
            if (b * b + N) % c == 0:
                a = (b * b + N) // c
                if a >= c:
                    if (2 * abs(b) == c or a == c) and b < 0:      # boundary convention
                        continue
                    out.append((a, b, c))
    return out

def proj_roots(a, b, c, d):
    """projective zeros mod d of a X^2 + 2b XY + c Y^2"""
    r = [(t, 1) for t in range(d) if (a * t * t + 2 * b * t + c) % d == 0]
    if a % d == 0:
        r.append((1, 0))
    return r

def count(N, d):
    lam = reduced(N)
    tot = totd = 0
    for (a1, b1, c1) in lam:
        roots = proj_roots(a1, b1, c1, d)
        lo = int(c1 * (3 - 2 * math.sqrt(2))) - 1
        hi = int(c1 * (3 + 2 * math.sqrt(2))) + 1
        for c in range(max(1, lo), hi + 1):
            S = 4 * N * c * c1 - N * (c - c1) ** 2
            if S < 0:
                continue
            W = math.isqrt(S)
            bmin = -((-(b1 * c - W)) // c1)
            bmax = (b1 * c + W) // c1
            if bmax < bmin:
                continue
            bs = np.arange(bmin, bmax + 1, dtype=np.int64)
            ok = ((bs * bs + N) % c == 0) & ((bs * c1 - b1 * c) ** 2 + N * (c - c1) ** 2 <= 4 * N * c * c1)
            bs = bs[ok]
            tot += len(bs)
            for b in bs:
                a = (int(b) * int(b) + N) // c
                if any((a * x * x + 2 * int(b) * x * y + c * y * y) % d == 0 for (x, y) in roots):
                    totd += 1
    return len(lam), tot, totd

if __name__ == "__main__":
    for (pa, pb, ds) in [(1, 2, [89, 281, 409]), (2, 3, [53, 181, 373])]:
        s = setup(pa, pb)
        for d in ds:
            m = (d + s['c']) ** 2 + s['D0']
            E = 2 ** (2 * s['j'] - s['v']); H = m >> s['v']; N = E * H
            nl, P, Pd = count(N, d)
            print(f"{{0,{pa},{pb}}} d={d:4d} N=EH={N:7d}: #Lambda_N={nl:5d} (/N^(1/2)={nl/math.sqrt(N):.2f}), "
                  f"P(N)={P:8d} (/N={P/N:.3f}, /(12 #Lambda^2)={P/(12*nl*nl):.4f}), "
                  f"P_d(N)={Pd:6d} (d*P_d/P={d*Pd/P:.2f})")
