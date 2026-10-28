"""Type I sums Xi of [IC, (6.1)] at level q = 4 E p1 p2 (Theorem 3.1 of the note), for E in {1, 4, 8}:
  Xi_kappa(K) = sum_{mu = kappa L (mod 4L)} psi1(mu/K) [ sum_{l: mu | E l^2 + H} psi2(l/X) - rho(mu)/mu X int psi2 ],
L = p1 p2.  Prints max |Xi| / (X^{1/2} H^{1/4}) over K = 2^{i/2} X <= L X and kappa in {1,3}, and
max |Xi| / M^{1/2} over K >= 4X, where M is the main term.   Run: python3 typeI_composite.py"""
import math
from typeI import spf_sieve, roots, psi1, psi2, I2
from fam import cubes_H
from seedsA import setup

def Xi(E, H, p1, p2, kap, K, X, spf):
    L = p1 * p2
    tot = main = 0.0
    k = int(K // L) + 1
    k += (kap - k) % 4
    while L * k < 2 * K:
        mu = L * k
        w1 = psi1(mu / K)
        if w1:
            fac = {}
            t = k
            while t > 1:
                p = int(spf[t]); t //= p; fac[p] = fac.get(p, 0) + 1
            fac[p1] = fac.get(p1, 0) + 1; fac[p2] = fac.get(p2, 0) + 1
            rs, nr = roots(E, H, fac)
            cnt = 0.0
            for r0 in rs:
                l = r0 - mu * math.ceil((r0 - X) / mu)
                while l <= X:
                    cnt += psi2(l / X); l += mu
            tot += w1 * cnt
            main += w1 * nr / mu * X * I2
        k += 4
    return tot - main, main

if __name__ == "__main__":
    X = 10 ** 6
    cases = []
    for (a, r, D) in [(1, 41, 73), (3, 41, 167)]:
        H = cubes_H(a, r, D)
        cases += [(f"cubes a={a}, E=1", 1, H, r, D), (f"cubes a={a}, E=4", 4, H, r, D)]
    s = setup(1, 2); E = 2 ** (2 * s['j'] - s['v'])
    r, d = 97, 761; M = (d + s['c'] * r) ** 2 + s['D0'] * r * r
    cases.append(("triples {0,1,2}", E, M >> s['v'], r, d))
    for (name, E, H, p1, p2) in cases:
        L = p1 * p2
        spf = spf_sieve(int(2 * X * 2 ** 0.5) + 10)
        worst = worst_far = 0.0; big = 0.0
        i = 0
        while X * 2 ** (i / 2) <= min(L, 64) * X:
            K = X * 2 ** (i / 2)
            for kap in (1, 3):
                e, mn = Xi(E, H, p1, p2, kap, K, X, spf)
                worst = max(worst, abs(e) / (math.sqrt(X) * H ** 0.25)); big = max(big, abs(e))
                if K >= 4 * X and mn > 0: worst_far = max(worst_far, abs(e) / math.sqrt(mn))
            i += 1
        print(f"{name}: L={L}, H={H}, X={X}: max |Xi|/(X^1/2 H^1/4) = {worst:.4f}, "
              f"max_(K>=4X) |Xi|/M^1/2 = {worst_far:.2f}, max |Xi| = {big:.1f} (X^1/2 = {math.sqrt(X):.0f})", flush=True)
