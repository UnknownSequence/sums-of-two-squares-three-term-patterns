"""Numerical illustration of Theorem 6.1 of triples_final.pdf (the Type I estimate; Section 14, Remark 13.1).

  Xi_r(K) = sum_{mu = r d (mod 4d)} psi1(mu/K) [ sum_{l in Z: mu | a l^2 + h} psi2(l/X) - rho(mu)/mu * X * int psi2 ],

for the polynomial a l^2 + h = E l^2 + H_d attached to a family (Proposition 3.2), a good prime d and
r = kappa in {1,3}; psi1(t) = phi(2t-3), psi2 = phi, phi(t) = exp(-1/(1-t^2)).
Theorem 6.1(a) gives Xi << X^{1/2} H^{1/4} (1 + X/(d H^{1/2}))^theta up to factors (qXH)^eta.
We print |Xi_r(K)| against the square root of the main term M_r(K) and against X^{1/2} H^{1/4}, and the largest
|Xi_r(K)| over all K and r together with the ratio X^{1/2} / max |Xi| (Remark 13.1, "the Cauchy-Schwarz step").
Run: python3 typeI.py"""
import math
import numpy as np
from seedsA import setup, v2

def spf_sieve(N):
    spf = np.zeros(N + 1, dtype=np.int64)
    for p in range(2, int(N ** 0.5) + 1):
        if spf[p] == 0:
            blk = spf[p * p::p]
            blk[blk == 0] = p
    idx = np.nonzero(spf == 0)[0]
    spf[idx] = idx
    return spf

def sqrt_mod_p(a, p):
    a %= p
    if a == 0:
        return [0]
    if pow(a, (p - 1) // 2, p) != 1:
        return []
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2; s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    M, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (M - i - 1), p)
        M, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return sorted({r, p - r})

_cache = {}
def roots_pp(a, h, p, e):
    """nu mod p^e with a nu^2 + h = 0 (mod p^e), p odd, p does not divide a"""
    key = (a, h, p, e)
    if key in _cache:
        return _cache[key]
    pe = p ** e
    target = (-h * pow(a, -1, pe)) % pe
    if target % p:
        sols = sqrt_mod_p(target, p); mod = p
        for _ in range(1, e):
            nm = mod * p
            sols = [(x - (x * x - target) * pow(2 * x, -1, nm)) % nm for x in sols]
            mod = nm
    else:
        sols = [x for x in range(pe) if (x * x - target) % pe == 0]
    _cache[key] = sols
    return sols

def roots(a, h, fac):
    res = [(0, 1)]
    for p, e in fac.items():
        s = roots_pp(a, h, p, e)
        if not s:
            return [], 0
        pe = p ** e
        res = [((r + M * ((t - r) * pow(M, -1, pe) % pe)) % (M * pe), M * pe) for (r, M) in res for t in s]
    return [r for r, _ in res], len(res)

bump = lambda t: math.exp(-1.0 / (1.0 - t * t)) if abs(t) < 1 else 0.0
psi1 = lambda t: bump(2 * t - 3)          # supported on [1,2]
psi2 = bump                                # supported on [-1,1]
I2 = sum(psi2(-1 + (i + 0.5) / 50000) for i in range(100000)) / 50000

def E(a, h, d, r, K, X, spf):
    tot = 0.0; main = 0.0
    k = int(K // d) + 1
    k += (r - k) % 4
    while d * k < 2 * K:
        mu = d * k
        w1 = psi1(mu / K)
        if w1:
            fac = {}
            t = k
            while t > 1:
                p = int(spf[t]); t //= p; fac[p] = fac.get(p, 0) + 1
            fac[d] = fac.get(d, 0) + 1
            rs, nr = roots(a, h, fac)
            cnt = 0.0
            for r0 in rs:
                l = r0 - mu * math.ceil((r0 - X) / mu)      # smallest l = r0 (mod mu) with l >= -X
                while l <= X:
                    cnt += psi2(l / X); l += mu
            tot += w1 * cnt
            main += w1 * nr / mu * X * I2
        k += 4
    return tot - main, main

if __name__ == "__main__":
    X = 2 * 10 ** 6
    for (pa, pb) in [(1, 2), (2, 3)]:
        s = setup(pa, pb)
        for d in ([89, 281] if (pa, pb) == (1, 2) else [53, 181]):
            m = (d + s['c']) ** 2 + s['D0']
            a = 2 ** (2 * s['j'] - s['v']); h = m >> s['v']
            spf = spf_sieve(int(2 * d * X / d) + 10)
            print(f"{{0,{pa},{pb}}}: d={d}, E={a}, H={h}, X={X}:  X^(1/2) H^(1/4) = {math.sqrt(X) * h ** 0.25:.0f}")
            worst = 0; worst_far = 0; big = (0.0, None, None)
            for i in range(0, 40):
                K = X * 2 ** (i / 2)
                if K > d * X:
                    break
                for r in (1, 3):
                    e, mn = E(a, h, d, r, K, X, spf)
                    worst = max(worst, abs(e) / math.sqrt(X) / h ** 0.25)
                    if abs(e) > big[0]:
                        big = (abs(e), i / 2, r)
                    if K >= 4 * X and mn > 0:
                        worst_far = max(worst_far, abs(e) / math.sqrt(mn))
                    if i % 4 == 0 and mn > 0:
                        print(f"   K/X=2^{i/2:4.1f} r={r}: main={mn:9.1f}  Xi={e:8.1f}  |Xi|/main^(1/2)={abs(e)/math.sqrt(mn):5.2f}")
            print(f"   max over K, r of |Xi_r(K)| / (X^(1/2) H^(1/4)) = {worst:.3f};  "
                  f"max over K >= 4X of |Xi_r(K)| / M_r(K)^(1/2) = {worst_far:.2f}")
            print(f"   largest |Xi| = {big[0]:.1f} at K/X = 2^{big[1]:.1f}, r = {big[2]};  "
                  f"X^(1/2) / largest |Xi| = {math.sqrt(X) / big[0]:.1f}")
