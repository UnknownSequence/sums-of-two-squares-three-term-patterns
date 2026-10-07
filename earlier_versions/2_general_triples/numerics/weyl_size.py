"""Sizes of the Weyl sums of Proposition 6.3 (Section 9).

  W(M) = sum_{M < mu <= 2M, d | mu, mu/d = gamma (mod 2^J)}  S_mu(h),
  S_mu(h) = sum_{w mod mu, 2^{2J} w^2 + m = 0 (mod mu)} e(h w / mu),

compared with the number of terms R(M) = sum rho(mu), which is the trivial bound.
Square-root cancellation means |W(M)| = O(R(M)^{1/2}); Proposition 6.3 gives O(M^{3/4+eps}).
Run: python3 weyl_size.py J d m imax   (default: J=4, d=37, m=1370, i.e. the pattern {0,1,2} with d=37)"""
import math, sys
import numpy as np

def spf_sieve(N):
    spf = np.zeros(N + 1, dtype=np.int32)
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
def roots_pp(a, p, k):
    """all nu mod p^k with nu^2 = a (mod p^k), p odd"""
    key = (p, k)
    if key in _cache:
        return _cache[key]
    pk = p ** k
    if a % p:
        sols = sqrt_mod_p(a, p)
        mod = p
        for _ in range(1, k):
            nm = mod * p
            sols = [(x - (x * x - a) * pow(2 * x, -1, nm)) % nm for x in sols]
            mod = nm
    else:
        sols = [x for x in range(pk) if (x * x - a) % pk == 0]
    _cache[key] = sols
    return sols

def factor_mu(spf, k, d):
    """factorisation of mu = d*k, using a smallest-prime-factor table for k"""
    f = {d: 1}
    while k % d == 0:
        k //= d; f[d] += 1
    while k > 1:
        p = int(spf[k]); k //= p
        f[p] = f.get(p, 0) + 1
    return f

def roots(fac, mu, J, m):
    res = [(0, 1)]
    for p, k in fac.items():
        s = roots_pp(-m, p, k)
        if not s:
            return []
        pk = p ** k
        res = [((r + M * ((t - r) * pow(M, -1, pk) % pk)) % (M * pk), M * pk) for (r, M) in res for t in s]
    inv = pow(2 ** J, -1, mu)
    return [(x * inv) % mu for (x, _) in res]

if __name__ == "__main__":
    args = [int(t) for t in sys.argv[1:]]
    J, d, m, imax = args if len(args) == 4 else (4, 37, 1370, 12)
    hs = np.array([1, 2, 3])
    Mmax = 10 ** 4 * 2 ** imax
    spf = spf_sieve(2 * Mmax // d + 1)
    print(f"J={J} d={d} m={m}; h in {hs.tolist()}")
    worst = 0
    for gamma in [1, 7]:
        for i in range(0, imax + 1):
            M = 10 ** 4 * 2 ** i
            if M < m:
                continue
            num = []; den = []
            kmin = M // d + 1
            k = kmin + ((gamma - kmin) % 2 ** J)
            while d * k <= 2 * M:
                mu = d * k
                fac = factor_mu(spf, k, d)
                ws = roots(fac, mu, J, m)
                num.extend(ws); den.extend([mu] * len(ws))
                k += 2 ** J
            w = np.array(num, dtype=np.float64); mu = np.array(den, dtype=np.float64)
            R = len(w)
            if R == 0:
                print(f"gamma={gamma} M={M:10d}  R(M)=0 (empty sum)")
                continue
            vals = [abs(np.exp(2j * np.pi * h * w / mu).sum()) for h in hs]
            mx = max(vals)
            worst = max(worst, mx / math.sqrt(R)) if M >= 10 ** 5 else worst
            print(f"gamma={gamma} M={M:10d}  R(M)={R:8d}  max_h|W|={mx:9.2f}  max|W|/R^(1/2)={mx/math.sqrt(R):5.2f}"
                  f"  max|W|/M^(3/4)={mx/M**0.75:8.5f}")
    print("max of |W|/R^(1/2) over M >= 10^5:", round(worst, 2))
