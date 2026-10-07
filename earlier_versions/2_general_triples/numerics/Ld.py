"""Exact evaluation of the singular series L_d of Lemma 5.3.

L_d = sum_k chi(k) f(k)/k = L(1,chi) L(1,psi) H_d, where chi is the character mod 4,
psi(n) = (m/n) for odd n (0 for even n), m = m_d, and H_d is the Euler product of Lemma 5.3(c).
L(1,psi) is computed from L(1,chi_D) for the fundamental discriminant D of Q(sqrt m), using the
rapidly convergent series L(1,chi_D) = sum_n chi_D(n) [erfc(n sqrt(pi/D))/n + E_1(pi n^2/D)/sqrt(D)]
(valid for even primitive real characters, which have root number 1).
"""
import math
import numpy as np
from scipy.special import erfc, exp1

def factor(n):
    f = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def jacobi(a, n):
    """Jacobi symbol (a/n), n odd positive."""
    assert n > 0 and n % 2 == 1
    a %= n
    s = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                s = -s
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            s = -s
        a %= n
    return s if n == 1 else 0

def kronecker(D, n):
    """Kronecker symbol (D/n) for a discriminant D and n >= 1."""
    s = 1
    while n % 2 == 0:
        n //= 2
        if D % 2 == 0:
            return 0
        s *= 1 if D % 8 in (1, 7) else -1
    return s * jacobi(D, n) if n > 1 else s

def fundamental_disc(m):
    sq = 1
    mp = 1
    for p, e in factor(m).items():
        mp *= p ** (e % 2)
    return mp if mp % 4 == 1 else 4 * mp

def L1_chiD(D):
    q = D
    N = int(8 * math.sqrt(q)) + 20
    n = np.arange(1, N + 1, dtype=np.float64)
    chi = np.array([kronecker(D, k) for k in range(1, N + 1)], dtype=np.float64)
    terms = erfc(n * math.sqrt(math.pi / q)) / n + exp1(math.pi * n * n / q) / math.sqrt(q)
    return float(np.sum(chi * terms))

def rho_pp(l, j, m):
    """number of nu mod l^j with nu^2 + m = 0 (mod l^j), l odd prime"""
    if j == 0:
        return 1
    al = 0
    mm = m
    while mm % l == 0:
        mm //= l
        al += 1
    if al == 0:
        return 1 + jacobi(-mm, l)
    if j <= al:
        return l ** (j // 2)
    if al % 2:
        return 0
    return l ** (al // 2) * (1 + jacobi(-mm, l))

def chi4(n):
    return 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)

def L_d(d, m):
    D = fundamental_disc(m)
    Lpsi = L1_chiD(D)
    for p in factor(2 * m):
        Lpsi *= 1 - kronecker(D, p) / p
    H = 6 / math.pi ** 2
    for p in set(factor(2 * d * m)):
        H /= 1 - p ** -2.0
    H *= 1 - 1 / d
    for l, al in factor(m).items():
        if l == 2:
            continue
        c = chi4(l)
        P = sum((c ** j) * rho_pp(l, j, m) * float(l) ** (-j) for j in range(0, al + 60))
        H *= (1 - c / l) * P
    return (math.pi / 4) * Lpsi * H, Lpsi, H

def params(a, b, d):
    kappa = 1 if b % 2 == 0 else 2
    g = kappa * b // 2
    c = kappa * a - g
    m = (d + c) ** 2 + kappa * kappa * a * (b - a)
    return kappa, g, c, m

if __name__ == "__main__":
    import sys
    a, b, d = map(int, sys.argv[1:4])
    kappa, g, c, m = params(a, b, d)
    L, Lpsi, H = L_d(d, m)
    print(f"{{0,{a},{b}}} d={d} m={m} D={fundamental_disc(m)} L(1,psi)={Lpsi:.6f} H_d={H:.6f} L_d={L:.6f}")
