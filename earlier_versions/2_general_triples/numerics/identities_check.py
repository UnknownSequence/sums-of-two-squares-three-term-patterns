"""Checks of Lemmas 2.1-2.3 and of the inequality r(n(n+b)) <= r(n) r(n+b)/4 used in Remark 8.4.
Run: python3 identities_check.py"""
import math

def factor(n):
    f = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def r(n):
    """number of representations of n >= 1 as a sum of two squares"""
    res = 4
    for p, e in factor(n).items():
        if p % 4 == 3 and e % 2:
            return 0
        if p % 4 == 1:
            res *= e + 1
    return res

def is_prime(n):
    return n > 1 and all(n % q for q in range(2, math.isqrt(n) + 1))

viol = {"2.1": 0, "2.2": 0, "2.3": 0, "8.4": 0}
tested = 0
for (a, b) in [(1, 2), (1, 3), (2, 3), (1, 4), (5, 8), (3, 10), (6, 9), (4, 12), (7, 20)]:
    kappa = 1 if b % 2 == 0 else 2
    g = kappa * b // 2; c = kappa * a - g; D0 = kappa * kappa * a * (b - a)
    m = lambda d: (d + c) ** 2 + D0
    # Lemma 2.3: #{(d,u): d,u >= 1, 2 kappa d (n+a) = u^2 + m_d} <= r(n(n+b))
    for n in range(1, 2000):
        X = kappa * n + g
        cnt = 0
        for d in range(1, 2 * X + 1):
            Q = 2 * kappa * d * (n + a) - m(d)
            if Q > 0 and math.isqrt(Q) ** 2 == Q:
                cnt += 1
        if cnt > r(n * (n + b)):
            viol["2.3"] += 1
    # Lemmas 2.1 and 2.2, and Remark 8.4, for n arising from primes d = 1 (mod 4)
    for d in [p for p in range(5, 400) if is_prime(p) and p % 4 == 1]:
        for u in range(1, 3000):
            Q = u * u + m(d)
            if Q % (2 * kappa * d):
                continue
            T = Q // (2 * kappa * d); n = T - a; X = kappa * n + g
            if n < 1:
                continue
            tested += 1
            if 2 * d * X != u * u + d * d + g * g or kappa ** 2 * n * (n + b) != (X - d) ** 2 + u * u:
                viol["2.1"] += 1
            if r(n) == 0 or r(n + b) == 0:
                viol["2.2"] += 1
            if 4 * r(n * (n + b)) > r(n) * r(n + b):
                viol["8.4"] += 1
print("violations:", viol, "  (Lemmas 2.1/2.2 and Remark 8.4 tested on", tested, "values of n)")
