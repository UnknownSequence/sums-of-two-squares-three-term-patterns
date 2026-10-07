"""Check of Lemma 6.1 (Gauss's correspondence and the reciprocity formula (6.1)).

For a determinant Delta (neither Delta nor Delta/3 a square) and a modulus M, the map
(phi, +-(R,S)) -> z = t1(AR+BS) + t2(BR+CS), with phi = [A,2B,C] reduced and R t2 - S t1 = 1,
is checked to be a bijection onto the roots of z^2 + Delta = 0 (mod M), and
z/M = Rbar/S - (AR+BS)/(S M) (mod 1) is checked whenever S != 0.
Tested for Delta = 2^{2J+2} m_d as in Proposition 6.3 and for random Delta.  Run: python3 gauss_check.py"""
from math import gcd, isqrt
from fractions import Fraction
import random

def reduced_forms(Det):
    """one reduced form [A,2B,C] (|2B| <= A <= C, B >= 0 on the boundary) per SL_2(Z)-class
    of positive definite forms of determinant AC - B^2 = Det"""
    out = []
    A = 1
    while 3 * A * A <= 4 * Det:
        for B in range(-(A // 2), A // 2 + 1):
            if (B * B + Det) % A:
                continue
            C = (B * B + Det) // A
            if C < A:
                continue
            if (abs(2 * B) == A or A == C) and B < 0:
                continue
            out.append((A, B, C))
        A += 1
    return out

def egcd(a, b):
    if b == 0:
        return (a, 1, 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a // b) * y)

def complete(R, S):
    """(t1, t2) with R t2 - S t1 = 1"""
    g, x, y = egcd(R, S)
    assert abs(g) == 1
    t2, t1 = x * g, -y * g
    assert R * t2 - S * t1 == 1
    return t1, t2

def representations(A, B, C, Det, Mmod):
    """primitive (R,S) with phi(R,S) = Mmod, one from each pair +-(R,S)"""
    Smax = isqrt(A * Mmod // Det) + 2
    for S in range(0, Smax + 1):
        rem = A * Mmod - Det * S * S       # A phi = (AR+BS)^2 + Det S^2
        if rem < 0:
            break
        t = isqrt(rem)
        if t * t != rem:
            continue
        for sgn in ([1, -1] if t else [1]):
            num = sgn * t - B * S
            if num % A:
                continue
            R = num // A
            if S == 0 and R <= 0:
                continue
            if gcd(R, S) == 1:
                yield R, S

def z_of(A, B, C, R, S):
    t1, t2 = complete(R, S)
    return t1 * (A * R + B * S) + t2 * (B * R + C * S)

def check(Det, Mmod):
    roots_direct = sorted(z for z in range(Mmod) if (z * z + Det) % Mmod == 0)
    got = {}
    for (A, B, C) in reduced_forms(Det):
        for R, S in representations(A, B, C, Det, Mmod):
            assert A * R * R + 2 * B * R * S + C * S * S == Mmod
            z = z_of(A, B, C, R, S) % Mmod
            assert (z * z + Det) % Mmod == 0, "not a root"
            assert z not in got, "not injective"
            got[z] = (A, B, C, R, S)
            if S != 0:
                Rbar = pow(R % S, -1, S) if S > 1 else 0
                diff = Fraction(z, Mmod) - (Fraction(Rbar, S) - Fraction(A * R + B * S, S * Mmod))
                assert diff.denominator == 1, "reciprocity formula fails"
    assert sorted(got) == roots_direct, "not surjective"
    return len(roots_direct)

def is_square(n):
    return n >= 0 and isqrt(n) ** 2 == n

if __name__ == "__main__":
    random.seed(1)
    tests = roots = 0
    # Delta = 2^{2J+2} m with m = m_d for several patterns and primes d (Proposition 6.3)
    for (a, b, d) in [(1, 2, 5), (1, 2, 37), (1, 3, 5), (1, 4, 97), (5, 8, 41), (2, 3, 13), (3, 7, 17)]:
        kappa = 1 if b % 2 == 0 else 2
        g = kappa * b // 2; c = kappa * a - g
        m = (d + c) ** 2 + kappa * kappa * a * (b - a)
        for J in [1, 2, 3]:
            Det = 2 ** (2 * J + 2) * m
            if is_square(Det) or (Det % 3 == 0 and is_square(Det // 3)):
                continue
            for _ in range(12):
                Mmod = 2 ** (2 * J + 2) * random.choice(range(1, 400, 2))
                roots += check(Det, Mmod); tests += 1
    # random determinants and moduli
    while tests < 600:
        Det = random.randint(1, 3000)
        if is_square(Det) or (Det % 3 == 0 and is_square(Det // 3)):
            continue
        roots += check(Det, random.randint(2, 5000)); tests += 1
    print("Lemma 6.1 checks passed:", tests, "cases,", roots, "roots")
