"""Library for the rescaled families of the note "Rescaled families and sums of two squares".

Cubes (Section 5).  For odd a, a prime r = 1 (mod 8) and a prime D = D_a (mod 8) with (3/D) = 1:
    w = D + 3ar,  H = (w/2)^2 - 3a^2 r^2,   family: odd l with rD | l^2 + H,   m = (l^2 + H)/(rD).
    Then 4 r^2 G(m) = (2l)^2 + (2rm - 3ar - D)^2 with G(m) = m^2 - 3am + 3a^2  (Lemma 2.1).
Triples (Section 6).  Data (B, A, c, D0=4A(B-A), v, J, j, d0) of [IC, Prop. 3.2] (seedsA.setup);
    r = 1 (mod 2^J), d = d0 (mod 2^J), M = (d + c r)^2 + D0 r^2, H = M / 2^v, E = 2^(2j-v),
    family: l in Z with rd | E l^2 + H,  T = 2^(v-2) (E l^2 + H)/(rd),  P = T - A,  Q = 2T - c.
"""
import math, random

def is_prime(n):
    if n < 2: return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

def rho_factor(n):
    if n % 2 == 0: return 2
    while True:
        c = random.randrange(1, n); f = lambda z: (z * z + c) % n
        x = y = random.randrange(2, n); g = 1
        while g == 1:
            x = f(x); y = f(f(y)); g = math.gcd(abs(x - y), n)
        if g != n: return g

def factor(n, out=None):
    out = {} if out is None else out
    if n == 1: return out
    for p in (2, 3, 5, 7, 11, 13):
        while n % p == 0: out[p] = out.get(p, 0) + 1; n //= p
    if n == 1: return out
    if is_prime(n): out[n] = out.get(n, 0) + 1; return out
    d = rho_factor(n); factor(d, out); factor(n // d, out); return out

def in_S(n):
    return n > 0 and all(e % 2 == 0 for p, e in factor(n).items() if p % 4 == 3)

def D_class(a):
    """D_a mod 8 (Lemma 5.2)."""
    return (4 - 3 * a) % 8 if a % 4 == 1 else (-3 * a) % 8

def cubes_H(a, r, D):
    w = D + 3 * a * r
    assert w % 4 == 0
    return (w // 2) ** 2 - 3 * a * a * r * r

def good_cubes_pair(a, r, D):
    if not (is_prime(r) and is_prime(D) and r % 8 == 1 and D % 8 == D_class(a) and D != r and D > 3 * a):
        return False
    if pow(3, (D - 1) // 2, D) != 1: return False
    H = cubes_H(a, r, D)
    s = math.isqrt(H)
    if s * s == H: return False
    if H % 3 == 0:
        t = math.isqrt(H // 3)
        if 3 * t * t == H: return False
    return True

def roots_mod(E, H, L):
    return [l for l in range(L) if (E * l * l + H) % L == 0]

def sqrt_mod_p(a, p):
    a %= p
    if a == 0: return [0]
    if pow(a, (p - 1) // 2, p) != 1: return []
    q, s = p - 1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1: z += 1
    M, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1: t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (M - i - 1), p)
        M, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return sorted({r, p - r})

def roots_two_primes(E, H, p1, p2):
    """l mod p1 p2 with E l^2 + H = 0, p1 != p2 odd primes not dividing EH."""
    out = []
    R1 = [x * pow(E, -1, p1) % p1 for x in sqrt_mod_p(-H * E, p1)]   # (E l)^2 = -EH
    R2 = [x * pow(E, -1, p2) % p2 for x in sqrt_mod_p(-H * E, p2)]
    L = p1 * p2
    for a1 in R1:
        for a2 in R2:
            out.append((a1 + p1 * ((a2 - a1) * pow(p1, -1, p2) % p2)) % L)
    return sorted(out)
