"""Checks of Lemmas 2.1, 2.2, 5.2, 6.1 of the note on family members with m (or T) up to about 1e12."""
import random, math
from fam import *
from seedsA import setup
random.seed(1)
bad = tot = fac_checked = 0
for a in [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23]:
    pairs = []
    while len(pairs) < 6:
        r = random.randrange(9, 300); D = random.randrange(a * r, 2 * a * r + 1)
        if good_cubes_pair(a, r, D): pairs.append((r, D))
    for (r, D) in pairs:
        H = cubes_H(a, r, D); L = r * D
        rts = roots_two_primes(1, H, r, D)
        assert len(rts) == 4
        for _ in range(25):
            lmax = math.isqrt(L * 10 ** 12)
            l = random.choice(rts) + L * random.randrange(0, lmax // L)
            if l % 2 == 0: l += L
            m = (l * l + H) // L
            ok = (l * l + H) % L == 0 and m % 2 == 0 and (m >> 1) % 4 == 1
            G = m * m - 3 * a * m + 3 * a * a
            ok &= 4 * r * r * G == (2 * l) ** 2 + (2 * r * m - 3 * a * r - D) ** 2
            ok &= in_S(G)                       # Lemma 2.1, checked by factorisation
            if in_S(m):                         # then n^3 + a^3 = m G(m) must be in S
                fac_checked += 1
            tot += 1; bad += not ok
print(f"cubes: {tot} members (a odd <= 23, 72 families, m <= ~1e12): failures {bad}; "
      f"{fac_checked} of them have m in S, hence n^3+a^3 in S")
bad = tot = 0
for (pa, pb) in [(1, 2), (1, 3), (2, 3), (1, 4), (3, 8), (5, 8), (4, 7), (6, 11)]:
    s = setup(pa, pb); B, A, c, D0, v, J, j, d0 = (s[k] for k in ('B', 'A', 'c', 'D0', 'v', 'J', 'j', 'd0'))
    E = 2 ** (2 * j - v); C0 = abs(c) + math.isqrt(abs(D0)) + 2
    cnt = 0
    while cnt < 5:
        r = random.randrange(1, 40) * 2 ** J + 1
        d = d0 + 2 ** J * random.randrange(C0 * r // 2 ** J, 2 * C0 * r // 2 ** J)
        if not (is_prime(r) and is_prime(d) and d > B and d != r): continue
        M = (d + c * r) ** 2 + D0 * r * r
        if M <= 0 or M % 2 ** v or (M >> v) % 2 == 0: bad += 1; continue
        H = M >> v; L = r * d; cnt += 1
        rts = roots_two_primes(E, H, r, d); assert len(rts) == 4
        for _ in range(20):
            lmax = math.isqrt(L * 10 ** 12 // E)
            l = random.choice(rts) + L * random.randrange(-(lmax // L), lmax // L)
            num = E * l * l + H
            T = 2 ** (v - 2) * num // L
            P = T - A; Q = 2 * T - c; u = 2 ** j * l
            ok = num % L == 0 and (num // L) % 4 == 1
            ok &= 2 * r * d * Q == u * u + d * d + r * r * B * B
            ok &= (r * Q - d) ** 2 + u * u == 4 * r * r * P * (P + B)
            if P > 0: ok &= in_S(P) and in_S(P + B)
            tot += 1; bad += not ok
print(f"triples: {tot} members (8 patterns, 40 families, T <= ~1e12): failures {bad}")
