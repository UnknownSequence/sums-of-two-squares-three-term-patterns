"""Remark 5.1 of the note: for a = 3 (mod 4), members with 4 | l have odd part of m = 3 (mod 4), so r(m) = 0."""
import random
from fam import is_prime, roots_two_primes
random.seed(5); bad = tot = 0
for a in [3, 7, 11, 15, 19]:
    for _ in range(40):
        r = random.choice([p for p in range(5, 400) if is_prime(p) and p % 4 == 1])
        D = random.choice([p for p in range(3 * a + 1, 2000) if is_prime(p) and p != r and pow(3, (p - 1) // 2, p) == 1])
        if (D + 3 * a * r) % 2: continue
        H = ((D + 3 * a * r) // 2) ** 2 - 3 * a * a * r * r
        if H <= 0 or H % r == 0 or H % D == 0: continue
        L = r * D
        for r0 in roots_two_primes(1, H, r, D):
            for k in range(200):
                l = r0 + L * k
                if l % 4: continue
                m = (l * l + H) // L
                if m <= 0: continue
                tot += 1
                o = m
                while o % 2 == 0: o //= 2
                bad += (o % 4 != 3)
print(f"a = 3 (mod 4): {tot} family members with 4 | l; members whose m has odd part not 3 mod 4: {bad}")
