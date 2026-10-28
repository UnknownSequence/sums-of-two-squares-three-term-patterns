"""Lemma 2.3 of the note: how often does one n arise from several families?  Cubes, a = 1 and a = 3:
all good pairs (r, D) with r <= R prime = 1 (mod 8), D in [ar, 2ar]; all members m <= x.
Run: python3 multiplicity.py"""
import math
from collections import Counter
from fam import is_prime, good_cubes_pair, cubes_H, roots_two_primes
def run(a, R, x):
    cnt = Counter(); fams = 0
    for r in range(2, R + 1):
        if not (is_prime(r) and r % 8 == 1): continue
        for D in range(a * r, 2 * a * r + 1):
            if not good_cubes_pair(a, r, D): continue
            fams += 1; H = cubes_H(a, r, D); L = r * D
            lmax = math.isqrt(L * int(x))
            for r0 in roots_two_primes(1, H, r, D):
                for l in range(r0 - L * ((r0 + lmax) // L + 1), lmax + 1, L):
                    if l % 2 == 0: continue
                    m = (l * l + H) // L
                    if 1 <= m <= x: cnt[m] += 1
    mult = Counter(cnt.values())
    # each m with multiplicity counted twice because of l and -l
    print(f"a={a}, R={R}, x={x:.0e}: {fams} families, {len(cnt)} distinct m, "
          f"multiplicity distribution (pairs +-l counted once): {dict(sorted((k//2, v) for k, v in mult.items()))}")
run(1, 200, 1e10)
run(3, 120, 1e10)
