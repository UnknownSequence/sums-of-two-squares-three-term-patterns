"""Table of Section 9: smoothed and sharp weighted counts along the families versus the main term of
Proposition 7.1.  Needs ./mainterm (gcc -O2 -o mainterm mainterm.c -lm).  Run: python3 table.py [x]

Good primes (Section 4): d = d0 (mod 2^J), d > d1 = 8(|c| + B), and neither m_d nor m_d/3 a perfect square.
mainterm sums over u >= 1 only, i.e. over l >= 1, which is half of Sigma_d(x); the predictions below are
therefore half of the main term 32 c_F L_d 2^{-j} sqrt(x/d) of Proposition 7.1."""
import math, subprocess, sys
from Ld import L_d
from seedsA import setup, v2

x = float(sys.argv[1]) if len(sys.argv) > 1 else 1e12
F = lambda t: math.exp(-0.05 / ((t - 0.5) * (1 - t))) if 0.5 < t < 1 else 0.0
NN = 400000
cF = sum(F(0.5 + (i + 0.5) * 0.5 / NN) / math.sqrt(0.5 + (i + 0.5) * 0.5 / NN) for i in range(NN)) * 0.5 / NN

def isprime(n):
    return n > 1 and all(n % p for p in range(2, int(n ** 0.5) + 1))

def is_square(n):
    return n >= 0 and math.isqrt(n) ** 2 == n

def good_prime_above(s, lo):
    d1 = 8 * (abs(s['c']) + s['B'])
    lo = max(lo, d1 + 1)
    d = lo + ((s['d0'] - lo) % 2 ** s['J'])
    while True:
        m = d * d + 2 * s['c'] * d + s['B'] ** 2
        assert m == (d + s['c']) ** 2 + s['D0'] and v2(m) == s['v']        # Proposition 3.2 with u = 0
        if isprime(d) and not is_square(m) and not (m % 3 == 0 and is_square(m // 3)):
            return d
        d += 2 ** s['J']

print(f"x = {x:.0e}; F(t) = exp(-1/(20(t-1/2)(1-t))) on (1/2,1), c_F = {cF:.6f}")
for (a, b) in [(1, 2), (1, 3), (2, 3), (1, 4), (5, 8)]:
    s = setup(a, b)
    for lo in (0, 1000):
        d = good_prime_above(s, lo)
        m = (d + s['c']) ** 2 + s['D0']
        L, _, _ = L_d(d, m)
        out = subprocess.run(["./mainterm", str(s['B']), str(s['A']), str(d), f"{x:.0f}", str(s['J']),
                              str(s['d0']), str(s['j'])], capture_output=True, text=True).stdout
        kv = dict(t.split("=") for t in out.split() if "=" in t)
        sharp, smooth = float(kv["sharp"]), float(kv["smooth"])
        p_sharp = 32 * L / 2 ** s['j'] * math.sqrt(x / d)
        p_smooth = 16 * cF * L / 2 ** s['j'] * math.sqrt(x / d)
        print(f"{{0,{a},{b}}} B={s['B']} A={s['A']} (v,J,d0,j)=({s['v']},{s['J']},{s['d0']},{s['j']}) d={d:5d} "
              f"L_d={L:.4f} #u={kv['count']:>7} smooth={smooth:9.1f} pred={p_smooth:9.1f} "
              f"ratio={smooth/p_smooth:.3f} | sharp={sharp:9.0f} pred={p_sharp:9.1f} ratio={sharp/p_sharp:.3f} | "
              f"T in S: {kv['inS']}, split failures {kv['badsplit']}, 2-adic failures {kv['bad2adic']}")
