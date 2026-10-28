"""The two families of Table 3 with the largest deviation, at x = 1e14 (see Section 8)."""
import math, subprocess
from Lfam import L_fam
from fam import cubes_H
from seedsA import setup
x = 1e14
def run(args):
    return [float(z) for z in subprocess.run(["./famcount"] + [str(a) for a in args], capture_output=True, text=True).stdout.split()]
a, r, D = 5, 233, 1213
H = cubes_H(a, r, D); L = r * D; Lf = L_fam(1, H, r, D)[0]
cnt, sharp, inS, bad2, _ = run([1, H, r, D, 1, 1, 1, repr(x)])
main = 32 * Lf * math.sqrt(x / L)
print(f"cubes a=5 r=233 D=1213 x=1e14: #l={int(cnt)} sum={sharp:.0f} main={main:.1f} ratio={sharp/main:.3f} bad2={int(bad2)}", flush=True)
s = setup(1, 4); B, A, c, D0, v, j = (s[k] for k in ('B', 'A', 'c', 'D0', 'v', 'j')); E = 2 ** (2 * j - v)
r, d = 257, 3929; M = (d + c * r) ** 2 + D0 * r * r; H = M >> v; L = r * d; Lf = L_fam(E, H, r, d)[0]
cnt, sharp, inS, bad2, bads = run([E, H, r, d, 0, v - 2, 0, repr(x), B, A])
main = 64 * Lf * math.sqrt(x / (2 ** (v - 2) * E * L))
print(f"triples {{0,1,4}} r=257 d=3929 x=1e14: #l={int(cnt)} sum={sharp:.0f} main={main:.1f} ratio={sharp/main:.3f} bad2={int(bad2)} badsplit={int(bads)}")
