"""Main-term check (Section 8 of the note): sharp sums of r(T) along rescaled families versus the main term
64 c_Lambda Lf sqrt(x/(kappa0 E L)) of Proposition 4.4 (sharp version, c_F replaced by 2).
Run: python3 table.py 1e12      (needs ./famcount)"""
import sys, math, subprocess
from fam import is_prime, good_cubes_pair, cubes_H
from Lfam import L_fam
from seedsA import setup
x = float(sys.argv[1]) if len(sys.argv) > 1 else 1e12
def run(E, H, p1, p2, odd, s, t, BA=None):
    args = ["./famcount", str(E), str(H), str(p1), str(p2), str(odd), str(s), str(t), repr(x)]
    if BA: args += [str(BA[0]), str(BA[1])]
    out = subprocess.run(args, capture_output=True, text=True).stdout.split()
    return [float(z) for z in out]
rows = []
def first_cubes_pair(a, rmin):
    r = rmin
    while True:
        if is_prime(r) and r % 8 == 1:
            for D in range(a * r, 2 * a * r + 1):
                if good_cubes_pair(a, r, D): return r, D
        r += 1
print(f"x = {x:.0e}")
print("case            r      D/d      L          H     #l    sum r(T)   main term   ratio  inS  bad2  badsplit")
for a in (1, 3, 5, 7):
    for rmin in (40, 200):
        r, D = first_cubes_pair(a, rmin)
        H = cubes_H(a, r, D); L = r * D
        Lf, _, _ = L_fam(1, H, r, D)
        cnt, sharp, inS, bad2, _ = run(1, H, r, D, 1, 1, 1)
        main = 64 * 0.5 * Lf * math.sqrt(x / L)
        print(f"cubes a={a:<4d} {r:6d} {D:6d} {L:9d} {H:10d} {int(cnt):7d} {sharp:11.0f} {main:11.1f} {sharp/main:7.3f} {int(inS):6d} {int(bad2):3d}")
for (pa, pb) in [(1, 2), (1, 3), (2, 3), (1, 4)]:
    s = setup(pa, pb); B, A, c, D0, v, J, j, d0 = (s[k] for k in ('B', 'A', 'c', 'D0', 'v', 'J', 'j', 'd0'))
    E = 2 ** (2 * j - v); C0 = abs(c) + math.isqrt(abs(D0)) + 2
    for rmin in (40, 200):
        r = rmin
        while not (is_prime(r) and (r - 1) % 2 ** J == 0): r += 1
        d = C0 * r + ((d0 - C0 * r) % 2 ** J)
        while True:
            M = (d + c * r) ** 2 + D0 * r * r
            H = M >> v; N = E * H
            if is_prime(d) and d != r and math.isqrt(N) ** 2 != N and not (N % 3 == 0 and math.isqrt(N // 3) ** 2 * 3 == N):
                break
            d += 2 ** J
        L = r * d
        Lf, _, _ = L_fam(E, H, r, d)
        cnt, sharp, inS, bad2, bads = run(E, H, r, d, 0, v - 2, 0, (B, A))
        main = 64 * Lf * math.sqrt(x / (2 ** (v - 2) * E * L))
        print(f"triples {{0,{pa},{pb}}} {r:5d} {d:6d} {L:9d} {H:10d} {int(cnt):7d} {sharp:11.0f} {main:11.1f} {sharp/main:7.3f} {int(inS):6d} {int(bad2):3d} {int(bads):4d}")
