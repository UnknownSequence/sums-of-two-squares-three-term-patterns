"""Table 1 of Section 9: weighted counts along T_d(u) versus the main term of Proposition 7.1.
Needs the compiled ./mainterm (gcc -O2 -o mainterm mainterm.c -lm).  Run: python3 table.py [x]"""
import math, subprocess, sys
from Ld import L_d, params
from seeds import seed

x = float(sys.argv[1]) if len(sys.argv) > 1 else 1e12
F = lambda t: math.exp(-0.05 / ((t - 0.5) * (1 - t))) if 0.5 < t < 1 else 0.0
NN = 400000
cF = sum(F(0.5 + (i + 0.5) * 0.5 / NN) / math.sqrt(0.5 + (i + 0.5) * 0.5 / NN) for i in range(NN)) * 0.5 / NN
rows = [(1, 2, [5, 37, 53]), (1, 3, [5, 197]), (1, 4, [97, 257]), (5, 8, [41, 137]), (2, 3, [1093])]
print(f"x = {x:.0e}, c_F = {cF:.6f} for the smooth weight")
for a, b, ds in rows:
    s = seed(a, b)
    J, d0, u0 = s['J'], s['d0'], s['u0']
    for d in ds:
        kappa, g, c, m = params(a, b, d)
        L, _, _ = L_d(d, m)
        out = subprocess.run(["./mainterm", str(a), str(b), str(d), f"{x:.0f}", str(J), str(d0), str(u0)],
                             capture_output=True, text=True).stdout
        kv = dict(t.split("=") for t in out.split() if "=" in t)
        sharp, smooth = float(kv["sharp"]), float(kv["smooth"])
        p_sharp = 16 * math.sqrt(2 * kappa) / 2 ** J * L * math.sqrt(x / d)   # F = 1_[0,1], c_F = 2
        p_smooth = 8 * math.sqrt(2 * kappa) * cF / 2 ** J * L * math.sqrt(x / d)
        print(f"{{0,{a},{b}}} (J,d0,u0)=({J},{d0},{u0}) d={d:5d} L_d={L:.4f} #u={kv['count']:>7} "
              f"sharp={sharp:9.0f} pred={p_sharp:9.0f} ratio={sharp/p_sharp:.3f} | "
              f"smooth={smooth:9.1f} pred={p_smooth:9.1f} ratio={smooth/p_smooth:.3f} | "
              f"n in S_ab: {kv['inS']}, failures of Lemma 2.2: {kv['badsplit']}, non-integral T: {kv['nonint']}")
