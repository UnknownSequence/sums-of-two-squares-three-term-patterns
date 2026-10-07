r"""
End-to-end illustration of GM-I Theorem 8.1 in the simplest case H=1, alpha_1 = I, alpha_2 = delta_{z0}:
    D(q,Y) = sum_{gamma in Gamma_0(q)/{+-1}} f(Re gamma z0) g(Im gamma z0 / Y) - (int f)(int g(s) ds/s^2) / (Y vol(Gamma_0(q)\H)).
Here F(g) = f(x(g)) g(y(g)/Y) is right K-invariant with X = 1 (x-support [-0.4,0.4]), and Theorem 8.1 with
Z_1 = q, Z_2 = 1, Z_0 = max(1, (1/Y + 1)/q) predicts |D| << (q/Y)^{o(1)} Y^{-1/2} Z_0^theta (the two kernels are O(1)
here, cf. [II, Lemma 6.3]).  We print D * Y^{1/2}.
"""
import numpy as np
from math import gcd, pi

def bumpf(t):
    t = np.asarray(t, dtype=float)
    out = np.zeros_like(t)
    m = np.abs(t) < 1
    out[m] = np.exp(-1.0 / (1 - t[m] ** 2))
    return out

def f(x):          # supported on [-0.4, 0.4]
    return bumpf(x / 0.4)

def g(s):          # supported on [1, 2]
    return bumpf(2 * s - 3)

xs = np.linspace(-0.4, 0.4, 200001); int_f = np.trapezoid(f(xs), xs)
ss = np.linspace(1, 2, 200001); int_g = np.trapezoid(g(ss) / ss ** 2, ss)

def index(q):
    r, n, p = q, 1, 2
    m = q
    res = q
    primes = []
    while p * p <= m:
        if m % p == 0:
            primes.append(p)
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        primes.append(m)
    for p in primes:
        res = res * (p + 1) // p
    return res

def D(q, Y, z0=complex(0.2137, 0.9123)):
    x0, y0 = z0.real, z0.imag
    total = 0.0
    R2max = y0 / Y           # |c z0 + d|^2 <= y0 / Y
    cmax = int(np.sqrt(R2max) / y0) + 1
    for c in range(q, cmax + 1, q):
        # |c z0 + d|^2 = (c x0 + d)^2 + (c y0)^2 in [y0/(2Y), y0/Y]
        rem_hi = R2max - (c * y0) ** 2
        if rem_hi < 0:
            continue
        rem_lo = max(0.0, R2max / 2 - (c * y0) ** 2)
        dlo = int(np.floor(-c * x0 - np.sqrt(rem_hi))) - 1
        dhi = int(np.ceil(-c * x0 + np.sqrt(rem_hi))) + 1
        for d in range(dlo, dhi + 1):
            w = (c * x0 + d) ** 2 + (c * y0) ** 2
            if w > R2max or w < R2max / 2:
                continue
            if gcd(c, d) != 1:
                continue
            a = pow(d, -1, c) if c > 1 else 0
            re = a / c - (c * x0 + d) / (c * w)
            im = y0 / w
            re = re - np.floor(re + 0.5)  # periodise: sum_n f(re+n) = f({re}) since supp f in [-0.4,0.4]
            total += f(re) * g(im / Y)
    vol = pi / 3 * index(q)
    main = int_f * int_g / (Y * vol)
    return total - main, main

print(f"{'q':>5} {'Y':>9} {'main term':>12} {'D':>10} {'D*Y^(1/2)':>10}")
rows = []
for q in [1, 7, 101]:
    for Y in [1e-2, 1e-3, 1e-4, 1e-5]:
        d, m = D(q, Y)
        rows.append((q, Y, m, d, d * np.sqrt(Y)))
        print(f"{q:>5} {Y:>9.0e} {m:>12.2f} {d:>10.3f} {d*np.sqrt(Y):>10.4f}")
with open("results_end_to_end.txt", "w") as fh:
    fh.write(f"{'q':>5} {'Y':>9} {'main term':>12} {'D':>10} {'D*Y^(1/2)':>10}\n")
    for r in rows:
        fh.write(f"{r[0]:>5} {r[1]:>9.0e} {r[2]:>12.2f} {r[3]:>10.3f} {r[4]:>10.4f}\n")
