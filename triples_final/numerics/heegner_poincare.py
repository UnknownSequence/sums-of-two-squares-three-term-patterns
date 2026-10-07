r"""
Check of the Heegner--Poincare identity (9.2) (Lemma 9.2 of triples_final.pdf; Section 14):

  sum_{mu = kappa d (4d), K <= mu < 2K} sum_{nu mod mu, E nu^2 + H = 0 (mu)} e(h nu / mu)
      =  sum_{i} sum_{gamma in Gamma_infty \ Gamma_0(q)} g(Im gamma z_i) e(h Re gamma z_i),

where z_i runs over representatives of the Gamma_0(q)-orbits on Q^kappa = { [[a,b],[b,c]] : ac-b^2 = N = EH,
b = 0 (E), c = kappa E d (4Ed) } (realised as tau<>z, z reduced, tau in Gamma_0(q)\SL_2(Z)), and
g(y) = 1_{[K,2K)}(sqrt(N)/(E y)), a sharp weight (the proof of (9.2) does not use smoothness).  In terms of forms, gamma<>g has lower-right entry
c'' = a' c^2 + 2 b' c d + c' d^2 (bottom row (c,d) of gamma) and Re z(gamma<>g) = b''/c''.
Both sides are computed exactly (floating point only in the exponentials).
Run: python3 heegner_poincare.py
"""
import math, cmath
from math import gcd

def egcd(a, b):
    if b == 0:
        return (a, 1, 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a // b) * y)

def reduced(N):
    """reduced positive definite forms [a,2b,c] (a c - b^2 = N): |2b| <= c <= a, one per SL_2(Z)-class"""
    out = []
    for c in range(1, math.isqrt(4 * N // 3) + 2):
        for b in range(-(c // 2), c // 2 + 1):
            if (b * b + N) % c == 0:
                a = (b * b + N) // c
                if a >= c:
                    if (2 * abs(b) == c or a == c) and b < 0:
                        continue
                    out.append((a, b, c))
    return out

def cosets(E, d):
    """representatives (a0,b0,c0,d0) of Gamma_0(q)\\SL_2(Z), q = 4Ed, via bottom rows in P^1(Z/4E) x P^1(F_d)"""
    m = 4 * E
    A = [(c, 1) for c in range(m)] + [(1, 2 * y) for y in range(m // 2)]
    Bp = [(c, 1) for c in range(d)] + [(1, 0)]
    q = m * d
    out = []
    inv_m = pow(m, -1, d); inv_p = pow(d, -1, m)
    for (c1, d1) in A:
        for (c2, d2) in Bp:
            c = (c1 * d * inv_p + c2 * m * inv_m) % q
            dd = (d1 * d * inv_p + d2 * m * inv_m) % q
            while gcd(c, dd) != 1:
                dd += q
            g, x, y = egcd(dd, c)
            a0, b0 = x, -y
            assert a0 * dd - b0 * c == 1
            out.append((a0, b0, c, dd))
    return out

def act(t, f):
    """t<>f = t f t^T for t = (a0,b0,c0,d0), f = (a,b,c) meaning [[a,b],[b,c]]"""
    a0, b0, c0, d0 = t
    a, b, c = f
    A2 = a0 * a0 * a + 2 * a0 * b0 * b + b0 * b0 * c
    B2 = a0 * c0 * a + (a0 * d0 + b0 * c0) * b + b0 * d0 * c
    C2 = c0 * c0 * a + 2 * c0 * d0 * b + d0 * d0 * c
    return (A2, B2, C2)

def e(x):
    return cmath.exp(2j * math.pi * x)

def lhs(E, H, d, kappa, K, hs):
    res = {h: 0j for h in hs}
    cnt = 0
    for mu in range(K, 2 * K):
        if (mu - kappa * d) % (4 * d):
            continue
        nus = [nu for nu in range(mu) if (E * nu * nu + H) % mu == 0] if mu < 2000 else \
              [int(v) for v in __import__("numpy").nonzero((E * __import__("numpy").arange(mu, dtype=__import__("numpy").int64) ** 2 + H) % mu == 0)[0]]
        for nu in nus:
            cnt += 1
            for h in hs:
                res[h] += e(h * nu / mu)
    return res, cnt

def rhs(E, H, d, kappa, K, hs):
    N = E * H; q = 4 * E * d
    reps = []
    for z in reduced(N):
        for t in cosets(E, d):
            g = act(t, z)
            if g[1] % E == 0 and (g[2] - kappa * E * d) % (4 * E * d) == 0:
                reps.append(g)
    res = {h: 0j for h in hs}
    cnt = 0
    lo, hi = E * K, 2 * E * K          # c'' = E mu in [EK, 2EK)
    for (a1, b1, c1) in reps:
        # gamma = [[ag,bg],[cg,dg]] in Gamma_0(q) modulo Gamma_infty: cg >= 0, q | cg, gcd(cg,dg) = 1,
        # (cg,dg) up to sign; c'' = a1 cg^2 + 2 b1 cg dg + c1 dg^2.
        cmax = math.isqrt((hi * c1) // N + 1) + 1          # from N cg^2 <= c1 * c''
        for cg in range(0, cmax + 1, q):
            if cg == 0:
                cands = [(0, 1)]
            else:
                # c1*c'' = (c1 dg + b1 cg)^2 + N cg^2 <= c1*hi
                rem = c1 * hi - N * cg * cg
                if rem < 0:
                    continue
                w = math.isqrt(rem)
                dmin = (-b1 * cg - w) // c1 - 1
                dmax = (-b1 * cg + w) // c1 + 1
                cands = [(cg, dg) for dg in range(dmin, dmax + 1) if gcd(cg, dg) == 1]
            for (cg, dg) in cands:
                cpp = a1 * cg * cg + 2 * b1 * cg * dg + c1 * dg * dg
                if not (lo <= cpp < hi):
                    continue
                if cg == 0:
                    ag, bg = 1, 0
                else:
                    gg, x, y = egcd(dg, cg)
                    ag, bg = x, -y          # ag*dg - bg*cg = 1
                bpp = ag * cg * a1 + (ag * dg + bg * cg) * b1 + bg * dg * c1
                cnt += 1
                for h in hs:
                    res[h] += e(h * bpp / cpp)
    return res, cnt, len(reps)

if __name__ == "__main__":
    out = []
    hs = [1, 2, 3, 7, 13]
    for (E, H, d) in [(8, 1057, 89), (8, 285, 53)]:
        for kappa in (1, 3):
            for K in [600, 2500, 20000, 60000]:
                L, nl = lhs(E, H, d, kappa, K, hs)
                R, nr, nreps = rhs(E, H, d, kappa, K, hs)
                err = max(abs(L[h] - R[h]) for h in hs)
                line = (f"E={E} H={H} d={d} kappa={kappa} K={K}: #orbits={nreps}, #(mu,nu)={nl}, #(i,gamma)={nr}; "
                        f"S_1={L[1].real:+.6f}{L[1].imag:+.6f}i; max_h |LHS-RHS| = {err:.2e}")
                print(line); out.append(line)
    open("results_heegner_poincare.txt", "w").write("\n".join(out) + "\n")
