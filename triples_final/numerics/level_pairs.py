"""The pair count P of Lemma 8.4 of triples_final.pdf, computed exactly (Section 14, Remark 13.1).

Notation as in Section 8: N = E H, q = 4 E d, Gamma = Gamma_0(q), Q_N = integral symmetric matrices
g = (a b; b c) with a, c > 0 and ac - b^2 = N, z(g) = (b + i sqrt N)/c, Lambda_N = reduced representatives,
Q^kappa = {g in Q_N : b = 0 (mod E), c = kappa E d (mod 4Ed)}, and z_1, ..., z_I the points z(tau<>zeta)
for zeta in Lambda_N and tau in T_q (cosets Gamma \\ SL_2(Z)) with tau<>zeta in Q^kappa (Lemma 8.1(b)).

    P = sum_{i,i'} #{gamma in Gamma : u(z_i, gamma z_i') <= 1},     u(z,w) = |z-w|^2 / (4 Im z Im w).

Since gamma z_i' = z(gamma<>g_i') and the stabiliser of g_i' is {+-I} (Lemma 8.1(a)),
    P = 2 sum_i #{g in Q^kappa : u(z(g), z_i) <= 1}.                                   (*)
We compute P in two ways.
  Method A (the reduction in the proof of Lemma 8.4, with the dropped condition kept):
      P = 2 sum_{zeta in Lambda_N} sum_{tau : tau<>zeta in Q^kappa} #{w in Q_N : tau<>w in Q^kappa, u(z(w), z(zeta)) <= 1},
      with T_q realised through bottom rows in P^1(Z/4E) x P^1(F_d) (as in the proof of Lemma 8.3).
  Method B: formula (*) directly, enumerating the matrices g in Q^kappa near each z_i.  Here each coset is
      represented by a matrix whose bottom row is a short vector of the lattice {(c,d): c d0 = d c0 (mod q)},
      so that Im z_i is not too small.
We also print I, the diagonal term 2I (i = i', gamma = +-I), the largest number of cosets tau with
tau<>zeta in Q^kappa (Lemma 8.3: at most 12E), the number of all pairs (zeta, w) in Lambda_N x Q_N with
u <= 1 (Lemma 8.4: P <= 192 times this number), and N, N/d, N^(1/2).
Run: python3 level_pairs.py     (about 1 minute)"""
import math
from math import gcd


def egcd(a, b):
    """(g, x, y) with x a + y b = g = gcd(a, b), for a, b >= 0"""
    if b == 0:
        return (a, 1, 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a // b) * y)


def reduced(N):
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


def P1_rows(m, p):
    """bottom rows (c0, d0) mod q = m p representing P^1(Z/m) x P^1(F_p), m a power of 2"""
    A = [(c, 1) for c in range(m)] + [(1, 2 * y) for y in range(m // 2)]
    Bp = [(c, 1) for c in range(p)] + [(1, 0)]
    q = m * p
    inv_m, inv_p = pow(m, -1, p), pow(p, -1, m)
    return [((c1 * p * inv_p + c2 * m * inv_m) % q, (d1 * p * inv_p + d2 * m * inv_m) % q)
            for (c1, d1) in A for (c2, d2) in Bp]


def complete(c, d):
    """a matrix (a, b, c, d) in SL_2(Z) with the given coprime bottom row"""
    sc, sd = (1 if c >= 0 else -1), (1 if d >= 0 else -1)
    g, x, y = egcd(abs(d), abs(c))          # x |d| + y |c| = 1
    assert g == 1
    a, b = x * sd, -y * sc
    assert a * d - b * c == 1
    return (a, b, c, d)


def long_rep(c, d, q):
    """the representative used in Method A: smallest non-negative lift of the bottom row, made coprime"""
    while gcd(c, d) != 1:
        d += q
    return complete(c, d)


def short_rep(c0, d0, q, form):
    """a representative of the same coset whose bottom row (c,d) is short for the binary form `form`"""
    A0, B0, C0 = form
    phi = lambda v: A0 * v[0] ** 2 + 2 * B0 * v[0] * v[1] + C0 * v[1] ** 2
    bil = lambda v, w: A0 * v[0] * w[0] + B0 * (v[0] * w[1] + v[1] * w[0]) + C0 * v[1] * w[1]
    g, x, _ = egcd(c0, q)                    # basis of L = {(c,d) : c d0 = d c0 (mod q)}
    v1, v2 = (g, x * d0), (0, gcd((q // g) * d0, q))
    if phi(v1) > phi(v2):
        v1, v2 = v2, v1
    while True:                              # Lagrange-Gauss reduction for phi
        t = round(bil(v1, v2) / phi(v1))
        v2 = (v2[0] - t * v1[0], v2[1] - t * v1[1])
        if phi(v2) >= phi(v1):
            break
        v1, v2 = v2, v1
    best = None
    for s in range(-6, 7):
        for t in range(-6, 7):
            v = (s * v1[0] + t * v2[0], s * v1[1] + t * v2[1])
            if v != (0, 0) and gcd(v[0], v[1]) == 1 and (best is None or phi(v) < phi(best)):
                best = v
    c, d = best
    assert (c * d0 - d * c0) % q == 0        # same point of P^1(Z/q), hence the same coset
    return complete(c, d)


def act(t, g):
    """t<>g = t g t^T for t = (a0, b0, c0, d0) and g = (A, B, C) = (A B; B C)"""
    a0, b0, c0, d0 = t
    A, B, C = g
    return (a0 * a0 * A + 2 * a0 * b0 * B + b0 * b0 * C,
            a0 * c0 * A + (a0 * d0 + b0 * c0) * B + b0 * d0 * C,
            c0 * c0 * A + 2 * c0 * d0 * B + d0 * d0 * C)


def in_Qk(g, E, d, kappa):
    return g[1] % E == 0 and (g[2] - kappa * E * d) % (4 * E * d) == 0


def near(N, g1, E=None, d=None, kappa=None):
    """all g in Q_N with u(z(g), z(g1)) <= 1; if d is given, only those in Q^kappa"""
    a1, b1, c1 = g1
    res = []
    lo = max(1, int(c1 * (3 - 2 * math.sqrt(2))) - 1)
    hi = int(c1 * (3 + 2 * math.sqrt(2))) + 1
    if d is None:
        cs, bstep = range(lo, hi + 1), 1
    else:
        mod = 4 * E * d
        cs, bstep = range(lo + (kappa * E * d - lo) % mod, hi + 1, mod), E
    for c in cs:
        S = 4 * N * c * c1 - N * (c - c1) ** 2
        if S < 0:
            continue
        W = math.isqrt(S)
        bmin = -((-(b1 * c - W)) // c1)
        bmax = (b1 * c + W) // c1
        bmin += (-bmin) % bstep
        for b in range(bmin, bmax + 1, bstep):
            if (b * b + N) % c == 0 and (b * c1 - b1 * c) ** 2 + N * (c - c1) ** 2 <= 4 * N * c * c1:
                res.append(((b * b + N) // c, b, c))
    return res


def run(E, H, d, kappa):
    N, q = E * H, 4 * E * d
    lam = reduced(N)
    rows = P1_rows(4 * E, d)
    assert len(rows) == 6 * E * (d + 1)
    reps = [long_rep(c, dd, q) for (c, dd) in rows]
    PA = PB = I = ntau_max = allpairs = 0
    for z in lam:
        W = near(N, z)
        allpairs += len(W)
        ntau = 0
        for (c0, d0), t in zip(rows, reps):
            if not in_Qk(act(t, z), E, d, kappa):
                continue
            ntau += 1
            PA += sum(1 for w in W if in_Qk(act(t, w), E, d, kappa))          # Method A
            gi = act(short_rep(c0, d0, q, z), z)                                # Method B
            assert in_Qk(gi, E, d, kappa)                                       # Q^kappa is Gamma-invariant
            PB += len(near(N, gi, E, d, kappa))
        I += ntau
        ntau_max = max(ntau_max, ntau)
    PA, PB = 2 * PA, 2 * PB
    assert PA == PB, (PA, PB)
    line = (f"E={E} H={H} d={d} kappa={kappa}: N={N}, N/d={N/d:.1f}, N^(1/2)={math.sqrt(N):.1f}, #Lambda_N={len(lam)}, "
            f"I={I}, max#tau={ntau_max} (<= 12E = {12*E}), all pairs={allpairs} (/N={allpairs/N:.2f}); "
            f"P={PA} (methods A and B agree), 2I={2*I}, P/(2I)={PA/(2*I):.3f}, P/N={PA/N:.4f}")
    print(line)
    return line


if __name__ == "__main__":
    out = [run(E, H, d, kappa) for (E, H, d) in [(8, 1057, 89), (8, 285, 53), (8, 3869, 181)] for kappa in (1, 3)]
    open("results_level_pairs.txt", "w").write("\n".join(out) + "\n")
