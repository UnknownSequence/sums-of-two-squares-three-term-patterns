"""2-adic set-up of Sections 2-3 of triples_final.pdf (Lemma 2.3 with Table 2, Lemma 3.1, Proposition 3.2),
with checks (Section 14, Table 3).

For a pattern {0,a,b} with a or b odd, Lemma 2.3 chooses an automatic pair with odd difference B and
the offset A' of the third element (relative to the smaller element P of the pair).  Lemma 3.1 builds
n_* in Z_2 with X_* = 2 n_* + B = 1 (mod 4), n_*(n_*+B) a non-zero square in Q_2 and n_* + A' in N.
Then d_* = X_* - 2 sqrt(n_*(n_*+B)), v = 2 + v_2(n_* + A'), and for d = d_* (mod 2^J), J = v+2, and
u = 0 (mod 2^j), 2j >= v+2, Proposition 3.2 asserts v_2(u^2+m_d) = v and (u^2+m_d)/2^v = d (mod 4).
Run: python3 seedsA.py"""
import random

def v2(n):
    if n == 0:
        return 10 ** 9
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v

def inN(z):
    if z == 0:
        return False
    return (z >> v2(z)) % 4 == 1 if z > 0 else ((-z) >> v2(-z)) % 4 == 3

def choose_pair(a, b):
    """Lemma 2.3 (Table 2): returns (B, A', which) with B odd and (B, A') admissible."""
    def admissible(B, A):
        return not ((B % 4 == 1 and A % 4 == 3) or (B % 4 == 3 and A % 4 == 2))
    if a % 2 == 1 and b % 2 == 0:
        cands = [(a, b, 'pair (n,n+a), detect n+b'), (b - a, -a, 'pair (n+a,n+b), detect n')]
    elif a % 2 == 0 and b % 2 == 1:
        cands = [(b, a, 'pair (n,n+b), detect n+a'), (b - a, -a, 'pair (n+a,n+b), detect n')]
    elif a % 2 == 1 and b % 2 == 1:
        cands = [(a, b, 'pair (n,n+a), detect n+b'), (b, a, 'pair (n,n+b), detect n+a')]
    else:
        raise ValueError("a and b both even: reduce first (Lemma 2.1)")
    for B, A, w in cands:
        if admissible(B, A):
            return B, A, w
    raise AssertionError("no admissible choice", a, b)

def adjust(c, o, t):
    """odd o1 = c (mod 8) such that o1 + o = 2^w * (1 mod 4) for some w>=2 (case o = 3, c = 1 mod 4)"""
    for o1 in range(1, 64, 2):
        if (o1 - c) % 8:
            continue
        s = o1 + o
        if s % 4 == 0 and inN(s):
            return o1
    raise AssertionError

def nstar(B, A):
    """Lemma 3.1, explicit construction."""
    assert B % 2 == 1
    if B % 4 == 1:                       # n even, n = 4^s o1, o1(n+B) = 1 (mod 8)
        cfun = lambda s: (5 * B) % 8 if s == 1 else B % 8
        if A % 2 == 1:
            assert A % 4 == 1
            s, o1 = 2, cfun(2)
        else:
            t, o = v2(A), A >> v2(A)
            if o % 4 == 1:
                s = max(2, (t + 3) // 2); o1 = cfun(s)
            elif t % 2 == 1:
                s = (t + 1) // 2; o1 = cfun(s)
            else:
                s = t // 2; o1 = adjust(cfun(s), o % 64, t)
        n = 4 ** s * o1
    else:                                # n odd, n + B = 4^s o2, n o2 = 1 (mod 8)
        cfun = lambda s: (3 * B) % 8 if s == 1 else (-B) % 8
        C = A - B
        if C % 2 == 1:
            assert A % 4 == 0
            s, o2 = 2, cfun(2)
        else:
            t, o = v2(C), C >> v2(C)
            if o % 4 == 1:
                s = max(2, (t + 3) // 2); o2 = cfun(s)
            elif t % 2 == 1:
                s = (t + 1) // 2; o2 = cfun(s)
            else:
                s = t // 2; o2 = adjust(cfun(s), o % 64, t)
        n = 4 ** s * o2 - B
    return n

def is_square_2adic(z):
    if z == 0:
        return False
    v = v2(z)
    o = z >> v if z > 0 else -((-z) >> v)
    return v % 2 == 0 and o % 8 == 1

def sqrt2(t, K):
    """a 2-adic square root of the square t, modulo 2^(K - v/2 - 2)"""
    v = v2(t)
    s = (t >> v) % 2 ** K
    r = 1
    for k in range(3, K - v):
        if (r * r - s) % 2 ** (k + 1):
            r += 2 ** (k - 1)
    return (r << (v // 2)) % 2 ** K

def setup(a, b, K=60):
    B, A, which = choose_pair(a, b)
    n = nstar(B, A)
    X = 2 * n + B
    assert X % 4 == 1 and is_square_2adic(n * (n + B)) and inN(n + A), (a, b, B, A, n)
    root = 2 * sqrt2(n * (n + B), K)
    dstar = (X - root) % 2 ** (K - 8)
    T = n + A
    v = 2 + v2(T)
    J = v + 2
    j = (v + 3) // 2
    c = 2 * A - B
    D0 = 4 * A * (B - A)
    d0 = dstar % 2 ** J
    assert d0 % 4 == 1
    return dict(B=B, A=A, which=which, n=n, X=X, T=T, v=v, J=J, j=j, d0=d0, c=c, D0=D0)

def check(s, trials=40):
    for _ in range(trials):
        d = s['d0'] + 2 ** s['J'] * random.randint(0, 10 ** 8)
        u = 2 ** s['j'] * random.randint(-10 ** 8, 10 ** 8)
        m = (d + s['c']) ** 2 + s['D0']
        Q = u * u + m
        if v2(Q) != s['v'] or ((Q >> s['v']) - d) % 4:
            return False
    return True

if __name__ == "__main__":
    random.seed(3)
    ok = 0
    for b in range(2, 101):
        for a in range(1, b):
            if a % 2 == 0 and b % 2 == 0:
                continue
            s = setup(a, b)
            assert check(s), (a, b, s)
            ok += 1
    print("patterns {0,a,b}, b <= 100, a or b odd: all", ok, "checked")
    for (a, b) in [(1, 2), (1, 3), (2, 3), (1, 4), (3, 8), (5, 8)]:
        s = setup(a, b)
        print(f"{{0,{a},{b}}}: B={s['B']}, A'={s['A']} ({s['which']}), n_*={s['n']}, v={s['v']}, "
              f"(J,d0,j)=({s['J']},{s['d0']},{s['j']}), m_d=(d+{s['c']})^2+({s['D0']})")
