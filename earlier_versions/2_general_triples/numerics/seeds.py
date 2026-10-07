"""2-adic seeds of Section 3 (Lemmas 3.1-3.3, Proposition 3.4), with checks.

For each pattern {0,a,b} with 0<a<b<=60, not of the type 4|b, a=2 (mod 4) (Lemma 3.5):
  * n_* is computed by the case analysis of Lemma 3.2 (built on Lemma 3.1);
  * A_*, u_* with X_*^2 - g^2 = A_*^2 + u_*^2 and X_* - A_* = 1 (mod 4) are found by a search
    over small A_* and a 2-adic square root (Lemma 3.3 guarantees existence);
  * J = v+3 with v = v_2(2 kappa T_*), d_0 = X_*-A_* and u_0 = u_* modulo 2^J, as in Prop. 3.4;
  * the conclusion of Proposition 3.4 is tested on random elements of the classes.
Run: python3 seeds.py
"""
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
    """z is a non-zero 2-adic norm from Q_2(i): odd part = 1 (mod 4)."""
    if z == 0:
        return False
    return (z >> v2(z)) % 4 == 1 if z > 0 else ((-z) >> v2(-z)) % 4 == 3

def lemma_S(delta, eps):
    """Lemma 3.1: odd delta, eps in {0,1}: y = eps (mod 2) with y, y+delta in N."""
    assert delta % 2 == 1
    if eps == 1:
        y = (2 - delta) % 8 if delta % 4 == 1 else (4 - delta) % 16
        assert y % 4 == 1 and inN(y) and inN(y + delta)
        return y
    y = lemma_S(-delta, 1) - delta
    assert y % 2 == 0 and inN(y) and inN(y + delta)
    return y

def nstar(a, b):
    """Lemma 3.2."""
    if b % 4 == 0:
        assert a % 4 != 2
        return 1 if a % 4 == 0 else lemma_S(a, 1)
    if b % 4 == 2:
        if a % 2 == 1:
            return 2 * lemma_S(b // 2, ((1 - a) // 2) % 2)
        return 2 * nstar(a // 2, b // 2)
    if a % 4 == 0:
        return lemma_S(b, 1)
    if a % 4 == 2:
        return 2 * lemma_S(a // 2, ((1 - b) // 2) % 2)
    if (a - b) % 4 == 0:
        return lemma_S(a, 0)
    return 2 * lemma_S((b - a) // 2, ((1 + a) // 2) % 2) - a

def is_sq2(z, K):
    """is z a square in Z_2, judged modulo 2^K"""
    z %= 2 ** K
    if z == 0:
        return True
    v = v2(z)
    return v % 2 == 0 and v < K - 2 and (z >> v) % 8 == 1

def sqrt2(t, K):
    """a 2-adic square root of t modulo 2^(K - v/2 - 2), t a square"""
    t %= 2 ** K
    if t == 0:
        return 0
    v = v2(t)
    s = t >> v
    r = 1
    for k in range(3, K - v):
        if (r * r - s) % 2 ** (k + 1):
            r += 2 ** (k - 1)
    return (r << (v // 2)) % 2 ** K

def seed(a, b, K=40):
    kappa = 1 if b % 2 == 0 else 2
    g = kappa * b // 2
    c = kappa * a - g
    n = nstar(a, b)
    assert inN(n) and inN(n + a) and inN(n + b)
    X = kappa * n + g
    assert X % 2 == 1
    Z = X * X - g * g
    for A in range(-64, 65):
        if (X - A) % 4 == 1 and is_sq2(Z - A * A, K):
            u = sqrt2(Z - A * A, K)
            T = n + a
            v = v2(2 * kappa * T)
            J = v + 3
            return dict(kappa=kappa, g=g, c=c, n=n, X=X, A=A, u=u, T=T, v=v, J=J,
                        d0=(X - A) % 2 ** J, u0=u % 2 ** J)
    return None

def check_classes(a, b, s, trials=30):
    kappa, c, J, v = s['kappa'], s['c'], s['J'], s['v']
    for _ in range(trials):
        d = s['d0'] + 2 ** J * random.randint(0, 10 ** 6)
        u = s['u0'] + 2 ** J * random.randint(0, 10 ** 6)
        Q = u * u + (d + c) ** 2 + kappa * kappa * a * (b - a)
        if v2(Q) != v or ((Q >> v) - d) % 4 != 0 or d % 4 != 1:
            return False
    return True

if __name__ == "__main__":
    random.seed(1)
    ok, bad = 0, []
    for b in range(2, 61):
        for a in range(1, b):
            if b % 4 == 0 and a % 4 == 2:
                continue
            s = seed(a, b)
            if s is None or not check_classes(a, b, s):
                bad.append((a, b))
            else:
                ok += 1
    print("patterns with b<=60 checked:", ok, " failures:", bad)
    for (a, b) in [(1, 2), (1, 3), (1, 4), (5, 8), (2, 3)]:
        s = seed(a, b)
        print(f"{{0,{a},{b}}}: n_*={s['n']} X_*={s['X']} A_*={s['A']} (J,d0,u0)=({s['J']},{s['d0']},{s['u0']})")
