"""Check of Steps 1-3 in the proof of Proposition 6.3.

Steps 1-2: for odd mu, S_mu(h) = sum_{w mod mu, 2^{2J}w^2+m = 0 (mu)} e(hw/mu), and
   Xi = sum_{M < mu <= 2M, d | mu, mu/d = gamma (2^J)} S_mu(h)
equals the form-side expression of Step 2 (with beta = 1): one half of the sum over reduced phi of
determinant Delta = 2^{2J+2} m and primitive (R,S), S >= 1, subject to conditions (i)-(iii), of
e(-2h(AR+BS)/(S phi(R,S))) e(2h Rbar/S).
Step 3: for fixed phi and S, admissibility of R depends only on R mod L = 2^{3J+2} d; if d does not
divide S there are at most 2^{3J+3} admissible classes; if d | S, admissible R exist only if d | A.
Run: python3 weyl_check.py"""
import cmath, random
from math import gcd, isqrt, pi
from gauss_check import reduced_forms, z_of

def e(t):
    return cmath.exp(2j * pi * t)

def xi_direct(J, d, m, gamma, h, M):
    tot = 0
    for mu in range(M + 1, 2 * M + 1):
        if mu % d or ((mu // d) - gamma) % 2 ** J:
            continue
        tot += sum(e(h * w / mu) for w in range(mu) if (2 ** (2 * J) * w * w + m) % mu == 0)
    return tot

def admissible(A, B, C, R, S, J, d, gamma):
    phi = A * R * R + 2 * B * R * S + C * S * S
    q = 2 ** (2 * J + 2) * d
    return (phi % q == 0 and ((phi // q) - gamma) % 2 ** J == 0
            and z_of(A, B, C, R, S) % 2 ** (2 * J + 1) == 0)

def xi_forms(J, d, m, gamma, h, M):
    Det = 2 ** (2 * J + 2) * m
    lo, hi = 2 ** (2 * J + 2) * M, 2 ** (2 * J + 3) * M
    tot = 0
    for (A, B, C) in reduced_forms(Det):
        assert A < lo                                   # hence S != 0 below
        S = 1
        while Det * S * S <= A * hi:
            w = isqrt(A * hi - Det * S * S)             # |AR+BS| <= w
            for R in range((-w - B * S) // A - 1, (w - B * S) // A + 2):
                phi = A * R * R + 2 * B * R * S + C * S * S
                if not (lo < phi <= hi) or gcd(R, S) != 1 or not admissible(A, B, C, R, S, J, d, gamma):
                    continue
                Rbar = pow(R % S, -1, S) if S > 1 else 0
                tot += e(-2 * h * (A * R + B * S) / (S * phi)) * e(2 * h * Rbar / S)
            S += 1
    return tot / 2

def step3(J, d, m, gamma, trials=6):
    Det = 2 ** (2 * J + 2) * m
    L = 2 ** (3 * J + 2) * d
    worst = 0
    for (A, B, C) in reduced_forms(Det):
        for S in random.sample(range(1, 60), trials) + [d, 2 * d]:
            cls = set()
            for R0 in range(L):
                if gcd(R0, S) != 1:
                    continue
                adm = admissible(A, B, C, R0, S, J, d, gamma)
                for _ in range(2):                      # same answer for R = R0 (mod L), (R,S) = 1
                    R = R0 + L * random.randint(1, 50)
                    if gcd(R, S) == 1:
                        assert admissible(A, B, C, R, S, J, d, gamma) == adm, "not periodic mod L"
                if adm:
                    cls.add(R0)
            if S % d:
                worst = max(worst, len(cls))
                assert len(cls) <= 2 ** (3 * J + 3)
            else:
                assert not cls or A % d == 0
    return worst

if __name__ == "__main__":
    random.seed(2)
    worst = 0
    cases = 0
    for (J, d, m) in [(1, 5, 26), (2, 5, 26), (2, 13, 170), (3, 5, 24), (2, 17, 290), (1, 13, 2 * 13 * 13 + 1)]:
        for _ in range(4):
            gamma = random.choice(range(1, 2 ** J, 2)) if J > 0 else 1
            h = random.choice([-3, -2, -1, 1, 2, 3, 5])
            M = random.randint(30, 400)
            a, b = xi_direct(J, d, m, gamma, h, M), xi_forms(J, d, m, gamma, h, M)
            worst = max(worst, abs(a - b)); cases += 1
    print(f"Steps 1-2: {cases} cases, max |direct - form side| = {worst:.2e}")
    for (J, d, m) in [(1, 5, 26), (2, 5, 26), (1, 13, 170)]:
        mx = step3(J, d, m, 1)
        print(f"Step 3 (J={J}, d={d}, m={m}): periodic mod L; max number of admissible classes (d not | S) = {mx} <= 2^(3J+3) = {2**(3*J+3)}")
