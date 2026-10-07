"""
Check of Lemma 3.1 of the paper (Poisson summation and truncation of the frequencies h).

For the polynomial E l^2 + H attached to a good prime d, kappa in {1,3}, psi1(t) = phi(2t-3) and the
NON-even weight psi2(t) = phi(t) (1 + t/2), phi(t) = exp(-1/(1-t^2)), we compute the Type I sum

   Xi = sum_{mu = kappa d (4d)} psi1(mu/K) [ sum_{l : mu | E l^2 + H} psi2(l/X) - rho(mu)/mu * X * int psi2 ]

directly, and through Poisson summation as  sum_{h != 0} W_h  with

   W_h = sum_{mu = kappa d (4d)} psi1(mu/K) (X/mu) hat(psi2)(h X/mu) S(h; mu),
   S(h; mu) = sum_{nu mod mu, E nu^2 + H = 0 (mu)} e(h nu / mu).

We also print the partial sums over 0 < |h| <= c K/X for c = 1, 2, 4, 8 (Lemma 3.1 truncates at
h_0 = (qX)^eta K/X), and check S(-h; mu) = S(h; mu), on which the reduction to h > 0 rests.
Run: python3 poisson_check.py
"""
import numpy as np
from scipy.interpolate import CubicSpline

def phi(t):
    t = np.asarray(t, dtype=float)
    out = np.zeros_like(t)
    m = np.abs(t) < 1
    out[m] = np.exp(-1.0 / (1.0 - t[m] ** 2))
    return out

psi1 = lambda t: phi(2 * t - 3)                 # supported on [1, 2]
psi2 = lambda t: phi(t) * (1 + t / 2)           # supported on [-1, 1], not even

# hat(psi2)(xi) = int psi2(t) e(-xi t) dt on a fine xi-grid (trapezoid rule; integrand is flat at +-1),
# then cubic-spline interpolation.  |hat(psi2)(xi)| < 1e-15 for |xi| > 60.
tt = np.linspace(-1, 1, 4001); wt = np.full(tt.size, tt[1] - tt[0]); wt[0] = wt[-1] = wt[0] / 2
p2 = psi2(tt) * wt
XI_MAX = 64.0
xig = np.linspace(-XI_MAX, XI_MAX, 2 ** 17 + 1)
F = np.empty(xig.size, dtype=complex)
for a in range(0, xig.size, 4096):
    blk = xig[a:a + 4096]
    F[a:a + 4096] = np.exp(-2j * np.pi * np.outer(blk, tt)) @ p2
splr, spli = CubicSpline(xig, F.real), CubicSpline(xig, F.imag)
def hat_psi2(xi):
    xi = np.asarray(xi, dtype=float)
    out = np.zeros(xi.shape, dtype=complex)
    m = np.abs(xi) <= XI_MAX
    out[m] = splr(xi[m]) + 1j * spli(xi[m])
    return out
I2 = F[xig.size // 2].real                       # = hat(psi2)(0) = int psi2

def roots(E, H, mu):
    nu = np.arange(mu, dtype=np.int64)
    return np.nonzero((E * nu * nu + H) % mu == 0)[0]

def check(E, H, d, kappa, X, K):
    direct, main, tot_terms = 0.0, 0.0, 0
    hmax = int(np.ceil(XI_MAX * 2 * K / X))
    hs = np.arange(1, hmax + 1)
    Wpos = np.zeros(hmax, dtype=complex); Wneg = np.zeros(hmax, dtype=complex)
    sym_err = 0.0
    mu0 = int(K) + ((kappa * d - int(K)) % (4 * d))
    for mu in range(mu0, int(2 * K) + 1, 4 * d):
        w = float(psi1(mu / K))
        if w == 0.0:
            continue
        r = roots(E, H, mu)
        if r.size == 0:
            continue
        tot_terms += r.size
        # direct: l = nu (mod mu), |l| <= X
        cnt = 0.0
        for nu in r:
            ls = np.arange(nu - mu * int(np.ceil((nu + X) / mu)), X + 1, mu)
            cnt += psi2(ls / X).sum()
        direct += w * cnt
        main += w * r.size / mu * X * I2
        # Poisson side
        ph = np.exp(2j * np.pi * np.outer(hs, r) / mu)
        S = ph.sum(axis=1)
        Sm = np.conj(ph).sum(axis=1)               # S(-h; mu)
        sym_err = max(sym_err, np.abs(S - Sm).max())
        Wpos += w * (X / mu) * hat_psi2(hs * X / mu) * S
        Wneg += w * (X / mu) * hat_psi2(-hs * X / mu) * Sm
    Xi = direct - main
    Xi_P = (Wpos + Wneg).sum()
    partial = {c: (Wpos[:int(c * K / X)] + Wneg[:int(c * K / X)]).sum().real for c in (1, 2, 4, 8)}
    return Xi, Xi_P, partial, tot_terms, sym_err

if __name__ == "__main__":
    out = []
    X = 3000
    for (E, H, d) in [(8, 1057, 89), (8, 285, 53)]:
        for kappa in (1, 3):
            for c in (0.5, 1, 4, 16, 64):
                K = c * X
                Xi, Xi_P, part, n, se = check(E, H, d, kappa, X, K)
                line = (f"E={E} H={H} d={d} kappa={kappa} X={X} K={c:>4}X: #(mu,nu)={n:5d}  Xi={Xi:+.10f}  "
                        f"sum_h W_h={Xi_P.real:+.10f}{Xi_P.imag:+.1e}i  |diff|={abs(Xi - Xi_P):.1e}  "
                        f"|h|<=cK/X, c=1,2,4,8: " + ", ".join(f"{part[k]:+.6f}" for k in (1, 2, 4, 8))
                        + f"  max|S(h)-S(-h)|={se:.1e}")
                print(line); out.append(line)
    open("results_poisson.txt", "w").write("\n".join(out) + "\n")
