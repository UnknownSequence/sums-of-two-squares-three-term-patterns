"""
Checks of GM-I Lemma 2.1/4.1 (explicit formula), the Casimir eigen-equation (sign check for
Proposition 5.1), the unitary normalisation (2.27)-(2.33) via Parseval, the size relation (2.36),
and Lemma 4.4.  Run:  python3 check_harmonics.py
"""
import numpy as np
from harmonics import (phi_direct, phi_lemma41, phi_lemma41_first, phi_all_l1, phi_ll_hyp,
                       norm_factor, casimir_residual)

np.set_printoptions(linewidth=150)
out = []


def say(s=""):
    print(s)
    out.append(s)


say("=== 1. Lemma 4.1 versus the definition (2.20) ===")
worst = 0.0
for u in [0.05, 0.7, 3.0, 25.0]:
    for nu in [0.3j, 2.5j, 0.1, 0.37, 1.5]:
        for (l1, l2) in [(0, 0), (2, 0), (-4, 0), (6, 2), (1, 3), (-3, 5), (8, -2)]:
            d = phi_direct(u, nu, l1, l2, N=1 << 15)
            f2 = phi_lemma41(u, nu, l1, l2)
            f1 = phi_lemma41_first(u, nu, l1, l2)
            err = max(abs(d - f2), abs(d - f1)) / max(1e-300, abs(d))
            worst = max(worst, err)
say(f"max relative discrepancy over 140 cases: {worst:.2e}")

say("\n=== 2. Hypergeometric form of phi_{l,l} versus Lemma 4.1 (2^20 quadrature nodes) ===")
say("(for complex nu and u/(u+1) > 0.9 phi_ll_hyp itself uses Lemma 4.1, so only the other cases are informative)")
worst = 0.0
for u in [0.01, 0.5, 4.0, 60.0, 900.0]:
    for nu in [0.05, 0.2, 0.45, 0.8j, 3j]:
        for l in [0, 2, 4, 10, -6]:
            a = phi_ll_hyp(u, nu, l)
            b = phi_lemma41(u, nu, l, l, N=1 << 20)
            worst = max(worst, abs(a - b) / max(1e-300, abs(b)))
say(f"max relative discrepancy: {worst:.2e}")

say("\n=== 3. Casimir equation Omega P = (1/4 - nu^2) P with Omega as in (2.12) ===")
for (u, nu, l1, l2) in [(0.8, 1.7j, 2, 0), (3.0, 0.25, 4, 2), (0.3, 0.6j, -2, 4), (2.0, 4.0j, 6, 0)]:
    lhs, rhs = casimir_residual(lambda x: phi_lemma41(x, nu, l1, l2, N=1 << 15), u, nu, l1, l2)
    say(f"u={u}, nu={nu}, (l1,l2)=({l1},{l2}):  Omega P / P = {lhs/ (rhs/(0.25-nu**2)):.10f},  1/4-nu^2 = {0.25-nu**2:.10f}")
say("Hence on P_nu^{(l1,l2)} the operator (1/4-Omega) - d_phi^2 - d_vartheta^2 acts by nu^2 + l1^2 + l2^2,")
say("which for nu = it equals l1^2 + l2^2 - t^2 (not 1 + (delta nu)^2 + ... with a plus sign).")
t, l1, l2, dl = 30.0, 4, 0, 0.1
say(f"Example: t={t}, (l1,l2)=({l1},{l2}), delta={dl}:  eigenvalue of Xi = 1 + delta^2 (nu^2 + l1^2 + l2^2) = {1 + dl**2*((1j*t)**2 + l1**2 + l2**2)}")
say("With Omega - 1/4 in place of 1/4 - Omega the eigenvalue is 1 + delta^2 (t^2 + l1^2 + l2^2) > 0, as intended.")

say("\n=== 4. Parseval test of the normalisation (2.30): sum_l |P_nu^{(l,0)}(a_u)|^2 = 1 ===")
say("(holds iff P^{(l,0)} are the matrix coefficients <pi(g) v_0, v_l> of a unitary representation)")
for nu in [0.4j, 3.0j, 12.0j, 0.03, 0.109375, 0.25, 0.45]:
    row = []
    for u in [0.02, 0.5, 3.0, 40.0, 400.0]:
        N = int(2 ** np.ceil(np.log2(max(1 << 14, 400 * (u + 1)))))
        l1, c = phi_all_l1(u, nu, 0, N)
        mask = np.abs(l1) < N // 2   # avoid the aliased top bins
        s = 0.0
        for L, cc in zip(l1[mask], c[mask]):
            s += abs(norm_factor(nu, L, 0) * cc) ** 2
        row.append(s)
    say(f"nu={nu!s:>10}:  " + "  ".join(f"{v:.12f}" for v in row))

say("\nDiscrete series D_k^+: sum_{l1>=k} |P^{(l1,l2)}_{(k-1)/2}(a_u)|^2 = 1 (fixed l2>=k)")
for k in [2, 4, 7]:
    kappa = k % 2
    nu = (k - 1) / 2
    for l2 in [k, k + 2, k + 6]:
        row = []
        for u in [0.1, 2.0, 50.0]:
            N = int(2 ** np.ceil(np.log2(max(1 << 14, 400 * (u + 1)))))
            l1s, c = phi_all_l1(u, nu, l2, N)
            s = 0.0
            for L, cc in zip(l1s, c):
                if L >= k and (L - k) % 2 == 0 and abs(L) < N // 2:
                    s += abs(norm_factor(nu, L, l2, kappa=kappa, k=k) * cc) ** 2
            row.append(s)
        say(f"k={k}, l2={l2}:  " + "  ".join(f"{v:.12f}" for v in row))

say("\n=== 5. The ratio (2.33) for nu in (0,1/2): GM (2.36) says it is ~ (1+l1)^{2nu}(1+l2)^{2nu} ===")
say("Computed ratio R and the corrected prediction ((1+l2)/(1+l1))^nu:")
for nu in [0.1, 0.3, 0.45]:
    for (l1, l2) in [(0, 40), (40, 0), (200, 2), (2, 200), (100, 100)]:
        R = abs(norm_factor(nu, l1, l2))
        say(f"nu={nu}, (l1,l2)=({l1},{l2}):  R={R:.4f},  ((1+l2)/(1+l1))^nu={((1+l2)/(1+l1))**nu:.4f},  (1+l1)^(2nu)(1+l2)^(2nu)={((1+l1)*(1+l2))**(2*nu):.2f}")

say("\n=== 6. Lemma 4.4: int_0^infty |P^{(l1,l2)}_{(k-1)/2}(a_u)|^2 du = 1/(k-1) ===")
say("(phi evaluated by the finite sum in harmonics.phi_discrete, which agrees with Lemma 4.1 to ~1e-12)")
from scipy.integrate import quad
from harmonics import phi_discrete
for k in [2, 3, 4, 5, 6, 8]:
    kappa = k % 2
    for (l1, l2) in [(k, k), (k + 2, k), (k + 4, k + 2), (k + 2, k + 6)]:
        fac = abs(norm_factor((k - 1) / 2, l1, l2, kappa=kappa, k=k))
        f = lambda u: (fac * phi_discrete(u, k, l1, l2)) ** 2
        val = quad(f, 0, np.inf, limit=400, epsabs=1e-14, epsrel=1e-12)[0]
        say(f"k={k}, (l1,l2)=({l1},{l2}):  integral = {val:.12f},   1/(k-1) = {1/(k-1):.12f}")

with open("results_harmonics.txt", "w") as fh:
    fh.write("\n".join(out) + "\n")
