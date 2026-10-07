"""
Checks of GM-I Lemma 4.2, Lemma 4.3, Proposition 6.1 (as imported from [GM0, Prop. 6.1]),
Proposition 6.2 and Lemma 6.4.   Run:  python3 check_majorants.py
"""
import numpy as np
from scipy.integrate import quad
from harmonics import (phi_lemma41, phi_ll_hyp, phi_ll_large_u, lemma43_main, kmat, a_u_entries)

out = []


def say(s=""):
    print(s)
    out.append(s)


def bump(x):
    """smooth, = 1 on |x|<=1/2, = 0 for |x|>=1"""
    x = np.abs(np.asarray(x, dtype=float))
    res = np.zeros_like(x)
    res[x <= 0.5] = 1.0
    m = (x > 0.5) & (x < 1)
    t = (x[m] - 0.5) / 0.5
    e1 = np.exp(-1 / (1 - t))
    e2 = np.exp(-1 / t)
    res[m] = e1 / (e1 + e2)
    return res



def smoothstep(t):
    """C^infty step: 0 for t<=0, 1 for t>=1"""
    t = np.asarray(t, dtype=float)
    out = np.zeros_like(t)
    out[t >= 1] = 1.0
    m = (t > 0) & (t < 1)
    e1 = np.exp(-1 / t[m]); e2 = np.exp(-1 / (1 - t[m]))
    out[m] = e1 / (e1 + e2)
    return out


def psi(s):
    """smooth, supported on [1/2,4], equal to 1 on [1,2] (as in GM-I Lemma 6.4)"""
    s = np.asarray(s, dtype=float)
    return smoothstep((s - 0.5) / 0.5) * smoothstep((4 - s) / 2)


if __name__ == "__main__":
    say("=== 1. Lemma 4.2 near u = 0 ===")
    say("GM bound: |phi_{l1,l2}(a_u,nu)| << min{log(1+u),(Re nu)^{-1}} (1+u)^{-1/2+Re nu}")
    for u in [1e-1, 1e-2, 1e-3, 1e-4]:
        for nu in [0.1, 2.0j]:
            v = abs(phi_lemma41(u, nu, 0, 0))
            rn = max(np.real(nu), 1e-300)
            gm = min(np.log(1 + u), 1 / rn) * (1 + u) ** (-0.5 + np.real(nu))
            fx = min(np.log(2 + u), 1 / rn) * (1 + u) ** (-0.5 + np.real(nu))
            say(f"u={u:.0e}, nu={nu}: |phi_00|={v:.4f},  GM bound={gm:.2e} (ratio {v/gm:.1e}),  with log(2+u): {fx:.3f}")
    say("Triangle-inequality bound actually proved: |phi_{l1,l2}(a_u,nu)| <= phi_{0,0}(a_u,Re nu); check:")
    worst = 0
    for u in [1e-3, 0.3, 5, 80]:
        for nu in [0.05, 0.3, 1.3j, 6j]:
            ref = abs(phi_lemma41(u, np.real(nu), 0, 0))
            for (l1, l2) in [(0, 0), (2, 0), (4, 6), (-8, 2), (1, 3)]:
                worst = max(worst, abs(phi_lemma41(u, nu, l1, l2)) / ref)
    say(f"max_l |phi_(l1,l2)(a_u,nu)| / phi_(0,0)(a_u,Re nu) over the grid = {worst:.6f}  (<= 1 as claimed)")

    say("\n=== 2. Lemma 4.3: phi_{l,l}(a_u,nu) for large u (l even) ===")
    say("ratio phi / M, where M = (Gamma(2nu)cos(pi nu)/pi)(-1)^{l/2} Gamma(1/2+l/2-nu)/Gamma(1/2+l/2+nu) u^{-1/2+nu}")
    for nu in [0.05, 0.109375, 0.2, 0.3]:
        for l in [0, 2, 4, 10]:
            row = []
            for u in [1e2, 1e4, 1e6, 1e8, 1e10]:
                row.append(phi_ll_large_u(u, nu, l) / lemma43_main(u, nu, l))
            say(f"nu={nu:<8} l={l:<3} " + "  ".join(f"{r:.5f}" for r in row))
    say("cross-check of the large-u formula against scipy hyp2f1 / Lemma 4.1 at moderate u:")
    worst = 0
    for nu in [0.05, 0.2, 0.3]:
        for l in [0, 2, 6]:
            for u in [50.0, 300.0, 2000.0]:
                a = phi_ll_large_u(u, nu, l)
                b = phi_lemma41(u, nu, l, l).real
                worst = max(worst, abs(a - b) / abs(b))
    say(f"max relative discrepancy {worst:.2e}")
    say("signs of phi_{l,l}(a_u,nu) at u=1e8, nu=0.1, l=0,2,4,6,8: " +
        " ".join("+" if phi_ll_large_u(1e8, 0.1, l) > 0 else "-" for l in [0, 2, 4, 6, 8]))
    say("=> phi_{l,l} ~ (-1)^{l/2} |...|: Lemma 4.3 holds for |phi_{l,l}|; the sign is (-1)^{l/2} for even l.")

    say("\n=== 3. [GM0, Prop. 6.1] / GM-I Prop. 6.1: the product kernel k0 = f(rho) F(phi+vartheta) ===")
    say("Phi_{l,l}(k0,nu) = c Fhat(l) * 2 int f(rho(u)) phi_{l,l}(a_u,nu) du.  [GM0] treat the last integral as")
    say("~ int f (Taylor approximation). Ratio J(l,nu) = int f phi_{l,l} du / int f du, f = bump(C K rho), C=8:")
    C = 8.0
    for K in [10.0, 40.0]:
        rmax = 1 / (C * K)
        umax = np.sinh(rmax / 2) ** 2
        us = np.linspace(0, umax, 4001)[1:]
        rh = np.arccosh(2 * us + 1)
        fw = bump(C * K * rh)
        den = np.trapezoid(fw, us)
        for nu in [0.0, 1j * K]:
            res = []
            for L in [K, 4 * K, 10 * K, 20 * K]:
                ls = np.arange(0, int(L) + 1, 2)
                Js = []
                for l in ls:
                    ph = np.array([phi_ll_hyp(x, nu, l) for x in us]).real
                    Js.append(np.trapezoid(fw * ph, us) / den)
                res.append(min(Js))
            say(f"K={K:.0f}, nu={nu}: min over |l|<=L of J for L=K,4K,10K,20K: " + "  ".join(f"{r:+.3f}" for r in res))
    say("=> for L <= K the integral is ~ int f (J ~ 1), as in [GM0]. For L/K large it collapses and changes sign")
    say("   (see results_prop61_lemma64.txt: sign change near l = 100 K for C = 8), so the construction of")
    say("   [GM0, Prop. 6.1] needs L <~ C K.  GM-I state Prop. 6.1 only for T >= L and apply it with")
    say("   T' = max(T,L), so GM-I is unaffected.")

    say("\n=== 4. GM-I Prop. 6.2 lower bound: int psi_Z(u) phi_{l,l}(a_u,nu) du with psi_Z = Z^{-1/4} psi(u/sqrt Z) ===")
    for nu in [0.06, 0.109375, 0.2, 0.25]:
        for l in [0, 2, 4, 6]:
            row = []
            for logZ in [20, 40, 80, 160]:
                Z = 10.0 ** (logZ / 4) if False else np.exp(logZ)
                s = np.linspace(0.5, 4, 2001)
                u = s * np.sqrt(Z)
                vals = np.array([phi_ll_large_u(x, nu, l) for x in u])
                I = Z ** (-0.25) * np.trapezoid(psi(s) * vals, u)
                row.append(I * (1 + abs(l)) / Z ** (nu / 2))
            say(f"nu={nu:<8} l={l}:  I(1+|l|)/Z^(nu/2) for log Z = 20,40,80,160: " + "  ".join(f"{r:+.4f}" for r in row))
    say("=> |I| >> Z^{nu/2}/(1+|l|) with constant sign (-1)^{l/2}; Lemma 6.3 only needs |<f_Z,P>|^2.")

    say("\n(Lemma 6.4 is checked in check_prop61_lemma64.py with a theta-grid adapted to |sin theta| < 20/sqrt(1+u).)")

    with open("results_majorants.txt", "w") as fh:
        fh.write("\n".join(out) + "\n")
