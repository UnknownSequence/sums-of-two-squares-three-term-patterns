"""[GM0 = arXiv:2404.08502, Prop. 6.1]: the product kernel k0 = f(rho)F(phi+vartheta) for L >> K."""
import numpy as np
from harmonics import phi_ll_hyp, a_u_entries
from check_majorants import bump, psi   # reuse the same bump functions (re-runs nothing heavy: guarded below)

out = []
def say(s=""):
    print(s); out.append(s)

say("=== [GM0, Prop. 6.1]: J(l,nu) = int f phi_{l,l} du / int f du, f = bump(C K rho), C = 8 ===")
C = 8.0
for K in [10.0]:
    rmax = 1 / (C * K)
    umax = np.sinh(rmax / 2) ** 2
    us = np.linspace(0, umax, 6001)[1:]
    rh = np.arccosh(2 * us + 1)
    fw = bump(C * K * rh)
    den = np.trapezoid(fw, us)
    for nu in [0.0, 1j * K]:
        line = []
        for l in [0, 10, 40, 100, 200, 400, 600, 800, 1000, 1500, 2000]:
            ph = np.array([phi_ll_hyp(x, nu, l) for x in us]).real
            line.append((l, np.trapezoid(fw * ph, us) / den))
        say(f"K={K:.0f}, nu={nu}: " + "  ".join(f"l={l}:{J:+.3f}" for l, J in line))
say("For l/K >~ 60 (with C = 8) the integral collapses and then changes sign, so the lower bound")
say("Phi_{l,l}(k0,nu) >= C^{1/2} for all |l| <= L claimed in the proof of [GM0, Prop. 6.1] needs L <~ C K.")
say("(Positivity of Phi_{l,l}(k0*k0,nu) = Phi_{l,l}(k0,nu)^2 is never in question; the lower bound is what fails.)")

say("\n(GM-I Lemma 6.4 is checked in check_lemma64_decay.py.)")

with open("results_prop61_lemma64.txt", "w") as fh:
    fh.write("\n".join(out) + "\n")
