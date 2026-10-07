"""GM-I Lemma 6.4: values of k_Z(a_u) sqrt(1+u) for u from 1 to 80 Z (tests the decay 1/sqrt(1+u) and the support u << Z)."""
import numpy as np
from harmonics import a_u_entries
from check_majorants import psi

def u_of(g):
    return (np.sum(g * g, axis=(-2, -1)) - 2) / 4
def psi_u(v, Z):
    return Z ** (-0.25) * psi(v / np.sqrt(Z))

out = []
for Z in [1e4, 1e6, 1e8]:
    vs = np.linspace(0.5, 4, 600) * np.sqrt(Z)
    row = []
    for fac in [1 / Z, 10 / Z, 1e-2, 1e-1, 1.0, 10.0, 40.0, 64.0, 70.0, 81.0]:
        u = fac * Z
        e1, e2 = a_u_entries(u)
        # the integrand is concentrated where |cos theta| << (sqrt(Z) u' v')^{1/2}, i.e. near theta = +-pi/2
        # (GM-I's proof says |sin theta|; with a_u = a[u'], u' < 1, it is cos theta that must be small).
        w = min(np.pi / 2, 40.0 / np.sqrt(1 + u))
        if w >= np.pi / 2:
            th = np.linspace(0, 2 * np.pi, 16384, endpoint=False); wts = np.full(th.size, 1.0 / th.size)
        else:
            th_near = np.linspace(-w, w, 8001)
            th = np.concatenate([th_near + np.pi / 2, th_near + 3 * np.pi / 2])
            wn = np.full(th_near.size, (2 * w) / (th_near.size - 1)); wn[[0, -1]] *= 0.5
            wts = np.concatenate([wn, wn]) / (2 * np.pi)
        c, s = np.cos(th), np.sin(th)
        tot = []
        for v in vs:
            f1, f2 = a_u_entries(v)
            g = np.empty((th.size, 2, 2))
            g[:, 0, 0] = f1 * c * e1; g[:, 0, 1] = f1 * s * e2
            g[:, 1, 0] = -f2 * s * e1; g[:, 1, 1] = f2 * c * e2
            tot.append(np.sum(wts * psi_u(u_of(g), Z)))
        kz = 2 * np.trapezoid(psi_u(vs, Z) * np.array(tot), vs)
        row.append((u, kz * np.sqrt(1 + u)))
    line = f"Z={Z:.0e}: " + "  ".join(f"u={u:.3g}:{val:.4f}" for u, val in row)
    print(line); out.append(line)
open("results_lemma64_decay.txt", "w").write("k_Z(a_u) sqrt(1+u) at selected u (GM-I Lemma 6.4)\n" + "\n".join(out) + "\n")
