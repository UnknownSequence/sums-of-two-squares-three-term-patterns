"""Singular series of Lemma 4.3 of the note: Lf = L(1,chi) L(1,psi) P, psi(n) = (EH/n) for odd n."""
import math
from Ld import factor, kronecker, fundamental_disc, L1_chiD, rho_pp, chi4
def L_fam(E, H, p1, p2):
    m = E * H
    D = fundamental_disc(m)
    Lpsi = L1_chiD(D)
    for p in factor(2 * m):
        Lpsi *= 1 - kronecker(D, p) / p
    P = 6 / math.pi ** 2
    for p in set(factor(2 * p1 * p2 * H)) | {2}:
        P /= 1 - p ** -2.0
    for p in (p1, p2):
        P *= 1 - chi4(p) / p
    for l, al in factor(H).items():
        c = chi4(l)
        Pl = sum((c ** j) * rho_pp(l, j, m) * float(l) ** (-j) for j in range(0, al + 60))
        P *= (1 - c / l) * Pl
    return (math.pi / 4) * Lpsi * P, Lpsi, P
