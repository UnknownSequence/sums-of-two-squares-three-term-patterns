"""
Exponents of triples_final.pdf in exact arithmetic: Table 1 (Theorems 1.1 and 1.3) and the conditional
exponents of Remark 13.1.

The weighted count Sigma_d(x) has main term x^{1/2} d^{-1/2} (Proposition 7.1, Lemma 5.3(d)) and error term
    x^{1/4+theta/2} d^{3/4 - c theta},   c = 3/2 with Theorem 6.1(a) (Pascadi),  c = 1 with Theorem 6.1(b) (DI only).
With d = x^varpi the ratio error/main is x^{-1/4+theta/2+varpi(5/4-c theta)}, which is a negative power of x
exactly for varpi < (1/4-theta/2)/(5/4-c theta); then delta = varpi/2 (Section 4).
  Theorem 1.1:  delta_theta  = (1-2 theta)/(10-12 theta)
  Theorem 1.3:  delta'_theta = (1-2 theta)/(10-8 theta)
Remark 13.1 (conditional): a pair count P << N^{1/2+eta} + N^{1+eta}/d would remove the factor H^{1/4} ~ d^{1/2},
so that the error term becomes x^{1/4+theta/2} d^{1/4 - c theta}; then varpi < (1/4-theta/2)/(3/4-c theta), which is
1/3 for c = 3/2 (delta < 1/6 for every theta) and (1-2 theta)/(3-4 theta) for c = 1 (delta < (1-2 theta)/(6-8 theta)).
Remark 13.4 quotes delta < 1/24 (that is, varpi < 1/12) from an earlier version that used Weil's bound; it is printed
for comparison only and is not computed here.
Run: python3 exponents.py
"""
from fractions import Fraction as Fr

def varpi(theta, c, base):
    return (Fr(1, 4) - theta / 2) / (base - c * theta)

rows = [("Selberg (lambda_1 >= 3/16)", Fr(1, 4)), ("Kim-Sarnak (lambda_1 >= 975/4096)", Fr(7, 64)), ("Selberg's conjecture", Fr(0))]
for _, th in rows:
    assert Fr(1, 4) - th * th in (Fr(3, 16), Fr(975, 4096), Fr(1, 4))      # lambda_1 = 1/4 - theta^2
hdr = f"{'theta':<38} {'Thm 1.1':>18} {'Thm 1.3 (DI only)':>20} {'Rem 13.1, (a)':>15} {'Rem 13.1, (b)':>18} {'Rem 13.4':>9}"
out = [hdr]
for name, th in rows:
    d11, d13 = varpi(th, Fr(3, 2), Fr(5, 4)) / 2, varpi(th, Fr(1), Fr(5, 4)) / 2
    ca, cb = varpi(th, Fr(3, 2), Fr(3, 4)) / 2, varpi(th, Fr(1), Fr(3, 4)) / 2
    assert d11 == (1 - 2 * th) / (10 - 12 * th) and d13 == (1 - 2 * th) / (10 - 8 * th)
    assert ca == Fr(1, 6) and cb == (1 - 2 * th) / (6 - 8 * th)
    assert 2 * d11 <= Fr(1, 5) and 2 * d13 <= Fr(1, 5)          # within the range d <= x^{1/4} of (7.1)
    out.append(f"{name + ' ' + str(th):<38} {f'{d11} = {float(d11):.4f}':>18} {f'{d13} = {float(d13):.4f}':>20} "
               f"{f'{ca} = {float(ca):.4f}':>15} {f'{cb} = {float(cb):.4f}':>18} {'1/24':>9}")
print("\n".join(out))
open("results_exponents.txt", "w").write("\n".join(out) + "\n")
