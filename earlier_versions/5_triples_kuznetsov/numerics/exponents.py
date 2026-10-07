"""
Exponents in Theorems 1.1 and 1.2 and in the comparison table (Table 1 of the paper), in exact arithmetic.

  varpi_P(theta)  = (1-2 theta)/(5-6 theta),  delta_P  = varpi_P/2   (Theorem 1.1 = [II, Theorem 1.1])
  varpi_DI(theta) = (1-2 theta)/(5-4 theta),  delta_DI = varpi_DI/2  (Theorem 1.2, classical inputs only)

They come from comparing the error term x^{1/4+theta/2} d^{3/4-c theta} (c = 3/2 resp. c = 1) with the
main term x^{1/2} d^{-1/2} of the weighted count Sigma_d(x): with d = x^varpi the ratio error/main is
x^{-1/4+theta/2+varpi(5/4-c theta)}, and the exponent vanishes at varpi = (1/4-theta/2)/(5/4-c theta).
Run: python3 exponents.py
"""
from fractions import Fraction as Fr

def varpi(theta, c):
    return (Fr(1, 4) - theta / 2) / (Fr(5, 4) - c * theta)

rows = [("Selberg (lambda_1 >= 3/16)", Fr(1, 4)), ("Kim-Sarnak", Fr(7, 64)), ("Selberg's conjecture", Fr(0))]
out = [f"{'theta':<30} {'[I]':>6} {'[II] = Thm 1.1':>22} {'Thm 1.2 (DI only)':>22}"]
for name, th in rows:
    dP, dD = varpi(th, Fr(3, 2)) / 2, varpi(th, Fr(1)) / 2
    assert dP == (1 - 2 * th) / (10 - 12 * th) and dD == (1 - 2 * th) / (10 - 8 * th)
    out.append(f"{name + ' ' + str(th):<30} {'1/24':>6} {f'{dP} = {float(dP):.4f}':>22} {f'{dD} = {float(dD):.4f}':>22}")
print("\n".join(out))
open("results_exponents.txt", "w").write("\n".join(out) + "\n")
