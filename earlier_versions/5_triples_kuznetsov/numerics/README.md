# Numerical checks for "Sums of two squares in three-term patterns via the Kuznetsov formula"

All scripts are self-contained (Python 3 with numpy and scipy). Section and lemma numbers refer to
`triples_kuznetsov.pdf`. Each script writes its output to the matching `results_*.txt`.

| file | what it does | paper | runtime |
|---|---|---|---|
| `heegner_poincare.py` | Checks the Heegner–Poincaré identity (3.2): the Weyl sums `sum_{K<=mu<2K} S(h; mu)` (with `mu = kappa d mod 4d`) equal the Poincaré series of frequency `h` on `Gamma_0(4Ed)`, summed over the Heegner points `z_i` of discriminant `-4EH`. Both sides are computed exactly, apart from the exponentials. Data: `(E,H,d) = (8,1057,89), (8,285,53)`, `kappa = 1, 3`, `K` up to `6*10^4`, `h in {1,2,3,7,13}`. | Lemma 3.2, §9 | ~10 s |
| `poisson_check.py` | Computes the Type I sum `Xi` directly and as `sum_{h != 0} W_h` after Poisson summation, for a non-even weight `psi_2`. Also prints the partial sums over `0 < |h| <= cK/X` (the truncation of Lemma 3.1) and checks `S(-h; mu) = S(h; mu)`. | Lemma 3.1, §9 | ~40 s |
| `bessel_checks.py` | Evaluates `K_{it}(y)` for real `t` by the convergent residue series of the Mellin–Barnes integral (no cancellation, accurate even when `K_{it}(y) ~ e^{-pi|t|/2}` is tiny), cross-checked against a contour-shifted quadrature. Then checks (1) the integral representation of `K_nu` in Lemma 6.1; (2) the Mellin–Barnes formula of Lemma 6.2 (residues plus the integral on `Re w = -3/2`); (3) that the remainder, computed exactly from the series, is *not* pointwise `O(y^{3/2}|t|^{-5/2}e^{-pi|t|/2})`, while its average against a smooth weight decays in `|t|`, which is all the proof uses. | Lemmas 6.1, 6.2, §9 | ~3 s |
| `weyl_stats.py` | Root mean square and maximum over `1 <= h <= 200` of `|S_h(K)|/sqrt(n)`, where `n` is the number of terms. This shows square-root cancellation in the Weyl sums. | §§8.3, 9 | ~25 s |
| `exponents.py` | The exponents of Table 1 in exact arithmetic: `(1-2θ)/(10-12θ)` (Theorem 1.1 = [II]) and `(1-2θ)/(10-8θ)` (Theorem 1.2), for `θ = 1/4, 7/64, 0`. | Table 1 | <1 s |

Summary of results (see the `results_*.txt` files):

* Heegner–Poincaré identity: in all 16 cases both sides have the same number of terms (up to 562). The largest difference is `1.2e-13`.
* Poisson summation: the direct and the Poisson-side values of `Xi` agree to within `3.2e-10` in all 20 cases. The partial sums over `|h| <= cK/X` are within `0.10, 0.045, 0.0080, 0.0012` of `Xi` for `c = 1, 2, 4, 8`. Also `|Xi| <= 0.0023 X^{1/2} H^{1/4}`.
* Bessel: the residue series agrees with the contour-shifted quadrature to relative accuracy `5e-14`. The representation in Lemma 6.1 holds to relative accuracy `2.3e-10`, and the Mellin–Barnes formula to within `4e-15 |t|^{-1/2} e^{-pi|t|/2}`. For `y = 0.02` the smoothed remainder, divided by `y^{3/2} e^{-pi|t|/2}`, falls from `3.2e-3` at `|t| = 1` to `1.2e-5` at `|t| = 15` and `1.6e-6` at `|t| = 25`, while the pointwise maximum for `y = 2` is `21.7 y^{3/2}|t|^{-5/2}e^{-pi|t|/2}` at `|t| = 25`.
* Weyl sums: the root mean square of `|S_h(K)|/sqrt(n)` lies between 0.83 and 0.99, and the maximum between 2.1 and 3.6.

The Type I sums, the pair counts of Heegner points and the exact kernel values that are relevant for the comparison in §8 are computed by the scripts of the companion folder `../3_triples_II/numerics` (see §9 of `triples_II.pdf`).
