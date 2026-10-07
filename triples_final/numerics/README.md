# Numerical checks for "Sums of two squares in three-term patterns"

These scripts produce every number reported in Section 14 of `triples_final.pdf`. Section, lemma, table and
equation numbers below refer to that paper. The scripts use Python 3 with `numpy` and `scipy`, and
one C program. Each script writes its output to the matching `results_*.txt` file. All outputs were
regenerated for the final version, and they agree with the outputs of the earlier versions where the
computations overlap.

| file | what it does | paper | runtime |
|---|---|---|---|
| `seedsA.py` | For all 3725 patterns `{0,a,b}` with `b <= 100` and `a` or `b` odd: chooses `(p_0, B, A)` by Table 2 (Lemma 2.3), builds `n_*` as in the proof of Lemma 3.1, computes `v, J, d_0, j` as in the proof of Proposition 3.2, and checks the conclusion of Proposition 3.2 on 40 random pairs `(d, u)` per pattern. Also a library used by the other scripts. | §§2–3, Table 3 | ~1 s |
| `mainterm.c` | Weighted counts along one family: the sharp sum of `r(T)` and the smoothed sum of `r(T) F(T/x)` over `l >= 1`, where `T = T_d(l)`. Also checks that every `T` has the 2-adic shape of Proposition 3.2 and that `P, P+B` are sums of two squares (Lemma 2.5). Compile with `gcc -O2 -o mainterm mainterm.c -lm`. | §§4, 7 | — |
| `Ld.py` | Exact value of the singular series `L_d = L(1,chi) L(1,psi) P_d` (Lemma 5.3(c)). `L(1,psi)` is computed from a rapidly convergent series that comes from the functional equation. | §5 | — |
| `table.py` | Table 4: compares the counts of `mainterm` with half of the main term `32 c_F L_d 2^{-j} sqrt(x/d)` of Proposition 7.1, for two good primes per pattern. Needs `./mainterm`. Run `python3 table.py 1e13`. | §14, Table 4 | ~2 min |
| `typeI.py` | The Type I sums `Xi` of (6.1) for four polynomials `E l^2 + H_d` and `K = 2^{i/2} X`, `X = 2*10^6`. Prints `|Xi|` against `X^{1/2} H^{1/4}` (Theorem 6.1) and against the square root of the main term, and the largest `|Xi|`. | §14, Remark 13.1 | ~2 min |
| `heegner_pairs.py` | Counts the pairs `(zeta, w)` in `Lambda_N x Q_N` with `u(z(w), z(zeta)) <= 1` (the count that bounds `P` in Lemma 8.4), compares it with the equidistribution prediction `12 (#Lambda_N)^2`, and counts the pairs whose binary forms have a common zero in `P^1(F_d)`. | Lemma 8.4, Remark 13.1, §14 | ~1.5 min |
| `level_pairs.py` | The pair count `P` of Lemma 8.4 computed exactly, in two independent ways: (A) by the reduction in the proof of Lemma 8.4 with the dropped condition kept, and (B) directly from `P = 2 sum_i #{g in Q^kappa : u(z(g), z_i) <= 1}`, using coset representatives with short bottom rows. Also prints `I`, the diagonal term `2I`, and the largest number of cosets `tau` with `tau<>zeta` in `Q^kappa` (Lemma 8.3). | Lemmas 8.3–8.4, Remark 13.1, §14 | ~30 s |
| `heegner_poincare.py` | Checks the Heegner–Poincaré identity (9.2) for a sharp weight, i.e. for `sum_{K <= mu < 2K} S(h; mu)`. Both sides are computed exactly, apart from the exponentials. | Lemma 9.2, §14 | ~30 s |
| `poisson_check.py` | Computes `Xi` directly and as `sum_{h != 0} W_h` (Lemma 9.1) for a non-even weight `psi_2`. Also prints the partial sums over `0 < |h| <= cK/X` and checks `S(-h; mu) = S(h; mu)`. | Lemma 9.1, §14 | ~1.5 min |
| `bessel_checks.py` | Evaluates `K_{it}(y)` for real `t` by the residue series of the Mellin–Barnes integral, and cross-checks it against a contour-shifted quadrature. Checks the representation of Lemma 11.1, the Mellin–Barnes formula of Lemma 11.2, and the behaviour of its remainder: the remainder is not pointwise `O(y^{3/2}|t|^{-5/2}e^{-pi|t|/2})`, but its smooth averages decay in `|t|`, which is all the proof uses. | Lemmas 11.1–11.2, §14 | ~10 s |
| `weyl_stats.py` | Root mean square and maximum over `1 <= h <= 200` of `|S_h(K)| / sqrt(n)`, where `S_h(K) = sum_{K <= mu < 2K} S(h; mu)` and `n` is the number of terms. | §14, Remark 13.1 | ~1 min |
| `exponents.py` | The exponents of Table 1 (Theorems 1.1 and 1.3) and the conditional exponents of Remark 13.1, in exact arithmetic. The exponent `1/24` of Remark 13.4 comes from an earlier version, and is printed only for comparison. | Table 1, Remarks 13.1 and 13.4 | <1 s |

## Summary of results

* **2-adic set-up.** No failures among the 3725 patterns. The rows of Table 3 are in `results_seeds.txt`.
* **Main term (Table 4).** At `x = 10^13`, the ratio of the smoothed count to half of the main term lies between 0.988 and 1.023, and the ratio for the sharp cut-off lies between 0.992 and 1.013. Every `T_d(l)` had the 2-adic shape of Proposition 3.2, and `P, P+B` were always sums of two squares.
* **Type I sums.** `|Xi| <= 0.03 X^{1/2} H^{1/4}` in all cases, with maxima 0.024, 0.003, 0.028 and 0.003. The largest values of `|Xi|` are 189.9, 48.4, 164.4 and 33.1, all at `K = X`, against `X^{1/2} = 1414`. For `K >= 4X` we always have `|Xi| <= M^{1/2}`.
* **Pairs of Heegner points.** The number of all pairs is between `4.5N` and `61N`, and it agrees with `12 (#Lambda_N)^2` to within 1.5%. The proportion of pairs with a common zero in `P^1(F_d)` is between `3.6/d` and `4.1/d`.
* **The exact pair count `P`.** For `(E,H,d) = (8,1057,89), (8,285,53), (8,3869,181)` we get `P = 1664, 256, 576`, against `2I = 896, 256, 576` and `N = 8456, 2280, 30952`. The results are the same for both `kappa`, and methods A and B agree. At most 8 cosets `tau` occur, against the bound `12E = 96`.
* **Heegner–Poincaré identity.** In all 16 cases both sides have the same number of terms (up to 562). The largest difference is `1.21e-13`.
* **Poisson summation.** The direct and the Poisson-side values of `Xi` agree to within `4e-10` in all 20 cases. The partial sums over `|h| <= cK/X` are within 0.102, 0.046, 0.0081 and 0.0012 of `Xi` for `c = 1, 2, 4, 8`.
* **Bessel functions.** The residue series agrees with the quadrature to relative accuracy `5e-14`. Lemma 11.1 holds to relative accuracy `2.3e-10`, and Lemma 11.2 to within `4e-15 |t|^{-1/2} e^{-pi|t|/2}`.
* **Weyl sums.** The root mean square of `|S_h(K)| / sqrt(n)` is between 0.827 and 0.985, and the maximum is between 2.10 and 3.60.

## Running

```
gcc -O2 -o mainterm mainterm.c -lm
python3 seedsA.py > results_seeds.txt
python3 table.py 1e13 > results_table_1e13.txt
python3 typeI.py > results_typeI.txt
python3 heegner_pairs.py > results_heegner_pairs.txt
python3 level_pairs.py          # writes results_level_pairs.txt
python3 heegner_poincare.py     # writes results_heegner_poincare.txt
python3 poisson_check.py        # writes results_poisson.txt
python3 bessel_checks.py        # writes results_bessel.txt
python3 weyl_stats.py           # writes results_weyl_stats.txt
python3 exponents.py            # writes results_exponents.txt
```

`table.py` calls `./mainterm`. Run it from a directory where the compiled binary can be executed. Some
mounted or synced folders do not allow this.
