# Numerical checks for "Sums of two squares in three-term patterns, II"

All scripts are self-contained (Python 3 with numpy and scipy; one C program).
Section and result numbers refer to the manuscript `triples_II.pdf`.

| file | what it does | paper |
|---|---|---|
| `seedsA.py` | Chooses the automatic pair (Table 1, Lemma 2.3), builds `n_*` as in the proof of Lemma 3.1, computes `(v, J, d_0, j)` as in Proposition 3.2, and checks the conclusion of Proposition 3.2 on random `(d, u)` for all 3725 patterns `{0,a,b}` with `b <= 100` and `a` or `b` odd. `python3 seedsA.py` | §§2–3, Table 2 |
| `mainterm.c` | Weighted counts along one family: sum of `r(T)` and of `r(T) F(T/x)` over `u >= 1` with `u = 0 mod 2^j` and `u^2 + B^2 = 0 mod d`, where `4dT = u^2 + m_d`; also checks that `T` has the 2-adic shape of Proposition 3.2 and that `P, P+B` are sums of two squares (Lemma 2.5). `gcc -O2 -o mainterm mainterm.c -lm`, then `./mainterm B A d x J d0 j` | §7, Table 3 |
| `Ld.py` | Exact value of the singular series `L_d = L(1,chi) L(1,psi) P_d` of Lemma 5.3 | §5 |
| `table.py` | Table 3: compares the counts with the main term of Proposition 7.1 for two good primes per pattern. `python3 table.py 1e13` | §9 |
| `typeI.py` | The Type I sums `Xi` of Proposition 6.5 for four polynomials `E l^2 + H_d`. `python3 typeI.py` | §9 |
| `heegner_pairs.py` | Counts pairs of Heegner points at bounded hyperbolic distance (the quantity bounded in Step 3 of Lemma 6.4), compares with the equidistribution prediction `12 (#Lambda_N)^2`, and finds the proportion of pairs compatible with the level-`d` congruence (Remark 8.1). `python3 heegner_pairs.py` | §9, Remark 8.1 |
| `kernel_exact.py` | Exact value of the second kernel of Lemma 6.4 (the pairing of `alpha` with `K_q k`) for `k = 1{u_1 <= 1}`, via the unfolding in Step 2 of its proof (written by an independent referee from the text of the paper). `python3 kernel_exact.py` | §9, Remark 8.1 |
| `results.txt` | Output of all of the above. | |

Notes.
* `mainterm` sums over `u >= 1` only, i.e. over half of the lattice `2^j Z`; `table.py` compares with half of the main term `32 c_F L_d 2^{-j} sqrt(x/d)` of Proposition 7.1.
* Good primes are as in Section 4: `d = d_0 mod 2^J`, `d > d_1 = 8(|c| + B)`, and neither `m_d` nor `m_d/3` a perfect square.
* Runtimes: `table.py 1e13` about 2 minutes, `typeI.py` and `heegner_pairs.py` about 1 minute each, `kernel_exact.py` about 10 seconds.
