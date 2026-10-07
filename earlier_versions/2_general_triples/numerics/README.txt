Numerical checks for "Sums of two squares in three-term patterns: beyond the square-root bound"
(Section 9 of triples_sos.pdf).  Requires Python 3 with numpy and scipy, and a C compiler.
The outputs of all scripts, as run for the paper, are collected in results.txt.

seeds.py            Section 3: for the 1650 patterns {0,a,b}, b <= 60, not excluded by Lemma 3.5,
                    computes n_* (Lemma 3.2), finds A_*, u_* by a search (they exist by Lemma 3.3),
                    forms (J, d_0, u_0) as in Proposition 3.4 and tests its conclusion on random
                    elements of the classes.                          python3 seeds.py
identities_check.py Lemmas 2.1-2.3 and the inequality r(n(n+b)) <= r(n) r(n+b)/4 of Remark 8.4.
                                                                      python3 identities_check.py
gauss_check.py      Lemma 6.1 (Gauss's correspondence and the reciprocity formula (6.1)).
                                                                      python3 gauss_check.py
weyl_check.py       Steps 1-3 of the proof of Proposition 6.3 (the form-side expression for Xi_h,
                    periodicity of admissibility modulo L, number of admissible classes).
                                                                      python3 weyl_check.py
weyl_size.py        Sizes of the Weyl sums W(M) of Proposition 6.3 versus the number of terms R(M).
                                        python3 weyl_size.py 4 37 1370 14 ; python3 weyl_size.py 6 197 38424 14
Ld.py               Exact evaluation of the singular series L_d = L(1,chi) L(1,psi) H_d (Lemma 5.3).
                                                                      python3 Ld.py a b d
mainterm.c          Sharp and smoothed weighted counts sum r(T_d(u)) along T_d(u) = (u^2+m_d)/(2 kappa d),
                    with checks of Lemma 2.2 and Proposition 3.4.      gcc -O2 -o mainterm mainterm.c -lm
table.py            Table 1 (calls ./mainterm, Ld.py and seeds.py).   python3 table.py 1e13
count_triples.c     S_{a,b}(x).          gcc -O2 -o count_triples count_triples.c -lm ; ./count_triples 1 2 1e8
