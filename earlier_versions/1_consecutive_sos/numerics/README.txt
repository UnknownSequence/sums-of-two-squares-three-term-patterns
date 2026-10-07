Numerical checks for "Three consecutive sums of two squares" (Section 7).

gauss_check.py  - verifies Gauss's correspondence and the reciprocity formula (Lemma 4.1)
weyl_check.py   - verifies Step 1-2 of Proposition 4.3 (S_mu(h) via binary forms); run from this folder
mainterm.c      - Table 1: sum_w r(N_d(w)) vs 4*sqrt(2)*L_d*sqrt(x/d)
                  gcc -O2 -o mainterm mainterm.c -lm ; ./mainterm 17 1e11 300000
family_clean.c  - S(10^8) and the number of triples produced by the d-family
                  gcc -O2 -o family_clean family_clean.c ; ./family_clean
