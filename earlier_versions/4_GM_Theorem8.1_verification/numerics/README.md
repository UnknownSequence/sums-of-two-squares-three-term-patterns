# Numerical checks for "Theorem 8.1 of Grimmelt–Merikoski: a verification report"

All scripts use only Python 3 with numpy and scipy. Section, lemma and finding numbers (F1–F10) refer to
`GM_Theorem8.1_report.pdf`; GM-I is arXiv:2505.00489v2 and GM0 is arXiv:2404.08502v2. Each script writes
its output to the matching `results_*.txt`. All outputs were reproduced exactly from a clean copy.

| file | what it does | report | runtime |
|---|---|---|---|
| `harmonics.py` | Library: the harmonics `phi_{l1,l2}(a_u, nu)` and the normalised harmonics `P_nu^{(l1,l2)}` of GM-I §§2, 4, in GM-I's conventions. They are computed from the integral formula of GM-I Lemma 4.1 (trapezoid rule, exponentially convergent), from the hypergeometric form with the connection formula for large `u`, and by an exact finite sum for the discrete series. Each representation is cross-checked against the others. | §6 | — |
| `check_harmonics.py` | GM-I Lemmas 2.1 and 4.1 against the definition (2.20). The Casimir eigen-equation (sign check behind finding F1). The unitary normalisation (2.27)–(2.33) via Parseval (Lemma 4.1 of the report). The size relation (2.36) (finding F3). GM-I Lemma 4.4. | §§4, 6, Tables 2–3 | ~50 s |
| `check_majorants.py` | GM-I Lemma 4.2 (finding F4), Lemma 4.3 (finding F5), Proposition 6.1 as imported from GM0, Proposition 6.2 (finding F6) and Lemma 6.4. | §§4, 6, Table 2 | ~40 s |
| `check_prop61_lemma64.py` | GM0 Proposition 6.1: the product kernel `k0 = f(rho) F(phi + vartheta)`. Shows that the lower bound fails for `L >> K` (finding F2). | §4, Table 2 | ~2 s |
| `check_lemma64_decay.py` | GM-I Lemma 6.4: `k_Z(a_u) sqrt(1+u)` for `u` from 1 to `80 Z`, which tests the decay `1/sqrt(1+u)` and the support `u << Z`. | §4, Table 2 | ~12 s |
| `end_to_end.py` | End-to-end illustration of GM-I Theorem 8.1 in the simplest case `H = 1`, `alpha_1 = I`, `alpha_2 = delta_{z0}`. It computes the discrepancy `D(q, Y)` of a smoothed count over `Gamma_0(q)` and prints `D Y^{1/2}`. | §6 | ~1 s |

Summary of results (details in the `results_*.txt` files and in Table 2 of the report):

* Lemmas 2.1 and 4.1 agree with the definition (2.20) to relative error `2.7e-12` over 140 cases.
* The Casimir equation holds with eigenvalue `1/4 - nu^2` (relative accuracy `3e-8`), which confirms the sign issue F1.
* Parseval holds to 12 digits, for the principal, complementary and discrete series.
* Lemma 4.2: the bound `|phi_{l1,l2}| <= phi_{0,0}(., Re nu)` holds, but the printed bound fails as `u -> 0` (F4).
* Lemma 4.3: the ratio to the main term at `u = 1e10` lies between 0.845 and 1.000, and the signs are `(-1)^{l/2}` (F5).
* GM0 Proposition 6.1: the lower bound fails for `l` greater than about `60 K` (F2), which does not affect GM-I.
* Lemma 6.4: `k_Z(a_u) sqrt(1+u)` lies in `[0.95, 1.43]` for `1 <= u <= 10 Z` and vanishes for `u >= 64 Z`.
* End-to-end: `|D| Y^{1/2} <= 0.017` for `q in {1, 7, 101}` and `Y in [1e-5, 1e-2]`.
