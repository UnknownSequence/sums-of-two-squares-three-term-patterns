# Sums of two squares in three-term patterns: final version

This folder contains the final, self-contained version of the project on three-term patterns of sums of
two squares, together with the scripts for its numerical checks. The earlier stages of the project are kept
in the folder `earlier_versions/` of this repository. The section "How the final version came about" below
lists them and says what each one contributed. You do not need to read them to follow the final paper. The
Lean 4 formalization of this paper is in `triples_lean/`.

## Contents

| file | |
|---|---|
| `triples_final.pdf` | the paper (33 pages) |
| `triples_final.tex` | its LaTeX source (a single file, `amsart`; compile twice with `pdflatex`) |
| `numerics/` | the scripts behind Section 14 and their outputs; see `numerics/README.md` |

## Results

Let `S_{a,b}(x)` be the number of `n <= x` such that `n`, `n+a` and `n+b` are all sums of two squares, where
`0 < a < b` are fixed. Let `theta` be an exponent towards Selberg's eigenvalue conjecture for all `Gamma_0(q)`.

* **Theorem 1.1.** `S_{a,b}(x) >> x^{1/2+delta}` for every `delta < (1-2theta)/(10-12theta)`. With the
  Kim–Sarnak exponent `theta = 7/64` (equivalently `lambda_1 >= 975/4096 = 1/4 - (7/64)^2` for the smallest
  Laplace eigenvalue, the bound quoted on Wikipedia) this is every `delta < 25/278 = 0.0899...`. Under Selberg's conjecture it
  is every `delta < 1/10`. For example, `n-1, n, n+1` are all sums of two squares for `>> x^{1/2+delta}` values of `n <= x`.
* **Theorem 1.3.** With only the large sieve inequalities of Deshouillers and Iwaniec (1982), the same argument
  gives every `delta < (1-2theta)/(10-8theta)`, which is `25/292 = 0.0856...` for `theta = 7/64`.

One-parameter constructions give only about `x^{1/2}` such `n`.

## Structure of the paper

1. Introduction: results, the method in six steps, notation, and a paragraph on the earlier versions.
2. The families: an identity makes two of the three numbers sums of two squares automatically.
3. Local analysis at the prime 2: all 2-adic conditions are put on the prime `d`.
4. Good primes and the deduction of Theorems 1.1 and 1.3 from Theorem 4.3 (the lower bound for `Sigma_d(x)`).
5. Arithmetic preliminaries: a smoothed hyperbola identity for `r(n)`, roots of quadratic congruences, the singular series.
6. The Type I estimate (Theorem 6.1, parts (a) and (b)).
7. The asymptotic formula for `Sigma_d(x)` (Proposition 7.1).
8. Heegner points: parametrisation of the roots by binary quadratic forms, and the pair count `P << N^{1+eps}` (Lemma 8.4).
9. Poisson summation and the Heegner–Poincaré identity.
10. Spectral expansion on `Gamma_0(4Ed)` and the large sieve inequalities (Deshouillers–Iwaniec, Pascadi).
11. The Bessel transform.
12. Proof of Theorem 6.1.
13. Remarks: where the loss is, the exceptional spectrum, why the hyperbola method is kept, other treatments
    (Weil's bound and Duke–Friedlander–Iwaniec), the Grimmelt–Merikoski kernel bound, effectivity, correlations of `r`.
14. Numerical checks.

## How the final version came about

The project went through five stages before this one. Each is kept in its own folder under
`earlier_versions/` in this repository.

1. **`earlier_versions/1_consecutive_sos/` — "Three consecutive sums of two squares: a power saving over the square-root bound".**
   This stage treats only the pattern `{n-1, n, n+1}`. The integers `n` for which `n^2 - 1` is a sum of two squares
   are exactly the numbers `(d + (b^2+1)/d)/2` with `d | b^2+1`. For such `n`, the numbers `n-1` and `n+1` are
   sums of two squares automatically. For primes `d = 1 mod 8`, these numbers are the values of a quadratic
   polynomial, and their `r`-weighted count is evaluated by Hooley's method (Gauss's correspondence plus Weil's
   bound). Result: `delta < 1/52`.
2. **`earlier_versions/2_general_triples/` — "Sums of two squares in three-term patterns: beyond the square-root bound" (called [I]).**
   This stage covers all patterns `{0,a,b}`, using the identity `kappa^2 n(n+b) = (X-d)^2 + u^2` with
   `2dX = u^2 + d^2 + g^2` and a 2-adic analysis. The method is still Hooley's with Weil's bound, with
   polynomial dependence on `d`. This admits primes `d <= x^{1/12-eps}`. Result: `delta < 1/24`
   (Remark 13.4 of the final paper).
3. **`earlier_versions/3_triples_II/` — "Sums of two squares in three-term patterns, II: automorphic kernels and an improved exponent" (called [II]).**
   The families were changed so that every 2-adic condition falls on `d`. The third number then becomes
   `2^{v-2}(E l^2 + H_d)/d` with `E in {4,8}`. The roots of the resulting quadratic congruences were parametrised
   by Heegner points of discriminant `-4EH_d` on `Gamma_0(4Ed)`, and the Type I sums were bounded with Theorem 8.1
   of Grimmelt–Merikoski (arXiv:2505.00489), a bound for weighted averages of automorphic kernels, together with
   two single-level kernel bounds. Result: Theorem 1.1, `delta < 25/278`. This is the first appearance of the
   exponent of the final paper. It relied on an unrefereed preprint.
4. **`earlier_versions/4_GM_Theorem8.1_verification/` — "Theorem 8.1 of Grimmelt–Merikoski: a verification report".**
   This is a line-by-line check of the external input of [II], with numerical tests of its analytic lemmas.
   Conclusion: the theorem is correct as stated. One sign error in a proof (Proposition 5.1 of GM-I) and one gap
   in an imported proof (Proposition 6.1 of GM0, in a range that GM-I does not use) were found, and both have
   local repairs.
5. **`earlier_versions/5_triples_kuznetsov/` — "Sums of two squares in three-term patterns via the Kuznetsov formula".**
   This is a second proof of the Type I estimate of [II], by the method of Duke–Friedlander–Iwaniec. Poisson
   summation gives Weyl sums, which are Poincaré series evaluated at Heegner points. These are expanded spectrally
   on `Gamma_0(4Ed)`. The frequency side is bounded with the Deshouillers–Iwaniec and Pascadi large sieve
   inequalities, and the Heegner side with the pre-trace formula and the pair count of [II]. This recovers
   `25/278` from published inputs only, and gives `25/292` (Theorem 1.3) with the 1982 inequalities alone.
   It does not use the kernel theorem of stage 4.
6. **`triples_final/` (this folder).** The final paper combines the analytic argument of stage 5 with the
   elementary parts of stage 3: the families, the 2-adic analysis, good primes, the hyperbola identity, the
   singular series, the asymptotic formula, the Heegner point parametrisation and counting, the remarks and the
   numerics. It is written so that a reader needs none of the earlier documents. In particular, it does not
   depend on Grimmelt–Merikoski, so stage 4 is not needed for its correctness.

### Where each part of the final paper comes from

| final paper | source |
|---|---|
| §1 Introduction | new; it merges the introductions of [II] and stage 5, and the literature survey of [I] |
| §§2–5 families, 2-adic analysis, good primes, preliminaries | [II] §§2–5, with the deduction of Theorem 1.3 added |
| §6 Type I estimate | stage 5, Theorem 2.1 (part (a) is [II], Proposition 6.5) |
| §7 asymptotic formula | [II] §7, with the variant for Theorem 6.1(b) from stage 5 |
| §8 Heegner points | [II] §6.2 and Steps 1–3 of [II], Lemma 6.4, rewritten as a direct count `P` of pairs of Heegner points instead of a kernel pairing |
| §9 Poisson summation, Heegner–Poincaré identity | stage 5, §3, with the Poisson formula derived in full |
| §§10–12 spectral expansion, large sieve, Bessel transform, proof | stage 5, §§4–7 |
| §13 Remarks | [II] §8 and stage 5, §8, rewritten so as not to refer to the earlier versions |
| §14 Numerical checks | [II] §9 and stage 5, §9, plus the exact values of `P` (new script `numerics/level_pairs.py`) |

### Changes made in the final version

* Self-containedness. No result is quoted from the earlier versions. The functional and kernel language of [II]
  is replaced by the pair count `P` of Lemma 8.4, which is what the pre-trace inequality (Lemma 10.7) needs.
* Theorem 6.1 states both the Pascadi version (a) and the Deshouillers–Iwaniec version (b), and Section 7
  carries both through to Theorems 1.1 and 1.3.
* The comparisons with the kernel approach (Remark 13.5), with Weil's bound and with Duke–Friedlander–Iwaniec
  (Remark 13.4), and the discussion of the loss (Remark 13.1), are now remarks inside the paper. Results of the
  earlier versions that are not proved in the final paper (the exponent `1/24`, the deduction from Grimmelt–Merikoski)
  are described there as such, and nothing in the proofs depends on them.
* Two independent referee passes (one for Sections 1–7, 13 and 14, one for Sections 8–12) found no critical or major
  problems. Their minor points were addressed: for example, a self-contained proof of Lemma 8.1(a), uniformity in
  Remark 13.6, explicit hypotheses for (12.1), and outward rounding of the numbers in Section 14.
* Notation was unified, because the two sources used some of the same letters for different things.
  The Bessel transform is `g_h-check` and the weight is `g_h` (was `f_h`). The hyperbolic Laplacian is `Delta_H`.
  The identity matrix is written `1`, because `I` is the number of Heegner points. The Selberg transform in
  Lemma 10.7 is `k-tilde`. Bottom rows of coset representatives are `(tau_3, tau_4)`.
  The Bessel integration variable is `sigma` (was `v`, which is the 2-adic parameter). The derivative scale in
  Lemma 10.5 is `L_G` (was `Lambda`, which is the set of reduced forms). The parameters in Lemma 12.1 are
  `alpha_1, beta_1, gamma_1` (were `a, b, c`, which are pattern parameters). The integration-by-parts orders are
  `k_eta`, `k'_eta`.
* Numerics. All scripts were rerun, and their docstrings refer to the final numbering. `level_pairs.py`
  computes `P` exactly in two independent ways, and `exponents.py` also checks the conditional exponents of
  Remark 13.1.

## Inputs

Besides elementary arguments, the proof uses Siegel's theorem (avoidable, see Remark 13.6), the Pólya–Vinogradov
inequality, the prime number theorem in arithmetic progressions, the spectral theory of `Gamma_0(q)` (Iwaniec's
book), the large sieve inequalities of Deshouillers–Iwaniec (Invent. Math. 1982, Theorems 2 and 5), Pascadi's
large sieve inequality for exceptional Maass forms (Forum Math. Pi 14 (2026), e8, Theorem 2; only for
Theorem 1.1), and the Kim–Sarnak bound `theta = 7/64`. All of these are published.
