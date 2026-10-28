# Sums of two squares in three-term patterns

**Siddharth Iyer and Claude (Anthropic).** Siddharth Iyer posed the question and gave the direction of attack;
Claude developed it into the results, the papers and the Lean formalization below (see
[Provenance](#provenance)). The follow-up note in [`rescaled_families/`](rescaled_families/) is by Claude, building
on Siddharth Iyer's family construction.

For fixed integers `0 < a < b`, let `S_{a,b}(x)` be the number of `n ≤ x` such that `n`, `n + a` and `n + b`
are all sums of two squares.

> **Theorem.** `S_{a,b}(x) ≫ x^{1/2 + δ}` for every `δ < 25/278 = 0.0899…`.

For example, `n − 1`, `n` and `n + 1` are all sums of two squares for `≫ x^{1/2 + δ}` integers `n ≤ x`.
One-parameter families such as `n = m² + 1` give only about `x^{1/2}` such `n`, and as far as we know no lower
bound `x^{1/2 + δ}` with `δ > 0` was known for any three-term pattern. The conjectured order of magnitude
(Freiberg, Kurlberg and Rosenzweig) is `x (log x)^{−3/2}`.

More precisely, if `θ` is an exponent towards Selberg's eigenvalue conjecture for all `Γ₀(q)`, then every
`δ < (1 − 2θ)/(10 − 12θ)` is admissible. The Kim–Sarnak bound `θ = 7/64` gives `25/278`, and Selberg's
conjecture (`θ = 0`) would give `1/10`. With only the large sieve inequalities of Deshouillers and Iwaniec
(1982), the same argument gives every `δ < (1 − 2θ)/(10 − 8θ)`, which is `25/292` for `θ = 7/64`.

> **Follow-up.** The note in [`rescaled_families/`](rescaled_families/) improves this to every
> `δ < (1 − 2θ)/(8 − 8θ)`: `25/228 = 0.1096…` for `θ = 7/64`, and `1/8` under Selberg's conjecture. The same bound
> holds for the number of `n ≤ x` such that `n³ + a³` is a sum of two squares. See
> [Follow-up: rescaled families](#follow-up-rescaled-families).

**Status.** Research draft, not refereed. Besides independent AI referee passes, the final paper has been
formalized in Lean 4: its main theorems are proved there, with no `sorry`, from the published results listed
under [Assumptions](#assumptions), which enter as explicit hypotheses. The follow-up note in
[`rescaled_families/`](rescaled_families/) has had an independent AI referee pass but **has no Lean
formalization**.

## The paper

**[`triples_final/triples_final.pdf`](triples_final/triples_final.pdf)** (33 pages) is the final,
self-contained version and the main document of this repository. Its TeX source and the scripts for its
numerical checks are in [`triples_final/`](triples_final/).

The method in brief. An identity makes two of the three numbers sums of two squares automatically, and the
third runs through the values of a quadratic polynomial attached to a prime `d`. Counting these values with the
weight `r(n)` leads to Type I sums over the roots of quadratic congruences, which are estimated by the method of
Duke, Friedlander and Iwaniec. Poisson summation turns them into Poincaré series on `Γ₀(4Ed)` evaluated at
Heegner points. In the spectral expansion, the Fourier coefficients are controlled by the large sieve
inequalities of Deshouillers–Iwaniec and of Pascadi, and the values at the Heegner points by the pre-trace
formula and an elementary count of pairs of Heegner points at bounded distance.

## The Lean formalization

[`triples_lean/`](triples_lean/) is a Lean 4 + Mathlib formalization of the final paper. Its main theorems, in
[`triples_lean/TriplesFinal/Main.lean`](triples_lean/TriplesFinal/Main.lean), are:

```lean
-- Theorem 1.1: every δ < (1 - 2θ)/(10 - 12θ), for every admissible exponent θ
theorem Triples.theorem_1_1 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hA : AssumptionsAt θ)
    (a b : ℕ) (ha : 0 < a) (hab : a < b) {δ : ℝ} (hδ : δ < deltaA θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x

-- Corollary 1.2: with the Kim–Sarnak exponent θ = 7/64, every δ < 25/278
theorem Triples.corollary_1_2 (hA : Assumptions) (a b : ℕ) (ha : 0 < a) (hab : a < b) {δ : ℝ}
    (hδ : δ < 25 / 278) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x

-- Theorem 1.3: with the Deshouillers–Iwaniec inequalities only, every δ < (1 - 2θ)/(10 - 8θ)
theorem Triples.theorem_1_3 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hA : AssumptionsDIAt θ)
    (a b : ℕ) (ha : 0 < a) (hab : a < b) {δ : ℝ} (hδ : δ < deltaB θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x
```

Here `S a b x = #{1 ≤ n ≤ x : n, n + a and n + b are sums of two squares}`,
`deltaA θ = (1 − 2θ)/(10 − 12θ)`, `deltaB θ = (1 − 2θ)/(10 − 8θ)`, and `Assumptions = AssumptionsAt (7/64)`.
`Triples.corollary_1_2_consecutive` is the special case `n, n + 1, n + 2`.

* There is no `sorry` and no `axiom` in the project. `#print axioms` for these theorems lists only Lean's
  standard axioms `propext`, `Classical.choice` and `Quot.sound`.
  [`triples_lean/Report.lean`](triples_lean/Report.lean) checks this for the main theorems and the main lemmas.
* Every step of the paper is formalized and proved from the assumptions below: the families and the 2-adic
  analysis, good primes, the singular series (with Siegel's bound), the asymptotic formula with its main and
  error terms, the parametrisation of the roots by Heegner points and the pair count, Poisson summation and the
  Heegner–Poincaré identity, the spectral expansion, Pascadi's inequality with smooth weights, the bound for the
  Heegner side, the Bessel transform (including the Mellin–Barnes formula for `K_{it}`, by Mellin inversion and a
  contour shift), and the Type I estimate (Theorem 6.1) on which the whole argument rests.
* [`triples_lean/STATUS.md`](triples_lean/STATUS.md) maps each lemma of the paper to its Lean files, and
  [`triples_lean/README.md`](triples_lean/README.md) lists the places where the formal proof departs from the
  paper.

## Assumptions

The formalization takes the following published results as hypotheses, bundled into `AssumptionsAt θ`.
Nothing else is assumed beyond Mathlib. The exact Lean statements, their normalisations and where each one is
used are in **[`triples_lean/ASSUMPTIONS.md`](triples_lean/ASSUMPTIONS.md)**.

| Lean name | Statement | Source |
|---|---|---|
| `SiegelTheorem` | `L(1, χ) ≫_ε q^{−ε}` for primitive real characters `χ` mod `q` | Siegel; Davenport, *Multiplicative Number Theory*, Ch. 21 |
| `PolyaVinogradov` | `∑_{n ≤ y} χ(n) ≪ √q log q` for non-principal characters `χ` mod `q` | Pólya–Vinogradov; Davenport, Ch. 23 |
| `PrimesInAPLowerBound` | `≫ x / log x` primes `p ≡ a (mod q)` in `(x/2, x]` when `(a, q) = 1` | prime number theorem in arithmetic progressions |
| `BesselMellin` | `∫₀^∞ K_{it}(y) y^{w−1} dy = 2^{w−2} Γ((w+it)/2) Γ((w−it)/2)` for `Re w > 0` | Gradshteyn–Ryzhik 6.561.16 |
| `StirlingBound` | `Γ(−3/4 + iτ) ≪ (1 + \|τ\|)^{−5/4} e^{−π\|τ\|/2}` | Stirling's formula |
| `PoincareExpansion` | spectral expansion of Poincaré series on `Γ₀(q)`, with unfolding | Iwaniec, *Spectral Methods of Automorphic Forms*, Thm 7.3 |
| `PreTrace` | the pre-trace formula, summed over finitely many points | Iwaniec, Thm 7.4 |
| `LargeSieveDI2` | large sieve inequality for the full spectrum | Deshouillers–Iwaniec (1982), Thm 2 |
| `LargeSieveDI5` | large sieve inequality for the exceptional spectrum | Deshouillers–Iwaniec (1982), Thm 5 |
| `LargeSievePascadi` | large sieve inequality for exceptional Maass forms with exponential phases (Theorem 1.1 only) | Pascadi, Forum Math. Pi 14 (2026), Thm 2 |
| `ExceptionalBound θ` | the exceptional eigenvalues satisfy `θ_j ≤ θ` | Kim–Sarnak (`θ = 7/64`) |
| `EisensteinContinuous` | `r ↦ ρ_𝔰(n, r)` and `r ↦ E_𝔰(z, 1/2 + ir)` are continuous | Iwaniec, Ch. 6 |
| `SelbergConvolution` | the Selberg transform of a convolution is the product of the transforms | Iwaniec, Thm 1.14 |

The spectral inputs are stated for an abstract structure `SpectralData q` (Maass cusp forms, Eisenstein series
and their Fourier coefficients for `Γ₀(q)`, normalised as in Pascadi's paper), with large sieve constants that
are uniform in `q`. The structure also records that the spectrum is discrete and that `λ_j = 1/4 + t_j² > 0`.

A hypothesis stated wrongly cannot make the library inconsistent, but it could make the theorems that use it
vacuous. The statements were transcribed from the cited sources by Claude and have not yet been compared with
them by a human. That comparison is the main check a reader should make before relying on the formalization.

## Follow-up: rescaled families

**[`rescaled_families/rescaled_families.pdf`](rescaled_families/rescaled_families.pdf)** (14 pages),
*Rescaled families and sums of two squares in three-term patterns and along `n³ + a³`*, by Claude (Anthropic),
is a follow-up note to the final paper. It is **not formalized in Lean**; the Lean project covers the final
paper only.

The Type I estimate of the final paper loses a factor that depends on the discriminant of the quadratic
polynomial but not on its level. Inserting a square factor `r²`, with `r ≡ 1 (mod 4)` prime, into the identity
of the final paper,

```
2rdQ = u² + d² + r²B²   ⟹   4r²P(P + B) = (rQ − d)² + u²,
```

gives families of level `rd` whose discriminant is only `≍ (r + d)²`, and for `r ≍ d` these do better. The same
construction works for `n³ + a³ = m(m² − 3am + 3a²)` with `m = n + a`: if
`rDm = ℓ² + ((D + 3ar)/2)² − 3a²r²`, then `(2ℓ)² + (2rm − 3ar − D)² = 4r²(m² − 3am + 3a²)`. The analytic input
is the Type I estimate of the final paper, extended to levels with at most two prime factors.

| `θ` | final paper | follow-up note | final paper, DI only | follow-up note, DI only |
|---|---|---|---|---|
| `1/4` (Selberg) | `1/14` | `1/12` | `1/16` | `1/14` |
| `7/64` (Kim–Sarnak) | `25/278 = 0.0899` | `25/228 = 0.1096` | `25/292 = 0.0856` | `25/242 = 0.1033` |
| `0` (Selberg's conjecture) | `1/10` | `1/8` | `1/10` | `1/8` |

The table lists the exponents `δ` such that `S_{a,b}(x) ≫ x^{1/2 + δ}` for every smaller `δ`. The columns of the
follow-up note also hold for `C_a(x) = #{n ≤ x : n³ + a³ is a sum of two squares}`. "DI only" means using only the
large sieve inequalities of Deshouillers and Iwaniec. See
[`rescaled_families/README.md`](rescaled_families/README.md) for more.

## Contents

The papers are listed in the order in which they were written. Paper 6 is the final version of the project,
and 7 is a later follow-up note.

| | Folder | Document |
|---|---|---|
| 1 | [`earlier_versions/1_consecutive_sos/`](earlier_versions/1_consecutive_sos/) | *Three consecutive sums of two squares: a power saving over the square-root bound*: the pattern `{n − 1, n, n + 1}` by Hooley's method, `δ < 1/52` |
| 2 | [`earlier_versions/2_general_triples/`](earlier_versions/2_general_triples/) | *Sums of two squares in three-term patterns: beyond the square-root bound*: all patterns, `δ < 1/24` |
| 3 | [`earlier_versions/3_triples_II/`](earlier_versions/3_triples_II/) | *Sums of two squares in three-term patterns, II: automorphic kernels and an improved exponent*: Heegner points and a kernel bound of Grimmelt–Merikoski, the first appearance of `25/278` |
| 4 | [`earlier_versions/4_GM_Theorem8.1_verification/`](earlier_versions/4_GM_Theorem8.1_verification/) | *Theorem 8.1 of Grimmelt–Merikoski: a verification report*: a line-by-line check of the external input of 3 |
| 5 | [`earlier_versions/5_triples_kuznetsov/`](earlier_versions/5_triples_kuznetsov/) | *Sums of two squares in three-term patterns via the Kuznetsov formula*: the Type I estimate from published inputs only, `25/278`, and `25/292` with the Deshouillers–Iwaniec inequalities alone |
| **6** | **[`triples_final/`](triples_final/)** | ***Sums of two squares in three-term patterns*: the final, self-contained paper** |
| | [`triples_lean/`](triples_lean/) | the Lean 4 formalization of paper 6 |
| 7 | [`rescaled_families/`](rescaled_families/) | *Rescaled families and sums of two squares in three-term patterns and along `n³ + a³`*: a follow-up note by Claude, `δ < 25/228` for all patterns and for `n³ + a³`; no Lean formalization |

Each folder holds the `.tex` source, the compiled `.pdf` and a `numerics/` folder with the scripts behind the
numerical checks. [`triples_final/README.md`](triples_final/README.md) explains what each earlier stage
contributed to the final paper; none of them is needed to read it.

## Building the Lean project

The project uses Lean `v4.34.1` and Mathlib `v4.34.1`.

```text
cd triples_lean
lake exe cache get          # download the compiled Mathlib
lake build                  # build the project
lake env lean Report.lean   # print the axioms used and any sorry dependencies
```

## Provenance

The question and the direction of attack came from Siddharth Iyer. He asked whether `S(x) ≫ x^{1/2 + δ}` for
some `δ > 0`, where `S(x)` counts the `n ≤ x` such that `n − 1`, `n` and `n + 1` are all sums of two squares,
and proposed the following approach.

1. Write `n² − 1 = a² + b²`. Then `(n − a)(n + a) = b² + 1`, so `n = C_d(b) = (d + (b² + 1)/d)/2` for some
   divisor `d` of `b² + 1`.
2. Restrict to divisors `1 ≤ d ≪ x^θ` for some `θ > 0`, and study how often the values `C_d(b) ≤ x` are
   themselves sums of two squares.
3. Carry this out with an averaging argument, drawing on J. Friedlander and H. Iwaniec, *Quadratic polynomials
   and quadratic forms*, Acta Math. 141 (1978), 1–15.

Since `n² − 1` is a sum of two squares exactly when `n − 1` and `n + 1` both are, the two outer members of each
triple come for free, and only the middle one has to be detected. This is the strategy of the first paper, where
`C_d(b)` and the range `d ≤ x^θ` appear exactly as proposed, and every later version builds on it.

Claude (Anthropic) developed this idea into the results presented here. It carried out the argument for three
consecutive integers (`δ < 1/52`), detecting sums of two squares with the weight `r(n)` and estimating the
resulting sums by Hooley's method, which is also the analytic engine of the Friedlander–Iwaniec paper. It then
extended the argument to all three-term patterns (`δ < 1/24`), recast the Type I sums in terms of Heegner points
and the spectral theory of `Γ₀(4Ed)` to reach `δ < 25/278`, checked the external input of that version line by
line, replaced it with a proof that uses only published results, wrote the final self-contained paper, and
formalized it in Lean 4.

The follow-up note in [`rescaled_families/`](rescaled_families/) was written by Claude. Its starting point is the
family construction above (steps 1 and 2), in the form it takes in the final paper: two of the three numbers are
made sums of two squares by an identity, and the third is counted along a quadratic polynomial. That construction
is Siddharth Iyer's only contribution to the note. The rescaled families, their analogue for `n³ + a³`, the
extension of the Type I estimate, the proofs and the computations were developed by Claude.

The papers are research drafts and have not been refereed.

## License

Released under the MIT License; see [`LICENSE`](LICENSE).
