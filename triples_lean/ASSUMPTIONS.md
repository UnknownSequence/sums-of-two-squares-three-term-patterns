# Assumptions of the formalization

This file lists every mathematical input that the Lean formalization of *Sums of two squares in
three-term patterns* (`triples_final.pdf`) takes for granted, apart from Mathlib.

**How the assumptions enter.** Nothing is declared with `axiom`. Each assumption is a `Prop`
(in `TriplesFinal/Assumptions/Assumptions.lean`) or a field of a data structure (in
`TriplesFinal/Assumptions/Defs.lean`), and the theorems that need it take it as a hypothesis.
A mis-stated assumption can therefore only make the theorems that use it vacuous; it cannot make
the library inconsistent. `Report.lean` (run with `lake env lean Report.lean`) prints the axioms
of the main theorems: only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`.
No `sorry` is left in the library, so the main theorems are proved from the assumptions below.

## The main theorems and their hypotheses

| theorem | Lean name | hypothesis bundle |
|---|---|---|
| Theorem 1.1 (exponent `δ_θ`) | `Triples.theorem_1_1` | `AssumptionsAt θ`, for an admissible `θ ∈ [0, 1/2)` |
| Theorem 1.3 (exponent `δ'_θ`) | `Triples.theorem_1_3` | `AssumptionsDIAt θ` |
| Corollary 1.2 (`δ < 25/278`) | `Triples.corollary_1_2` | `Assumptions = AssumptionsAt (7/64)` |
| Corollary 1.2 under Selberg's conjecture (`δ < 1/10`) | `Triples.corollary_1_2_selberg` | `AssumptionsAt 0` |

`AssumptionsAt θ` consists of `ArithmeticAssumptions`, `BesselAssumptions`, `SelbergConvolution`
and `SpectralHypothesis θ`. `AssumptionsDIAt θ` is the same with `SpectralHypothesisDI θ`, which
omits Pascadi's inequality.

## 1. Arithmetic inputs (`ArithmeticAssumptions`)

| Lean name | statement | source | used in |
|---|---|---|---|
| `SiegelTheorem` | for every `ε > 0` there is `c > 0` with `|L(1, χ)| ≥ c q^(-ε)` for every primitive real non-principal character `χ` mod `q` | Siegel; [Da, Ch. 21] | Lemma 5.3(d): the lower bound for `L_d` |
| `PolyaVinogradov` | `|∑_{n ≤ y} χ(n)| ≤ C √q log q` for every non-principal character `χ` mod `q ≥ 2` | Pólya–Vinogradov; [Da, Ch. 23] | Lemma 5.3(b)–(d), Lemma 7.2 |
| `PrimesInAPLowerBound` | for `(a, q) = 1` there are `c > 0`, `x₀` with `#{p ≡ a (mod q) : x/2 < p ≤ x} ≥ c x / log x` for `x ≥ x₀` | prime number theorem in arithmetic progressions | §4: good primes in dyadic ranges |

## 2. Bessel functions and the Gamma function (`BesselAssumptions`)

The `K`-Bessel function is *defined* in `Defs.lean` by the integral representation
`K_ν(y) = ½ ∫_ℝ exp(-y cosh σ + νσ) dσ` [Wat, §6.22].

| Lean name | statement | source | used in |
|---|---|---|---|
| `BesselMellin` | `∫_0^∞ K_{it}(y) y^(w-1) dy = 2^(w-2) Γ((w+it)/2) Γ((w-it)/2)` for real `t` and `Re w > 0` | [GR, 6.561.16] | Lemma 11.2 (the Mellin–Barnes formula, by Mellin inversion on `Re w = 1/2`) |
| `StirlingBound` | `|Γ(-3/4 + iτ)| ≤ C (1 + |τ|)^(-5/4) e^(-π|τ|/2)` | Stirling's formula | Lemma 11.2: the bound for `G_t`, and (by Phragmén–Lindelöf) the bound for `Γ` in the strip `-3/4 ≤ Re s ≤ 1/4` used in the contour shift |

## 3. Spectral theory of `Γ₀(q)` (`SpectralHypothesis θ`, `SpectralHypothesisDI θ`)

The spectral theory enters as an abstract *spectral package*. `SpectralData q` (in `Defs.lean`)
records, for the level `q`, an orthonormal basis of Maass cusp forms `u_j` with spectral
parameters `t_j` and Fourier coefficients `ρ_j(n)` at `∞` (in the normalisation of
[Pas, (3.15)]), the Eisenstein series `E_𝔰(z, 1/2 + ir)` at the finitely many cusps `𝔰` with
their Fourier coefficients `ρ_𝔰(n, r)`, and the volume of `Γ₀(q) \ ℍ`. Two properties are part of
the structure itself:

| field | statement | source |
|---|---|---|
| `finite_le` | only finitely many `t_j` satisfy `|t_j| ≤ T`, for every `T` | discreteness of the spectrum (Weyl's law) [Iw, Ch. 11] |
| `t_mem` | `t_j ∈ [0, ∞) ∪ i(0, 1/2)` | `λ_j = 1/4 + t_j² > 0` for cusp forms [Iw, Ch. 4] |

`SpectralHypothesis θ` says: there are constants `C(η)` such that for every level `q ≥ 1` there is
spectral data `D : SpectralData q` with all of the following properties (with the same `C(η)` for
every `q`). `SpectralHypothesisDI θ` is the same without `LargeSievePascadi`.

| Lean name | statement | source | used in |
|---|---|---|---|
| `PoincareExpansion` | the spectral expansion of the Poincaré series `P_{g,h}`, with `⟨P_{g,h}, u_j⟩ = conj(ρ_j(h)) ǧ(t_j)` (unfolding), absolutely convergent | [Iw, Theorem 7.3] | Lemma 10.1 |
| `PreTrace` | the pre-trace formula, summed over a finite family of points | [Iw, Theorem 7.4] | Lemma 10.7 |
| `LargeSieveDI2 C` | `∑_{|t_j| ≤ T} |∑ a_n ρ_j(n)|²/cosh(πt_j) + ∑_𝔰 ∫_{-T}^{T} |∑ a_n ρ_𝔰(n, r)|²/cosh(πr) dr ≤ C(η)(T² + M^(1+η)/q) ∑ |a_n|²` for `a_n` supported on `(M, 2M]` | [DI, Theorem 2]; [Pas, Lemma H] | Lemma 10.2 |
| `LargeSieveDI5 C` | `∑_{exc} 𝒴^(2θ_j) |∑ a_n ρ_j(n)|² ≤ C(η)(qM)^η (1 + M/q) ∑ |a_n|²` for `1 ≤ 𝒴 ≤ max(1, q/M)` | [DI, Theorem 5]; [Pas, Theorem A] | Lemma 10.3 (Theorem 6.1(b)) |
| `LargeSievePascadi C` | `∑_{exc} 𝒴^(2θ_j) |∑_{n ∼ M} e(nα) ρ_j(n)|² ≤ C(η)(qM)^η (1 + M/q) M` for `1 ≤ 𝒴 ≤ max(M, q)/(1 + M‖α‖)` | [Pas, Theorem 2] | Lemmas 10.4–10.5 (Theorem 6.1(a)) |
| `ExceptionalBound θ` | `θ_j ≤ θ` for every exceptional `t_j = iθ_j` (admissibility of `θ`) | Kim–Sarnak [Kim, Appendix 2] for `θ = 7/64`; `θ = 0` is Selberg's conjecture | Theorem 6.1 |
| `EisensteinContinuous` | `r ↦ ρ_𝔰(n, r)` and `r ↦ E_𝔰(z, 1/2 + ir)` are continuous | analyticity of Eisenstein series in `s` [Iw, Ch. 6] | the continuous spectrum in the proof of Theorem 6.1 (`TypeIProof/ContinuousFamily.lean`) |

## 4. The convolution of point-pair invariants (`SelbergConvolution`)

| Lean name | statement | source | used in |
|---|---|---|---|
| `SelbergConvolution` | for smooth compactly supported profiles `φ₁, φ₂` there is a smooth compactly supported `φ` with `φ(u(z, w)) = (k₁ * k₂)(z, w)` and `h_φ = h_{φ₁} h_{φ₂}` | [Iw, Theorem 1.14] | Lemma 10.7 |

## What is *not* assumed

Classical facts that are elementary enough are proved in the library rather than assumed:
Jacobi's formula for `r(n)`, the divisor bound, the count of solutions of Pell-type equations,
reduction theory of binary quadratic forms, Poisson summation for the weights of §9 (from
Mathlib's Poisson summation formula), the positivity of `L(1, χ)` for real characters,
`L(1, χ₄) = π/4`, the hyperbolic integrals behind Lemma 10.7 (areas of discs, the radial formula
for the Selberg transform), `|Γ(iτ)|² = π/(τ sinh πτ)`, bounds for `Γ` in vertical strips, the
Mellin–Barnes formula of Lemma 11.2 (by Mellin inversion and a contour shift), and all the
analysis of §§9–12, including the assembly of the proof of Theorem 6.1.

## References

* [Da] H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Springer, 2000.
* [DI] J.-M. Deshouillers, H. Iwaniec, *Kloosterman sums and Fourier coefficients of cusp forms*,
  Invent. Math. 70 (1982), 219–288.
* [GR] I. S. Gradshteyn, I. M. Ryzhik, *Table of Integrals, Series, and Products*.
* [Iw] H. Iwaniec, *Spectral Methods of Automorphic Forms*, 2nd ed., AMS, 2002.
* [Kim] H. Kim, *Functoriality for the exterior square of GL₄ and the symmetric fourth of GL₂*
  (with appendices by D. Ramakrishnan and by H. Kim and P. Sarnak), JAMS 16 (2003), 139–183.
* [Pas] A. Pascadi, *Large sieve inequalities for exceptional Maass forms and applications*,
  Forum Math. Pi 14 (2026), e8.
* [Wat] G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., CUP, 1944.
