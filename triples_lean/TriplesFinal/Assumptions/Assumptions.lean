import TriplesFinal.Assumptions.Defs
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The assumed results

This file states, as `Prop`s, every published result that the formalization of
*Sums of two squares in three-term patterns* (`triples_final.pdf`) takes for granted.

Nothing here is declared with `axiom`. The theorems that need these results take them as
hypotheses, so a mis-stated assumption can only make those theorems vacuous; it cannot make the
rest of the library inconsistent. `#print axioms` for the main theorems lists only Lean's
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Classical facts that are elementary enough to be proved in the library are *not* assumed here:
Jacobi's formula for `r(n)`, the divisor bound, the count of solutions of a Pell-type equation,
Poisson summation for our weights (Lemma 9.1(a), from Mathlib's Poisson summation formula), the
positivity of `L(1, χ)` for real characters, bounds for `Γ` in vertical strips and the
Mellin–Barnes formula for `K_{it}` (Lemma 11.2) are proved. See `STATUS.md` and `ASSUMPTIONS.md`.

## Contents

* `ArithmeticAssumptions`: Siegel's theorem, the Pólya–Vinogradov inequality, and the prime
  number theorem in arithmetic progressions (lower bound form).
* `BesselAssumptions`: the Mellin transform of `K_{it}` and Stirling's bound on `Re s = -3/4`.
* The spectral theory of `Γ₀(q)`, as an abstract *spectral package*: for every level `q` there
  is spectral data (`SpectralData q`) satisfying
  - the spectral expansion of Poincaré series [Iw, Theorem 7.3], with the standard unfolding;
  - the pre-trace formula [Iw, Theorem 7.4];
  - the large sieve inequalities of Deshouillers and Iwaniec [DI, Theorems 2 and 5] and of
    Pascadi [Pas, Theorem 2], with constants independent of `q`;
  - the bound `θ_j ≤ θ` for the exceptional spectrum (admissibility of `θ`; Kim–Sarnak:
    `θ = 7/64`, i.e. `λ₁ ≥ 975/4096`);
  - the continuity of the Eisenstein data `ρ_𝔰(n, r)`, `E_𝔰(z, 1/2 + ir)` in `r`.
  These are bundled in `SpectralHypothesis θ` (for Theorem 1.1) and `SpectralHypothesisDI θ`
  (without Pascadi's inequality, for Theorem 1.3).
* `SelbergConvolution`: the convolution property of Selberg transforms [Iw, Theorem 1.14].
* `Assumptions`: everything used for Corollary 1.2 (with `θ = 7/64`).

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
-/

namespace Triples

open scoped MatrixGroups

open Complex MeasureTheory
open scoped UpperHalfPlane
open scoped ContDiff

noncomputable section

/-! ## Arithmetic inputs -/

/-- **Siegel's theorem** [Da, Ch. 21]: for every `ε > 0` there is `c > 0` such that
`|L(1, χ)| ≥ c q^(-ε)` for every primitive real non-principal Dirichlet character `χ` modulo `q`.
-/
def SiegelTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
      c * (q : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖

/-- **The Pólya–Vinogradov inequality** [Da, Ch. 23]: there is an absolute constant `C` such that
`|∑_{n ≤ y} χ(n)| ≤ C √q log q` for every non-principal Dirichlet character `χ` modulo `q ≥ 2`. -/
def PolyaVinogradov : Prop :=
  ∃ C : ℝ, ∀ q : ℕ, 2 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ y : ℕ,
    ‖∑ n ∈ Finset.range (y + 1), χ n‖ ≤ C * Real.sqrt q * Real.log q

/-- **The prime number theorem in arithmetic progressions**, in the lower bound form used in
§4: for `q ≥ 1` and `a` coprime to `q` there are `c > 0` and `x₀` such that for `x ≥ x₀`
there are at least `c x / log x` primes `p ≡ a (mod q)` in `(x/2, x]`. -/
def PrimesInAPLowerBound : Prop :=
  ∀ (q : ℕ) (a : ℤ), 0 < q → IsCoprime a q → ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    c * x / Real.log x ≤
      ({p : ℕ | p.Prime ∧ x / 2 < p ∧ (p : ℝ) ≤ x ∧ (p : ℤ) ≡ a [ZMOD q]}.ncard : ℝ)

/-- The arithmetic assumptions (used in §§4–5). -/
structure ArithmeticAssumptions : Prop where
  siegel : SiegelTheorem
  polyaVinogradov : PolyaVinogradov
  primesInAP : PrimesInAPLowerBound

/-! ## Bessel functions -/

/-- **The Mellin transform of `K_{it}`** [GR, 6.561.16]: for real `t` and `Re w > 0`,
`∫_0^∞ K_{it}(y) y^(w-1) dy = 2^(w-2) Γ((w+it)/2) Γ((w-it)/2)`. -/
def BesselMellin : Prop :=
  ∀ (t : ℝ) (w : ℂ), 0 < w.re →
    (∫ y in Set.Ioi (0 : ℝ), besselK (I * t) y * (y : ℂ) ^ (w - 1)) =
      (2 : ℂ) ^ (w - 2) * Complex.Gamma ((w + I * t) / 2) * Complex.Gamma ((w - I * t) / 2)

/-- **Stirling's bound** on the line `Re s = -3/4`:
`|Γ(-3/4 + iτ)| ≤ C (1 + |τ|)^(-5/4) e^(-π|τ|/2)` for all real `τ`. -/
def StirlingBound : Prop :=
  ∃ C : ℝ, ∀ τ : ℝ,
    ‖Complex.Gamma (-3 / 4 + I * τ)‖ ≤
      C * (1 + |τ|) ^ (-(5 : ℝ) / 4) * Real.exp (-Real.pi * |τ| / 2)

/-- The facts about Bessel functions and the Gamma function used in §11. -/
structure BesselAssumptions : Prop where
  besselMellin : BesselMellin
  stirling : StirlingBound

/-! ## The spectral package for `Γ₀(q)` -/

namespace SpectralData

variable {q : ℕ} (D : SpectralData q)

/-- **Spectral expansion of Poincaré series** [Iw, Theorem 7.3] together with the unfolding
computation `⟨P_{g,h}, u_j⟩ = conj(ρ_j(h)) ǧ(t_j)` (the proof of Lemma 10.1): for `g` smooth with
compact support in `(0, ∞)`, `h ≠ 0` and `z ∈ ℍ`, the expansion converges absolutely and
`P_{g,h}(z) = ∑_j conj(ρ_j(h)) ǧ(t_j) u_j(z) + (1/4π) ∑_𝔰 ∫ conj(ρ_𝔰(h, r)) ǧ(r) E_𝔰(z, 1/2+ir) dr`. -/
def PoincareExpansion : Prop :=
  ∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → (∃ a b : ℝ, 0 < a ∧ ∀ y, g y ≠ 0 → a ≤ y ∧ y ≤ b) →
  ∀ h : ℤ, h ≠ 0 → ∀ z : ℍ,
    Summable (fun j => ‖(starRingEnd ℂ) (D.ρ j h) * besselTransform g h (D.t j) * D.u j z‖) ∧
    (∀ 𝔰, Integrable (fun r : ℝ => (starRingEnd ℂ) (D.ρEis 𝔰 r h) * besselTransform g h r *
      D.Eis 𝔰 r z)) ∧
    poincare q g h z =
      (∑' j, (starRingEnd ℂ) (D.ρ j h) * besselTransform g h (D.t j) * D.u j z) +
        (1 / (4 * Real.pi) : ℂ) * ∑ 𝔰, ∫ r : ℝ, (starRingEnd ℂ) (D.ρEis 𝔰 r h) *
          besselTransform g h r * D.Eis 𝔰 r z

/-- **The pre-trace formula** [Iw, Theorem 7.4], summed over a finite family of points: for a
smooth compactly supported profile `φ` and points `z_1, …, z_n`,
`∑_j h(t_j) |∑_i u_j(z_i)|² + h(i/2) n²/vol + (1/4π) ∑_𝔰 ∫ h(r) |∑_i E_𝔰(z_i, 1/2+ir)|² dr`
equals `∑_{i,i'} ∑_{γ ∈ Γ₀(q)/{±1}} φ(u(z_i, γ z_{i'}))`; we write the right-hand side as half of
the sum over all matrices `γ ∈ Γ₀(q)` (note `-1 ∈ Γ₀(q)`). The constant eigenfunction
`vol^(-1/2)`, with `t = i/2`, is written separately. -/
def PreTrace : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
  ∀ (n : ℕ) (z : Fin n → ℍ),
    Summable (fun j => selbergTransform φ (D.t j) * ((‖∑ i, D.u j (z i)‖ ^ 2 : ℝ) : ℂ)) ∧
    (∀ 𝔰, Integrable (fun r : ℝ =>
      selbergTransform φ r * ((‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2 : ℝ) : ℂ))) ∧
    (∑' j, selbergTransform φ (D.t j) * ((‖∑ i, D.u j (z i)‖ ^ 2 : ℝ) : ℂ)) +
        selbergTransform φ (I / 2) * ((n : ℂ) ^ 2 / (D.vol : ℂ)) +
        (1 / (4 * Real.pi) : ℂ) * ∑ 𝔰, ∫ r : ℝ,
          selbergTransform φ r * ((‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2 : ℝ) : ℂ) =
      (((1 / 2 : ℝ) * ∑ i, ∑ i', ∑' γ : CongruenceSubgroup.Gamma0 q,
        φ (pointPair (z i) ((γ : SL(2, ℤ)) • z i')) : ℝ) : ℂ)

/-- **Large sieve inequality of Deshouillers and Iwaniec** [DI, Theorem 2] in the form of
[Pas, Lemma H] for the cusp `∞` (the Maass sum includes the exceptional forms): for `η > 0`,
`T ≥ 1`, `M ≥ 1/2` and `(a_n)` supported on `M < n ≤ 2M`,
`∑_{|t_j| ≤ T} |∑ a_n ρ_j(n)|² / cosh(π t_j) + ∑_𝔰 ∫_{-T}^{T} |∑ a_n ρ_𝔰(n, r)|² dr / cosh(πr)
  ≤ C(η) (T² + M^(1+η)/q) ∑ |a_n|²` (Lemma 10.2). -/
def LargeSieveDI2 (C : ℝ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ T : ℝ, 1 ≤ T → ∀ M : ℝ, 1 / 2 ≤ M → ∀ a : ℕ → ℂ,
    (∀ n, a n ≠ 0 → M < n ∧ (n : ℝ) ≤ 2 * M) →
    (∑ᶠ j ∈ {j | ‖D.t j‖ ≤ T},
        ‖∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, a n * D.ρ j n‖ ^ 2 / (Complex.cosh (Real.pi * D.t j)).re) +
      ∑ 𝔰, ∫ r in Set.Icc (-T) T,
        ‖∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, a n * D.ρEis 𝔰 r n‖ ^ 2 / Real.cosh (Real.pi * r) ≤
    C η * (T ^ 2 + M ^ (1 + η) / q) * ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2

/-- **Large sieve inequality of Deshouillers and Iwaniec for the exceptional spectrum**
[DI, Theorem 5]; see [Pas, Theorem A] (Lemma 10.3): for `η > 0`, `M ≥ 1/2`,
`1 ≤ 𝒴 ≤ max(1, q/M)` and `(a_n)` supported on `M < n ≤ 2M`,
`∑_{exc} 𝒴^(2θ_j) |∑ a_n ρ_j(n)|² ≤ C(η) (qM)^η (1 + M/q) ∑ |a_n|²`. -/
def LargeSieveDI5 (C : ℝ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ M : ℝ, 1 / 2 ≤ M → ∀ Y : ℝ, 1 ≤ Y → Y ≤ max 1 (q / M) →
  ∀ a : ℕ → ℂ, (∀ n, a n ≠ 0 → M < n ∧ (n : ℝ) ≤ 2 * M) →
    ∑ᶠ j ∈ {j | D.IsExceptional j},
        Y ^ (2 * (D.t j).im) * ‖∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, a n * D.ρ j n‖ ^ 2 ≤
      C η * (q * M) ^ η * (1 + M / q) * ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2

/-- **Pascadi's large sieve inequality** [Pas, Theorem 2] (dilation parameter `1`, cusp `∞`;
Lemma 10.4): for `η > 0`, `M ≥ 1/2`, `α ∈ ℝ` and `1 ≤ 𝒴 ≤ max(M, q)/(1 + M‖α‖)`,
`∑_{exc} 𝒴^(2θ_j) |∑_{M < n ≤ 2M} e(nα) ρ_j(n)|² ≤ C(η) (qM)^η (1 + M/q) M`. -/
def LargeSievePascadi (C : ℝ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ M : ℝ, 1 / 2 ≤ M → ∀ α : ℝ, ∀ Y : ℝ, 1 ≤ Y →
    Y ≤ max M q / (1 + M * |α - round α|) →
    ∑ᶠ j ∈ {j | D.IsExceptional j},
        Y ^ (2 * (D.t j).im) *
          ‖∑ n ∈ (Finset.Icc 1 ⌊2 * M⌋₊).filter (fun n : ℕ => M < n),
            Complex.exp (2 * Real.pi * I * (n * α)) * D.ρ j n‖ ^ 2 ≤
      C η * (q * M) ^ η * (1 + M / q) * M

/-- Admissibility of `θ` at level `q`: every exceptional `θ_j` satisfies `θ_j ≤ θ`. -/
def ExceptionalBound (θ : ℝ) : Prop := ∀ j, D.IsExceptional j → (D.t j).im ≤ θ

/-- **Continuity of the Eisenstein data in the spectral parameter**: `r ↦ ρ_𝔰(n, r)` and
`r ↦ E_𝔰(z, 1/2 + ir)` are continuous on `ℝ`. (They are real-analytic in `r`: the Eisenstein
series `E_𝔰(z, s)` and its Fourier coefficients are holomorphic in `s` near the line
`Re s = 1/2` [Iw, Ch. 6, Theorem 6.5 and (3.21)–(3.22)].) This is used to integrate over the
continuous spectrum in the proof of Theorem 6.1. -/
def EisensteinContinuous : Prop :=
  (∀ (𝔰 : D.κ) (n : ℤ), Continuous fun r : ℝ => D.ρEis 𝔰 r n) ∧
    ∀ (𝔰 : D.κ) (z : ℍ), Continuous fun r : ℝ => D.Eis 𝔰 r z

end SpectralData

/-- The **spectral hypothesis with the Deshouillers–Iwaniec inequalities only**, at exponent `θ`:
there are constants `C(η)` such that for every level `q ≥ 1` there is spectral data for `Γ₀(q)`
satisfying the expansion of Poincaré series, the pre-trace formula, [DI, Theorems 2 and 5] with
the constants `C(η)`, `θ_j ≤ θ`, and the continuity of the Eisenstein data. This is used for
Theorem 1.3. -/
def SpectralHypothesisDI (θ : ℝ) : Prop :=
  ∃ C : ℝ → ℝ, ∀ q : ℕ, 0 < q → ∃ D : SpectralData q,
    D.PoincareExpansion ∧ D.PreTrace ∧ D.LargeSieveDI2 C ∧ D.LargeSieveDI5 C ∧
      D.ExceptionalBound θ ∧ D.EisensteinContinuous

/-- The **spectral hypothesis** at exponent `θ`: as `SpectralHypothesisDI θ`, together with
Pascadi's inequality [Pas, Theorem 2]. This is used for Theorem 1.1. -/
def SpectralHypothesis (θ : ℝ) : Prop :=
  ∃ C : ℝ → ℝ, ∀ q : ℕ, 0 < q → ∃ D : SpectralData q,
    D.PoincareExpansion ∧ D.PreTrace ∧ D.LargeSieveDI2 C ∧ D.LargeSieveDI5 C ∧
      D.LargeSievePascadi C ∧ D.ExceptionalBound θ ∧ D.EisensteinContinuous

theorem SpectralHypothesis.toDI {θ : ℝ} (h : SpectralHypothesis θ) : SpectralHypothesisDI θ := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun q hq => ?_⟩
  obtain ⟨D, h1, h2, h3, h4, -, h6, h7⟩ := hC q hq
  exact ⟨D, h1, h2, h3, h4, h6, h7⟩

/-- **The convolution property of Selberg transforms** [Iw, Theorem 1.14]: for smooth compactly
supported profiles `φ₁, φ₂` there is a smooth compactly supported profile `φ` with
`φ(u(z, w)) = (k₁ * k₂)(z, w)` and `h_φ = h_{φ₁} h_{φ₂}`. -/
def SelbergConvolution : Prop :=
  ∀ φ₁ φ₂ : ℝ → ℝ, ContDiff ℝ ∞ φ₁ → HasCompactSupport φ₁ → ContDiff ℝ ∞ φ₂ →
    HasCompactSupport φ₂ → ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ z w : ℍ, φ (pointPair z w) = pairConv φ₁ φ₂ z w) ∧
      ∀ t : ℂ, selbergTransform φ t = selbergTransform φ₁ t * selbergTransform φ₂ t

/-- All assumptions used for Theorem 1.1 at an exponent `θ`. -/
structure AssumptionsAt (θ : ℝ) : Prop where
  arith : ArithmeticAssumptions
  bessel : BesselAssumptions
  selbergConv : SelbergConvolution
  spectral : SpectralHypothesis θ

/-- All assumptions used for Theorem 1.3 at an exponent `θ`. -/
structure AssumptionsDIAt (θ : ℝ) : Prop where
  arith : ArithmeticAssumptions
  bessel : BesselAssumptions
  selbergConv : SelbergConvolution
  spectral : SpectralHypothesisDI θ

/-- All assumptions used for Corollary 1.2: the arithmetic and Bessel inputs, the convolution
property of Selberg transforms, and the spectral hypothesis at the Kim–Sarnak exponent
`θ = 7/64` (`λ₁(Γ) ≥ 975/4096 = 1/4 - (7/64)²` [Kim, Appendix 2]). -/
abbrev Assumptions : Prop := AssumptionsAt (7 / 64)

theorem AssumptionsAt.toDI {θ : ℝ} (h : AssumptionsAt θ) : AssumptionsDIAt θ :=
  ⟨h.arith, h.bessel, h.selbergConv, h.spectral.toDI⟩

end

end Triples
