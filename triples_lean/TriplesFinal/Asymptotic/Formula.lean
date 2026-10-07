import TriplesFinal.Asymptotic.MainTerm
import TriplesFinal.Asymptotic.ErrorTerm

/-!
# Proposition 7.1: the asymptotic formula for `Σ_d(x)`

For good primes `d ≤ x^(1/4)` and `x ≥ x₀(a, b, ε)`:
`Σ_d(x) = 32 c_F 𝔏_d 2^(-j) √(x/d) + O(x^(1/4+ε) d^(1/2+ε) + x^(1/4+θ/2+ε) d^(3/4-3θ/2))`,
and with Theorem 6.1(b) in place of Theorem 6.1(a) the same with `d^(3/4-θ)`.

This follows from Lemmas 7.2 and 7.3, since `Σ_d(x) = ℳ_d + ℰ_d`.

Paper: §7, Proposition 7.1.
-/

namespace Triples

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- The combination step: `|Σ - main| ≤ |ℳ - main| + |ℰ|`. -/
theorem asymptotic_of_terms (F : Cutoff) (W : HyperbolaWeight) {ε β θ : ℝ}
    {C₁ C₂ x₁ x₂ : ℝ}
    (h₁ : ∀ x : ℝ, x₁ ≤ x → ∀ d : ℕ, P.IsGood d → (d : ℝ) ≤ x ^ (1 / 4 : ℝ) →
      |P.Md F W d x - 32 * F.cF * P.Ld d / 2 ^ P.j * Real.sqrt (x / d)| ≤
        C₁ * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε)))
    (h₂ : ∀ x : ℝ, x₂ ≤ x → ∀ d : ℕ, P.IsGood d → (d : ℝ) ≤ x ^ (1 / 4 : ℝ) →
      |P.Ed F W d x| ≤ C₂ * (x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ β)) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, P.IsGood d → (d : ℝ) ≤ x ^ (1 / 4 : ℝ) →
      |P.Sigma F.F d x - 32 * F.cF * P.Ld d / 2 ^ P.j * Real.sqrt (x / d)| ≤
        C * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε) +
          x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ β) := by
  refine ⟨|C₁| + |C₂|, max (max x₁ x₂) 1, fun x hx d hd hdx => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  have e1 := h₁ x hx1 d hd hdx
  have e2 := h₂ x hx2 d hd hdx
  set A := x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε) with hA
  set B := x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ β with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  set main := 32 * F.cF * P.Ld d / 2 ^ P.j * Real.sqrt (x / d)
  have hsplit : P.Sigma F.F d x - main = (P.Md F W d x - main) + P.Ed F W d x := by
    unfold Ed; ring
  rw [hsplit]
  calc |(P.Md F W d x - main) + P.Ed F W d x|
      ≤ |P.Md F W d x - main| + |P.Ed F W d x| := abs_add_le _ _
    _ ≤ C₁ * A + C₂ * B := add_le_add e1 e2
    _ ≤ |C₁| * A + |C₂| * B := by
        gcongr
        · exact le_abs_self _
        · exact le_abs_self _
    _ ≤ (|C₁| + |C₂|) * (A + B) := by
        have := abs_nonneg C₁
        have := abs_nonneg C₂
        nlinarith

/-- **Proposition 7.1** (with Theorem 6.1(a)). -/
theorem asymptotic_a {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hA : AssumptionsAt θ)
    (F : Cutoff) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, P.IsGood d → (d : ℝ) ≤ x ^ (1 / 4 : ℝ) →
      |P.Sigma F.F d x - 32 * F.cF * P.Ld d / 2 ^ P.j * Real.sqrt (x / d)| ≤
        C * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε) +
          x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ (3 / 4 - 3 * θ / 2)) := by
  obtain ⟨W⟩ := exists_hyperbolaWeight
  obtain ⟨C₁, x₁, h₁⟩ := P.main_term hA.arith.polyaVinogradov F W hε hε'
  obtain ⟨C₂, x₂, h₂⟩ :=
    P.error_term_a hθ0 hθ hA.bessel hA.selbergConv hA.spectral F W hε hε'
  exact P.asymptotic_of_terms F W h₁ h₂

/-- **Proposition 7.1** (with Theorem 6.1(b)). -/
theorem asymptotic_b {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hA : AssumptionsDIAt θ)
    (F : Cutoff) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, P.IsGood d → (d : ℝ) ≤ x ^ (1 / 4 : ℝ) →
      |P.Sigma F.F d x - 32 * F.cF * P.Ld d / 2 ^ P.j * Real.sqrt (x / d)| ≤
        C * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε) +
          x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ (3 / 4 - θ)) := by
  obtain ⟨W⟩ := exists_hyperbolaWeight
  obtain ⟨C₁, x₁, h₁⟩ := P.main_term hA.arith.polyaVinogradov F W hε hε'
  obtain ⟨C₂, x₂, h₂⟩ :=
    P.error_term_b hθ0 hθ hA.bessel hA.selbergConv hA.spectral F W hε hε'
  exact P.asymptotic_of_terms F W h₁ h₂

end PatternData

end Triples
