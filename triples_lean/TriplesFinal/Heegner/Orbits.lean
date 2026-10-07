import TriplesFinal.Heegner.Stabiliser
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Lemma 8.1(b): representatives of the `Γ₀(q)`-orbits

If `Λ` is a system of representatives of the `SL₂(ℤ)`-orbits on `Q_N`, `𝒯` a system of
representatives of `Γ₀(q) \ SL₂(ℤ)`, and `𝒬 ⊆ Q_N` is `Γ₀(q)`-invariant, then the matrices
`τ ⋄ ζ` with `ζ ∈ Λ`, `τ ∈ 𝒯` and `τ ⋄ ζ ∈ 𝒬` form a system of representatives of the
`Γ₀(q)`-orbits on `𝒬`.

Paper: §8, Lemma 8.1(b).
-/

namespace Triples

open scoped MatrixGroups

namespace SymMat

open CongruenceSubgroup

theorem act_coe_mul (γ δ : SL(2, ℤ)) (g : SymMat) :
    act ((γ * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) g = act γ (act δ g) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, act_mul]

theorem act_coe_one (g : SymMat) : act ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) g = g := by
  rw [Matrix.SpecialLinearGroup.coe_one, act_one]

theorem act_coe_inv_act (γ : SL(2, ℤ)) (g : SymMat) :
    act ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (act γ g) = g := by
  rw [← act_coe_mul, inv_mul_cancel, act_coe_one]

theorem act_coe_act_inv (γ : SL(2, ℤ)) (g : SymMat) :
    act γ (act ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) g) = g := by
  rw [← act_coe_mul, mul_inv_cancel, act_coe_one]

theorem act_coe_neg (γ : SL(2, ℤ)) (g : SymMat) :
    act ((-γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) g = act γ g := by
  rw [Matrix.SpecialLinearGroup.coe_neg, act_neg]

/-- `Λ` is a system of representatives of the `SL₂(ℤ)`-orbits on `Q_N`. -/
def IsOrbitReps (N : ℤ) (Λ : Set SymMat) : Prop :=
  Λ ⊆ QN N ∧ ∀ g ∈ QN N, ∃! ζ : SymMat, ζ ∈ Λ ∧ ∃ γ : SL(2, ℤ), g = act γ ζ

/-- `𝒯` is a system of representatives of the cosets `Γ₀(q) \ SL₂(ℤ)`. -/
def IsCosetReps (q : ℕ) (T : Set SL(2, ℤ)) : Prop :=
  ∀ γ : SL(2, ℤ), ∃! τ : SL(2, ℤ), τ ∈ T ∧ ∃ δ ∈ Gamma0 q, γ = δ * τ

theorem neg_one_mem_Gamma0 (q : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 q := by
  rw [Gamma0_mem]
  simp [Matrix.SpecialLinearGroup.coe_neg]

/-- **Lemma 8.1(b)**, existence: every element of `𝒬` is `Γ₀(q)`-equivalent to some `τ ⋄ ζ`
with `ζ ∈ Λ`, `τ ∈ 𝒯` and `τ ⋄ ζ ∈ 𝒬`. -/
theorem orbit_reps_exists {N : ℤ} {q : ℕ} {Λ : Set SymMat} (hΛ : IsOrbitReps N Λ)
    {T : Set SL(2, ℤ)} (hT : IsCosetReps q T) {Q : Set SymMat} (hQ : Q ⊆ QN N)
    (hQinv : ∀ γ ∈ Gamma0 q, ∀ g ∈ Q, act γ g ∈ Q) {g : SymMat} (hg : g ∈ Q) :
    ∃ ζ ∈ Λ, ∃ τ ∈ T, act τ ζ ∈ Q ∧ ∃ γ ∈ Gamma0 q, g = act γ (act τ ζ) := by
  obtain ⟨ζ, ⟨hζ, γ, hγ⟩, -⟩ := hΛ.2 g (hQ hg)
  obtain ⟨τ, ⟨hτ, δ, hδ, rfl⟩, -⟩ := hT γ
  have hg' : g = act δ (act τ ζ) := by rw [hγ, act_coe_mul]
  refine ⟨ζ, hζ, τ, hτ, ?_, δ, hδ, hg'⟩
  have := hQinv δ⁻¹ (inv_mem hδ) g hg
  rwa [hg', act_coe_inv_act] at this

/-- **Lemma 8.1(b)**, uniqueness: if `τ' ⋄ ζ' = γ ⋄ (τ ⋄ ζ)` with `γ ∈ Γ₀(q)`, then `ζ' = ζ`
and `τ' = τ`. This uses Lemma 8.1(a). -/
theorem orbit_reps_unique {N : ℤ} (hN0 : 0 < N) (hsq : ¬ ∃ s : ℤ, N = s ^ 2)
    (h3 : ¬ ∃ s : ℤ, N = 3 * s ^ 2) {q : ℕ} {Λ : Set SymMat} (hΛ : IsOrbitReps N Λ)
    {T : Set SL(2, ℤ)} (hT : IsCosetReps q T) {ζ ζ' : SymMat} (hζ : ζ ∈ Λ) (hζ' : ζ' ∈ Λ)
    {τ τ' : SL(2, ℤ)} (hτ : τ ∈ T) (hτ' : τ' ∈ T) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 q)
    (h : act τ' ζ' = act γ (act τ ζ)) : ζ' = ζ ∧ τ' = τ := by
  -- `ζ' = (τ'⁻¹ γ τ) ⋄ ζ`
  have hζ'eq : ζ' = act ((τ'⁻¹ * γ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ζ := by
    rw [act_coe_mul, act_coe_mul, ← h, act_coe_inv_act]
  have hζζ' : ζ' = ζ :=
    ExistsUnique.unique (hΛ.2 ζ' (hΛ.1 hζ')) ⟨hζ', 1, (act_coe_one ζ').symm⟩
      ⟨hζ, _, hζ'eq⟩
  refine ⟨hζζ', ?_⟩
  -- `τ'⁻¹ γ τ` stabilises `ζ`, so it is `±1`
  have hfix : act ((τ'⁻¹ * γ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ζ = ζ := by
    rw [← hζ'eq, hζζ']
  have hpm := stabiliser_SL hN0 hsq h3 (hΛ.1 hζ) hfix
  -- hence `τ' = (±γ) τ` with `±γ ∈ Γ₀(q)`
  obtain ⟨δ, hδ, hτ'eq⟩ : ∃ δ ∈ Gamma0 q, τ' = δ * τ := by
    rcases hpm with h1 | h1
    · refine ⟨γ, hγ, ?_⟩
      have : τ' * (τ'⁻¹ * γ * τ) = τ' * 1 := by rw [h1]
      simpa [← mul_assoc] using this.symm
    · refine ⟨-γ, ?_, ?_⟩
      · have : -γ = (-1) * γ := by simp
        rw [this]
        exact mul_mem (neg_one_mem_Gamma0 q) hγ
      · have : τ' * (τ'⁻¹ * γ * τ) = τ' * (-1) := by rw [h1]
        simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_neg, mul_one] at this
        rw [neg_mul, this, neg_neg]
  exact ExistsUnique.unique (hT τ') ⟨hτ', 1, one_mem _, (one_mul τ').symm⟩
    ⟨hτ, δ, hδ, hτ'eq⟩

end SymMat

end Triples
