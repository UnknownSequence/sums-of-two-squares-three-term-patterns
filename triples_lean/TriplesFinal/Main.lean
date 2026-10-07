import TriplesFinal.Main.Deduction

/-!
# The main theorems

* **Theorem 1.1.** Let `0 < a < b` and let `θ ∈ [0, 1/2)` be admissible. For every
  `δ < δ_θ = (1 - 2θ)/(10 - 12θ)`, `S_{a,b}(x) ≫ x^(1/2+δ)` for `x ≥ x₀(a, b, δ)`.
* **Corollary 1.2.** With the Kim–Sarnak exponent `θ = 7/64`: every `δ < 25/278`; under
  Selberg's eigenvalue conjecture (`θ = 0`): every `δ < 1/10`. In particular there are
  `≫ x^(1/2+δ)` integers `n ≤ x` with `n, n + 1, n + 2` all sums of two squares.
* **Theorem 1.3.** With the Deshouillers–Iwaniec inequalities only: every
  `δ < δ'_θ = (1 - 2θ)/(10 - 8θ)`.

"Admissible" and the other published inputs are the hypotheses `AssumptionsAt θ`
(respectively `AssumptionsDIAt θ`); see `TriplesFinal/Assumptions/Assumptions.lean`.

Paper: §1, Theorems 1.1 and 1.3, Corollary 1.2; deduction in §4.
-/

namespace Triples

/-- `δ_θ = (1 - 2θ)/(10 - 12θ)`. -/
noncomputable def deltaA (θ : ℝ) : ℝ := (1 - 2 * θ) / (10 - 12 * θ)

/-- `δ'_θ = (1 - 2θ)/(10 - 8θ)`. -/
noncomputable def deltaB (θ : ℝ) : ℝ := (1 - 2 * θ) / (10 - 8 * θ)

theorem deltaA_eq (θ : ℝ) : deltaA θ = varpiA θ / 2 := by
  unfold deltaA varpiA
  rw [div_div, show (10 : ℝ) - 12 * θ = (5 - 6 * θ) * 2 by ring]

theorem deltaB_eq (θ : ℝ) : deltaB θ = varpiB θ / 2 := by
  unfold deltaB varpiB
  rw [div_div, show (10 : ℝ) - 8 * θ = (5 - 4 * θ) * 2 by ring]

theorem varpiA_pos {θ : ℝ} (hθ : θ < 1 / 2) : 0 < varpiA θ := by
  unfold varpiA; apply div_pos <;> linarith

theorem varpiB_pos {θ : ℝ} (hθ : θ < 1 / 2) : 0 < varpiB θ := by
  unfold varpiB; apply div_pos <;> linarith

/-- A `ϖ` strictly between `2δ` (or `0`) and `ϖ_max`. -/
theorem exists_varpi {δ ϖmax : ℝ} (hmax : 0 < ϖmax) (hδ : δ < ϖmax / 2) :
    ∃ ϖ : ℝ, 0 < ϖ ∧ ϖ < ϖmax ∧ δ < ϖ / 2 := by
  refine ⟨(2 * max δ 0 + ϖmax) / 2, ?_, ?_, ?_⟩
  · have := le_max_right δ 0; linarith
  · rcases le_total δ 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  · rcases le_total δ 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith

/-- **Theorem 1.1.** -/
theorem theorem_1_1 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hA : AssumptionsAt θ)
    (a b : ℕ) (ha : 0 < a) (hab : a < b) {δ : ℝ} (hδ : δ < deltaA θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x := by
  apply lower_general _ a b ha hab
  intro a' b' ha' hab' hodd
  obtain ⟨P⟩ := PatternData.nonempty ha' hab' hodd
  obtain ⟨F⟩ := exists_cutoff
  rw [deltaA_eq θ] at hδ
  obtain ⟨ϖ, hϖ0, hϖ, hδϖ⟩ := exists_varpi (varpiA_pos hθ) hδ
  exact P.lower_from_sigma hA.arith.primesInAP F hϖ0
    (P.sigma_lower_a hθ0 hθ hA F hϖ0 hϖ) hδϖ

/-- **Theorem 1.3.** -/
theorem theorem_1_3 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hA : AssumptionsDIAt θ)
    (a b : ℕ) (ha : 0 < a) (hab : a < b) {δ : ℝ} (hδ : δ < deltaB θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x := by
  apply lower_general _ a b ha hab
  intro a' b' ha' hab' hodd
  obtain ⟨P⟩ := PatternData.nonempty ha' hab' hodd
  obtain ⟨F⟩ := exists_cutoff
  rw [deltaB_eq θ] at hδ
  obtain ⟨ϖ, hϖ0, hϖ, hδϖ⟩ := exists_varpi (varpiB_pos hθ) hδ
  exact P.lower_from_sigma hA.arith.primesInAP F hϖ0
    (P.sigma_lower_b hθ0 hθ hA F hϖ0 hϖ) hδϖ

/-- `δ_{7/64} = 25/278`. -/
theorem deltaA_kim_sarnak : deltaA (7 / 64) = 25 / 278 := by unfold deltaA; norm_num

/-- `δ'_{7/64} = 25/292`. -/
theorem deltaB_kim_sarnak : deltaB (7 / 64) = 25 / 292 := by unfold deltaB; norm_num

/-- `δ_0 = δ'_0 = 1/10`. -/
theorem delta_selberg : deltaA 0 = 1 / 10 ∧ deltaB 0 = 1 / 10 := by
  unfold deltaA deltaB; norm_num

/-- `δ_{1/4} = 1/14` and `δ'_{1/4} = 1/16` (Selberg's `λ₁ ≥ 3/16`). -/
theorem delta_selberg_bound : deltaA (1 / 4) = 1 / 14 ∧ deltaB (1 / 4) = 1 / 16 := by
  unfold deltaA deltaB; norm_num

/-- **Corollary 1.2**, unconditional part: with the Kim–Sarnak bound (`θ = 7/64`, contained in
`Assumptions`), `S_{a,b}(x) ≫ x^(1/2+δ)` for every `δ < 25/278`. -/
theorem corollary_1_2 (hA : Assumptions) (a b : ℕ) (ha : 0 < a) (hab : a < b) {δ : ℝ}
    (hδ : δ < 25 / 278) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x :=
  theorem_1_1 (by norm_num) (by norm_num) hA a b ha hab (by rw [deltaA_kim_sarnak]; exact hδ)

/-- **Corollary 1.2**, conditional part: if `θ = 0` is admissible (Selberg's eigenvalue
conjecture, together with the other assumptions), then every `δ < 1/10` is allowed. -/
theorem corollary_1_2_selberg (hA : AssumptionsAt 0) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    {δ : ℝ} (hδ : δ < 1 / 10) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x :=
  theorem_1_1 le_rfl (by norm_num) hA a b ha hab (by rw [delta_selberg.1]; exact hδ)

/-- **Corollary 1.2**, the pattern `{0, 1, 2}`: there are `≫ x^(1/2+δ)` integers `n ≤ x` with
`n`, `n + 1` and `n + 2` all sums of two squares, for every `δ < 25/278`. (Shifting `n` by one
gives the statement about `n - 1, n, n + 1` in the paper.) -/
theorem corollary_1_2_consecutive (hA : Assumptions) {δ : ℝ} (hδ : δ < 25 / 278) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S 1 2 x :=
  corollary_1_2 hA 1 2 (by norm_num) (by norm_num) hδ

end Triples
