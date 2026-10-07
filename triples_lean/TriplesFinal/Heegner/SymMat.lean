import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Integral symmetric matrices and the action `γ ⋄ 𝔤 = γ 𝔤 γᵗ`

`Q_N` is the set of integral symmetric matrices `𝔤 = (𝔞 𝔟; 𝔟 𝔠)` with `𝔞, 𝔠 > 0` and
`𝔞𝔠 - 𝔟² = N`. The group `SL₂(ℤ)` acts on `Q_N` by `γ ⋄ 𝔤 = γ 𝔤 γᵗ`.

Paper: §8.1.
-/

namespace Triples

/-- An integral symmetric matrix `(𝔞 𝔟; 𝔟 𝔠)`. -/
@[ext] structure SymMat where
  /-- the upper left entry `𝔞` -/
  a : ℤ
  /-- the off-diagonal entry `𝔟` -/
  b : ℤ
  /-- the lower right entry `𝔠` -/
  c : ℤ
deriving DecidableEq

namespace SymMat

/-- The determinant `𝔞𝔠 - 𝔟²`. -/
def det (g : SymMat) : ℤ := g.a * g.c - g.b ^ 2

/-- The binary quadratic form `φ_𝔤(s, t) = 𝔞 s² + 2𝔟 s t + 𝔠 t²`. -/
def form (g : SymMat) (s t : ℤ) : ℤ := g.a * s ^ 2 + 2 * g.b * s * t + g.c * t ^ 2

/-- `γ ⋄ 𝔤 = γ 𝔤 γᵗ`. -/
def act (γ : Matrix (Fin 2) (Fin 2) ℤ) (g : SymMat) : SymMat where
  a := γ 0 0 ^ 2 * g.a + 2 * γ 0 0 * γ 0 1 * g.b + γ 0 1 ^ 2 * g.c
  b := γ 0 0 * γ 1 0 * g.a + (γ 0 0 * γ 1 1 + γ 0 1 * γ 1 0) * g.b + γ 0 1 * γ 1 1 * g.c
  c := γ 1 0 ^ 2 * g.a + 2 * γ 1 0 * γ 1 1 * g.b + γ 1 1 ^ 2 * g.c

/-- `Q_N`: positive definite integral symmetric matrices of determinant `N`. -/
def QN (N : ℤ) : Set SymMat := {g | 0 < g.a ∧ 0 < g.c ∧ g.det = N}

theorem act_a (γ : Matrix (Fin 2) (Fin 2) ℤ) (g : SymMat) :
    (act γ g).a = g.form (γ 0 0) (γ 0 1) := by
  simp only [act, form]; ring

theorem act_c (γ : Matrix (Fin 2) (Fin 2) ℤ) (g : SymMat) :
    (act γ g).c = g.form (γ 1 0) (γ 1 1) := by
  simp only [act, form]; ring

theorem act_one (g : SymMat) : act 1 g = g := by
  ext <;> simp [act]

theorem act_neg (γ : Matrix (Fin 2) (Fin 2) ℤ) (g : SymMat) : act (-γ) g = act γ g := by
  ext <;> simp only [act, Matrix.neg_apply] <;> ring

/-- `(γ₁ γ₂) ⋄ 𝔤 = γ₁ ⋄ (γ₂ ⋄ 𝔤)`. -/
theorem act_mul (γ₁ γ₂ : Matrix (Fin 2) (Fin 2) ℤ) (g : SymMat) :
    act (γ₁ * γ₂) g = act γ₁ (act γ₂ g) := by
  ext <;> simp only [act, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `det(γ ⋄ 𝔤) = det(γ)² det(𝔤)`. -/
theorem det_act (γ : Matrix (Fin 2) (Fin 2) ℤ) (g : SymMat) :
    (act γ g).det = γ.det ^ 2 * g.det := by
  rw [Matrix.det_fin_two]; simp only [det, act]; ring

/-- A positive definite form takes positive values at non-zero vectors. -/
theorem form_pos {g : SymMat} (ha : 0 < g.a) (hdet : 0 < g.det) {s t : ℤ}
    (hst : s ≠ 0 ∨ t ≠ 0) : 0 < g.form s t := by
  have key : g.a * g.form s t = (g.a * s + g.b * t) ^ 2 + g.det * t ^ 2 := by
    simp only [form, det]; ring
  rcases eq_or_ne t 0 with rfl | ht
  · have hs : s ≠ 0 := by tauto
    simp only [form]
    have : 0 < s ^ 2 := by positivity
    nlinarith
  · have h1 : 0 < g.det * t ^ 2 := by positivity
    have h2 : 0 ≤ (g.a * s + g.b * t) ^ 2 := sq_nonneg _
    have : 0 < g.a * g.form s t := by rw [key]; linarith
    exact pos_of_mul_pos_right this ha.le

/-- `SL₂(ℤ)` (more generally, every integral matrix of determinant `1`) preserves `Q_N` for
`N > 0`. -/
theorem act_mem_QN {N : ℤ} (hN : 0 < N) {γ : Matrix (Fin 2) (Fin 2) ℤ} (hγ : γ.det = 1)
    {g : SymMat} (hg : g ∈ QN N) : act γ g ∈ QN N := by
  obtain ⟨ha, hc, hdet⟩ := hg
  rw [Matrix.det_fin_two] at hγ
  have hdet' : 0 < g.det := hdet ▸ hN
  refine ⟨?_, ?_, ?_⟩
  · rw [act_a]
    apply form_pos ha hdet'
    by_contra h
    push Not at h
    rw [h.1, h.2] at hγ
    simp at hγ
  · rw [act_c]
    apply form_pos ha hdet'
    by_contra h
    push Not at h
    rw [h.1, h.2] at hγ
    simp at hγ
  · rw [det_act, Matrix.det_fin_two, hγ, one_pow, one_mul, hdet]

end SymMat

end Triples
