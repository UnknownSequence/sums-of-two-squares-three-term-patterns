import TriplesFinal.Heegner.SymMat
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Prime.Int

/-!
# Lemma 8.1(a): trivial stabilisers

If `N ≥ 1` is neither a square nor three times a square, then the stabiliser in `SL₂(ℤ)` of
every `𝔤 ∈ Q_N` is `{±1}`.

Paper: §8, Lemma 8.1(a). The paper deduces this from the stabilisers of points of `ℍ`; here we
give a direct elementary proof. If `γ ⋄ 𝔤 = 𝔤` with `γ = (p q; r s)`, then
`𝔞(p - s) + 2q𝔟 = 0`, `𝔞r + 𝔠q = 0`, and hence `𝔞²((p + s)² - 4) + 4Nq² = 0`.
If `q ≠ 0`, then `(p + s)² < 4`, and `p + s = 0` gives `N q² = 𝔞²`, while `p + s = ±1` gives
`4Nq² = 3𝔞²`.
-/

namespace Triples

open scoped MatrixGroups

namespace SymMat

/-- If `N q² = A²` with `q ≠ 0`, then `N` is a perfect square. -/
theorem isSquare_of_mul_sq_eq_sq {N q A : ℤ} (hq : q ≠ 0) (h : N * q ^ 2 = A ^ 2) :
    ∃ s : ℤ, N = s ^ 2 := by
  have hQ : IsSquare (N : ℚ) := by
    refine ⟨(A : ℚ) / q, ?_⟩
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
    have h' : (N : ℚ) * (q : ℚ) ^ 2 = (A : ℚ) ^ 2 := by exact_mod_cast h
    field_simp
    linear_combination h'
  obtain ⟨s, hs⟩ := Rat.isSquare_intCast_iff.1 hQ
  exact ⟨s, by rw [hs]; ring⟩

/-- **Lemma 8.1(a).** Let `N > 0` be neither a square nor three times a square, let
`𝔤 ∈ Q_N`, and let `γ` be an integral matrix of determinant `1` with `γ ⋄ 𝔤 = 𝔤`.
Then `γ = ±1`. -/
theorem stabiliser {N : ℤ} (hN0 : 0 < N) (hsq : ¬ ∃ s : ℤ, N = s ^ 2)
    (h3 : ¬ ∃ s : ℤ, N = 3 * s ^ 2) {g : SymMat} (hg : g ∈ QN N)
    {γ : Matrix (Fin 2) (Fin 2) ℤ} (hγ : γ.det = 1) (hfix : act γ g = g) :
    γ = 1 ∨ γ = -1 := by
  obtain ⟨ha, hc, hN⟩ := hg
  simp only [det] at hN
  rw [Matrix.det_fin_two] at hγ
  have h1 : γ 0 0 ^ 2 * g.a + 2 * γ 0 0 * γ 0 1 * g.b + γ 0 1 ^ 2 * g.c = g.a :=
    congrArg SymMat.a hfix
  have h2 : γ 0 0 * γ 1 0 * g.a + (γ 0 0 * γ 1 1 + γ 0 1 * γ 1 0) * g.b +
      γ 0 1 * γ 1 1 * g.c = g.b := congrArg SymMat.b hfix
  have hR1 : g.a * (γ 0 0 - γ 1 1) + 2 * γ 0 1 * g.b = 0 := by
    linear_combination γ 1 1 * h1 - γ 0 1 * h2 - (γ 0 0 * g.a + γ 0 1 * g.b) * hγ
  have hR2 : g.a * γ 1 0 + g.c * γ 0 1 = 0 := by
    linear_combination -γ 1 0 * h1 + γ 0 0 * h2 - (γ 0 0 * g.b + γ 0 1 * g.c) * hγ
  have hT : g.a ^ 2 * ((γ 0 0 + γ 1 1) ^ 2 - 4) + 4 * N * γ 0 1 ^ 2 = 0 := by
    linear_combination (g.a * (γ 0 0 - γ 1 1) - 2 * γ 0 1 * g.b) * hR1 + 4 * g.a ^ 2 * hγ +
      4 * g.a * γ 0 1 * hR2 - 4 * γ 0 1 ^ 2 * hN
  by_cases hq : γ 0 1 = 0
  · -- `q = 0`: then `p = s`, `r = 0` and `p² = 1`
    have hps : γ 0 0 = γ 1 1 := by
      have h' : g.a * (γ 0 0 - γ 1 1) = 0 := by rw [hq] at hR1; linarith
      rcases mul_eq_zero.1 h' with h | h
      · exact absurd h ha.ne'
      · linarith
    have hr : γ 1 0 = 0 := by
      have h' : g.a * γ 1 0 = 0 := by rw [hq] at hR2; linarith
      rcases mul_eq_zero.1 h' with h | h
      · exact absurd h ha.ne'
      · exact h
    have hp : (γ 0 0 - 1) * (γ 0 0 + 1) = 0 := by
      rw [hq, hr, ← hps] at hγ; linear_combination hγ
    rcases mul_eq_zero.1 hp with hp | hp
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> linarith
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> linarith
  · -- `q ≠ 0`: then `(p + s)² < 4`
    exfalso
    have hq2 : 0 < γ 0 1 ^ 2 := by positivity
    have ha2 : 0 < g.a ^ 2 := by positivity
    have hlt : (γ 0 0 + γ 1 1) ^ 2 < 4 := by
      by_contra hge
      push Not at hge
      have : 0 ≤ g.a ^ 2 * ((γ 0 0 + γ 1 1) ^ 2 - 4) := by
        apply mul_nonneg ha2.le; linarith
      have : 0 < 4 * N * γ 0 1 ^ 2 := by positivity
      linarith
    obtain ⟨t, ht⟩ : ∃ t, γ 0 0 + γ 1 1 = t := ⟨_, rfl⟩
    rw [ht] at hT hlt
    have htl : -1 ≤ t := by nlinarith
    have htu : t ≤ 1 := by nlinarith
    interval_cases t
    · -- `p + s = -1`: `4Nq² = 3𝔞²`, so `3N` is a square
      obtain ⟨k, hk⟩ := isSquare_of_mul_sq_eq_sq (N := 3 * N) (q := 2 * γ 0 1) (A := 3 * g.a)
        (by positivity) (by linear_combination 3 * hT)
      have h3k : (3 : ℤ) ∣ k := by
        have hp3 : Prime (3 : ℤ) := by simpa using Nat.prime_iff_prime_int.mp Nat.prime_three
        apply hp3.dvd_of_dvd_pow (n := 2)
        exact ⟨N, by rw [← hk]⟩
      obtain ⟨m, rfl⟩ := h3k
      exact h3 ⟨m, by linarith⟩
    · -- `p + s = 0`: `N q² = 𝔞²`
      exact hsq (isSquare_of_mul_sq_eq_sq (A := g.a) hq (by linarith))
    · -- `p + s = 1`
      obtain ⟨k, hk⟩ := isSquare_of_mul_sq_eq_sq (N := 3 * N) (q := 2 * γ 0 1) (A := 3 * g.a)
        (by positivity) (by linear_combination 3 * hT)
      have h3k : (3 : ℤ) ∣ k := by
        have hp3 : Prime (3 : ℤ) := by simpa using Nat.prime_iff_prime_int.mp Nat.prime_three
        apply hp3.dvd_of_dvd_pow (n := 2)
        exact ⟨N, by rw [← hk]⟩
      obtain ⟨m, rfl⟩ := h3k
      exact h3 ⟨m, by linarith⟩

/-- **Lemma 8.1(a)** for elements of `SL₂(ℤ)`. -/
theorem stabiliser_SL {N : ℤ} (hN0 : 0 < N) (hsq : ¬ ∃ s : ℤ, N = s ^ 2)
    (h3 : ¬ ∃ s : ℤ, N = 3 * s ^ 2) {g : SymMat} (hg : g ∈ QN N) {γ : SL(2, ℤ)}
    (hfix : act γ g = g) : γ = 1 ∨ γ = -1 := by
  rcases stabiliser hN0 hsq h3 hg γ.det_coe hfix with h | h
  · left
    exact Subtype.ext (h.trans Matrix.SpecialLinearGroup.coe_one.symm)
  · right
    exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]; exact h)

end SymMat

end Triples
