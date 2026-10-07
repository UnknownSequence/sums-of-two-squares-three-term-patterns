import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Thue's lemma

For `m ≥ 1` and any `ν ∈ ℤ` there are integers `(x, y) ≠ (0, 0)` with `x² + y² < 2m` and
`x ≡ νy (mod m)`. The proof is the pigeonhole principle applied to the `(⌊√m⌋ + 1)(T + 1) > m`
values `x - νy mod m` with `0 ≤ x ≤ ⌊√m⌋`, `0 ≤ y ≤ T`.

This is the first step of the proof of Jacobi's two-square theorem (`Basic/Jacobi.lean`): if
`m ∣ ν² + 1`, then `m ∣ x² + y² < 2m`, so `x² + y² = m`.

Paper: §1, Notation (Jacobi's formula for `r(n)`).
-/

namespace Triples

/-- **Thue's lemma.** For `m ≥ 1` and any `ν`, there is `(x, y) ≠ 0` with `x² + y² < 2m` and
`x ≡ νy (mod m)`. -/
theorem thue (m : ℕ) (hm : 1 ≤ m) (ν : ℤ) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ x ^ 2 + y ^ 2 < 2 * m ∧ (m : ℤ) ∣ x - ν * y := by
  classical
  set S := Nat.sqrt m with hS
  have hS2 : S * S ≤ m := Nat.sqrt_le m
  have hS3 : m < (S + 1) * (S + 1) := Nat.lt_succ_sqrt m
  have hS1 : 1 ≤ S := by
    rw [hS]; exact Nat.le_sqrt.2 (by omega)
  set T := if S * S < m then S else S - 1 with hT
  have hcard : m < (S + 1) * (T + 1) := by
    rw [hT]; split_ifs with h
    · exact hS3
    · have : S * S = m := by omega
      have : S - 1 + 1 = S := by omega
      rw [this]; nlinarith
  have hbound : S * S + T * T < 2 * m := by
    rw [hT]; split_ifs with h
    · omega
    · have : S * S = m := by omega
      have h1 : (S - 1) * (S - 1) < S * S := Nat.mul_self_lt_mul_self (by omega)
      omega
  set B := (Finset.range (S + 1)) ×ˢ (Finset.range (T + 1)) with hB
  set f : ℕ × ℕ → ℤ := fun p => ((p.1 : ℤ) - ν * p.2) % m with hf
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
  have hmaps : ∀ p ∈ B, f p ∈ Finset.Ico (0 : ℤ) m := by
    intro p _
    simp only [hf, Finset.mem_Ico]
    exact ⟨Int.emod_nonneg _ hm0.ne', Int.emod_lt_of_pos _ hm0⟩
  have hlt : (Finset.Ico (0 : ℤ) m).card < B.card := by
    rw [Int.card_Ico, hB, Finset.card_product, Finset.card_range, Finset.card_range]
    simp only [sub_zero, Int.toNat_natCast]
    exact hcard
  obtain ⟨p, hp, p', hp', hne, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  rw [hB, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp hp'
  refine ⟨(p.1 : ℤ) - p'.1, (p.2 : ℤ) - p'.2, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    apply hne
    exact Prod.ext (by omega) (by omega)
  · have h1 : ((p.1 : ℤ) - p'.1) ^ 2 ≤ S * S := by
      have : |(p.1 : ℤ) - p'.1| ≤ S := by rw [abs_le]; constructor <;> omega
      nlinarith [sq_abs ((p.1 : ℤ) - p'.1), abs_nonneg ((p.1 : ℤ) - p'.1)]
    have h2 : ((p.2 : ℤ) - p'.2) ^ 2 ≤ T * T := by
      have : |(p.2 : ℤ) - p'.2| ≤ T := by rw [abs_le]; constructor <;> omega
      nlinarith [sq_abs ((p.2 : ℤ) - p'.2), abs_nonneg ((p.2 : ℤ) - p'.2)]
    have h3 : ((S * S + T * T : ℕ) : ℤ) < 2 * m := by exact_mod_cast hbound
    push_cast at h3
    linarith
  · have := Int.ModEq.dvd hfeq.symm
    have e : (p.1 : ℤ) - ν * p.2 - ((p'.1 : ℤ) - ν * p'.2) =
        (p.1 : ℤ) - p'.1 - ν * ((p.2 : ℤ) - p'.2) := by ring
    rw [← e]
    simpa [hf] using this

/-- `x² + y² = (x - νy)(x + νy) + (ν² + 1) y²`. -/
theorem sum_sq_identity (x y ν : ℤ) :
    x ^ 2 + y ^ 2 = (x - ν * y) * (x + ν * y) + (ν ^ 2 + 1) * y ^ 2 := by ring

/-- If `x ≡ νy (mod m)` and `m ∣ ν² + 1`, then `m ∣ x² + y²`. -/
theorem dvd_sum_sq {m x y ν : ℤ} (h1 : m ∣ x - ν * y) (h2 : m ∣ ν ^ 2 + 1) : m ∣ x ^ 2 + y ^ 2 := by
  rw [sum_sq_identity x y ν]
  exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _)

end Triples
