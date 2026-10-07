import TriplesFinal.Families.Choice
import TriplesFinal.Families.Identity

/-!
# Definitions for the local analysis at `2`

For integers (as elements of `ℤ₂`) we use the following equivalent descriptions.
* `InN z` : `z ∈ 𝒩`, i.e. `z ≠ 0` and the odd part of `z` is `≡ 1 (mod 4)`.
* `IsSqQ2 z` : `z` is a non-zero square in `ℚ₂`, i.e. `v₂(z)` is even and the odd part is
  `≡ 1 (mod 8)`.

Paper: §3.
-/

namespace Triples

/-- `z ∈ 𝒩`: `z = 2^k w` with `w ≡ 1 (mod 4)`. -/
def InN (z : ℤ) : Prop := ∃ k : ℕ, ∃ w : ℤ, z = 2 ^ k * w ∧ w % 4 = 1

/-- `z` is a non-zero square in `ℚ₂`: `z = 4^k w` with `w ≡ 1 (mod 8)`. -/
def IsSqQ2 (z : ℤ) : Prop := ∃ k : ℕ, ∃ w : ℤ, z = 4 ^ k * w ∧ w % 8 = 1

/-- Odd squares are `≡ 1 (mod 8)`. -/
theorem sq_emod_eight_of_odd {β : ℤ} (h : β % 2 = 1) : β ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, β = 2 * k + 1 := ⟨β / 2, by omega⟩
  have h1 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [h1]
  have h2 : (k * (k + 1)) % 2 = 0 := by
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have : (m + m) * (m + m + 1) = 2 * (m * (m + m + 1)) := by ring
      rw [this]; omega
    · have : (2 * m + 1) * (2 * m + 1 + 1) = 2 * ((2 * m + 1) * (m + 1)) := by ring
      rw [this]; omega
  generalize k * (k + 1) = K at h2 ⊢
  omega

/-- Every integer `≠ 0` is `2^t w` with `w` odd. -/
theorem exists_two_pow_mul_odd {C : ℤ} (hC : C ≠ 0) :
    ∃ t : ℕ, ∃ w : ℤ, C = 2 ^ t * w ∧ w % 2 = 1 := by
  obtain ⟨t, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := C.natAbs) (by omega)
  rcases Int.natAbs_eq C with h | h
  · refine ⟨t, m, ?_, ?_⟩
    · rw [h, hn]; push_cast; ring
    · obtain ⟨k, rfl⟩ := hm; push_cast; omega
  · refine ⟨t, -(m : ℤ), ?_, ?_⟩
    · rw [h, hn]; push_cast; ring
    · obtain ⟨k, rfl⟩ := hm; push_cast; omega

end Triples
