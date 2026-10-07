import TriplesFinal.Basic.Defs
import Mathlib.Data.Int.Interval

/-!
# Elementary facts about the representation function `r`

* the representation sets are finite;
* `r(4z) = r(z)` (both squares in a representation of `4z` are even).
-/

namespace Triples

/-- The set of representations of `n` as a sum of two squares. -/
def repSet (n : ℤ) : Set (ℤ × ℤ) := {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = n}

theorem r_eq_ncard (n : ℤ) : r n = (repSet n).ncard := rfl

theorem abs_le_of_sq_add_sq {x y n : ℤ} (h : x ^ 2 + y ^ 2 = n) : |x| ≤ |n| := by
  have hx : |x| ≤ x ^ 2 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have h1 : 1 ≤ |x| := Int.one_le_abs hx
      calc |x| = |x| * 1 := by ring
        _ ≤ |x| * |x| := by gcongr
        _ = x ^ 2 := by rw [abs_mul_abs_self, sq]
  have hy : 0 ≤ y ^ 2 := sq_nonneg y
  have hn : n ≤ |n| := le_abs_self n
  linarith

theorem repSet_finite (n : ℤ) : (repSet n).Finite := by
  apply (Set.finite_Icc (-|n|) |n| |>.prod (Set.finite_Icc (-|n|) |n|)).subset
  rintro ⟨x, y⟩ h
  simp only [repSet, Set.mem_ofPred_eq] at h
  have hx := abs_le_of_sq_add_sq h
  have hy := abs_le_of_sq_add_sq (show y ^ 2 + x ^ 2 = n by linarith)
  simp only [Set.mem_prod, Set.mem_Icc]
  exact ⟨abs_le.1 hx, abs_le.1 hy⟩

/-- In a representation `x² + y² = 4z` both `x` and `y` are even. -/
theorem even_of_sq_add_sq_eq_four_mul {x y z : ℤ} (h : x ^ 2 + y ^ 2 = 4 * z) :
    Even x ∧ Even y := by
  rcases Int.even_or_odd x with hx | ⟨k, rfl⟩ <;> rcases Int.even_or_odd y with hy | ⟨l, rfl⟩
  · exact ⟨hx, hy⟩
  · exfalso
    obtain ⟨k, rfl⟩ := hx
    have h1 : 4 * z = 4 * (k ^ 2 + l ^ 2 + l) + 1 := by rw [← h]; ring
    generalize k ^ 2 + l ^ 2 + l = K at h1
    omega
  · exfalso
    obtain ⟨l, rfl⟩ := hy
    have h1 : 4 * z = 4 * (k ^ 2 + k + l ^ 2) + 1 := by rw [← h]; ring
    generalize k ^ 2 + k + l ^ 2 = K at h1
    omega
  · exfalso
    have h1 : 4 * z = 4 * (k ^ 2 + k + l ^ 2 + l) + 2 := by rw [← h]; ring
    generalize k ^ 2 + k + l ^ 2 + l = K at h1
    omega

/-- `r(4z) = r(z)`. -/
theorem r_four_mul (z : ℤ) : r (4 * z) = r z := by
  rw [r_eq_ncard, r_eq_ncard]
  have hset : repSet (4 * z) = (fun p : ℤ × ℤ => (2 * p.1, 2 * p.2)) '' repSet z := by
    ext ⟨x, y⟩
    simp only [repSet, Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq, Prod.exists]
    constructor
    · intro h
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := even_of_sq_add_sq_eq_four_mul h
      exact ⟨a, b, by linarith, by ring, by ring⟩
    · rintro ⟨a, b, hab, rfl, rfl⟩
      rw [← hab]; ring
  rw [hset, Set.ncard_image_of_injective _ ?_]
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk.injEq] at h
  ext <;> simp <;> omega

end Triples
