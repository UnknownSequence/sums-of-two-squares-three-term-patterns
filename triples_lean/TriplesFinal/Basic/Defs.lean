import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Basic definitions

* `Triples.IsSumTwoSq n` : the integer `n` is a sum of two squares of integers
  (the set `𝒮` of the paper).
* `Triples.r n` : the number of representations `n = x ^ 2 + y ^ 2` with `x y : ℤ`.
* `Triples.S a b x` : the counting function `S_{a,b}(x)` of the paper.

Paper: *Sums of two squares in three-term patterns* (triples_final.pdf), §1.
-/

namespace Triples

/-- The integer `n` is a sum of two squares of integers. -/
def IsSumTwoSq (n : ℤ) : Prop := ∃ x y : ℤ, n = x ^ 2 + y ^ 2

/-- The representation function `r(n) = #{(x, y) ∈ ℤ² : x² + y² = n}`. -/
noncomputable def r (n : ℤ) : ℕ := {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = n}.ncard

/-- The set of `1 ≤ n ≤ x` with `n, n + a, n + b ∈ 𝒮`. -/
def SSet (a b : ℕ) (x : ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ (n : ℝ) ≤ x ∧ IsSumTwoSq n ∧ IsSumTwoSq ((n : ℤ) + a) ∧
    IsSumTwoSq ((n : ℤ) + b)}

/-- The counting function `S_{a,b}(x) = #{1 ≤ n ≤ x : n, n + a, n + b ∈ 𝒮}`. -/
noncomputable def S (a b : ℕ) (x : ℝ) : ℕ := (SSet a b x).ncard

theorem SSet_subset_Icc (a b : ℕ) (x : ℝ) :
    SSet a b x ⊆ (Finset.Icc 1 ⌊x⌋₊ : Set ℕ) := by
  rintro n ⟨h1, hx, -⟩
  simp only [Finset.coe_Icc, Set.mem_Icc]
  refine ⟨h1, ?_⟩
  have hx0 : (0 : ℝ) ≤ x := le_trans (Nat.cast_nonneg n) hx
  exact Nat.le_floor hx

theorem SSet_finite (a b : ℕ) (x : ℝ) : (SSet a b x).Finite :=
  (Finset.finite_toSet _).subset (SSet_subset_Icc a b x)

theorem isSumTwoSq_zero : IsSumTwoSq 0 := ⟨0, 0, by ring⟩

theorem IsSumTwoSq.nonneg {n : ℤ} (h : IsSumTwoSq n) : 0 ≤ n := by
  obtain ⟨x, y, rfl⟩ := h
  positivity

/-- For natural numbers, `IsSumTwoSq` agrees with the notion used in Mathlib. -/
theorem isSumTwoSq_natCast_iff (n : ℕ) :
    IsSumTwoSq (n : ℤ) ↔ ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨x.natAbs, y.natAbs, ?_⟩
    zify
    simpa [sq_abs] using h
  · rintro ⟨x, y, h⟩
    exact ⟨x, y, by exact_mod_cast h⟩

/-- `𝒮` is closed under multiplication by `2`: `2(x² + y²) = (x + y)² + (x - y)²`. -/
theorem IsSumTwoSq.two_mul {n : ℤ} (h : IsSumTwoSq n) : IsSumTwoSq (2 * n) := by
  obtain ⟨x, y, rfl⟩ := h
  exact ⟨x + y, x - y, by ring⟩

/-- `𝒮` is closed under multiplication: the Brahmagupta–Fibonacci identity. -/
theorem IsSumTwoSq.mul {m n : ℤ} (hm : IsSumTwoSq m) (hn : IsSumTwoSq n) :
    IsSumTwoSq (m * n) := by
  obtain ⟨x, y, rfl⟩ := hm
  obtain ⟨u, v, rfl⟩ := hn
  exact ⟨x * u - y * v, x * v + y * u, by ring⟩

/-- If `4 z` is a sum of two squares, so is `z`: both squares must be even. -/
theorem IsSumTwoSq.of_four_mul {z : ℤ} (h : IsSumTwoSq (4 * z)) : IsSumTwoSq z := by
  obtain ⟨x, y, hxy⟩ := h
  rcases Int.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;>
    rcases Int.even_or_odd y with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · have h1 : 4 * z = 4 * (k ^ 2 + l ^ 2) := by rw [hxy]; ring
    exact ⟨k, l, by linarith⟩
  · exfalso
    have h1 : 4 * z = 4 * (k ^ 2 + l ^ 2 + l) + 1 := by rw [hxy]; ring
    generalize k ^ 2 + l ^ 2 + l = K at h1
    omega
  · exfalso
    have h1 : 4 * z = 4 * (k ^ 2 + k + l ^ 2) + 1 := by rw [hxy]; ring
    generalize k ^ 2 + k + l ^ 2 = K at h1
    omega
  · exfalso
    have h1 : 4 * z = 4 * (k ^ 2 + k + l ^ 2 + l) + 2 := by rw [hxy]; ring
    generalize k ^ 2 + k + l ^ 2 + l = K at h1
    omega

end Triples
