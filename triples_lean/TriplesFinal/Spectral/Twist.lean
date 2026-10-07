import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Lemma 10.6: removing a twist (partial summation)

Let `M ≥ 1/2`, let `(ξ_j(n))_{n ∼ M}` be complex numbers and `ω_j ≥ 0` for `j` in a finite set,
and let `φ_j : [M, 2M] → ℂ` be continuously differentiable with `|φ_j| ≤ D₀` and `|φ_j'| ≤ D₁`.
Then
`∑_j ω_j |∑_{n ∼ M} ξ_j(n) φ_j(n)|² ≤ 2(D₀² + M² D₁²) sup_{M ≤ y ≤ 2M} ∑_j ω_j |∑_{M < n ≤ y} ξ_j(n)|²`.

We state it with an explicit bound `B` for the supremum, for a finite family `j ∈ J`; the paper
applies it to countable families with `∑_j ω_j < ∞` on the relevant ranges and to the
continuous spectrum, by the same argument.

The proof is discrete partial summation (`Finset.sum_range_by_parts`), the mean value theorem
for `φ_j(n + 1) - φ_j(n)`, and the Cauchy–Schwarz inequality; the number of `n` with
`M < n < ⌊2M⌋` is at most `M`.

Paper: §10.4, Lemma 10.6.
-/

namespace Triples

/-- `(a + b)² ≤ 2a² + 2b²`. -/
theorem sq_add_le_two_mul (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **Lemma 10.6.** -/
theorem twist_removal {ι : Type*} (J : Finset ι) {M D₀ D₁ B : ℝ} (hM : 1 / 2 ≤ M)
    (ω : ι → ℝ) (hω : ∀ j, 0 ≤ ω j) (ξ : ι → ℕ → ℂ) (φ : ι → ℝ → ℂ)
    (hφd : ∀ j, ∀ y ∈ Set.Icc M (2 * M), HasDerivAt (φ j) (deriv (φ j) y) y)
    (_hφc : ∀ j, ContinuousOn (deriv (φ j)) (Set.Icc M (2 * M)))
    (hD₀ : ∀ j, ∀ y ∈ Set.Icc M (2 * M), ‖φ j y‖ ≤ D₀)
    (hD₁ : ∀ j, ∀ y ∈ Set.Icc M (2 * M), ‖deriv (φ j) y‖ ≤ D₁)
    (hB : ∀ y ∈ Set.Icc M (2 * M), ∑ j ∈ J, ω j *
      ‖∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => M < n), ξ j n‖ ^ 2 ≤ B) :
    ∑ j ∈ J, ω j *
        ‖∑ n ∈ (Finset.Icc 1 ⌊2 * M⌋₊).filter (fun n : ℕ => M < n), ξ j n * φ j n‖ ^ 2 ≤
      2 * (D₀ ^ 2 + M ^ 2 * D₁ ^ 2) * B := by
  classical
  have hM0 : 0 ≤ M := by linarith
  have hMmem : M ∈ Set.Icc M (2 * M) := ⟨le_refl _, by linarith⟩
  have h2Mmem : 2 * M ∈ Set.Icc M (2 * M) := ⟨by linarith, le_refl _⟩
  have hB0 : 0 ≤ B := le_trans (Finset.sum_nonneg fun j _ => mul_nonneg (hω j) (sq_nonneg _))
    (hB M hMmem)
  set N := ⌊2 * M⌋₊ with hN
  have hNle : (N : ℝ) ≤ 2 * M := Nat.floor_le (by linarith)
  -- the truncated sequence and its partial sums
  set g : ι → ℕ → ℂ := fun j i => if M < i then ξ j i else 0 with hg
  set S : ι → ℕ → ℂ := fun j k => ∑ i ∈ Finset.range k, g j i with hS
  -- the partial sums as in `hB`
  have hS_eq : ∀ j, ∀ k : ℕ,
      S j (k + 1) = ∑ n ∈ (Finset.Icc 1 k).filter (fun n : ℕ => M < n), ξ j n := by
    intro j k
    simp only [hS, hg]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨?_, by omega⟩, h2⟩
      by_contra h0
      have : n = 0 := by omega
      subst this
      simp at h2; linarith
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨by omega, h3⟩
  -- `S j (i + 1) = 0` for `i ≤ M`
  have hS_zero : ∀ j, ∀ i : ℕ, ¬ M < i → S j (i + 1) = 0 := by
    intro j i hi
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : (k : ℝ) ≤ i := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    simp only [hg]
    rw [ite_eq_right_iff.2 (fun h => absurd h ?_)]
    push Not at hi ⊢
    linarith
  -- summation by parts
  have hsum : ∀ j, ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => M < n), ξ j n * φ j n =
      φ j N * S j (N + 1) -
        ∑ i ∈ Finset.range N, (φ j ((i + 1 : ℕ) : ℝ) - φ j i) * S j (i + 1) := by
    intro j
    have h := Finset.sum_range_by_parts (fun i : ℕ => φ j i) (g j) (N + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at h
    rw [← h]
    rw [Finset.sum_filter]
    have e : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [e, Finset.sum_insert (by simp)]
    have h0 : ¬ M < ((0 : ℕ) : ℝ) := by simp; linarith
    simp only [hg, h0, ite_false, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring_nf
  -- the size of the range of summation
  set I := (Finset.range N).filter (fun i : ℕ => M < i) with hI
  have hIcard : (I.card : ℝ) ≤ M := by
    have hsub : I ⊆ Finset.Ico (⌊M⌋₊ + 1) N := by
      intro i hi
      simp only [hI, Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_Ico]
      exact ⟨Nat.succ_le_of_lt ((Nat.floor_lt hM0).2 hi.2), hi.1⟩
    have h1 : I.card ≤ N - (⌊M⌋₊ + 1) := (Finset.card_le_card hsub).trans (by simp)
    have h3 : M < ⌊M⌋₊ + 1 := Nat.lt_floor_add_one M
    rcases le_total N (⌊M⌋₊ + 1) with h | h
    · have : I.card = 0 := by omega
      rw [this]; simp; linarith
    · have : (I.card : ℝ) ≤ (N : ℝ) - (⌊M⌋₊ + 1) := by
        have := Nat.cast_le (α := ℝ) |>.2 h1
        rw [Nat.cast_sub h] at this
        push_cast at this
        linarith
      linarith
  -- the pointwise bound
  have hpt : ∀ j, ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => M < n), ξ j n * φ j n‖ ≤
      D₀ * ‖S j (N + 1)‖ + D₁ * ∑ i ∈ I, ‖S j (i + 1)‖ := by
    intro j
    have hD₁0 : 0 ≤ D₁ := le_trans (norm_nonneg _) (hD₁ j M hMmem)
    rw [hsum j]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      by_cases hNM : M < N
      · exact mul_le_mul_of_nonneg_right (hD₀ j N ⟨hNM.le, hNle⟩) (norm_nonneg _)
      · rw [hS_zero j N hNM, norm_zero, mul_zero, mul_zero]
    · refine (norm_sum_le _ _).trans ?_
      rw [hI, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hiN := Finset.mem_range.1 hi
      rw [norm_mul]
      split_ifs with hMi
      · have hmem1 : (i : ℝ) ∈ Set.Icc M (2 * M) := by
          refine ⟨hMi.le, le_trans ?_ hNle⟩
          exact_mod_cast hiN.le
        have hmem2 : ((i + 1 : ℕ) : ℝ) ∈ Set.Icc M (2 * M) := by
          refine ⟨by push_cast; linarith, le_trans ?_ hNle⟩
          exact_mod_cast hiN
        have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun y hy => (hφd j y hy).hasDerivWithinAt) (hD₁ j) (convex_Icc M (2 * M)) hmem1 hmem2
        have : ‖((i + 1 : ℕ) : ℝ) - (i : ℝ)‖ = 1 := by push_cast; simp
        rw [this, mul_one] at hmvt
        exact mul_le_mul_of_nonneg_right hmvt (norm_nonneg _)
      · rw [hS_zero j i hMi, norm_zero, mul_zero, mul_zero]
  -- squaring
  have hsq : ∀ j, ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => M < n), ξ j n * φ j n‖ ^ 2 ≤
      2 * D₀ ^ 2 * ‖S j (N + 1)‖ ^ 2 + 2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ‖S j (i + 1)‖ ^ 2 := by
    intro j
    have hD₀0 : 0 ≤ D₀ := le_trans (norm_nonneg _) (hD₀ j M hMmem)
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hpt j) 2
    have h2 := sq_add_le_two_mul (D₀ * ‖S j (N + 1)‖) (D₁ * ∑ i ∈ I, ‖S j (i + 1)‖)
    have h3 : (∑ i ∈ I, ‖S j (i + 1)‖) ^ 2 ≤ I.card * ∑ i ∈ I, ‖S j (i + 1)‖ ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun i => ‖S j (i + 1)‖)
      simpa using this
    have h4 : 2 * (D₁ * ∑ i ∈ I, ‖S j (i + 1)‖) ^ 2 ≤
        2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ‖S j (i + 1)‖ ^ 2 := by
      calc 2 * (D₁ * ∑ i ∈ I, ‖S j (i + 1)‖) ^ 2
          = 2 * D₁ ^ 2 * (∑ i ∈ I, ‖S j (i + 1)‖) ^ 2 := by ring
        _ ≤ 2 * D₁ ^ 2 * (I.card * ∑ i ∈ I, ‖S j (i + 1)‖ ^ 2) := by gcongr
        _ = 2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ‖S j (i + 1)‖ ^ 2 := by ring
    calc _ ≤ (D₀ * ‖S j (N + 1)‖ + D₁ * ∑ i ∈ I, ‖S j (i + 1)‖) ^ 2 := h1
      _ ≤ 2 * (D₀ * ‖S j (N + 1)‖) ^ 2 + 2 * (D₁ * ∑ i ∈ I, ‖S j (i + 1)‖) ^ 2 := h2
      _ ≤ 2 * D₀ ^ 2 * ‖S j (N + 1)‖ ^ 2 + 2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ‖S j (i + 1)‖ ^ 2 := by
          rw [mul_pow]; linarith
  -- the bounds from `hB`
  have hBN : ∑ j ∈ J, ω j * ‖S j (N + 1)‖ ^ 2 ≤ B := by
    have := hB (2 * M) h2Mmem
    simp only [hS_eq]
    exact this
  have hBi : ∀ i ∈ I, ∑ j ∈ J, ω j * ‖S j (i + 1)‖ ^ 2 ≤ B := by
    intro i hi
    simp only [hI, Finset.mem_filter, Finset.mem_range] at hi
    have hmem : (i : ℝ) ∈ Set.Icc M (2 * M) := by
      refine ⟨hi.2.le, le_trans ?_ hNle⟩
      exact_mod_cast hi.1.le
    have := hB i hmem
    rw [Nat.floor_natCast] at this
    simp only [hS_eq]
    exact this
  -- combine
  have hD₁sq : 0 ≤ D₁ ^ 2 := sq_nonneg _
  calc ∑ j ∈ J, ω j * ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => M < n), ξ j n * φ j n‖ ^ 2
      ≤ ∑ j ∈ J, ω j * (2 * D₀ ^ 2 * ‖S j (N + 1)‖ ^ 2 +
          2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ‖S j (i + 1)‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hsq j) (hω j)
    _ = 2 * D₀ ^ 2 * ∑ j ∈ J, ω j * ‖S j (N + 1)‖ ^ 2 +
          2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ∑ j ∈ J, ω j * ‖S j (i + 1)‖ ^ 2 := by
        rw [Finset.sum_comm (s := I)]
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring_nf
    _ ≤ 2 * D₀ ^ 2 * B + 2 * D₁ ^ 2 * I.card * ∑ _i ∈ I, B := by
        gcongr with i hi
        exact hBi i hi
    _ = 2 * D₀ ^ 2 * B + 2 * D₁ ^ 2 * ((I.card : ℝ) * I.card) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * D₀ ^ 2 * B + 2 * D₁ ^ 2 * (M * M) * B := by
        gcongr
    _ = 2 * (D₀ ^ 2 + M ^ 2 * D₁ ^ 2) * B := by ring

end Triples
