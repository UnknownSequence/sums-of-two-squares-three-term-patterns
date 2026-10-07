import TriplesFinal.Spectral.Twist
import TriplesFinal.Analysis.MeasureTools

/-!
# Lemma 10.6 for families indexed by a measure space

The pointwise form of the partial summation of Lemma 10.6 (`twist_pointwise`), and the version
for a family indexed by a measure space (`twist_removal_measure`), which the proof of
Theorem 6.1 applies to the continuous spectrum (the paper: "the proof of Lemma 10.6 applies
verbatim to a family indexed by `(𝔰, r)` with the measure `dr/4π`").

Paper: §10.4, Lemma 10.6.
-/

namespace Triples

open MeasureTheory

/-- The index set `{i < ⌊2M⌋ : M < i}` of the partial summation in Lemma 10.6. -/
noncomputable def twistIdx (M : ℝ) : Finset ℕ :=
  (Finset.range ⌊2 * M⌋₊).filter (fun i : ℕ => M < i)

theorem card_twistIdx_le {M : ℝ} (hM0 : 0 ≤ M) : ((twistIdx M).card : ℝ) ≤ M := by
  set N := ⌊2 * M⌋₊ with hN
  have hNle : (N : ℝ) ≤ 2 * M := Nat.floor_le (by linarith)
  set I := twistIdx M with hI
  have hsub : I ⊆ Finset.Ico (⌊M⌋₊ + 1) N := by
    intro i hi
    simp only [hI, twistIdx, Finset.mem_filter, Finset.mem_range] at hi
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

theorem mem_twistIdx_Icc {M : ℝ} (hM0 : 0 ≤ M) {i : ℕ} (hi : i ∈ twistIdx M) :
    (i : ℝ) ∈ Set.Icc M (2 * M) := by
  simp only [twistIdx, Finset.mem_filter, Finset.mem_range] at hi
  have hNle : (⌊2 * M⌋₊ : ℝ) ≤ 2 * M := Nat.floor_le (by linarith)
  refine ⟨hi.2.le, le_trans ?_ hNle⟩
  exact_mod_cast hi.1.le

/-- **Lemma 10.6, pointwise form**: with `P(y) = ∑_{M < n ≤ y} ξ(n)` and `I = twistIdx M`
(`#I ≤ M`, `I ⊆ [M, 2M]`),
`|∑_{n ∼ M} ξ(n) φ(n)|² ≤ 2D₀² |P(2M)|² + 2D₁² #I ∑_{i ∈ I} |P(i)|²`. -/
theorem twist_pointwise {M D₀ D₁ : ℝ} (hM : 1 / 2 ≤ M) (ξ : ℕ → ℂ) (φ : ℝ → ℂ)
    (hφd : ∀ y ∈ Set.Icc M (2 * M), HasDerivAt φ (deriv φ y) y)
    (hD₀ : ∀ y ∈ Set.Icc M (2 * M), ‖φ y‖ ≤ D₀)
    (hD₁ : ∀ y ∈ Set.Icc M (2 * M), ‖deriv φ y‖ ≤ D₁) :
    ‖∑ n ∈ (Finset.Icc 1 ⌊2 * M⌋₊).filter (fun n : ℕ => M < n), ξ n * φ n‖ ^ 2 ≤
      2 * D₀ ^ 2 * ‖∑ n ∈ (Finset.Icc 1 ⌊2 * M⌋₊).filter (fun n : ℕ => M < n), ξ n‖ ^ 2 +
      2 * D₁ ^ 2 * (twistIdx M).card *
        ∑ i ∈ twistIdx M, ‖∑ n ∈ (Finset.Icc 1 i).filter (fun n : ℕ => M < n), ξ n‖ ^ 2 := by
  classical
  have hM0 : 0 ≤ M := by linarith
  have hMmem : M ∈ Set.Icc M (2 * M) := ⟨le_refl _, by linarith⟩
  set N := ⌊2 * M⌋₊ with hN
  have hNle : (N : ℝ) ≤ 2 * M := Nat.floor_le (by linarith)
  -- the truncated sequence and its partial sums
  set g : ℕ → ℂ := fun i => if M < i then ξ i else 0 with hg
  set S : ℕ → ℂ := fun k => ∑ i ∈ Finset.range k, g i with hS
  have hS_eq : ∀ k : ℕ,
      S (k + 1) = ∑ n ∈ (Finset.Icc 1 k).filter (fun n : ℕ => M < n), ξ n := by
    intro k
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
  have hS_zero : ∀ i : ℕ, ¬ M < i → S (i + 1) = 0 := by
    intro i hi
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : (k : ℝ) ≤ i := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    simp only [hg]
    rw [ite_eq_right_iff.2 (fun h => absurd h ?_)]
    push Not at hi ⊢
    linarith
  have hsum : ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => M < n), ξ n * φ n =
      φ N * S (N + 1) -
        ∑ i ∈ Finset.range N, (φ ((i + 1 : ℕ) : ℝ) - φ i) * S (i + 1) := by
    have h := Finset.sum_range_by_parts (fun i : ℕ => φ i) g (N + 1)
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
  set I := twistIdx M with hI
  have hpt : ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => M < n), ξ n * φ n‖ ≤
      D₀ * ‖S (N + 1)‖ + D₁ * ∑ i ∈ I, ‖S (i + 1)‖ := by
    have hD₁0 : 0 ≤ D₁ := le_trans (norm_nonneg _) (hD₁ M hMmem)
    rw [hsum]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      by_cases hNM : M < N
      · exact mul_le_mul_of_nonneg_right (hD₀ N ⟨hNM.le, hNle⟩) (norm_nonneg _)
      · rw [hS_zero N hNM, norm_zero, mul_zero, mul_zero]
    · refine (norm_sum_le _ _).trans ?_
      rw [hI, twistIdx, Finset.sum_filter, Finset.mul_sum]
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
          (fun y hy => (hφd y hy).hasDerivWithinAt) hD₁ (convex_Icc M (2 * M)) hmem1 hmem2
        have : ‖((i + 1 : ℕ) : ℝ) - (i : ℝ)‖ = 1 := by push_cast; simp
        rw [this, mul_one] at hmvt
        exact mul_le_mul_of_nonneg_right hmvt (norm_nonneg _)
      · rw [hS_zero i hMi, norm_zero, mul_zero, mul_zero]
  have hsq : ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => M < n), ξ n * φ n‖ ^ 2 ≤
      2 * D₀ ^ 2 * ‖S (N + 1)‖ ^ 2 + 2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ‖S (i + 1)‖ ^ 2 := by
    have hD₀0 : 0 ≤ D₀ := le_trans (norm_nonneg _) (hD₀ M hMmem)
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hpt 2
    have h2 := sq_add_le_two_mul (D₀ * ‖S (N + 1)‖) (D₁ * ∑ i ∈ I, ‖S (i + 1)‖)
    have h3 : (∑ i ∈ I, ‖S (i + 1)‖) ^ 2 ≤ I.card * ∑ i ∈ I, ‖S (i + 1)‖ ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun i => ‖S (i + 1)‖)
      simpa using this
    have h4 : 2 * (D₁ * ∑ i ∈ I, ‖S (i + 1)‖) ^ 2 ≤
        2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ‖S (i + 1)‖ ^ 2 := by
      calc 2 * (D₁ * ∑ i ∈ I, ‖S (i + 1)‖) ^ 2
          = 2 * D₁ ^ 2 * (∑ i ∈ I, ‖S (i + 1)‖) ^ 2 := by ring
        _ ≤ 2 * D₁ ^ 2 * (I.card * ∑ i ∈ I, ‖S (i + 1)‖ ^ 2) := by gcongr
        _ = 2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ‖S (i + 1)‖ ^ 2 := by ring
    calc _ ≤ (D₀ * ‖S (N + 1)‖ + D₁ * ∑ i ∈ I, ‖S (i + 1)‖) ^ 2 := h1
      _ ≤ 2 * (D₀ * ‖S (N + 1)‖) ^ 2 + 2 * (D₁ * ∑ i ∈ I, ‖S (i + 1)‖) ^ 2 := h2
      _ ≤ 2 * D₀ ^ 2 * ‖S (N + 1)‖ ^ 2 + 2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ‖S (i + 1)‖ ^ 2 := by
          rw [mul_pow]; linarith
  simp only [hS_eq] at hsq
  exact hsq

/-- **Lemma 10.6 for a measure**: if `∫_S ω |∑_{M < n ≤ y} ξ_x(n)|² dμ(x) ≤ B` for all
`y ∈ [M, 2M]` (with integrable integrands), then
`∫_S ω |∑_{n ∼ M} ξ_x(n) φ_x(n)|² dμ(x) ≤ 2(D₀² + M² D₁²) B`. -/
theorem twist_removal_measure {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    {M D₀ D₁ B : ℝ} (hM : 1 / 2 ≤ M) (ω : α → ℝ) (hω : ∀ x, 0 ≤ ω x) (ξ : α → ℕ → ℂ)
    (φ : α → ℝ → ℂ) (hφd : ∀ x, ∀ y ∈ Set.Icc M (2 * M), HasDerivAt (φ x) (deriv (φ x) y) y)
    (hD₀ : ∀ x, ∀ y ∈ Set.Icc M (2 * M), ‖φ x y‖ ≤ D₀)
    (hD₁ : ∀ x, ∀ y ∈ Set.Icc M (2 * M), ‖deriv (φ x) y‖ ≤ D₁)
    (hint : ∀ y ∈ Set.Icc M (2 * M), IntegrableOn (fun x => ω x *
      ‖∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => M < n), ξ x n‖ ^ 2) S μ)
    (hB : ∀ y ∈ Set.Icc M (2 * M), ∫ x in S, ω x *
      ‖∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => M < n), ξ x n‖ ^ 2 ∂μ ≤ B) :
    ∫ x in S, ω x *
        ‖∑ n ∈ (Finset.Icc 1 ⌊2 * M⌋₊).filter (fun n : ℕ => M < n), ξ x n * φ x n‖ ^ 2 ∂μ ≤
      2 * (D₀ ^ 2 + M ^ 2 * D₁ ^ 2) * B := by
  classical
  have hM0 : 0 ≤ M := by linarith
  have hMmem : M ∈ Set.Icc M (2 * M) := ⟨le_refl _, by linarith⟩
  have h2Mmem : 2 * M ∈ Set.Icc M (2 * M) := ⟨by linarith, le_refl _⟩
  have hB0 : 0 ≤ B := le_trans (integral_nonneg fun x => mul_nonneg (hω x) (sq_nonneg _))
    (hB M hMmem)
  set I := twistIdx M with hI
  have hIc := card_twistIdx_le hM0
  set P : α → ℕ → ℂ := fun x k => ∑ n ∈ (Finset.Icc 1 k).filter (fun n : ℕ => M < n), ξ x n
    with hP
  have hintN : IntegrableOn (fun x => ω x * ‖P x ⌊2 * M⌋₊‖ ^ 2) S μ := hint _ h2Mmem
  have hintI : ∀ i ∈ I, IntegrableOn (fun x => ω x * ‖P x i‖ ^ 2) S μ := by
    intro i hi
    have := hint i (mem_twistIdx_Icc hM0 hi)
    simpa only [Nat.floor_natCast] using this
  have hBN : ∫ x in S, ω x * ‖P x ⌊2 * M⌋₊‖ ^ 2 ∂μ ≤ B := hB _ h2Mmem
  have hBI : ∀ i ∈ I, ∫ x in S, ω x * ‖P x i‖ ^ 2 ∂μ ≤ B := by
    intro i hi
    have := hB i (mem_twistIdx_Icc hM0 hi)
    simpa only [Nat.floor_natCast] using this
  set R : α → ℝ := fun x => 2 * D₀ ^ 2 * (ω x * ‖P x ⌊2 * M⌋₊‖ ^ 2) +
    2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ω x * ‖P x i‖ ^ 2 with hR
  have hRint : IntegrableOn R S μ :=
    (hintN.const_mul _).add ((integrable_finsetSum _ hintI).const_mul _)
  have hpt : ∀ x, ω x * ‖∑ n ∈ (Finset.Icc 1 ⌊2 * M⌋₊).filter (fun n : ℕ => M < n),
      ξ x n * φ x n‖ ^ 2 ≤ R x := by
    intro x
    have h := twist_pointwise hM (ξ x) (φ x) (hφd x) (hD₀ x) (hD₁ x)
    have h' := mul_le_mul_of_nonneg_left h (hω x)
    rw [← hI] at h'
    calc _ ≤ _ := h'
      _ = R x := by
        simp only [hR, hP]
        rw [← Finset.mul_sum]
        ring
  calc ∫ x in S, ω x * ‖∑ n ∈ (Finset.Icc 1 ⌊2 * M⌋₊).filter (fun n : ℕ => M < n),
          ξ x n * φ x n‖ ^ 2 ∂μ
      ≤ ∫ x in S, R x ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => mul_nonneg (hω x)
          (sq_nonneg _)) hRint (Filter.Eventually.of_forall hpt)
    _ = 2 * D₀ ^ 2 * ∫ x in S, ω x * ‖P x ⌊2 * M⌋₊‖ ^ 2 ∂μ +
          2 * D₁ ^ 2 * I.card * ∑ i ∈ I, ∫ x in S, ω x * ‖P x i‖ ^ 2 ∂μ := by
        rw [hR, integral_add (hintN.const_mul _) ((integrable_finsetSum _ hintI).const_mul _),
          integral_const_mul, integral_const_mul, integral_finsetSum _ hintI]
    _ ≤ 2 * D₀ ^ 2 * B + 2 * D₁ ^ 2 * I.card * ∑ _i ∈ I, B := by
        gcongr with i hi
        exact hBI i hi
    _ = 2 * D₀ ^ 2 * B + 2 * D₁ ^ 2 * ((I.card : ℝ) * I.card) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * D₀ ^ 2 * B + 2 * D₁ ^ 2 * (M * M) * B := by
        gcongr
    _ = 2 * (D₀ ^ 2 + M ^ 2 * D₁ ^ 2) * B := by ring

end Triples
