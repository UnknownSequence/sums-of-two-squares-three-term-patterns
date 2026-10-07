import TriplesFinal.TypeIProof.SpectralSum

/-!
# The exceptional sums on `𝒥₀` via Lemma 10.3

The alternative to `J0_exc` used for Theorem 6.1(b): with `Y₀ = min(V, max(1, q/M))` and
`θ_j ≤ θ`, `V^(2θ_j) ≤ Y₀^(2θ_j) (1 + V/max(1, q/M))^(2θ)`, and Lemma 10.3 applies with `Y₀`.

Paper: §12.2 ("If instead we use Lemma 10.3 …").
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition) (F : SpecFam)

/-- `V^(2θ') ≤ Y₀^(2θ') (1 + V/max(1, q/M))^(2θ)` for `0 ≤ θ' ≤ θ`. -/
theorem V_rpow_le {θ θ' : ℝ} (hθ' : 0 ≤ θ') (hθθ : θ' ≤ θ) :
    S.V ^ (2 * θ') ≤ (min S.V (max 1 (S.q / S.M))) ^ (2 * θ') *
      (1 + S.V / max 1 (S.q / S.M)) ^ (2 * θ) := by
  have hV1 : 1 ≤ S.V := by linarith [S.V_ge]
  have hm1 : 1 ≤ max 1 (S.q / S.M) := le_max_left _ _
  set m := max 1 (S.q / S.M) with hm
  set Y₀ := min S.V m with hY₀
  have hY₀1 : 1 ≤ Y₀ := le_min hV1 hm1
  have hY₀0 : 0 < Y₀ := by linarith
  have hratio : 1 ≤ S.V / Y₀ := by
    rw [le_div_iff₀ hY₀0, one_mul]; exact min_le_left _ _
  have hratio' : S.V / Y₀ ≤ 1 + S.V / m := by
    by_cases h : S.V ≤ m
    · have : Y₀ = S.V := min_eq_left h
      rw [this, div_self (by linarith)]
      have : 0 ≤ S.V / m := by positivity
      linarith
    · push Not at h
      have : Y₀ = m := min_eq_right h.le
      rw [this]; linarith
  have e : S.V = Y₀ * (S.V / Y₀) := by field_simp
  calc S.V ^ (2 * θ') = (Y₀ * (S.V / Y₀)) ^ (2 * θ') := by rw [← e]
    _ = Y₀ ^ (2 * θ') * (S.V / Y₀) ^ (2 * θ') :=
        Real.mul_rpow hY₀0.le (by linarith)
    _ ≤ Y₀ ^ (2 * θ') * (S.V / Y₀) ^ (2 * θ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hratio (by linarith)
    _ ≤ Y₀ ^ (2 * θ') * (1 + S.V / m) ^ (2 * θ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow (by linarith) hratio' (by linarith)

/-- **The exceptional sums on `𝒥₀`, by Lemma 10.3.** -/
theorem J0_exc_DI {θ C : ℝ} (hC : 0 ≤ C) (hEB : F.ExcBound θ)
    (hB : F.ExcB S.q S.η C) :
    ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∫ x in F.exc, S.V ^ (2 * (F.t x).im) *
        ‖S.Ssum ψ₀ (F.ρ x) s σ‖ ^ 2 ∂F.ν ≤
      (1 + S.V / max 1 (S.q / S.M)) ^ (2 * θ) *
        (C * (S.q * S.M) ^ S.η * (1 + S.M / S.q) * (2 * S.M * (2 * S.C₀) ^ 2)) := by
  intro s hs σ
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hM := S.M_pos
  have hq := S.q_pos
  have hV1 : 1 ≤ S.V := by linarith [S.V_ge]
  set m := max 1 (S.q / S.M) with hm
  set Y₀ := min S.V m with hY₀
  have hY₀1 : 1 ≤ Y₀ := le_min hV1 (le_max_left _ _)
  have hY₀m : Y₀ ≤ m := min_le_right _ _
  set E := (1 + S.V / m) ^ (2 * θ) with hE
  have hE0 : 0 ≤ E := by positivity
  set a : ℕ → ℂ := fun n => S.Gfun ψ₀ s σ (n / S.M) with ha
  have hsupp : ∀ n, a n ≠ 0 → S.M < n ∧ (n : ℝ) ≤ 2 * S.M := by
    intro n hn
    have := S.Gfun_support ψ₀ s σ _ hn
    constructor
    · rw [lt_div_iff₀ hM, one_mul] at this; exact this.1
    · rw [div_le_iff₀ hM] at this; linarith [this.2]
  have hLS := hB S.M S.hM1 Y₀ hY₀1 hY₀m a hsupp
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, ‖a n‖ ^ 2 ≤ 2 * S.M * (2 * S.C₀) ^ 2 := by
    calc ∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, ‖a n‖ ^ 2
        ≤ ∑ _n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, (2 * S.C₀) ^ 2 :=
          Finset.sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _)
            (S.norm_Gfun_le ψ₀ hs0 σ _) 2
      _ = ((Finset.Icc 1 ⌊2 * S.M⌋₊).card : ℝ) * (2 * S.C₀) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * S.M * (2 * S.C₀) ^ 2 :=
          mul_le_mul_of_nonneg_right S.card_Hs_le (sq_nonneg _)
  -- integrability of the weighted sums on `exc ⊆ ball 1`
  have hsub : F.exc ⊆ F.ball 1 := F.exc_subset_ball (by norm_num)
  have hc : ∀ n, Measurable fun _ : F.Ω => a n := fun n => measurable_const
  have hcb : ∀ (x : F.Ω) n, ‖a n‖ ≤ 2 * S.C₀ := fun _ n => S.norm_Gfun_le ψ₀ hs0 σ _
  have hmeas_im : Measurable fun x => (F.t x).im := Complex.measurable_im.comp F.meas_t
  have hI1 : IntegrableOn (fun x => S.V ^ (2 * (F.t x).im) *
      ‖∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, a n * F.ρ x n‖ ^ 2) F.exc F.ν := by
    refine (F.integrableOn_weight_sq_sum (Finset.Icc 1 ⌊2 * S.M⌋₊) (c := fun _ n => a n) hc hcb 1
      (w := fun x => S.V ^ (2 * (F.t x).im)) (measurable_const.pow (hmeas_im.const_mul 2))
      (W := S.V) (fun x _ => ?_)).mono_set hsub
    rw [Real.norm_of_nonneg (by positivity)]
    calc S.V ^ (2 * (F.t x).im) ≤ S.V ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hV1 (by linarith [F.im_lt_half x])
      _ = S.V := Real.rpow_one _
  have hI2 : IntegrableOn (fun x => E * (Y₀ ^ (2 * (F.t x).im) *
      ‖∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, a n * F.ρ x n‖ ^ 2)) F.exc F.ν := by
    refine ((F.integrableOn_weight_sq_sum (Finset.Icc 1 ⌊2 * S.M⌋₊) (c := fun _ n => a n) hc hcb 1
      (w := fun x => Y₀ ^ (2 * (F.t x).im)) (measurable_const.pow (hmeas_im.const_mul 2))
      (W := Y₀) (fun x _ => ?_)).mono_set hsub).const_mul E
    rw [Real.norm_of_nonneg (by positivity)]
    calc Y₀ ^ (2 * (F.t x).im) ≤ Y₀ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hY₀1 (by linarith [F.im_lt_half x])
      _ = Y₀ := Real.rpow_one _
  have hSsum : ∀ x, S.Ssum ψ₀ (F.ρ x) s σ = ∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, a n * F.ρ x n :=
    fun x => rfl
  simp only [hSsum]
  calc ∫ x in F.exc, S.V ^ (2 * (F.t x).im) *
        ‖∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, a n * F.ρ x n‖ ^ 2 ∂F.ν
      ≤ ∫ x in F.exc, E * (Y₀ ^ (2 * (F.t x).im) *
          ‖∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, a n * F.ρ x n‖ ^ 2) ∂F.ν := by
        refine setIntegral_mono_on hI1 hI2 F.measurableSet_exc fun x hx => ?_
        have hx0 : 0 < (F.t x).im := hx
        have hθx := hEB x hx0
        have := S.V_rpow_le hx0.le hθx
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [mul_comm E]; exact this) (sq_nonneg _)
    _ = E * ∫ x in F.exc, Y₀ ^ (2 * (F.t x).im) *
          ‖∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, a n * F.ρ x n‖ ^ 2 ∂F.ν := integral_const_mul _ _
    _ ≤ E * (C * (S.q * S.M) ^ S.η * (1 + S.M / S.q) *
          ∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, ‖a n‖ ^ 2) := mul_le_mul_of_nonneg_left hLS hE0
    _ ≤ E * (C * (S.q * S.M) ^ S.η * (1 + S.M / S.q) * (2 * S.M * (2 * S.C₀) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hE0
        exact mul_le_mul_of_nonneg_left hsum (by positivity)

end Setup

end Triples
