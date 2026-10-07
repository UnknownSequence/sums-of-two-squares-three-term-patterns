import TriplesFinal.Poisson.Defs
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Fourier transforms of bump functions and Poisson summation

For `ψ : ℝ → ℂ` smooth and supported in `[-1, 1]`:

* `ψ̂ = 𝓕 ψ` is Mathlib's Fourier transform (`fourier_eq_fourierIntegral`);
* if `|ψ^(k)| ≤ B`, then `(2π|ξ|)^k |ψ̂(ξ)| ≤ 2B` (`norm_fourier_le`; integration by parts `k`
  times, via `Real.fourier_iteratedDeriv`);
* **Poisson summation**: `∑_m ψ((ν + mμ)/X) = ∑_h (X/μ) ψ̂(hX/μ) e(hν/μ)`, with an absolutely
  convergent right-hand side (`hasSum_poisson`, from `Real.tsum_eq_tsum_fourier_of_rpow_decay`);
* the decay bound for `ψ` supported in any interval `[a, b]` (`norm_fourier_le_Icc`), used in
  Lemma 10.5.

Paper: §9.1, proof of Lemma 9.1.
-/

namespace Triples

open MeasureTheory Filter Asymptotics
open scoped FourierTransform ContDiff Real

/-- Our Fourier transform agrees with Mathlib's `𝓕`. -/
theorem fourier_eq_fourierIntegral (ψ : ℝ → ℂ) : fourier ψ = 𝓕 ψ := by
  ext ξ
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold fourier eC
  congr 1; ext t
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast; ring

section Bump

variable {ψ : ℝ → ℂ}

theorem tsupport_subset_Icc (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) :
    tsupport ψ ⊆ Set.Icc (-1) 1 :=
  closure_minimal (fun x hx => hs x hx) isClosed_Icc

theorem tsupport_iteratedDeriv_subset (k : ℕ) : tsupport (iteratedDeriv k ψ) ⊆ tsupport ψ := by
  induction k with
  | zero => simp
  | succ k ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem iteratedDeriv_eq_zero_of_not_mem (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) (k : ℕ) {t : ℝ}
    (ht : t ∉ Set.Icc (-1 : ℝ) 1) : iteratedDeriv k ψ t = 0 :=
  image_eq_zero_of_notMem_tsupport fun h =>
    ht (tsupport_subset_Icc hs (tsupport_iteratedDeriv_subset k h))

theorem hasCompactSupport_iteratedDeriv (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k ψ) :=
  HasCompactSupport.intro isCompact_Icc fun _ ht => iteratedDeriv_eq_zero_of_not_mem hs k ht

theorem integrable_iteratedDeriv (hψ : ContDiff ℝ ∞ ψ) (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1)
    (k : ℕ) : Integrable (iteratedDeriv k ψ) :=
  (hψ.continuous_iteratedDeriv k (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv hs k)

/-- `∫ |ψ^(k)| ≤ 2B` if `|ψ^(k)| ≤ B`. -/
theorem integral_norm_iteratedDeriv_le (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) {k : ℕ} {B : ℝ}
    (hB : ∀ t, ‖iteratedDeriv k ψ t‖ ≤ B) : ∫ t, ‖iteratedDeriv k ψ t‖ ≤ 2 * B := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-1 : ℝ) 1)
    (fun t ht => by rw [iteratedDeriv_eq_zero_of_not_mem hs k ht, norm_zero])]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (-1 : ℝ) 1)
    (f := fun t => ‖iteratedDeriv k ψ t‖) (C := B) (by simp) (fun t _ => by
      rw [Real.norm_eq_abs, abs_norm]; exact hB t)
  rw [Real.volume_real_Icc_of_le (by norm_num)] at this
  have h0 : 0 ≤ ∫ t in Set.Icc (-1 : ℝ) 1, ‖iteratedDeriv k ψ t‖ :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h0] at this
  linarith

/-- **Decay of the Fourier transform.** If `ψ` is smooth, supported in `[-1, 1]`, and
`|ψ^(k)| ≤ B`, then `|ψ̂(ξ)| ≤ 2B (2π|ξ|)^(-k)`. -/
theorem norm_fourier_le (hψ : ContDiff ℝ ∞ ψ) (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) {k : ℕ}
    {B : ℝ} (hB : ∀ t, ‖iteratedDeriv k ψ t‖ ≤ B) (ξ : ℝ) :
    (2 * π * |ξ|) ^ k * ‖fourier ψ ξ‖ ≤ 2 * B := by
  have h := congrFun (Real.fourier_iteratedDeriv (N := ⊤) hψ
    (fun n _ => integrable_iteratedDeriv hψ hs n) (n := k) le_top) ξ
  have h2 : ‖𝓕 (iteratedDeriv k ψ) ξ‖ ≤ 2 * B :=
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
      (integral_norm_iteratedDeriv_le hs hB)
  rw [h, norm_smul, norm_pow] at h2
  rw [fourier_eq_fourierIntegral]
  convert h2 using 2
  simp [abs_of_pos Real.pi_pos]

end Bump

/-- `|e(t)| = 1`. -/
theorem norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  rw [show 2 * (π : ℂ) * Complex.I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- The Fourier transform of `t ↦ ψ(at)` (`a > 0`) is `ξ ↦ a⁻¹ ψ̂(ξ/a)`. -/
theorem fourier_comp_mul (ψ : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun t => ψ (a * t)) ξ = ((a⁻¹ : ℝ) : ℂ) * 𝓕 ψ (ξ / a) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have := Measure.integral_comp_mul_left (fun u : ℝ => 𝐞 (-(u * (ξ / a))) • ψ u) a
  have e : ∀ x : ℝ, a * x * (ξ / a) = x * ξ := fun x => by field_simp
  simp_rw [e] at this
  rw [this, abs_of_pos (inv_pos.2 ha), Complex.real_smul]

section Poisson

variable {ψ : ℝ → ℂ}

/-- **Poisson summation** for a dilated bump function:
`∑_m ψ((ν + mμ)/X) = ∑_h (X/μ) ψ̂(hX/μ) e(hν/μ)`, the right-hand side converging absolutely. -/
theorem hasSum_poisson (hψ : ContDiff ℝ ∞ ψ) (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1)
    {B : ℝ} (hB : ∀ t, ‖iteratedDeriv 2 ψ t‖ ≤ B) {μ X : ℝ} (hμ : 0 < μ) (hX : 0 < X) (ν : ℝ) :
    HasSum (fun h : ℤ => ((X / μ : ℝ) : ℂ) * fourier ψ (h * X / μ) * eC (h * ν / μ))
      (∑' m : ℤ, ψ ((ν + m * μ) / X)) := by
  set a := μ / X with ha_def
  have ha : 0 < a := div_pos hμ hX
  set f : ℝ → ℂ := fun t => ψ (a * t) with hf
  have hFf : ∀ w, 𝓕 f w = ((X / μ : ℝ) : ℂ) * fourier ψ (w * X / μ) := by
    intro w
    rw [hf, fourier_comp_mul ψ ha, fourier_eq_fourierIntegral, ha_def]
    congr 2
    · rw [inv_div]
    · field_simp
  -- `𝓕 f` decays like `|w|⁻²`
  set C₀ : ℝ := X / μ * (2 * B) * (2 * π * (X / μ))⁻¹ ^ 2 with hC₀
  have hdecay : ∀ w : ℝ, w ≠ 0 → ‖𝓕 f w‖ ≤ C₀ * |w| ^ (-2 : ℝ) := by
    intro w hw
    have h1 := norm_fourier_le hψ hs hB (w * X / μ)
    have hpos : 0 < 2 * π * |w * X / μ| := by
      have : 0 < |w * X / μ| := abs_pos.2 (by positivity)
      positivity
    rw [hFf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hX hμ)]
    have h2 : ‖fourier ψ (w * X / μ)‖ ≤ 2 * B / (2 * π * |w * X / μ|) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have e : 2 * B / (2 * π * |w * X / μ|) ^ 2 = 2 * B * (2 * π * (X / μ))⁻¹ ^ 2 * |w| ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (abs_nonneg w), Real.rpow_two, abs_div, abs_mul, abs_of_pos hX,
        abs_of_pos hμ]
      have : |w| ≠ 0 := abs_ne_zero.2 hw
      field_simp
    rw [hC₀]
    calc X / μ * ‖fourier ψ (w * X / μ)‖ ≤ X / μ * (2 * B / (2 * π * |w * X / μ|) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (div_pos hX hμ).le
      _ = _ := by rw [e]; ring
  have hc : Continuous f := hψ.continuous.comp (continuous_const.mul continuous_id)
  have hfO : f =O[cocompact ℝ] (|·| ^ (-2 : ℝ)) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [(isCompact_Icc (a := -a⁻¹) (b := a⁻¹)).compl_mem_cocompact] with w hw
    have : ψ (a * w) = 0 := by
      by_contra hne
      obtain ⟨h1, h2⟩ := hs _ hne
      have hle : a * |w| ≤ 1 := by
        rw [← abs_of_pos ha, ← abs_mul]; exact abs_le.2 ⟨h1, h2⟩
      apply hw
      rw [Set.mem_Icc, ← abs_le]
      calc |w| = a⁻¹ * (a * |w|) := by field_simp
        _ ≤ a⁻¹ * 1 := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 ha.le)
        _ = a⁻¹ := mul_one _
    simp [hf, this]
  have hFfO : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-2 : ℝ)) := by
    refine IsBigO.of_bound C₀ ?_
    filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with w hw
    rw [Real.norm_eq_abs (|w| ^ (-2 : ℝ)), abs_of_nonneg (Real.rpow_nonneg (abs_nonneg w) _)]
    exact hdecay w hw
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hc one_lt_two hfO hFfO (ν / μ)
  have hsum : Summable fun n : ℤ => 𝓕 f n :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hFfO.comp_tendsto Int.tendsto_coe_cofinite)
  have hG : ∀ n : ℤ, ((X / μ : ℝ) : ℂ) * fourier ψ (n * X / μ) * eC (n * ν / μ) =
      𝓕 f n * _root_.fourier n ((ν / μ : ℝ) : UnitAddCircle) := by
    intro n
    rw [hFf, fourier_coe_apply, eC]
    congr 2
    push_cast; ring
  have hsum' : Summable fun n : ℤ =>
      ((X / μ : ℝ) : ℂ) * fourier ψ (n * X / μ) * eC (n * ν / μ) := by
    refine Summable.of_norm_bounded hsum.norm (fun n => ?_)
    rw [norm_mul, norm_eC, mul_one, hFf]
  convert hsum'.hasSum using 1
  rw [tsum_congr hG, ← hP]
  apply tsum_congr
  intro m
  rw [hf]
  congr 1
  rw [ha_def]
  field_simp

end Poisson

section General

variable {ψ : ℝ → ℂ} {a b : ℝ}

theorem iteratedDeriv_eq_zero_of_not_mem_Icc (hs : ∀ t, ψ t ≠ 0 → a ≤ t ∧ t ≤ b) (k : ℕ)
    {t : ℝ} (ht : t ∉ Set.Icc a b) : iteratedDeriv k ψ t = 0 :=
  image_eq_zero_of_notMem_tsupport fun h =>
    ht ((closure_minimal (fun x hx => hs x hx) isClosed_Icc) (tsupport_iteratedDeriv_subset k h))

theorem integrable_iteratedDeriv_Icc (hψ : ContDiff ℝ ∞ ψ) (hs : ∀ t, ψ t ≠ 0 → a ≤ t ∧ t ≤ b)
    (k : ℕ) : Integrable (iteratedDeriv k ψ) :=
  (hψ.continuous_iteratedDeriv k (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun _ ht => iteratedDeriv_eq_zero_of_not_mem_Icc hs k ht)

theorem integral_norm_iteratedDeriv_le_Icc (hab : a ≤ b) (hs : ∀ t, ψ t ≠ 0 → a ≤ t ∧ t ≤ b)
    {k : ℕ} {B : ℝ} (hB : ∀ t, ‖iteratedDeriv k ψ t‖ ≤ B) :
    ∫ t, ‖iteratedDeriv k ψ t‖ ≤ (b - a) * B := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc a b)
    (fun t ht => by rw [iteratedDeriv_eq_zero_of_not_mem_Icc hs k ht, norm_zero])]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc a b)
    (f := fun t => ‖iteratedDeriv k ψ t‖) (C := B) (by simp) (fun t _ => by
      rw [Real.norm_eq_abs, abs_norm]; exact hB t)
  rw [Real.volume_real_Icc_of_le hab] at this
  have h0 : 0 ≤ ∫ t in Set.Icc a b, ‖iteratedDeriv k ψ t‖ :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h0] at this
  linarith

/-- **Decay of the Fourier transform** for `ψ` supported in `[a, b]`:
`(2π|ξ|)^k |ψ̂(ξ)| ≤ (b - a) B` if `|ψ^(k)| ≤ B`. -/
theorem norm_fourier_le_Icc (hψ : ContDiff ℝ ∞ ψ) (hab : a ≤ b)
    (hs : ∀ t, ψ t ≠ 0 → a ≤ t ∧ t ≤ b) {k : ℕ} {B : ℝ} (hB : ∀ t, ‖iteratedDeriv k ψ t‖ ≤ B)
    (ξ : ℝ) : (2 * π * |ξ|) ^ k * ‖𝓕 ψ ξ‖ ≤ (b - a) * B := by
  have h := congrFun (Real.fourier_iteratedDeriv (N := ⊤) hψ
    (fun n _ => integrable_iteratedDeriv_Icc hψ hs n) (n := k) le_top) ξ
  have h2 : ‖𝓕 (iteratedDeriv k ψ) ξ‖ ≤ (b - a) * B :=
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
      (integral_norm_iteratedDeriv_le_Icc hab hs hB)
  rw [h, norm_smul, norm_pow] at h2
  convert h2 using 2
  simp [abs_of_pos Real.pi_pos]

/-- The Fourier transform of an integrable function is continuous. -/
theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simp only [innerₗ_apply_apply]; fun_prop) hf

end General

end Triples
