import TriplesFinal.Assumptions.Defs
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Lemma 11.1: the integral representation of `K_ν`

`K_ν(y) = ½ ∫_ℝ exp(-y cosh σ + νσ) dσ` for `y > 0` (this is our definition `besselK`).
If `|Re ν| ≤ 1/2`, `V ≥ 1` and `y ≥ y₀ > 0`, then the integral over `|σ| > log V` contributes at
most `(2/y₀) e^(-y₀V/2)` in absolute value.

The proof bounds the integrand by `e^|σ| exp(-(y₀/2) e^|σ|)`, which has the antiderivative
`-(2/y₀) exp(-(y₀/2) e^σ)` on `σ > log V`, and treats `σ < -log V` by `σ ↦ -σ`.

Paper: §11, Lemma 11.1.
-/

namespace Triples

open MeasureTheory Set Filter Topology

/-- `cosh σ ≥ e^|σ|/2`. -/
theorem exp_abs_le_two_mul_cosh (σ : ℝ) : Real.exp |σ| ≤ 2 * Real.cosh σ := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have := Real.exp_pos (-|σ|)
  linarith

/-- **Lemma 11.1**, the tail bound. -/
theorem besselK_tail {ν : ℂ} (hν : |ν.re| ≤ 1 / 2) {V y y₀ : ℝ} (hV : 1 ≤ V) (hy₀ : 0 < y₀)
    (hy : y₀ ≤ y) :
    ‖(1 / 2 : ℂ) * ∫ σ in {σ : ℝ | Real.log V < |σ|},
        Complex.exp (-((y * Real.cosh σ : ℝ) : ℂ) + ν * σ)‖ ≤
      2 / y₀ * Real.exp (-(y₀ * V / 2)) := by
  set L := Real.log V with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hV
  have hVpos : 0 < V := by linarith
  set f : ℝ → ℂ := fun σ => Complex.exp (-((y * Real.cosh σ : ℝ) : ℂ) + ν * σ) with hf
  set G : ℝ → ℝ := fun σ => Real.exp σ * Real.exp (-(y₀ / 2 * Real.exp σ)) with hG
  set Φ : ℝ → ℝ := fun σ => -(2 / y₀) * Real.exp (-(y₀ / 2 * Real.exp σ)) with hΦ
  have hderiv : ∀ σ, HasDerivAt Φ (G σ) σ := by
    intro σ
    have h0 : HasDerivAt (fun σ => -(y₀ / 2 * Real.exp σ)) (-(y₀ / 2 * Real.exp σ)) σ :=
      ((Real.hasDerivAt_exp σ).const_mul (y₀ / 2)).neg
    have h1 := h0.exp.const_mul (-(2 / y₀))
    convert h1 using 1
    simp only [hG]
    field_simp
  have hlim : Tendsto Φ atTop (𝓝 0) := by
    have h1 : Tendsto (fun σ => y₀ / 2 * Real.exp σ) atTop atTop :=
      Real.tendsto_exp_atTop.const_mul_atTop (by positivity)
    have h2 := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).const_mul
      (-(2 / y₀))
    simpa [Φ, Function.comp_def] using h2
  have hGnn : ∀ σ, 0 ≤ G σ := fun σ => by positivity
  have hGint : IntegrableOn G (Ioi L) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun σ _ => hderiv σ) (fun σ _ => hGnn σ) hlim
  have hGval : ∫ σ in Ioi L, G σ = 2 / y₀ * Real.exp (-(y₀ * V / 2)) := by
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun σ _ => hderiv σ) (fun σ _ => hGnn σ) hlim]
    simp only [hΦ, hL, Real.exp_log hVpos]
    ring_nf
  -- the pointwise bound
  have hpt : ∀ σ : ℝ, ‖f σ‖ ≤ G |σ| := by
    intro σ
    simp only [hf, hG, Complex.norm_exp]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    have h1 : ν.re * σ ≤ |σ| / 2 := by
      have := abs_mul ν.re σ
      have h2 : |ν.re| * |σ| ≤ 1 / 2 * |σ| := mul_le_mul_of_nonneg_right hν (abs_nonneg σ)
      have h3 := le_abs_self (ν.re * σ)
      linarith
    have h2 : y₀ * Real.exp |σ| ≤ y * (2 * Real.cosh σ) := by
      have := exp_abs_le_two_mul_cosh σ
      have h0 : 0 ≤ Real.exp |σ| := (Real.exp_pos _).le
      nlinarith [Real.cosh_pos σ]
    have h3 : 0 ≤ |σ| := abs_nonneg σ
    linarith
  have hpos : 0 ≤ 2 / y₀ * Real.exp (-(y₀ * V / 2)) := by positivity
  by_cases hfi : IntegrableOn f {σ : ℝ | L < |σ|}
  swap
  · rw [integral_undef hfi, mul_zero, norm_zero]; exact hpos
  have hS : {σ : ℝ | L < |σ|} = Ioi L ∪ Iio (-L) := by
    ext σ
    simp only [mem_ofPred_eq, mem_union, mem_Ioi, mem_Iio, lt_abs]
    constructor <;> rintro (h | h) <;> [left; right; left; right] <;> linarith
  rw [hS] at hfi ⊢
  have hdisj : Disjoint (Ioi L) (Iio (-L)) := by
    rw [Set.disjoint_left]
    intro σ h1 h2
    simp only [mem_Ioi, mem_Iio] at h1 h2
    linarith
  rw [setIntegral_union hdisj measurableSet_Iio (hfi.mono_set subset_union_left)
    (hfi.mono_set subset_union_right)]
  -- the two halves
  have hA : ‖∫ σ in Ioi L, f σ‖ ≤ 2 / y₀ * Real.exp (-(y₀ * V / 2)) := by
    rw [← hGval]
    apply norm_integral_le_of_norm_le hGint
    refine (ae_restrict_mem measurableSet_Ioi).mono fun σ hσ => ?_
    have := hpt σ
    rwa [abs_of_pos (lt_of_le_of_lt hL0 hσ)] at this
  have hB : ‖∫ σ in Iio (-L), f σ‖ ≤ 2 / y₀ * Real.exp (-(y₀ * V / 2)) := by
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi, ← hGval]
    apply norm_integral_le_of_norm_le hGint
    refine (ae_restrict_mem measurableSet_Ioi).mono fun σ hσ => ?_
    have := hpt (-σ)
    rwa [abs_neg, abs_of_pos (lt_of_le_of_lt hL0 hσ)] at this
  calc ‖(1 / 2 : ℂ) * ((∫ σ in Ioi L, f σ) + ∫ σ in Iio (-L), f σ)‖
      ≤ 1 / 2 * (‖∫ σ in Ioi L, f σ‖ + ‖∫ σ in Iio (-L), f σ‖) := by
        rw [norm_mul]
        gcongr
        · simp
        · exact norm_add_le _ _
    _ ≤ 1 / 2 * (2 / y₀ * Real.exp (-(y₀ * V / 2)) + 2 / y₀ * Real.exp (-(y₀ * V / 2))) := by
        gcongr
    _ = 2 / y₀ * Real.exp (-(y₀ * V / 2)) := by ring

end Triples
