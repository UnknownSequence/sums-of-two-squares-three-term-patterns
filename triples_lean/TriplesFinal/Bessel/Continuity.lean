import TriplesFinal.Bessel.Integral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Continuity of `K_ν` on `(0, ∞)`

For `|Re ν| ≤ 1/2` and `y > 0` the integrand `e^(-y cosh σ + νσ)` of
`K_ν(y) = ½ ∫ e^(-y cosh σ + νσ) dσ` is bounded by `e^(1/(2y)) e^(-yσ²/8)`, so it is integrable,
and `K_ν` is continuous on `(0, ∞)` by dominated convergence.

Paper: §11 (used for Lemma 11.2 and §10.2).
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology

/-! ### The integrand of `K_ν` -/

/-- `cosh σ ≥ σ²/4`. -/
theorem sq_div_four_le_cosh (σ : ℝ) : σ ^ 2 / 4 ≤ Real.cosh σ := by
  have h1 := exp_abs_le_two_mul_cosh σ
  have h2 := Real.quadratic_le_exp_of_nonneg (abs_nonneg σ)
  have h3 : |σ| ^ 2 = σ ^ 2 := sq_abs σ
  nlinarith [abs_nonneg σ]

/-- `|e^(-y cosh σ + νσ)| ≤ e^(1/(2y)) e^(-yσ²/8)` for `|Re ν| ≤ 1/2`, `y > 0`. -/
theorem norm_besselK_integrand_le {ν : ℂ} (hν : |ν.re| ≤ 1 / 2) {y : ℝ} (hy : 0 < y) (σ : ℝ) :
    ‖Complex.exp (-((y * Real.cosh σ : ℝ) : ℂ) + ν * σ)‖ ≤
      Real.exp (1 / (2 * y)) * Real.exp (-(y / 8) * σ ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.2
  simp only [add_re, neg_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero]
  have h1 : ν.re * σ ≤ |σ| / 2 := by
    have h2 : |ν.re| * |σ| ≤ 1 / 2 * |σ| := mul_le_mul_of_nonneg_right hν (abs_nonneg σ)
    have h3 := le_abs_self (ν.re * σ)
    rw [abs_mul] at h3
    linarith
  have h2 := sq_div_four_le_cosh σ
  have h3 : |σ| / 2 - y * σ ^ 2 / 8 ≤ 1 / (2 * y) := by
    rw [le_div_iff₀ (by positivity)]
    have e : (y * |σ| - 2) ^ 2 = y ^ 2 * σ ^ 2 - 4 * y * |σ| + 4 := by
      rw [sub_sq, mul_pow, sq_abs]; ring
    nlinarith [sq_nonneg (y * |σ| - 2)]
  nlinarith

theorem continuous_besselK_integrand (ν : ℂ) :
    Continuous (fun p : ℝ × ℝ => Complex.exp (-((p.1 * Real.cosh p.2 : ℝ) : ℂ) + ν * p.2)) := by
  fun_prop

/-- The integrand of `K_ν(y)` is integrable for `|Re ν| ≤ 1/2`, `y > 0`. -/
theorem integrable_besselK_integrand {ν : ℂ} (hν : |ν.re| ≤ 1 / 2) {y : ℝ} (hy : 0 < y) :
    Integrable (fun σ : ℝ => Complex.exp (-((y * Real.cosh σ : ℝ) : ℂ) + ν * σ)) := by
  have hg := (integrable_exp_neg_mul_sq (b := y / 8) (by positivity)).const_mul
    (Real.exp (1 / (2 * y)))
  refine hg.mono' ?_ (Eventually.of_forall (norm_besselK_integrand_le hν hy))
  exact ((continuous_besselK_integrand ν).comp
    (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable

/-- `K_ν` is continuous on `(0, ∞)` for `|Re ν| ≤ 1/2`. -/
theorem continuousOn_besselK {ν : ℂ} (hν : |ν.re| ≤ 1 / 2) : ContinuousOn (besselK ν) (Ioi 0) := by
  intro y₀ hy₀
  have hy₀' : (0 : ℝ) < y₀ := hy₀
  apply ContinuousAt.continuousWithinAt
  unfold besselK
  apply ContinuousAt.mul continuousAt_const
  set b : ℝ := y₀ / 2 with hb
  have hb0 : 0 < b := by positivity
  apply continuousAt_of_dominated (bound := fun σ => Real.exp (1 / (2 * b)) *
    Real.exp (-(b / 8) * σ ^ 2))
  · exact Eventually.of_forall fun y => ((continuous_besselK_integrand ν).comp
      (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (show b < y₀ by linarith)] with y hy
    refine Eventually.of_forall fun σ => ?_
    have hy' : b < y := hy
    have hy0 : 0 < y := by linarith
    refine (norm_besselK_integrand_le hν hy0 σ).trans ?_
    apply mul_le_mul
    · apply Real.exp_le_exp.2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    · apply Real.exp_le_exp.2
      have : b / 8 * σ ^ 2 ≤ y / 8 * σ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg σ)
      linarith
    · exact (Real.exp_pos _).le
    · exact (Real.exp_pos _).le
  · exact (integrable_exp_neg_mul_sq (b := b / 8) (by positivity)).const_mul _
  · exact Eventually.of_forall fun σ => by
      have := (continuous_besselK_integrand ν).comp
        (Continuous.prodMk continuous_id (continuous_const (y := σ)))
      exact this.continuousAt


end Triples
