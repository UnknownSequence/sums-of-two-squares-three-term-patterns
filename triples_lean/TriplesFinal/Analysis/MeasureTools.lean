import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Measure-theoretic tools for the proof of Theorem 6.1

* the Cauchy–Schwarz inequality on a set, `∫_S f g ≤ (∫_S f²)^(1/2) (∫_S g²)^(1/2)`;
* integrals over countable disjoint unions of nonnegative functions with summable bounds;
* the Cauchy–Schwarz inequality for interval integrals, `‖∫_a^b f‖² ≤ (b - a) ∫_a^b ‖f‖²`.
-/

namespace Triples

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Cauchy–Schwarz on a set.** -/
theorem setIntegral_mul_le_sqrt {S : Set α} {f g : α → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hg0 : ∀ x, 0 ≤ g x) (hfm : AEStronglyMeasurable f (μ.restrict S))
    (hgm : AEStronglyMeasurable g (μ.restrict S)) (hf : IntegrableOn (fun x => f x ^ 2) S μ)
    (hg : IntegrableOn (fun x => g x ^ 2) S μ) :
    ∫ x in S, f x * g x ∂μ ≤
      Real.sqrt (∫ x in S, f x ^ 2 ∂μ) * Real.sqrt (∫ x in S, g x ^ 2 ∂μ) := by
  have hf2 : MemLp f (ENNReal.ofReal 2) (μ.restrict S) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hfm).2 hf
  have hg2 : MemLp g (ENNReal.ofReal 2) (μ.restrict S) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hgm).2 hg
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0) hf2 hg2
  simp only [Real.rpow_two] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert h using 3

/-- **Cauchy–Schwarz on a set**, with bounds: if `∫_S f² ≤ A` and `∫_S g² ≤ B` then
`∫_S f g ≤ √A √B`. -/
theorem setIntegral_mul_le_of_sq {S : Set α} {f g : α → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hg0 : ∀ x, 0 ≤ g x) (hfm : AEStronglyMeasurable f (μ.restrict S))
    (hgm : AEStronglyMeasurable g (μ.restrict S)) (hf : IntegrableOn (fun x => f x ^ 2) S μ)
    (hg : IntegrableOn (fun x => g x ^ 2) S μ) {A B : ℝ}
    (hA : ∫ x in S, f x ^ 2 ∂μ ≤ A) (hB : ∫ x in S, g x ^ 2 ∂μ ≤ B) :
    ∫ x in S, f x * g x ∂μ ≤ Real.sqrt A * Real.sqrt B := by
  refine (setIntegral_mul_le_sqrt hf0 hg0 hfm hgm hf hg).trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-- The product of two functions whose squares are integrable is integrable. -/
theorem IntegrableOn.mul_of_sq {S : Set α} {f g : α → ℝ}
    (hfm : AEStronglyMeasurable f (μ.restrict S)) (hgm : AEStronglyMeasurable g (μ.restrict S))
    (hf : IntegrableOn (fun x => f x ^ 2) S μ) (hg : IntegrableOn (fun x => g x ^ 2) S μ) :
    IntegrableOn (fun x => f x * g x) S μ := by
  have hfg : Integrable (fun x => (f x ^ 2 + g x ^ 2) / 2) (μ.restrict S) :=
    (hf.add hg).div_const 2
  refine hfg.mono' (hfm.mul hgm) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]

/-- **Countable unions**: if `f ≥ 0` is integrable on each of the disjoint measurable sets
`s n` with `∫_{s n} f ≤ a n` and `∑ a n < ∞`, then `f` is integrable on `⋃ s n` and
`∫_{⋃ s n} f ≤ ∑ a n`. -/
theorem setIntegral_iUnion_le {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Function.onFun Disjoint s)) {f : α → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfi : ∀ n, IntegrableOn f (s n) μ) {a : ℕ → ℝ} (ha : ∀ n, ∫ x in s n, f x ∂μ ≤ a n)
    (hsa : Summable a) :
    IntegrableOn f (⋃ n, s n) μ ∧ ∫ x in ⋃ n, s n, f x ∂μ ≤ ∑' n, a n := by
  have hnorm : ∀ n, ∫ x in s n, ‖f x‖ ∂μ = ∫ x in s n, f x ∂μ := fun n =>
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.norm_of_nonneg (hf0 x))
  have hsum : Summable fun n => ∫ x in s n, ‖f x‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) hsa
    rw [hnorm]; exact ha n
  have hint := integrableOn_iUnion_of_summable_integral_norm hfi hsum
  refine ⟨hint, ?_⟩
  rw [integral_iUnion hs hd hint]
  have hsum' : Summable fun n => ∫ x in s n, f x ∂μ := by
    simpa only [hnorm] using hsum
  exact hsum'.tsum_le_tsum ha hsa

/-- **Cauchy–Schwarz for interval integrals**: `‖∫_a^b f‖² ≤ (b - a) ∫_a^b ‖f‖²`. -/
theorem norm_intervalIntegral_sq_le {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume a b) :
    ‖∫ x in a..b, f x‖ ^ 2 ≤ (b - a) * ∫ x in a..b, ‖f x‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have h1 : ‖∫ x in Set.Ioc a b, f x‖ ≤ ∫ x in Set.Ioc a b, ‖f x‖ := norm_integral_le_integral_norm _
  have h2 : ∫ x in Set.Ioc a b, ‖f x‖ = ∫ x in Set.Ioc a b, (1 : ℝ) * ‖f x‖ := by simp
  have hm : AEStronglyMeasurable (fun x => ‖f x‖) (volume.restrict (Set.Ioc a b)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf).1.norm
  have hcs := setIntegral_mul_le_sqrt (μ := volume) (S := Set.Ioc a b) (f := fun _ => (1 : ℝ))
    (g := fun x => ‖f x‖) (fun _ => zero_le_one) (fun x => norm_nonneg _)
    aestronglyMeasurable_const hm
    (by simp only [one_pow]; exact integrableOn_const (by simp))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf2)
  rw [← h2] at hcs
  simp only [one_pow, setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc_of_le hab] at hcs
  have h0 : 0 ≤ ∫ x in Set.Ioc a b, ‖f x‖ := integral_nonneg fun x => norm_nonneg _
  have h3 : ‖∫ x in Set.Ioc a b, f x‖ ^ 2 ≤ (∫ x in Set.Ioc a b, ‖f x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 : (∫ x in Set.Ioc a b, ‖f x‖) ^ 2 ≤
      (Real.sqrt (b - a) * Real.sqrt (∫ x in Set.Ioc a b, ‖f x‖ ^ 2)) ^ 2 :=
    pow_le_pow_left₀ h0 hcs 2
  rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (integral_nonneg fun x => by positivity)]
    at h4
  linarith

end Triples
