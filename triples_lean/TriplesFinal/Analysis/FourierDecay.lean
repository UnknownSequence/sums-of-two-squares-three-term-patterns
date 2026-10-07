import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Fourier transforms of smooth compactly supported functions

For `f : ℝ → ℂ` smooth with compact support:

* `(2π|ξ|)^n |𝓕f(ξ)| ≤ ∫ |f^(n)|` and `(1 + |ξ|)^n |𝓕f(ξ)| ≤ 2^n (∫|f| + ∫|f^(n)|)`;
* `𝓕f` is integrable, and the Fourier inversion formula `f(v) = ∫ e^{2πiξv} 𝓕f(ξ) dξ` holds.

Here `𝓕f(ξ) = ∫ f(v) e^{-2πivξ} dv` is Mathlib's Fourier transform. These are used to separate
the variables in the proof of Lemma 7.3.
-/

namespace Triples

open scoped ContDiff FourierTransform
open Complex MeasureTheory

variable {f : ℝ → ℂ}

theorem integrable_iteratedDeriv_of_compactSupport (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (n : ℕ) : Integrable (iteratedDeriv n f) := by
  have hcont : Continuous (iteratedDeriv n f) :=
    hf.continuous_iteratedDeriv n (by exact_mod_cast le_top)
  apply hcont.integrable_of_hasCompactSupport
  apply hc.mono'
  intro u hu
  by_contra hu'
  have h : f =ᶠ[nhds u] fun _ => 0 := (notMem_tsupport_iff_eventuallyEq).1 hu'
  apply hu
  rw [Filter.EventuallyEq.iteratedDeriv_eq n h]
  simp

theorem continuous_fourierTransform (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) hf

/-- `(2π|ξ|)^n |𝓕f(ξ)| ≤ ∫ |f^(n)|`. -/
theorem pow_mul_norm_fourier_le (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (n : ℕ)
    (ξ : ℝ) : (2 * Real.pi * |ξ|) ^ n * ‖𝓕 f ξ‖ ≤ ∫ v, ‖iteratedDeriv n f v‖ := by
  have h := Real.fourier_iteratedDeriv (N := ⊤) (n := n) hf
    (fun k _ => integrable_iteratedDeriv_of_compactSupport hf hc k) (by exact_mod_cast le_top)
  have h2 := congrFun h ξ
  have h3 : ‖𝓕 (iteratedDeriv n f) ξ‖ ≤ ∫ v, ‖iteratedDeriv n f v‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [h2, norm_smul, norm_pow] at h3
  convert h3 using 2
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_ofNat,
    abs_of_pos Real.pi_pos]

/-- `(1 + |ξ|)^n |𝓕f(ξ)| ≤ 2^n (∫ |f| + ∫ |f^(n)|)`. -/
theorem one_add_pow_mul_norm_fourier_le (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (n : ℕ) (ξ : ℝ) :
    (1 + |ξ|) ^ n * ‖𝓕 f ξ‖ ≤ 2 ^ n * ((∫ v, ‖f v‖) + ∫ v, ‖iteratedDeriv n f v‖) := by
  have hI0 : 0 ≤ ∫ v, ‖f v‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hIn : 0 ≤ ∫ v, ‖iteratedDeriv n f v‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hF0 : ‖𝓕 f ξ‖ ≤ ∫ v, ‖f v‖ := VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rcases le_or_gt |ξ| 1 with hξ | hξ
  · calc (1 + |ξ|) ^ n * ‖𝓕 f ξ‖ ≤ 2 ^ n * ∫ v, ‖f v‖ :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) n) hF0 (norm_nonneg _)
            (by positivity)
      _ ≤ _ := by gcongr; linarith
  · have h := pow_mul_norm_fourier_le hf hc n ξ
    have h1 : (1 + |ξ|) ^ n ≤ 2 ^ n * (2 * Real.pi * |ξ|) ^ n := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [Real.two_le_pi]
    calc (1 + |ξ|) ^ n * ‖𝓕 f ξ‖ ≤ 2 ^ n * (2 * Real.pi * |ξ|) ^ n * ‖𝓕 f ξ‖ := by
          gcongr
      _ = 2 ^ n * ((2 * Real.pi * |ξ|) ^ n * ‖𝓕 f ξ‖) := by ring
      _ ≤ 2 ^ n * ∫ v, ‖iteratedDeriv n f v‖ := by gcongr
      _ ≤ _ := by gcongr; linarith

theorem integrable_fourier_of_compactSupport (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (𝓕 f) := by
  set A : ℝ := 2 ^ 2 * ((∫ v, ‖f v‖) + ∫ v, ‖iteratedDeriv 2 f v‖)
  have hint : Integrable (fun ξ : ℝ => A * (1 + ‖ξ‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (by simp)).const_mul A
  apply hint.mono' (continuous_fourierTransform
    (hf.continuous.integrable_of_hasCompactSupport hc)).aestronglyMeasurable
  refine Filter.Eventually.of_forall (fun ξ => ?_)
  have h := one_add_pow_mul_norm_fourier_le hf hc 2 ξ
  have hpos : 0 < (1 + ‖ξ‖) ^ (2 : ℕ) := by positivity
  rw [Real.rpow_neg (by positivity), Real.norm_eq_abs, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rw [Real.norm_eq_abs] at *
  have : (1 + |ξ|) ^ (2 : ℝ) = (1 + |ξ|) ^ (2 : ℕ) := by norm_cast
  rw [this]
  linarith

/-- **Fourier inversion** for smooth compactly supported functions:
`f(v) = ∫ e^{2πiξv} 𝓕f(ξ) dξ`. -/
theorem fourier_inversion_of_compactSupport (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (v : ℝ) :
    ∫ ξ : ℝ, Complex.exp (((2 * Real.pi * ξ * v : ℝ) : ℂ) * I) * 𝓕 f ξ = f v := by
  have h := hf.continuous.fourierInv_fourier_eq (hf.continuous.integrable_of_hasCompactSupport hc)
    (integrable_fourier_of_compactSupport hf hc)
  have h2 := congrFun h v
  rw [Real.fourierInv_eq'] at h2
  rw [← h2]
  congr 1
  ext ξ
  simp only [smul_eq_mul]
  congr 3
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- `∫ |g| ≤ M (b - a)` for `g` supported in `[a, b]` with `|g| ≤ M`. -/
theorem integral_norm_le_of_support {g : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b)
    (hsupp : ∀ v, g v ≠ 0 → a ≤ v ∧ v ≤ b) (hM : ∀ v, ‖g v‖ ≤ M) :
    ∫ v, ‖g v‖ ≤ M * (b - a) := by
  have h1 : ∫ v in Set.Icc a b, ‖g v‖ = ∫ v, ‖g v‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    by_contra h
    exact hv (hsupp v (fun h' => h (by rw [h', norm_zero])))
  rw [← h1]
  have h2 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc a b)
    (f := fun v => ‖g v‖) (C := M) (by simp) (fun v _ => by rw [norm_norm]; exact hM v)
  rw [Real.volume_real_Icc_of_le hab] at h2
  exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at h2)

end Triples
