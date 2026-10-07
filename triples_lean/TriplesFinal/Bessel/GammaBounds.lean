import TriplesFinal.Bessel.MellinBarnes
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Gamma function facts for the proof of Theorem 6.1

* `|Γ(it)|² = π/(t sinh(πt))` for real `t ≠ 0`, hence `|Γ(±it)|² ≤ 7/cosh(πt)` for `|t| ≥ 1`;
* `(t, ξ) ↦ G_t(-3/2 + iξ)` is continuous;
* `ξ ↦ G_t(-3/2 + iξ)` is integrable.

Paper: §12.3 (`|Γ(it)|² = π/(|t| sinh(π|t|)) ≤ 7/cosh(πt)` for `|t| ≥ 1`) and Lemma 11.2.
-/

namespace Triples

open Complex MeasureTheory

/-- `|Γ(it)|² = π/(t sinh(πt))` for real `t ≠ 0`. -/
theorem norm_Gamma_I_mul_sq {τ : ℝ} (hτ : τ ≠ 0) :
    ‖Complex.Gamma (I * τ)‖ ^ 2 = Real.pi / (τ * Real.sinh (Real.pi * τ)) := by
  have hz : I * (τ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hτ)
  have hconj : (starRingEnd ℂ) (I * τ) = -(I * τ) := by
    rw [map_mul, conj_I, Complex.conj_ofReal]; ring
  have h1 : (‖Complex.Gamma (I * τ)‖ ^ 2 : ℂ) =
      Complex.Gamma (I * τ) * Complex.Gamma (-(I * τ)) := by
    rw [← hconj, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have h2 : Complex.Gamma (1 - I * τ) = -(I * τ) * Complex.Gamma (-(I * τ)) := by
    rw [show (1 : ℂ) - I * τ = -(I * τ) + 1 by ring]
    exact Complex.Gamma_add_one _ (neg_ne_zero.2 hz)
  have h3 := Complex.Gamma_mul_Gamma_one_sub (I * τ)
  rw [h2, show (Real.pi : ℂ) * (I * τ) = ((Real.pi * τ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.sin_mul_I] at h3
  have hs : Real.sinh (Real.pi * τ) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_pos.ne' hτ
  have hs' : ((Real.sinh (Real.pi * τ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have key : Complex.Gamma (I * τ) * Complex.Gamma (-(I * τ)) =
      ((Real.pi / (τ * Real.sinh (Real.pi * τ)) : ℝ) : ℂ) := by
    have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
    rw [← Complex.ofReal_sinh] at h3
    have e : Complex.Gamma (I * τ) * Complex.Gamma (-(I * τ)) * (-(I * τ)) =
        Real.pi / (Real.sinh (Real.pi * τ) * I) := by
      rw [← h3]; ring
    have hnz : -(I * (τ : ℂ)) ≠ 0 := neg_ne_zero.2 hz
    rw [← eq_div_iff hnz] at e
    rw [e]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have h4 : ((‖Complex.Gamma (I * τ)‖ ^ 2 : ℝ) : ℂ) =
      ((Real.pi / (τ * Real.sinh (Real.pi * τ)) : ℝ) : ℂ) := by
    push_cast; rw [h1, key]; push_cast; ring
  exact_mod_cast h4

/-- `sinh x ≥ cosh x / 2` for `x ≥ 1`. -/
theorem cosh_le_two_mul_sinh {x : ℝ} (hx : 1 ≤ x) : Real.cosh x ≤ 2 * Real.sinh x := by
  have h1 : Real.cosh x - Real.sinh x = Real.exp (-x) := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  have h2 : Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    linarith
  have h4 : 1 ≤ Real.cosh x := Real.one_le_cosh x
  linarith

/-- `|Γ(it)|² ≤ 7/cosh(πt)` for `|t| ≥ 1`. -/
theorem norm_Gamma_I_mul_sq_le {τ : ℝ} (hτ : 1 ≤ |τ|) :
    ‖Complex.Gamma (I * τ)‖ ^ 2 ≤ 7 / Real.cosh (Real.pi * τ) := by
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h, abs_zero] at hτ; linarith
  rw [norm_Gamma_I_mul_sq hτ0]
  have e : τ * Real.sinh (Real.pi * τ) = |τ| * Real.sinh (Real.pi * |τ|) := by
    rcases le_or_gt 0 τ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, mul_neg, Real.sinh_neg]; ring
  rw [e, ← Real.cosh_abs (Real.pi * τ), abs_mul, abs_of_pos Real.pi_pos]
  have hpi := Real.pi_pos
  have hx : 1 ≤ Real.pi * |τ| := by
    have : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  have hcs := cosh_le_two_mul_sinh hx
  have hc0 : 0 < Real.cosh (Real.pi * |τ|) := Real.cosh_pos _
  have hs0 : 0 < Real.sinh (Real.pi * |τ|) := by linarith
  rw [div_le_div_iff₀ (by positivity) hc0]
  have h7 : Real.pi * 2 ≤ 7 := by linarith [Real.pi_lt_d2]
  nlinarith [mul_le_mul_of_nonneg_left hcs hpi.le, mul_le_mul_of_nonneg_left hτ hs0.le]

theorem norm_Gamma_neg_I_mul_sq_le {τ : ℝ} (hτ : 1 ≤ |τ|) :
    ‖Complex.Gamma (-(I * τ))‖ ^ 2 ≤ 7 / Real.cosh (Real.pi * τ) := by
  have h : -(I * (τ : ℂ)) = I * ((-τ : ℝ) : ℂ) := by push_cast; ring
  rw [h]
  have := norm_Gamma_I_mul_sq_le (τ := -τ) (by rwa [abs_neg])
  rwa [mul_neg, Real.cosh_neg] at this

/-- `Γ` is continuous at points with real part `-3/4`. -/
theorem continuousAt_Gamma_of_re {s : ℂ} (hs : s.re = -3 / 4) : ContinuousAt Complex.Gamma s := by
  apply (Complex.differentiableAt_Gamma s _).continuousAt
  intro m hm
  have := congrArg Complex.re hm
  rw [hs] at this
  simp at this
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  have : (m : ℝ) = 3 / 4 := by linarith
  have hm1 : m = 0 ∨ 1 ≤ m := by omega
  rcases hm1 with h | h
  · rw [h] at this; norm_num at this
  · have : (1 : ℝ) ≤ m := by exact_mod_cast h
    linarith

/-- `(t, ξ) ↦ G_t(-3/2 + iξ)` is continuous. -/
theorem continuous_Gt_line : Continuous (fun p : ℝ × ℝ => Gt p.1 (-3 / 2 + I * p.2)) := by
  unfold Gt
  apply Continuous.mul
  · apply Continuous.mul
    · exact Continuous.const_cpow (by fun_prop) (Or.inl two_ne_zero)
    · rw [continuous_iff_continuousAt]
      intro p
      apply ContinuousAt.comp (g := Complex.Gamma)
      · apply continuousAt_Gamma_of_re
        simp; ring
      · fun_prop
  · rw [continuous_iff_continuousAt]
    intro p
    apply ContinuousAt.comp (g := Complex.Gamma)
    · apply continuousAt_Gamma_of_re
      simp; ring
    · fun_prop

/-- `ξ ↦ (1 + |ξ + t|)^(-5/4)` is integrable. -/
theorem integrable_one_add_abs_shift (t : ℝ) :
    Integrable (fun ξ : ℝ => (1 + |ξ + t|) ^ (-(5 : ℝ) / 4)) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 5 / 4) (by simp; norm_num)
  have h2 := h.comp_add_right t
  refine h2.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Real.norm_eq_abs]
  rw [show (-(5 : ℝ) / 4) = -(5 / 4) by ring]

/-- `ξ ↦ G_t(-3/2 + iξ)` is integrable, with `∫ |G_t| ≤ C e^(-π|t|/2) I`, `I = ∫(1+|ξ|)^(-5/4)`. -/
theorem integrable_Gt (hB : BesselAssumptions) (t : ℝ) :
    Integrable (fun ξ : ℝ => Gt t (-3 / 2 + I * ξ)) := by
  obtain ⟨C, hC⟩ := Gt_bound hB
  have hm : AEStronglyMeasurable (fun ξ : ℝ => Gt t (-3 / 2 + I * ξ)) volume :=
    (continuous_Gt_line.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  have hdom : Integrable (fun ξ : ℝ => |C| * Real.exp (-Real.pi * |t| / 2) *
      (1 + |ξ + t|) ^ (-(5 : ℝ) / 4)) :=
    (integrable_one_add_abs_shift t).const_mul _
  refine hdom.mono' hm (Filter.Eventually.of_forall fun ξ => ?_)
  have h1 := hC t ξ
  have h2 : (1 + |ξ - t|) ^ (-(5 : ℝ) / 4) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (ξ - t)]) (by norm_num)
  have h3 : 0 ≤ (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) := by positivity
  have h4 : 0 ≤ Real.exp (-Real.pi * |t| / 2) := (Real.exp_pos _).le
  calc ‖Gt t (-3 / 2 + I * ξ)‖ ≤ C * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4) := h1
    _ ≤ |C| * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) * 1 := by
        have hC0 : C * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) ≤
            |C| * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) := by
          gcongr; exact le_abs_self C
        have hC1 : 0 ≤ |C| * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) := by
          positivity
        rcases le_or_gt 0 (C * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4))
          with h | h
        · calc _ ≤ C * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) * 1 :=
                mul_le_mul_of_nonneg_left h2 h
            _ ≤ _ := by gcongr
        · have : C * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
              (1 + |ξ - t|) ^ (-(5 : ℝ) / 4) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg h.le (by positivity)
          linarith
    _ = |C| * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) := by ring

end Triples
