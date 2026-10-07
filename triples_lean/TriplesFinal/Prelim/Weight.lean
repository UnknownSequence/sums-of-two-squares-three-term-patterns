import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The weight `W` of the smoothed hyperbola identity

A weight `W : (0, ∞) → [0, 1]`, smooth, with `W(t) = 1` for `t ≤ 1/2`, `W(t) = 0` for `t ≥ 2`
and `W(t) + W(1/t) = 1` (equation (5.1)). It is constructed as `W(t) = λ(log t)` with
`λ(u) = ½(λ₀(u) + 1 - λ₀(-u))`, where `λ₀` is a smooth non-increasing function equal to `1` on
`(-∞, -log 2]` and to `0` on `[log 2, ∞)`.

Paper: §5.1, equation (5.1).
-/

namespace Triples

open Real
open scoped ContDiff

/-- A weight `W` with the properties (5.1) (on `t > 0`). -/
structure HyperbolaWeight where
  /-- the weight -/
  W : ℝ → ℝ
  smooth : ContDiffOn ℝ ∞ W (Set.Ioi 0)
  nonneg : ∀ t, 0 < t → 0 ≤ W t
  le_one : ∀ t, 0 < t → W t ≤ 1
  eq_one : ∀ t, 0 < t → t ≤ 1 / 2 → W t = 1
  eq_zero : ∀ t, 2 ≤ t → W t = 0
  symm : ∀ t, 0 < t → W t + W t⁻¹ = 1

/-- `λ₀(u) = 1 - s((u + log 2)/(2 log 2))`, with `s` the smooth transition function. -/
noncomputable def lam0 (u : ℝ) : ℝ := 1 - smoothTransition ((u + log 2) / (2 * log 2))

/-- `λ(u) = ½(λ₀(u) + 1 - λ₀(-u))`. -/
noncomputable def lam (u : ℝ) : ℝ := (lam0 u + 1 - lam0 (-u)) / 2

theorem log_two_pos' : 0 < log 2 := log_pos (by norm_num)

theorem lam0_eq_one {u : ℝ} (hu : u ≤ -log 2) : lam0 u = 1 := by
  unfold lam0
  rw [smoothTransition.zero_of_nonpos, sub_zero]
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by have := log_two_pos'; positivity)

theorem lam0_eq_zero {u : ℝ} (hu : log 2 ≤ u) : lam0 u = 0 := by
  unfold lam0
  rw [smoothTransition.one_of_one_le, sub_self]
  have := log_two_pos'
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem lam0_mem (u : ℝ) : 0 ≤ lam0 u ∧ lam0 u ≤ 1 := by
  unfold lam0
  constructor
  · linarith [smoothTransition.le_one ((u + log 2) / (2 * log 2))]
  · linarith [smoothTransition.nonneg ((u + log 2) / (2 * log 2))]

theorem lam_add_lam_neg (u : ℝ) : lam u + lam (-u) = 1 := by
  unfold lam; rw [neg_neg]; ring

theorem contDiff_lam0 : ContDiff ℝ ∞ lam0 := by
  unfold lam0
  apply contDiff_const.sub
  apply smoothTransition.contDiff.comp
  exact (contDiff_id.add contDiff_const).div_const _

theorem contDiff_lam : ContDiff ℝ ∞ lam := by
  unfold lam
  apply ContDiff.div_const
  exact (contDiff_lam0.add contDiff_const).sub (contDiff_lam0.comp contDiff_neg)

/-- **The weight of (5.1)** exists. -/
theorem exists_hyperbolaWeight : Nonempty HyperbolaWeight := by
  have hl2 := log_two_pos'
  refine ⟨⟨fun t => lam (log t), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact contDiff_lam.comp_contDiffOn (contDiffOn_log.mono (fun t ht => ne_of_gt ht))
  · intro t _
    have h1 := lam0_mem (log t)
    have h2 := lam0_mem (-log t)
    show 0 ≤ (lam0 (log t) + 1 - lam0 (-log t)) / 2
    linarith
  · intro t _
    have h1 := lam0_mem (log t)
    have h2 := lam0_mem (-log t)
    show (lam0 (log t) + 1 - lam0 (-log t)) / 2 ≤ 1
    linarith
  · intro t ht ht2
    have hlog : log t ≤ -log 2 := by
      have : log t ≤ log (1 / 2) := log_le_log ht ht2
      rwa [one_div, log_inv] at this
    show (lam0 (log t) + 1 - lam0 (-log t)) / 2 = 1
    rw [lam0_eq_one hlog, lam0_eq_zero (by linarith)]
    ring
  · intro t ht
    have hlog : log 2 ≤ log t := log_le_log (by norm_num) ht
    show (lam0 (log t) + 1 - lam0 (-log t)) / 2 = 0
    rw [lam0_eq_zero hlog, lam0_eq_one (by linarith)]
    ring
  · intro t _
    show lam (log t) + lam (log t⁻¹) = 1
    rw [log_inv]
    exact lam_add_lam_neg _

end Triples
