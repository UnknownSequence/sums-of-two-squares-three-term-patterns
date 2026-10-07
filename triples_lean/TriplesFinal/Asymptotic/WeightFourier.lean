import TriplesFinal.Prelim.Weight
import TriplesFinal.Analysis.DerivBounds
import TriplesFinal.Analysis.FourierDecay
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The weight `W` as a Fourier integral

For the proof of Lemma 7.3 the weight `W(2^((v-2)/2) k/√T(t))` has to be written as a
superposition of products of a function of `k` and a function of `t`. Put `Λ(u) = W(e^u)` and
`f_{u₀}(v) = Λ(u₀ + v) β(v)`, where `β` is a smooth bump with `β = 1` on `[0, 2]` and support
in `[-1, 3]`. Then `f_{u₀}` is smooth with compact support, so by Fourier inversion
`W(e^(u₀ + v)) = ∫ e^{2πiξv} 𝓕f_{u₀}(ξ) dξ` for `0 ≤ v ≤ 2` (`W_exp_eq_integral`), and
`|𝓕f_{u₀}(ξ)| ≤ A_n (1 + |ξ|)^(-n)` uniformly in `u₀` (`exists_fourier_bound_fW'`).

This replaces the Mellin inversion of the paper (which uses `W̃(w)` on `Re w = 1`): with
`u₀ = log(2^((v-2)/2) K/√x)` and `v = log(k/K) - ½ log(T(t)/x)`, the factor `e^{2πiξv}` splits
as `(k/K)^{2πiξ} (T(t)/x)^{-πiξ}`.

Paper: §7.3, proof of Lemma 7.3.
-/

namespace Triples

open scoped ContDiff FourierTransform Nat
open Complex MeasureTheory

namespace WeightFourier

/-- The bump `β(v) = s(v + 1) s(3 - v)`: `β = 1` on `[0, 2]`, `β = 0` outside `(-1, 3)`. -/
noncomputable def beta (v : ℝ) : ℝ :=
  Real.smoothTransition (v + 1) * Real.smoothTransition (3 - v)

theorem beta_eq_one {v : ℝ} (h0 : 0 ≤ v) (h2 : v ≤ 2) : beta v = 1 := by
  unfold beta
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem beta_support {v : ℝ} (h : beta v ≠ 0) : -1 ≤ v ∧ v ≤ 3 := by
  unfold beta at h
  constructor
  · by_contra h'
    exact h (by rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul])
  · by_contra h'
    exact h (by rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 - v ≤ 0), mul_zero])

theorem contDiff_beta : ContDiff ℝ ∞ beta := by
  unfold beta
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

variable (W : HyperbolaWeight)

/-- `Λ(u) = W(e^u)`, as a complex function. -/
noncomputable def lam (u : ℝ) : ℂ := (W.W (Real.exp u) : ℂ)

theorem contDiff_lam : ContDiff ℝ ∞ (lam W) := by
  have h : ContDiff ℝ ∞ (fun u => W.W (Real.exp u)) :=
    W.smooth.comp_contDiff Real.contDiff_exp (fun u => Real.exp_pos u)
  exact ofRealCLM.contDiff.comp h

theorem lam_eq_one {u : ℝ} (hu : u < -Real.log 2) : lam W u = 1 := by
  unfold lam
  rw [W.eq_one _ (Real.exp_pos u)]
  · simp
  · have : Real.exp u ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 hu.le
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at this
    linarith

theorem lam_eq_zero {u : ℝ} (hu : Real.log 2 < u) : lam W u = 0 := by
  unfold lam
  rw [W.eq_zero]
  · simp
  · have : Real.exp (Real.log 2) ≤ Real.exp u := Real.exp_le_exp.2 hu.le
    rw [Real.exp_log (by norm_num)] at this
    exact this

/-- The derivatives of `Λ` are bounded. -/
theorem exists_bound_lam (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ u, ‖iteratedDeriv j (lam W) u‖ ≤ B := by
  have hcont : Continuous (iteratedDeriv j (lam W)) :=
    (contDiff_lam W).continuous_iteratedDeriv j (by exact_mod_cast le_top)
  obtain ⟨B₁, hB₁⟩ := (isCompact_Icc (a := -Real.log 2) (b := Real.log 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max B₁ 1, le_trans zero_le_one (le_max_right _ _), fun u => ?_⟩
  by_cases hu : u ∈ Set.Icc (-Real.log 2) (Real.log 2)
  · exact (hB₁ u hu).trans (le_max_left _ _)
  · simp only [Set.mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · have heq : Set.EqOn (lam W) (fun _ => (1 : ℂ)) (Set.Iio (-Real.log 2)) :=
        fun y hy => lam_eq_one W hy
      rw [heq.iteratedDeriv_of_isOpen isOpen_Iio j hu, iteratedDeriv_const]
      split_ifs <;> simp
    · have heq : Set.EqOn (lam W) (fun _ => (0 : ℂ)) (Set.Ioi (Real.log 2)) :=
        fun y hy => lam_eq_zero W hy
      rw [heq.iteratedDeriv_of_isOpen isOpen_Ioi j hu, iteratedDeriv_const]
      split_ifs <;> simp

/-- `f_{u₀}(v) = Λ(u₀ + v) β(v)`. -/
noncomputable def fW (u₀ : ℝ) (v : ℝ) : ℂ := lam W (u₀ + v) * (beta v : ℂ)

theorem contDiff_fW (u₀ : ℝ) : ContDiff ℝ ∞ (fW W u₀) :=
  ((contDiff_lam W).comp (contDiff_const.add contDiff_id)).mul
    (ofRealCLM.contDiff.comp contDiff_beta)

theorem fW_support (u₀ : ℝ) {v : ℝ} (h : fW W u₀ v ≠ 0) : -1 ≤ v ∧ v ≤ 3 := by
  apply beta_support
  intro h'
  apply h
  simp [fW, h']

theorem hasCompactSupport_fW (u₀ : ℝ) : HasCompactSupport (fW W u₀) :=
  hasCompactSupport_of_support (fun _ h => fW_support W u₀ h)

/-- The derivatives of `f_{u₀}` are bounded uniformly in `u₀`. -/
theorem exists_bound_fW (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u₀ v, ‖iteratedDeriv n (fW W u₀) v‖ ≤ M := by
  choose B hB0 hB using exists_bound_lam W
  have hbeta : ContDiff ℝ ∞ (fun v : ℝ => (beta v : ℂ)) := ofRealCLM.contDiff.comp contDiff_beta
  obtain ⟨Bβ, hBβ0, hBβ⟩ := exists_bound_iteratedDeriv_le hbeta
    (hasCompactSupport_of_support (fun _ (h : (beta _ : ℂ) ≠ 0) =>
      beta_support (by exact_mod_cast h))) n
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * Bβ,
    Finset.sum_nonneg (fun i _ => by have := hB0 i; positivity), ?_⟩
  intro u₀ v
  have hlam : ContDiff ℝ ∞ (fun v : ℝ => lam W (u₀ + v)) :=
    (contDiff_lam W).comp (contDiff_const.add contDiff_id)
  have hL := norm_iteratedDeriv_mul_le_of_isOpen isOpen_univ hlam.contDiffOn hbeta.contDiffOn
    (Set.mem_univ v) n
  refine (le_of_eq_of_le rfl hL).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 : ‖iteratedDeriv i (fun v => lam W (u₀ + v)) v‖ ≤ B i := by
    rw [iteratedDeriv_comp_const_add i (lam W) u₀]
    exact hB i _
  have h2 := hBβ (n - i) (by omega) v
  have := mul_le_mul h1 h2 (norm_nonneg _) (hB0 i)
  calc (n.choose i : ℝ) * ‖iteratedDeriv i (fun v => lam W (u₀ + v)) v‖ *
        ‖iteratedDeriv (n - i) (fun v => (beta v : ℂ)) v‖
      = (n.choose i : ℝ) * (‖iteratedDeriv i (fun v => lam W (u₀ + v)) v‖ *
        ‖iteratedDeriv (n - i) (fun v => (beta v : ℂ)) v‖) := by ring
    _ ≤ (n.choose i : ℝ) * (B i * Bβ) := by gcongr
    _ = (n.choose i : ℝ) * B i * Bβ := by ring

theorem iteratedDeriv_fW_support (u₀ : ℝ) (n : ℕ) {v : ℝ}
    (h : iteratedDeriv n (fW W u₀) v ≠ 0) : -1 ≤ v ∧ v ≤ 3 := by
  by_contra hv
  apply h
  apply iteratedDeriv_eq_zero_of_notMem_tsupport
  intro hv'
  exact hv (tsupport_subset_Icc_of_support (fun v h => fW_support W u₀ h) hv')

/-- **Uniform decay** of `𝓕 f_{u₀}`: `(1 + |ξ|)^n |𝓕 f_{u₀}(ξ)| ≤ A_n`. -/
theorem exists_fourier_bound_fW (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u₀ ξ, (1 + |ξ|) ^ n * ‖𝓕 (fW W u₀) ξ‖ ≤ A := by
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_bound_fW W 0
  obtain ⟨M, hM0, hM⟩ := exists_bound_fW W n
  refine ⟨2 ^ n * (M₀ * 4 + M * 4), by positivity, fun u₀ ξ => ?_⟩
  refine (one_add_pow_mul_norm_fourier_le (contDiff_fW W u₀) (hasCompactSupport_fW W u₀) n ξ).trans ?_
  have h1 : ∫ v, ‖fW W u₀ v‖ ≤ M₀ * (3 - (-1)) :=
    integral_norm_le_of_support (by norm_num) (fun v h => fW_support W u₀ h)
      (fun v => by simpa using hM₀ u₀ v)
  have h2 : ∫ v, ‖iteratedDeriv n (fW W u₀) v‖ ≤ M * (3 - (-1)) :=
    integral_norm_le_of_support (by norm_num) (fun v h => iteratedDeriv_fW_support W u₀ n h)
      (fun v => hM u₀ v)
  norm_num at h1 h2
  gcongr

/-- The bound in the form `|𝓕 f_{u₀}(ξ)| ≤ A_n (1 + |ξ|)^(-n)`. -/
theorem exists_fourier_bound_fW' (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u₀ ξ, ‖𝓕 (fW W u₀) ξ‖ ≤ A * (1 + |ξ|) ^ (-(n : ℝ)) := by
  obtain ⟨A, hA0, hA⟩ := exists_fourier_bound_fW W n
  refine ⟨A, hA0, fun u₀ ξ => ?_⟩
  have hpos : 0 < (1 + |ξ|) ^ n := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos,
    mul_comm]
  exact hA u₀ ξ

/-- **Fourier representation of the weight**: for `0 ≤ v ≤ 2`,
`W(e^(u₀ + v)) = ∫ e^{2πiξv} 𝓕 f_{u₀}(ξ) dξ`. -/
theorem W_exp_eq_integral (u₀ : ℝ) {v : ℝ} (hv0 : 0 ≤ v) (hv2 : v ≤ 2) :
    ∫ ξ : ℝ, Complex.exp (((2 * Real.pi * ξ * v : ℝ) : ℂ) * I) * 𝓕 (fW W u₀) ξ =
      (W.W (Real.exp (u₀ + v)) : ℂ) := by
  rw [fourier_inversion_of_compactSupport (contDiff_fW W u₀) (hasCompactSupport_fW W u₀)]
  simp [fW, lam, beta_eq_one hv0 hv2]

end WeightFourier

end Triples
