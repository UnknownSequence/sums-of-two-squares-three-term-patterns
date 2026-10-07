import TriplesFinal.Asymptotic.Setup

/-!
# Lemma 7.2: the integral of the cutoff along `T(t) = At² + B`

For the cutoff `F` (supported in `[1/2, 1]`, smooth, `0 ≤ F ≤ 1`):

* `c_F = ∫_0^1 F(t) t^(-1/2) dt = ∫_{-1}^{1} F(s²) ds` (`cF_eq_J_zero`, substituting `t = s²`);
* with `J(δ) = ∫_{-1}^{1} F(s² + δ) ds`: `0 ≤ J(δ) ≤ 2` and `|J(δ) - c_F| ≤ 2Lδ` for `δ ≥ 0`,
  `L` a Lipschitz constant of `F`;
* `∫_ℝ F((At² + B)/x) dt = √(x/A) J(B/x)` (`integral_quadratic`, substituting `t = √(x/A) s`).

This replaces the substitution `T = T(t)` in the paper's proof of Lemma 7.2.

Paper: §7.2, proof of Lemma 7.2.
-/

namespace Triples

open MeasureTheory intervalIntegral

namespace Cutoff

variable (F : Cutoff)

theorem F_eq_zero_of_lt {t : ℝ} (ht : t < 1 / 2) : F.F t = 0 := by
  by_contra h; have := (F.support t h).1; linarith

theorem F_eq_zero_of_gt {t : ℝ} (ht : 1 < t) : F.F t = 0 := by
  by_contra h; have := (F.support t h).2; linarith

theorem hasCompactSupport : HasCompactSupport F.F := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 1))
  intro t ht
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with h | h
  · exact F.F_eq_zero_of_lt h
  · exact F.F_eq_zero_of_gt h

/-- `F` is Lipschitz. -/
theorem exists_lipschitz : ∃ L : ℝ, 0 ≤ L ∧ ∀ a b : ℝ, |F.F a - F.F b| ≤ L * |a - b| := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport F.hasCompactSupport F.smooth
    (by simp)
  refine ⟨C, C.2, fun a b => ?_⟩
  have := hC.dist_le_mul a b
  simpa [Real.dist_eq] using this

/-- `J(δ) = ∫_{-1}^{1} F(s² + δ) ds`. -/
noncomputable def J (δ : ℝ) : ℝ := ∫ s in (-1 : ℝ)..1, F.F (s ^ 2 + δ)

theorem continuous_F_sq_add (δ : ℝ) : Continuous (fun s : ℝ => F.F (s ^ 2 + δ)) :=
  F.smooth.continuous.comp ((continuous_pow 2).add continuous_const)

/-- `c_F = ∫_{-1}^{1} F(s²) ds`. -/
theorem cF_eq_J_zero : F.cF = F.J 0 := by
  set g : ℝ → ℝ := fun t => F.F t * (max t (1 / 4)) ^ (-(1 : ℝ) / 2) with hg
  have hmax : ∀ t : ℝ, 0 < max t (1 / 4) := fun t =>
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hgc : Continuous g := by
    apply F.smooth.continuous.mul
    exact (continuous_id.max continuous_const).rpow_const (fun t => Or.inl (hmax t).ne')
  have h1 : F.cF = ∫ t in (0 : ℝ)..1, g t := by
    unfold Cutoff.cF
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hg]
    by_cases h : t < 1 / 2
    · simp [F.F_eq_zero_of_lt h]
    · rw [max_eq_left (by linarith)]
  have h2 : ∫ s in (0 : ℝ)..1, (g ∘ fun s : ℝ => s ^ 2) s * (2 * s) =
      ∫ t in ((0 : ℝ) ^ 2)..((1 : ℝ) ^ 2), g t := by
    apply intervalIntegral.integral_comp_mul_deriv (f := fun s : ℝ => s ^ 2)
      (f' := fun s => 2 * s)
    · intro s _
      simpa using hasDerivAt_pow 2 s
    · exact (continuous_const.mul continuous_id).continuousOn
    · exact hgc
  have h3 : ∫ s in (0 : ℝ)..1, (g ∘ fun s : ℝ => s ^ 2) s * (2 * s) =
      ∫ s in (0 : ℝ)..1, 2 * F.F (s ^ 2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    simp only [Function.comp_apply, hg]
    by_cases h : s ^ 2 < 1 / 2
    · simp [F.F_eq_zero_of_lt h]
    · push Not at h
      have hs0 : 0 < s := by
        rcases lt_or_eq_of_le hs.1 with h' | h'
        · exact h'
        · rw [← h'] at h; norm_num at h
      rw [max_eq_left (by linarith)]
      have : (s ^ 2) ^ (-(1 : ℝ) / 2) = s⁻¹ := by
        rw [show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg (by positivity),
          ← Real.sqrt_eq_rpow, Real.sqrt_sq hs0.le]
      rw [this]
      field_simp
  have h4 : F.J 0 = 2 * ∫ s in (0 : ℝ)..1, F.F (s ^ 2) := by
    unfold J
    simp only [add_zero]
    have hint : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => F.F (s ^ 2)) volume a b := by
      intro a b
      exact (F.smooth.continuous.comp (continuous_pow 2)).intervalIntegrable a b
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-1) 0) (hint 0 1)]
    have hneg : ∫ s in (-1 : ℝ)..0, F.F (s ^ 2) = ∫ s in (0 : ℝ)..1, F.F (s ^ 2) := by
      have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
        (fun s : ℝ => F.F (s ^ 2))
      simp only [neg_sq, neg_zero] at this
      rw [this]
    rw [hneg]; ring
  have h2' : ∫ t in (0 : ℝ)..1, g t = ∫ s in (0 : ℝ)..1, (g ∘ fun s : ℝ => s ^ 2) s * (2 * s) := by
    rw [h2]; norm_num
  rw [h1, h2', h3, h4, intervalIntegral.integral_const_mul]

/-- `0 ≤ J(δ) ≤ 2`. -/
theorem J_nonneg (δ : ℝ) : 0 ≤ F.J δ := by
  unfold J
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro s _
  exact F.nonneg _

theorem J_le_two (δ : ℝ) : F.J δ ≤ 2 := by
  unfold J
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
    (C := 1) (f := fun s : ℝ => F.F (s ^ 2 + δ)) (fun s _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (F.nonneg _)]; exact F.le_one _)
  rw [Real.norm_eq_abs] at h
  have := le_abs_self (∫ s in (-1 : ℝ)..1, F.F (s ^ 2 + δ))
  norm_num at h
  linarith

/-- `|J(δ) - c_F| ≤ 2 L δ`. -/
theorem abs_J_sub_cF_le {L : ℝ} (hL : ∀ a b : ℝ, |F.F a - F.F b| ≤ L * |a - b|) {δ : ℝ}
    (hδ : 0 ≤ δ) : |F.J δ - F.cF| ≤ 2 * L * δ := by
  rw [F.cF_eq_J_zero, J, J, ← intervalIntegral.integral_sub
    ((F.continuous_F_sq_add δ).intervalIntegrable _ _)
    ((F.continuous_F_sq_add 0).intervalIntegrable _ _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
    (C := L * δ) (f := fun s : ℝ => F.F (s ^ 2 + δ) - F.F (s ^ 2 + 0)) (fun s _ => by
      rw [Real.norm_eq_abs]
      have := hL (s ^ 2 + δ) (s ^ 2 + 0)
      rwa [add_sub_add_left_eq_sub, sub_zero, abs_of_nonneg hδ] at this)
  rw [Real.norm_eq_abs] at h
  simp only [add_zero] at h ⊢
  norm_num at h
  linarith

/-- `∫_ℝ F(s² + δ) ds = J(δ)` for `δ ≥ 0`. -/
theorem integral_eq_J {δ : ℝ} (hδ : 0 ≤ δ) : ∫ s : ℝ, F.F (s ^ 2 + δ) = F.J δ := by
  unfold J
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro s hs
  apply F.F_eq_zero_of_gt
  simp only [Set.mem_Icc, not_and_or, not_le] at hs
  have : 1 < s ^ 2 := by
    rcases hs with h | h
    · nlinarith
    · nlinarith
  linarith

/-- **The integral of the weight** `F(T(t)/x)`, `T(t) = At² + B`:
`∫_ℝ F((At² + B)/x) dt = √(x/A) J(B/x)`. -/
theorem integral_quadratic {A B x : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hx : 0 < x) :
    ∫ t : ℝ, F.F ((A * t ^ 2 + B) / x) = Real.sqrt (x / A) * F.J (B / x) := by
  set c := Real.sqrt (x / A) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hcA : A * c ^ 2 = x := by
    rw [hc, Real.sq_sqrt (by positivity)]; field_simp
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun t : ℝ => F.F ((A * t ^ 2 + B) / x)) c
  have h' : ∫ s : ℝ, F.F ((A * (c * s) ^ 2 + B) / x) = ∫ s : ℝ, F.F (s ^ 2 + B / x) := by
    congr 1
    ext s
    congr 1
    rw [mul_pow, ← mul_assoc, hcA]
    field_simp
  rw [h', F.integral_eq_J (by positivity), abs_of_pos (inv_pos.2 hc0), smul_eq_mul] at h
  rw [h]
  field_simp

end Cutoff

end Triples
