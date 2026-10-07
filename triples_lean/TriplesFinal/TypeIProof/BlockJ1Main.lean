import TriplesFinal.TypeIProof.BlockJ0Total
import TriplesFinal.TypeIProof.BJ1
import TriplesFinal.Spectral.TwistMeasure
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The main terms on `𝒥₁`: `1 < |t| ≤ T₁`

On the real spectrum with `1 < |t| ≤ T₁`, the main terms `B^±` of the Mellin–Barnes splitting
are bounded by the twist removal (Lemma 10.6, in the measure form `twist_removal_measure`) and
the large sieve inequality with the coefficients `1_{M < n ≤ y}`:
`∫ m_main ≤ (X/K)² Y^(-1) (7/4) · 2((2C₀²)² + (K₁T₁)²) · C(η)(T₁² + M^(1+η)/q) · 2M`, where
`K₁ = (C_ψ + 1)(2C₀²) + 2C_d` collects the bounds for `ψ₀'` and `∂_h M_h`.

Paper: §12.3.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

namespace DyadicPartition

/-- `ψ₀'` is bounded. -/
theorem exists_deriv_bound (ψ₀ : DyadicPartition) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |deriv ψ₀.ψ₀ y| ≤ C := by
  have hc : Continuous (deriv ψ₀.ψ₀) := ψ₀.smooth.continuous_deriv (by exact_mod_cast le_top)
  have hs : HasCompactSupport (deriv ψ₀.ψ₀) := by
    have : HasCompactSupport ψ₀.ψ₀ := by
      refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
      intro t ht
      by_contra hne
      exact ht (ψ₀.support t hne)
    exact this.deriv
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  have := hC y
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

end DyadicPartition

namespace SpecFam

variable (F : SpecFam)

/-- The annulus `T₀ < ‖t‖ ≤ T`. -/
def annulus (T₀ T : ℝ) : Set F.Ω := {x | T₀ < ‖F.t x‖ ∧ ‖F.t x‖ ≤ T}

theorem measurableSet_annulus (T₀ T : ℝ) : MeasurableSet (F.annulus T₀ T) :=
  (measurableSet_lt measurable_const F.meas_t.norm).inter
    (measurableSet_le F.meas_t.norm measurable_const)

theorem annulus_subset_ball (T₀ T : ℝ) : F.annulus T₀ T ⊆ F.ball T := fun _ hx => hx.2

theorem not_exc_of_mem_annulus {T₀ T : ℝ} (h : 1 / 2 ≤ T₀) {x : F.Ω}
    (hx : x ∈ F.annulus T₀ T) : x ∉ F.exc :=
  F.not_exc_of_lt h hx.1

end SpecFam

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition) (F : SpecFam)

/-- The derivative of `y ↦ (π y Y)^(-iτ)`. -/
theorem hasDerivAt_cpow_piY (τ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => ((Real.pi * y * S.Y : ℝ) : ℂ) ^ (-(I * τ)))
      (-(I * τ) * ((Real.pi * y * S.Y : ℝ) : ℂ) ^ (-(I * τ) - 1) * ((Real.pi * S.Y : ℝ) : ℂ))
      y := by
  have hP : 0 < Real.pi * y * S.Y := by have := S.Y_pos; positivity
  have h1 : HasDerivAt (fun y : ℝ => ((Real.pi * y * S.Y : ℝ) : ℂ))
      ((Real.pi * S.Y : ℝ) : ℂ) y := by
    have : HasDerivAt (fun y : ℝ => Real.pi * y * S.Y) (Real.pi * S.Y) y := by
      have := ((hasDerivAt_id y).const_mul Real.pi).mul_const S.Y
      simpa using this
    exact this.ofReal_comp
  have h2 : HasDerivAt (fun z : ℂ => z ^ (-(I * τ)))
      (-(I * τ) * ((Real.pi * y * S.Y : ℝ) : ℂ) ^ (-(I * τ) - 1))
      ((Real.pi * y * S.Y : ℝ) : ℂ) := by
    have := (hasDerivAt_id ((Real.pi * y * S.Y : ℝ) : ℂ)).cpow_const (c := -(I * τ))
      (Complex.ofReal_mem_slitPlane.2 hP)
    simp only [id_eq, mul_one] at this
    exact this
  exact h2.comp y h1

/-- `|(π y Y)^(-iτ)| = 1`. -/
theorem norm_cpow_piY (τ : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖((Real.pi * y * S.Y : ℝ) : ℂ) ^ (-(I * τ))‖ = 1 := by
  have hP : 0 < Real.pi * y * S.Y := by have := S.Y_pos; positivity
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hP]
  simp

/-- `|d/dy (π y Y)^(-iτ)| = |τ|/y`. -/
theorem norm_deriv_cpow_piY (τ : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖-(I * τ) * ((Real.pi * y * S.Y : ℝ) : ℂ) ^ (-(I * τ) - 1) * ((Real.pi * S.Y : ℝ) : ℂ)‖ =
      |τ| / y := by
  have hY := S.Y_pos
  have hP : 0 < Real.pi * y * S.Y := by positivity
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hP, norm_neg, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (by positivity)]
  have hre : (-(I * (τ : ℂ)) - 1).re = -1 := by simp
  rw [hre, Real.rpow_neg_one]
  field_simp

/-- **The derivative of the twist** `φ_τ`. -/
theorem phiT_deriv {Cψ : ℝ} (hψ : ∀ y, |deriv ψ₀.ψ₀ y| ≤ Cψ) {Cd : ℝ}
    (hMd : ∀ h : ℝ, S.M ≤ h → h ≤ 2 * S.M → ∀ w : ℂ, w.re = 0 →
      DifferentiableAt ℝ (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h ∧
        ‖deriv (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h‖ ≤ Cd * S.X / S.K)
    (τ : ℝ) {y : ℝ} (hy : y ∈ Icc S.M (2 * S.M)) :
    HasDerivAt (S.phiT ψ₀ τ) (deriv (S.phiT ψ₀ τ) y) y ∧
      ‖deriv (S.phiT ψ₀ τ) y‖ ≤ (Cψ + |τ|) / S.M * (2 * S.C₀ ^ 2) + Cd * S.X / S.K := by
  have hM := S.M_pos
  have hy0 : 0 < y := lt_of_lt_of_le hM hy.1
  -- the three factors
  have ha : HasDerivAt (fun y : ℝ => (ψ₀.ψ₀ (y / S.M) : ℂ))
      ((deriv ψ₀.ψ₀ (y / S.M) * S.M⁻¹ : ℝ) : ℂ) y := by
    have hd : DifferentiableAt ℝ ψ₀.ψ₀ (y / S.M) :=
      (ψ₀.smooth.differentiable (by exact_mod_cast WithTop.top_ne_zero)).differentiableAt
    have : HasDerivAt (fun y : ℝ => ψ₀.ψ₀ (y / S.M)) (deriv ψ₀.ψ₀ (y / S.M) * S.M⁻¹) y := by
      have h2 := hd.hasDerivAt.comp y ((hasDerivAt_id y).div_const S.M)
      rw [one_div] at h2
      exact h2
    exact this.ofReal_comp
  have hb := S.hasDerivAt_cpow_piY τ hy0
  obtain ⟨hcd, hcb⟩ := hMd y hy.1 hy.2 (I * τ) (by simp)
  have hc := hcd.hasDerivAt
  set a' := ((deriv ψ₀.ψ₀ (y / S.M) * S.M⁻¹ : ℝ) : ℂ) with ha'
  set a := (ψ₀.ψ₀ (y / S.M) : ℂ) with ha_
  set b := ((Real.pi * y * S.Y : ℝ) : ℂ) ^ (-(I * τ)) with hb_
  set b' := -(I * τ) * ((Real.pi * y * S.Y : ℝ) : ℂ) ^ (-(I * τ) - 1) *
    ((Real.pi * S.Y : ℝ) : ℂ) with hb'
  set c := Mh S.ψ₁ S.ψ₂ S.X S.K y (I * τ) with hc_
  set c' := deriv (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' (I * τ)) y with hc'
  have hA : HasDerivAt (S.phiT ψ₀ τ) (star ((a' * b + a * b') * c + a * b * c')) y := by
    have h := ((ha.mul hb).mul hc).star
    convert h using 1
    all_goals rfl
  refine ⟨hA.differentiableAt.hasDerivAt, ?_⟩
  rw [hA.deriv, norm_star]
  -- the bounds for the factors
  have ha0 : ‖(ψ₀.ψ₀ (y / S.M) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (ψ₀.nonneg _)]; exact ψ₀.le_one _
  have ha1 : ‖((deriv ψ₀.ψ₀ (y / S.M) * S.M⁻¹ : ℝ) : ℂ)‖ ≤ Cψ / S.M := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hM, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (hψ _) hM.le
  have hb0 := S.norm_cpow_piY τ hy0
  have hb1 := S.norm_deriv_cpow_piY τ hy0
  have hc0 : ‖Mh S.ψ₁ S.ψ₂ S.X S.K y (I * τ)‖ ≤ 2 * S.C₀ ^ 2 :=
    S.norm_Mh_le' y (w := I * τ) (by simp)
  have hC0 := S.C₀_nonneg
  have hτy : |τ| / y ≤ |τ| / S.M := div_le_div_of_nonneg_left (abs_nonneg _) hM hy.1
  have h1 : ‖(a' * b + a * b') * c + a * b * c'‖ ≤
      ‖a'‖ * ‖b‖ * ‖c‖ + ‖a‖ * ‖b'‖ * ‖c‖ + ‖a‖ * ‖b‖ * ‖c'‖ := by
    calc ‖(a' * b + a * b') * c + a * b * c'‖ ≤ ‖(a' * b + a * b') * c‖ + ‖a * b * c'‖ :=
          norm_add_le _ _
      _ ≤ (‖a' * b‖ + ‖a * b'‖) * ‖c‖ + ‖a * b * c'‖ := by
          rw [norm_mul (a' * b + a * b')]
          gcongr
          exact norm_add_le _ _
      _ = _ := by simp only [norm_mul]; ring
  refine h1.trans ?_
  rw [hb0, hb1]
  have hc'0 : 0 ≤ ‖c'‖ := norm_nonneg _
  have hcn : 0 ≤ ‖c‖ := norm_nonneg _
  have ha'n : 0 ≤ ‖a'‖ := norm_nonneg _
  have han : 0 ≤ ‖a‖ := norm_nonneg _
  have e2 : (Cψ + |τ|) / S.M * (2 * S.C₀ ^ 2) =
      Cψ / S.M * (2 * S.C₀ ^ 2) + |τ| / S.M * (2 * S.C₀ ^ 2) := by ring
  rw [e2]
  have t1 : ‖a'‖ * 1 * ‖c‖ ≤ Cψ / S.M * (2 * S.C₀ ^ 2) := by
    rw [mul_one]; exact mul_le_mul ha1 hc0 hcn (le_trans ha'n ha1)
  have t2 : ‖a‖ * (|τ| / y) * ‖c‖ ≤ |τ| / S.M * (2 * S.C₀ ^ 2) := by
    have : ‖a‖ * (|τ| / y) ≤ |τ| / S.M := by
      calc ‖a‖ * (|τ| / y) ≤ 1 * (|τ| / S.M) :=
            mul_le_mul ha0 hτy (by positivity) zero_le_one
        _ = _ := one_mul _
    exact mul_le_mul this hc0 hcn (by positivity)
  have t3 : ‖a‖ * 1 * ‖c'‖ ≤ Cd * S.X / S.K := by
    rw [mul_one]
    calc ‖a‖ * ‖c'‖ ≤ 1 * (Cd * S.X / S.K) := mul_le_mul ha0 hcb hc'0 zero_le_one
      _ = _ := one_mul _
  linarith

/-- The large sieve with the coefficients `1_{M < n ≤ y}`. -/
theorem LS_partial {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls) {T : ℝ} (hT : 1 ≤ T) {y : ℝ}
    (hy : y ∈ Icc S.M (2 * S.M)) :
    ∫ x in F.ball T, ‖∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => S.M < n), F.ρ x n‖ ^ 2 /
        F.ch x ∂F.ν ≤
      Cls S.η * (T ^ 2 + S.M ^ (1 + S.η) / S.q) * (2 * S.M) := by
  classical
  have hM := S.M_pos
  set a : ℕ → ℂ := fun n => if S.M < n ∧ (n : ℝ) ≤ y then 1 else 0 with ha
  have hsupp : ∀ n, a n ≠ 0 → S.M < n ∧ (n : ℝ) ≤ 2 * S.M := by
    intro n hn
    have : S.M < n ∧ (n : ℝ) ≤ y := by
      by_contra hc; exact hn (by simp [ha, hc])
    exact ⟨this.1, this.2.trans hy.2⟩
  have h := hLS S.η S.hη T hT S.M S.hM1 a hsupp
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have e1 : ∀ x, ∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, a n * F.ρ x n =
      ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => S.M < n), F.ρ x n := by
    intro x
    have hfl : ⌊y⌋₊ ≤ ⌊2 * S.M⌋₊ := Nat.floor_le_floor hy.2
    rw [Finset.sum_filter]
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hfl)]
    · apply Finset.sum_congr rfl
      intro n hn
      have hn' : (n : ℝ) ≤ y := (Nat.le_floor_iff hy0).1 (Finset.mem_Icc.1 hn).2
      by_cases hMn : S.M < n
      · simp [ha, hMn, hn']
      · simp [ha, hMn]
    · intro n hn hn'
      have : ¬ ((n : ℝ) ≤ y) := by
        intro hle
        exact hn' (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hn).1, Nat.le_floor hle⟩)
      simp [ha, this]
  have e2 : ∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, ‖a n‖ ^ 2 ≤ 2 * S.M := by
    calc ∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, ‖a n‖ ^ 2
        ≤ ∑ _n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, (1 : ℝ) := Finset.sum_le_sum fun n _ => by
          by_cases hc : S.M < n ∧ (n : ℝ) ≤ y
          · simp [ha, hc]
          · simp [ha, hc]
      _ = ((Finset.Icc 1 ⌊2 * S.M⌋₊).card : ℝ) := by simp
      _ ≤ 2 * S.M := S.card_Hs_le
  simp only [e1] at h
  have hC := S.Cls_nonneg F hLS
  have hq := S.q_pos
  have hpos : 0 ≤ Cls S.η * (T ^ 2 + S.M ^ (1 + S.η) / S.q) := mul_nonneg hC (by positivity)
  exact h.trans (mul_le_mul_of_nonneg_left e2 hpos)

/-- `φ_τ(h) = 0` unless `M < h`. -/
theorem phiT_eq_zero {τ : ℝ} {h : ℝ} (hh : h ≤ S.M) : S.phiT ψ₀ τ h = 0 := by
  have hM := S.M_pos
  unfold phiT
  rw [ψ₀.eq_zero_of_le_one ((div_le_one hM).2 hh)]
  simp

theorem norm_phiT_le (τ h : ℝ) : ‖S.phiT ψ₀ τ h‖ ≤ 2 * S.C₀ ^ 2 := by
  have hC0 := S.C₀_nonneg
  by_cases hh : h ≤ S.M
  · rw [S.phiT_eq_zero ψ₀ hh, norm_zero]; positivity
  push Not at hh
  have hh0 : 0 < h := lt_trans S.M_pos hh
  unfold phiT
  rw [RCLike.norm_conj, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (ψ₀.nonneg _), S.norm_cpow_piY τ hh0]
  have h1 := ψ₀.le_one (h / S.M)
  have h3 := S.norm_Mh_le' h (w := I * τ) (by simp)
  have h0 := ψ₀.nonneg (h / S.M)
  calc ψ₀.ψ₀ (h / S.M) * 1 * ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ ≤ 1 * 1 * (2 * S.C₀ ^ 2) := by
        gcongr
    _ = _ := by ring

theorem measurable_phiT_comp {τf : F.Ω → ℝ} (hτm : Measurable τf) (n : ℝ) :
    Measurable fun x => S.phiT ψ₀ (τf x) n := by
  unfold phiT
  have hτc : Measurable fun x => ((τf x : ℝ) : ℂ) := Complex.measurable_ofReal.comp hτm
  have h1 : Measurable fun x => (ψ₀.ψ₀ (n / S.M) : ℂ) *
      ((Real.pi * n * S.Y : ℝ) : ℂ) ^ (-(I * (τf x : ℂ))) *
        Mh S.ψ₁ S.ψ₂ S.X S.K n (I * (τf x : ℂ)) := by
    refine (measurable_const.mul (measurable_const.pow (measurable_const.mul hτc).neg)).mul ?_
    exact (S.continuous_Mh_w n).measurable.comp (measurable_const.mul hτc)
  exact Complex.continuous_conj.measurable.comp h1

set_option maxHeartbeats 1000000 in
/-- **The main terms on `𝒥₁`**: for `σ = ±1`,
`∫_{1 < |t| ≤ T₁} m_main(ρ, σt) ≤ (X/K)² Y^(-1) (7/4) · 2((2C₀²)² + (K₁T₁)²) · C(η)(T₁² + M^(1+η)/q) 2M`
with `K₁ = (C_ψ + 1)(2C₀²) + 2C_d`. -/
theorem J1_main_block {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls) {Cψ : ℝ} (hCψ : 0 ≤ Cψ)
    (hψ : ∀ y, |deriv ψ₀.ψ₀ y| ≤ Cψ) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hMd : ∀ h : ℝ, S.M ≤ h → h ≤ 2 * S.M → ∀ w : ℂ, w.re = 0 →
      DifferentiableAt ℝ (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h ∧
        ‖deriv (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h‖ ≤ Cd * S.X / S.K)
    {sg : ℝ} (hsg : sg = 1 ∨ sg = -1) :
    IntegrableOn (fun x => S.mMain ψ₀ (F.ρ x) (sg * (F.t x).re)) (F.annulus 1 S.T₁) F.ν ∧
    ∫ x in F.annulus 1 S.T₁, S.mMain ψ₀ (F.ρ x) (sg * (F.t x).re) ∂F.ν ≤
      S.Bk ^ 2 * (7 / 4) * (2 * ((2 * S.C₀ ^ 2) ^ 2 +
        (((Cψ + 1) * (2 * S.C₀ ^ 2) + 2 * Cd) * S.T₁) ^ 2) *
          (Cls S.η * (S.T₁ ^ 2 + S.M ^ (1 + S.η) / S.q) * (2 * S.M))) := by
  classical
  have hM := S.M_pos
  have hC0 := S.C₀_nonneg
  have hT1 := S.one_le_T₁
  set A := F.annulus 1 S.T₁ with hA
  have hAm : MeasurableSet A := F.measurableSet_annulus 1 S.T₁
  set τf : F.Ω → ℝ := fun x => sg * (F.t x).re with hτf
  have hτm : Measurable τf := measurable_const.mul (Complex.measurable_re.comp F.meas_t)
  -- on the annulus, `t` is real and `|τ| ≤ T₁`
  have hnexc : ∀ x ∈ A, x ∉ F.exc := fun x hx => F.not_exc_of_mem_annulus (by norm_num) hx
  have habs : ∀ x ∈ A, |τf x| ≤ S.T₁ := by
    intro x hx
    have h1 := F.norm_eq_abs_re_of_not_exc (hnexc x hx)
    have h2 : |τf x| = |(F.t x).re| := by
      simp only [hτf, abs_mul]
      rcases hsg with h | h <;> simp [h]
    rw [h2, ← h1]; exact hx.2
  have hch : ∀ x ∈ A, Real.cosh (Real.pi * τf x) = F.ch x := by
    intro x hx
    rw [F.ch_of_not_exc (hnexc x hx)]
    rcases hsg with h | h
    · simp [hτf, h]
    · rw [← Real.cosh_neg]; congr 1; simp [hτf, h]
  -- the twist
  set φ : F.Ω → ℝ → ℂ := fun x y => if x ∈ A then S.phiT ψ₀ (τf x) y else 0 with hφ
  set K₁ := (Cψ + 1) * (2 * S.C₀ ^ 2) + 2 * Cd with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set D₁ := K₁ * S.T₁ / S.M with hD₁
  have hD₁0 : 0 ≤ D₁ := by have := S.T₁_pos; positivity
  set B := Cls S.η * (S.T₁ ^ 2 + S.M ^ (1 + S.η) / S.q) * (2 * S.M) with hB
  have hφd : ∀ x, ∀ y ∈ Icc S.M (2 * S.M), HasDerivAt (φ x) (deriv (φ x) y) y := by
    intro x y hy
    by_cases hx : x ∈ A
    · have e : φ x = S.phiT ψ₀ (τf x) := by funext y; simp [hφ, hx]
      rw [e]; exact (S.phiT_deriv ψ₀ hψ hMd (τf x) hy).1
    · have e : φ x = fun _ => 0 := by funext y; simp [hφ, hx]
      rw [e, deriv_const]; exact hasDerivAt_const y 0
  have hD₀ : ∀ x, ∀ y ∈ Icc S.M (2 * S.M), ‖φ x y‖ ≤ 2 * S.C₀ ^ 2 := by
    intro x y _
    by_cases hx : x ∈ A
    · simp only [hφ, hx, ↓reduceIte]; exact S.norm_phiT_le ψ₀ _ _
    · simp only [hφ, hx, ↓reduceIte, norm_zero]; positivity
  have hD₁' : ∀ x, ∀ y ∈ Icc S.M (2 * S.M), ‖deriv (φ x) y‖ ≤ D₁ := by
    intro x y hy
    by_cases hx : x ∈ A
    · have e : φ x = S.phiT ψ₀ (τf x) := by funext y; simp [hφ, hx]
      rw [e]
      refine (S.phiT_deriv ψ₀ hψ hMd (τf x) hy).2.trans ?_
      have hτ := habs x hx
      have e1 : (Cψ + |τf x|) / S.M * (2 * S.C₀ ^ 2) ≤ (Cψ + 1) * (2 * S.C₀ ^ 2) * S.T₁ / S.M := by
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hM.le
        have : Cψ + |τf x| ≤ (Cψ + 1) * S.T₁ := by nlinarith
        nlinarith
      have e2 : Cd * S.X / S.K ≤ 2 * Cd * S.T₁ / S.M := by
        have h1 := S.XK_le
        have h2 := S.Qη_le_T₁
        rw [mul_div_assoc]
        calc Cd * (S.X / S.K) ≤ Cd * (2 * S.Q ^ S.η / S.M) := mul_le_mul_of_nonneg_left h1 hCd
          _ ≤ Cd * (2 * S.T₁ / S.M) := by gcongr
          _ = 2 * Cd * S.T₁ / S.M := by ring
      calc (Cψ + |τf x|) / S.M * (2 * S.C₀ ^ 2) + Cd * S.X / S.K
          ≤ (Cψ + 1) * (2 * S.C₀ ^ 2) * S.T₁ / S.M + 2 * Cd * S.T₁ / S.M := add_le_add e1 e2
        _ = D₁ := by rw [hD₁, hK₁]; ring
    · have e : φ x = fun _ => 0 := by funext y; simp [hφ, hx]
      rw [e, deriv_const, norm_zero]; exact hD₁0
  -- the partial sums
  have hint : ∀ y ∈ Icc S.M (2 * S.M), IntegrableOn (fun x => (F.ch x)⁻¹ *
      ‖∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => S.M < n), F.ρ x n‖ ^ 2) A F.ν := by
    intro y _
    have h1 := F.integrableOn_sq_sum ((Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => S.M < n))
      (c := fun _ _ => (1 : ℂ)) (fun _ => measurable_const) (B := 1) (fun _ _ => by simp) S.T₁
    simp only [one_mul] at h1
    have h2 := (F.integrableOn_div_ch h1).mono_set (F.annulus_subset_ball 1 S.T₁)
    refine h2.congr_fun (fun x _ => ?_) hAm
    exact (inv_mul_eq_div _ _).symm
  have hBy : ∀ y ∈ Icc S.M (2 * S.M), ∫ x in A, (F.ch x)⁻¹ *
      ‖∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => S.M < n), F.ρ x n‖ ^ 2 ∂F.ν ≤ B := by
    intro y hy
    have h1 := F.integrableOn_sq_sum ((Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => S.M < n))
      (c := fun _ _ => (1 : ℂ)) (fun _ => measurable_const) (B := 1) (fun _ _ => by simp) S.T₁
    simp only [one_mul] at h1
    calc ∫ x in A, (F.ch x)⁻¹ *
          ‖∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => S.M < n), F.ρ x n‖ ^ 2 ∂F.ν
        = ∫ x in A, ‖∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => S.M < n), F.ρ x n‖ ^ 2 /
            F.ch x ∂F.ν := setIntegral_congr_fun hAm (fun x _ => inv_mul_eq_div _ _)
      _ ≤ ∫ x in F.ball S.T₁,
            ‖∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => S.M < n), F.ρ x n‖ ^ 2 /
              F.ch x ∂F.ν :=
          setIntegral_mono_set (F.integrableOn_div_ch h1)
            (Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (F.ch_pos x).le)
            (Eventually.of_forall (F.annulus_subset_ball 1 S.T₁))
      _ ≤ B := S.LS_partial F hLS hT1 hy
  have htw := twist_removal_measure (μ := F.ν) (S := A) S.hM1 (fun x => (F.ch x)⁻¹)
    (fun x => (inv_pos.2 (F.ch_pos x)).le) F.ρ φ hφd hD₀ hD₁' hint hBy
  have hMD : S.M ^ 2 * D₁ ^ 2 = (K₁ * S.T₁) ^ 2 := by
    rw [hD₁]; field_simp
  rw [hMD] at htw
  -- `m_main` on the annulus
  have hm : ∀ x ∈ A, S.mMain ψ₀ (F.ρ x) (τf x) = S.Bk ^ 2 * (7 / 4) * ((F.ch x)⁻¹ *
      ‖∑ n ∈ (Finset.Icc 1 ⌊2 * S.M⌋₊).filter (fun n : ℕ => S.M < n), F.ρ x n * φ x n‖ ^ 2) := by
    intro x hx
    unfold mMain
    rw [hch x hx]
    have e : ∑ h ∈ S.Hs, F.ρ x h * S.phiT ψ₀ (τf x) h =
        ∑ n ∈ (Finset.Icc 1 ⌊2 * S.M⌋₊).filter (fun n : ℕ => S.M < n), F.ρ x n * φ x n := by
      rw [Finset.sum_filter_of_ne]
      · apply Finset.sum_congr rfl
        intro n _
        simp [hφ, hx]
      · intro n _ hne
        by_contra hMn
        push Not at hMn
        apply hne
        simp [hφ, hx, S.phiT_eq_zero ψ₀ hMn]
    rw [e]
    ring
  -- integrability
  have hφm : ∀ n : ℕ, Measurable fun x => φ x n := by
    intro n
    exact Measurable.ite hAm (S.measurable_phiT_comp ψ₀ F hτm n) measurable_const
  have hφb : ∀ x (n : ℕ), ‖φ x n‖ ≤ 2 * S.C₀ ^ 2 := by
    intro x n
    by_cases hx : x ∈ A
    · simp only [hφ, hx, ↓reduceIte]; exact S.norm_phiT_le ψ₀ _ _
    · simp only [hφ, hx, ↓reduceIte, norm_zero]; positivity
  have hsq := F.integrableOn_sq_sum ((Finset.Icc 1 ⌊2 * S.M⌋₊).filter (fun n : ℕ => S.M < n))
    (c := fun x n => φ x n) hφm hφb S.T₁
  have hsq' : IntegrableOn (fun x => (F.ch x)⁻¹ *
      ‖∑ n ∈ (Finset.Icc 1 ⌊2 * S.M⌋₊).filter (fun n : ℕ => S.M < n), F.ρ x n * φ x n‖ ^ 2)
      A F.ν := by
    refine ((F.integrableOn_div_ch hsq).mono_set (F.annulus_subset_ball 1 S.T₁)).congr_fun
      (fun x _ => ?_) hAm
    simp only [mul_comm (φ x _) (F.ρ x _)]
    exact (inv_mul_eq_div _ _).symm
  have hint' : IntegrableOn (fun x => S.mMain ψ₀ (F.ρ x) (τf x)) A F.ν :=
    IntegrableOn.congr_fun (hsq'.const_mul (S.Bk ^ 2 * (7 / 4))) (fun x hx => (hm x hx).symm) hAm
  refine ⟨hint', ?_⟩
  rw [setIntegral_congr_fun hAm hm, integral_const_mul]
  exact mul_le_mul_of_nonneg_left htw (by positivity)

end Setup

end Triples
