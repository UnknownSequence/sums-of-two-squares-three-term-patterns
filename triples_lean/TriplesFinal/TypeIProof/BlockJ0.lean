import TriplesFinal.TypeIProof.Gfun
import TriplesFinal.TypeIProof.SpecFam

/-!
# The spectrum `𝒥₀`: the large sieve for each `(s, σ)`

For a spectral family with the large sieve inequality and a bound `E` for the exceptional sums
`∫_{exc} V^(2 Im t) |S(ρ, s, σ)|²`, `J0_inner` bounds, for each `(s, σ)`,
`∫_{‖t‖ ≤ 1} V^(2|Im t|) |S(ρ_t, s, σ)|² ≤ cosh π · C(η)(1 + M^(1+η)/q) 2M (2C₀)² + E`.
`LS_single` is the large sieve inequality with a single coefficient, and `Cls_nonneg` records
that its constant is nonnegative.

Next step (not yet formalized): integrate over `(s, σ)` (Fubini) to bound `∫_{‖t‖ ≤ 1} m₀`.

Paper: §12.2.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition) (F : SpecFam)

/-- The large sieve inequality with a single coefficient. -/
theorem LS_single {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls) {h : ℕ} (hh : 1 ≤ h) {T : ℝ}
    (hT : 1 ≤ T) :
    ∫ x in F.ball T, ‖F.ρ x h‖ ^ 2 / F.ch x ∂F.ν ≤
      Cls S.η * (T ^ 2 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q) := by
  classical
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  set a : ℕ → ℂ := fun n => if n = h then 1 else 0 with ha
  have hsupp : ∀ n, a n ≠ 0 → (h : ℝ) / 2 < n ∧ (n : ℝ) ≤ 2 * ((h : ℝ) / 2) := by
    intro n hn
    have : n = h := by by_contra hne; exact hn (by simp [ha, hne])
    subst this
    constructor <;> linarith
  have hLS' := hLS S.η S.hη T hT ((h : ℝ) / 2) (by linarith) a hsupp
  have hfl : ⌊2 * ((h : ℝ) / 2)⌋₊ = h := by
    rw [show 2 * ((h : ℝ) / 2) = h by ring, Nat.floor_natCast]
  have hmem : h ∈ Finset.Icc 1 ⌊2 * ((h : ℝ) / 2)⌋₊ := by
    rw [hfl]; exact Finset.mem_Icc.2 ⟨hh, le_refl _⟩
  have e1 : ∀ x, ∑ n ∈ Finset.Icc 1 ⌊2 * ((h : ℝ) / 2)⌋₊, a n * F.ρ x n = F.ρ x h := by
    intro x
    rw [Finset.sum_eq_single h]
    · simp [ha]
    · intro n _ hn; simp [ha, hn]
    · intro hn; exact absurd hmem hn
  have e2 : ∑ n ∈ Finset.Icc 1 ⌊2 * ((h : ℝ) / 2)⌋₊, ‖a n‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single h]
    · simp [ha]
    · intro n _ hn; simp [ha, hn]
    · intro hn; exact absurd hmem hn
  simp only [e1, e2, mul_one] at hLS'
  exact hLS'

/-- The constant of the large sieve inequality is nonnegative. -/
theorem Cls_nonneg {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls) : 0 ≤ Cls S.η := by
  have h1 := S.LS_single F hLS (h := 1) le_rfl (T := 1) le_rfl
  have h0 : 0 ≤ ∫ x in F.ball 1, ‖F.ρ x 1‖ ^ 2 / F.ch x ∂F.ν :=
    integral_nonneg fun x => div_nonneg (sq_nonneg _) (F.ch_pos x).le
  have hq := S.q_pos
  have hpos : (0 : ℝ) < (1 : ℝ) ^ 2 + (((1 : ℕ) : ℝ) / 2) ^ (1 + S.η) / S.q := by positivity
  exact (mul_nonneg_iff_of_pos_right hpos).1 (h0.trans h1)

theorem norm_sq_Ssum_le (ρ : ℕ → ℂ) {s : ℝ} (hs : 0 ≤ s) (σ : ℝ) :
    ‖S.Ssum ψ₀ ρ s σ‖ ^ 2 ≤ 2 * S.M * (2 * S.C₀) ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2 := by
  unfold Ssum
  refine (SpecFam.sq_norm_sum_le S.Hs _).trans ?_
  have h1 := S.card_Hs_le
  have h2 : ∑ h ∈ S.Hs, ‖S.Gfun ψ₀ s σ (h / S.M) * ρ h‖ ^ 2 ≤
      (2 * S.C₀) ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (S.norm_Gfun_le ψ₀ hs σ _) 2) (sq_nonneg _)
  have h3 : 0 ≤ (2 * S.C₀) ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2 := by positivity
  calc ((S.Hs).card : ℝ) * ∑ h ∈ S.Hs, ‖S.Gfun ψ₀ s σ (h / S.M) * ρ h‖ ^ 2
      ≤ (2 * S.M) * ((2 * S.C₀) ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2) :=
        mul_le_mul h1 h2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by linarith [S.M_pos])
    _ = _ := by ring

theorem measurable_Ssum_joint :
    Measurable (fun z : F.Ω × (ℝ × ℝ) => S.Ssum ψ₀ (F.ρ z.1) z.2.1 z.2.2) := by
  unfold Ssum
  apply Finset.measurable_sum
  intro h _
  exact (((S.continuous_Gfun ψ₀ _).measurable).comp measurable_snd).mul
    ((F.meas_ρ h).comp measurable_fst)

theorem measurable_Ssum (s σ : ℝ) : Measurable (fun x => S.Ssum ψ₀ (F.ρ x) s σ) := by
  unfold Ssum
  exact Finset.measurable_sum _ fun h _ => measurable_const.mul (F.meas_ρ h)

/-- The large sieve bound for each `(s, σ)`. -/
theorem J0_inner {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls) {Eexc : ℝ}
    (hE : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∫ x in F.exc, S.V ^ (2 * (F.t x).im) *
      ‖S.Ssum ψ₀ (F.ρ x) s σ‖ ^ 2 ∂F.ν ≤ Eexc)
    {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 1) (σ : ℝ) :
    ∫ x in F.ball 1, S.V ^ (2 * |(F.t x).im|) * ‖S.Ssum ψ₀ (F.ρ x) s σ‖ ^ 2 ∂F.ν ≤
      Real.cosh Real.pi * Cls S.η * (1 + S.M ^ (1 + S.η) / S.q) * (2 * S.M * (2 * S.C₀) ^ 2) +
        Eexc := by
  classical
  have hs0 : 0 ≤ s := by linarith [hs.1]
  set f : F.Ω → ℝ := fun x => ‖S.Ssum ψ₀ (F.ρ x) s σ‖ ^ 2 with hf
  have hfm : Measurable f := ((S.measurable_Ssum ψ₀ F s σ).norm).pow_const 2
  -- integrability
  have hfi : IntegrableOn f (F.ball 1) F.ν := by
    have := F.integrableOn_sq_sum S.Hs (c := fun _ h => S.Gfun ψ₀ s σ (h / S.M))
      (fun _ => measurable_const) (B := 2 * S.C₀) (fun _ h => S.norm_Gfun_le ψ₀ hs0 σ _) 1
    simpa [hf, Setup.Ssum] using this
  have hV1 : 1 ≤ S.V := by linarith [S.V_ge]
  have hVi : IntegrableOn (fun x => S.V ^ (2 * |(F.t x).im|) * f x) (F.ball 1) F.ν := by
    refine (hfi.const_mul S.V).mono' ?_ ?_
    · have hm1 : Measurable fun x => |(F.t x).im| :=
        continuous_abs.measurable.comp (Complex.measurable_im.comp F.meas_t)
      exact ((measurable_const.pow (hm1.const_mul 2)).mul hfm).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc S.V ^ (2 * |(F.t x).im|) ≤ S.V ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hV1 (by linarith [F.abs_im_le_half x])
        _ = S.V := Real.rpow_one _
  -- split `ball 1 = (ball 1 \ exc) ∪ exc`
  have hsub : F.exc ⊆ F.ball 1 := F.exc_subset_ball (by norm_num)
  have hunion : F.ball 1 = (F.ball 1 \ F.exc) ∪ F.exc := (Set.sdiff_union_of_subset hsub).symm
  rw [hunion, setIntegral_union disjoint_sdiff_left F.measurableSet_exc
    (hVi.mono_set Set.sdiff_subset) (hVi.mono_set hsub)]
  apply add_le_add
  · -- the real spectrum
    have h1 : ∫ x in F.ball 1 \ F.exc, S.V ^ (2 * |(F.t x).im|) * f x ∂F.ν =
        ∫ x in F.ball 1 \ F.exc, f x ∂F.ν := by
      apply setIntegral_congr_fun ((F.measurableSet_ball 1).diff F.measurableSet_exc)
      intro x hx
      simp only
      rw [F.real_of_not_exc hx.2, abs_zero, mul_zero, Real.rpow_zero, one_mul]
    rw [h1]
    have hdiv := F.integrableOn_div_ch hfi
    have h2 : ∫ x in F.ball 1 \ F.exc, f x ∂F.ν ≤
        ∫ x in F.ball 1 \ F.exc, Real.cosh Real.pi * (f x / F.ch x) ∂F.ν := by
      apply setIntegral_mono_on (hfi.mono_set Set.sdiff_subset)
        ((hdiv.mono_set Set.sdiff_subset).const_mul _)
        ((F.measurableSet_ball 1).diff F.measurableSet_exc)
      intro x hx
      have hch := F.ch_pos x
      have hle : F.ch x ≤ Real.cosh Real.pi := by
        have := F.ch_le hx.1; rwa [mul_one] at this
      have hf0 : 0 ≤ f x := sq_nonneg _
      rw [mul_div_assoc', le_div_iff₀ hch]
      exact (mul_le_mul_of_nonneg_left hle hf0).trans_eq (mul_comm _ _)
    have h3 : ∫ x in F.ball 1 \ F.exc, Real.cosh Real.pi * (f x / F.ch x) ∂F.ν ≤
        Real.cosh Real.pi * ∫ x in F.ball 1, f x / F.ch x ∂F.ν := by
      rw [← integral_const_mul]
      exact setIntegral_mono_set (hdiv.const_mul _)
        (Eventually.of_forall fun x => mul_nonneg (Real.cosh_pos _).le
          (div_nonneg (sq_nonneg _) (F.ch_pos x).le))
        (Eventually.of_forall Set.sdiff_subset)
    -- the large sieve
    set a : ℕ → ℂ := fun n => S.Gfun ψ₀ s σ (n / S.M) with ha
    have hsupp : ∀ n, a n ≠ 0 → S.M < n ∧ (n : ℝ) ≤ 2 * S.M := by
      intro n hn
      have := S.Gfun_support ψ₀ s σ _ hn
      have hM := S.M_pos
      constructor
      · rw [lt_div_iff₀ hM, one_mul] at this; exact this.1
      · rw [div_le_iff₀ hM] at this; linarith [this.2]
    have hLS' := hLS S.η S.hη 1 le_rfl S.M S.hM1 a hsupp
    have ha2 : ∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, ‖a n‖ ^ 2 ≤ 2 * S.M * (2 * S.C₀) ^ 2 := by
      have h4 : ∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, ‖a n‖ ^ 2 ≤
          ∑ _n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, (2 * S.C₀) ^ 2 :=
        Finset.sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _)
          (S.norm_Gfun_le ψ₀ hs0 σ _) 2
      rw [Finset.sum_const, nsmul_eq_mul] at h4
      have h5 := S.card_Hs_le
      unfold Setup.Hs at h5
      have h6 : 0 ≤ (2 * S.C₀) ^ 2 := sq_nonneg _
      nlinarith
    have hfeq : ∀ x, f x = ‖∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, a n * F.ρ x n‖ ^ 2 := fun x => rfl
    simp only [← hfeq, one_pow] at hLS'
    have hCls : 0 ≤ Cls S.η := S.Cls_nonneg F hLS
    have hq := S.q_pos
    have hM := S.M_pos
    have hpos : 0 ≤ Cls S.η * (1 + S.M ^ (1 + S.η) / S.q) := mul_nonneg hCls (by positivity)
    calc ∫ x in F.ball 1 \ F.exc, f x ∂F.ν
        ≤ Real.cosh Real.pi * ∫ x in F.ball 1, f x / F.ch x ∂F.ν := h2.trans h3
      _ ≤ Real.cosh Real.pi * (Cls S.η * (1 + S.M ^ (1 + S.η) / S.q) *
            ∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, ‖a n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hLS' (Real.cosh_pos _).le
      _ ≤ Real.cosh Real.pi * (Cls S.η * (1 + S.M ^ (1 + S.η) / S.q) *
            (2 * S.M * (2 * S.C₀) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha2 hpos) (Real.cosh_pos _).le
      _ = _ := by ring
  · -- the exceptional spectrum
    have h1 : ∫ x in F.exc, S.V ^ (2 * |(F.t x).im|) * f x ∂F.ν =
        ∫ x in F.exc, S.V ^ (2 * (F.t x).im) * f x ∂F.ν := by
      apply setIntegral_congr_fun F.measurableSet_exc
      intro x hx
      have : 0 < (F.t x).im := hx
      simp only
      rw [abs_of_pos this]
    rw [h1]
    exact hE s hs σ

end Setup

end Triples
