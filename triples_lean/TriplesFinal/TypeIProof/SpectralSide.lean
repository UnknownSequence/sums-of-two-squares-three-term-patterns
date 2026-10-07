import TriplesFinal.TypeIProof.Combine

/-!
# The spectral side of `Ξ_M`

For a spectral family with the large sieve inequality and the Heegner side bound,
`∫ |B(ρ_t, t)| |U| ≤ ∑_n √(A_n) √(256/π T_n² P)`, where `A_n` bounds `∫_{block n} |B|²`
(`blockA`: the bounds of `J0_block`, `J1_main_block`, `tail_block` and `rem_block`) and `T_n` is
the outer radius of the block.

Paper: §§12.2–12.6.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition) (F : SpecFam)

/-- The bound of `J0_block`. -/
noncomputable def boundJ0 (Cls : ℝ → ℝ) (Eexc : ℝ) : ℝ :=
  2 * S.Bk ^ 2 * (S.ℓ / 4 * (2 * S.C₀) ^ 2 * (S.ℓ *
    (Real.cosh Real.pi * Cls S.η * (1 + S.M ^ (1 + S.η) / S.q) * (2 * S.M * (2 * S.C₀) ^ 2) +
      Eexc)) +
    2 * S.M * S.eps0 ^ 2 * ∑ h ∈ S.Hs,
      Real.cosh Real.pi * (Cls S.η * (1 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q)))

/-- The bound of `J1_main_block`. -/
noncomputable def boundMain (Cls : ℝ → ℝ) (Cψ Cd : ℝ) : ℝ :=
  S.Bk ^ 2 * (7 / 4) * (2 * ((2 * S.C₀ ^ 2) ^ 2 +
    (((Cψ + 1) * (2 * S.C₀ ^ 2) + 2 * Cd) * S.T₁) ^ 2) *
      (Cls S.η * (S.T₁ ^ 2 + S.M ^ (1 + S.η) / S.q) * (2 * S.M)))

/-- The bound of `rem_block`. -/
noncomputable def boundRem (Cls : ℝ → ℝ) (C6 CGt R R₁ : ℝ) : ℝ :=
  S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ * (CGt ^ 2 * (1 + R) ^ (-(5 : ℝ)) *
    (Cls S.η * (R₁ ^ 2 + S.M ^ (1 + S.η) / S.q)) *
      (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) * c₅)

/-- The bound of `tail_block`. -/
noncomputable def boundTail (Cls : ℝ → ℝ) (k Ck R R₁ : ℝ) : ℝ :=
  S.Bk ^ 2 * (7 / 4) * (2 * S.M * (Ck * (1 + R) ^ (-k)) ^ 2) *
    (2 * S.M * (Cls S.η * (R₁ ^ 2 + S.M ^ (1 + S.η) / S.q)))

/-- The bounds for `∫_{block n} |B|²`. -/
noncomputable def blockA (Cls : ℝ → ℝ) (Eexc Cψ Cd C6 CGt k Ck : ℝ) : ℕ → ℝ
  | 0 => S.boundJ0 Cls Eexc
  | 1 => 3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls C6 CGt 1 S.T₁)
  | (m + 2) => 3 * (2 * S.boundTail Cls k Ck (2 ^ m * S.T₁) (2 ^ (m + 1) * S.T₁) +
      S.boundRem Cls C6 CGt (2 ^ m * S.T₁) (2 ^ (m + 1) * S.T₁))

/-- `|B|²` on an annulus of the real spectrum, from the bounds for the three majorants. -/
theorem annulus_sq_bound (hB : BesselAssumptions)
    (hBm : Measurable fun x => S.B ψ₀ (F.ρ x) (F.t x)) {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {R R₁ : ℝ} (hR : 1 ≤ R) {A₁ A₂ A₃ : ℝ}
    (h1 : IntegrableOn (fun x => S.mMain ψ₀ (F.ρ x) (1 * (F.t x).re)) (F.annulus R R₁) F.ν ∧
      ∫ x in F.annulus R R₁, S.mMain ψ₀ (F.ρ x) (1 * (F.t x).re) ∂F.ν ≤ A₁)
    (h2 : IntegrableOn (fun x => S.mMain ψ₀ (F.ρ x) (-1 * (F.t x).re)) (F.annulus R R₁) F.ν ∧
      ∫ x in F.annulus R R₁, S.mMain ψ₀ (F.ρ x) (-1 * (F.t x).re) ∂F.ν ≤ A₂)
    (h3 : IntegrableOn (fun x => S.mRem ψ₀ (F.ρ x) (F.t x).re) (F.annulus R R₁) F.ν ∧
      ∫ x in F.annulus R R₁, S.mRem ψ₀ (F.ρ x) (F.t x).re ∂F.ν ≤ A₃) :
    IntegrableOn (fun x => ‖S.B ψ₀ (F.ρ x) (F.t x)‖ ^ 2) (F.annulus R R₁) F.ν ∧
      ∫ x in F.annulus R R₁, ‖S.B ψ₀ (F.ρ x) (F.t x)‖ ^ 2 ∂F.ν ≤ 3 * (A₁ + A₂ + A₃) := by
  have hAm := F.measurableSet_annulus R R₁
  have hpt : ∀ x ∈ F.annulus R R₁, ‖S.B ψ₀ (F.ρ x) (F.t x)‖ ^ 2 ≤
      3 * (S.mMain ψ₀ (F.ρ x) (1 * (F.t x).re) + S.mMain ψ₀ (F.ρ x) (-1 * (F.t x).re) +
        S.mRem ψ₀ (F.ρ x) (F.t x).re) := by
    intro x hx
    have hx' : x ∉ F.exc := F.not_exc_of_mem_annulus (by linarith) hx
    have hτ : 1 ≤ |(F.t x).re| := by
      rw [← F.norm_eq_abs_re_of_not_exc hx']; linarith [hx.1]
    rw [F.eq_re_of_not_exc hx', one_mul, neg_one_mul]
    simp only [Complex.ofReal_re]
    exact S.normSq_B_le_J1 ψ₀ hB hC6 hM6 hGt (F.ρ x) hτ
  have hmaj : IntegrableOn (fun x => 3 * (S.mMain ψ₀ (F.ρ x) (1 * (F.t x).re) +
      S.mMain ψ₀ (F.ρ x) (-1 * (F.t x).re) + S.mRem ψ₀ (F.ρ x) (F.t x).re))
      (F.annulus R R₁) F.ν :=
    ((h1.1.add h2.1).add h3.1).const_mul 3
  have hint : IntegrableOn (fun x => ‖S.B ψ₀ (F.ρ x) (F.t x)‖ ^ 2) (F.annulus R R₁) F.ν := by
    refine hmaj.mono' (hBm.norm.pow_const 2).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hAm).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt x hx
  refine ⟨hint, ?_⟩
  calc ∫ x in F.annulus R R₁, ‖S.B ψ₀ (F.ρ x) (F.t x)‖ ^ 2 ∂F.ν
      ≤ ∫ x in F.annulus R R₁, 3 * (S.mMain ψ₀ (F.ρ x) (1 * (F.t x).re) +
          S.mMain ψ₀ (F.ρ x) (-1 * (F.t x).re) + S.mRem ψ₀ (F.ρ x) (F.t x).re) ∂F.ν :=
        setIntegral_mono_on hint hmaj hAm hpt
    _ = 3 * ((∫ x in F.annulus R R₁, S.mMain ψ₀ (F.ρ x) (1 * (F.t x).re) ∂F.ν) +
          (∫ x in F.annulus R R₁, S.mMain ψ₀ (F.ρ x) (-1 * (F.t x).re) ∂F.ν) +
          ∫ x in F.annulus R R₁, S.mRem ψ₀ (F.ρ x) (F.t x).re ∂F.ν) := by
        have h12 : IntegrableOn (fun x => S.mMain ψ₀ (F.ρ x) (1 * (F.t x).re) +
            S.mMain ψ₀ (F.ρ x) (-1 * (F.t x).re)) (F.annulus R R₁) F.ν := h1.1.add h2.1
        rw [integral_const_mul, integral_add h12 h3.1, integral_add h1.1 h2.1]
    _ ≤ 3 * (A₁ + A₂ + A₃) := by linarith [h1.2, h2.2, h3.2]

set_option maxHeartbeats 1000000 in
/-- **The blocks**: `∫_{block n} |B|² ≤ A_n`. -/
theorem block_sq_bound (hB : BesselAssumptions) {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls)
    (hBm : Measurable fun x => S.B ψ₀ (F.ρ x) (F.t x)) {Eexc : ℝ}
    (hE : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∫ x in F.exc, S.V ^ (2 * (F.t x).im) *
      ‖S.Ssum ψ₀ (F.ρ x) s σ‖ ^ 2 ∂F.ν ≤ Eexc)
    {Cψ : ℝ} (hCψ : 0 ≤ Cψ) (hψ : ∀ y, |deriv ψ₀.ψ₀ y| ≤ Cψ) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hMd : ∀ h : ℝ, S.M ≤ h → h ≤ 2 * S.M → ∀ w : ℂ, w.re = 0 →
      DifferentiableAt ℝ (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h ∧
        ‖deriv (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h‖ ≤ Cd * S.X / S.K)
    {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {k Ck : ℝ} (hk : 0 ≤ k) (hCk : 0 ≤ Ck)
    (hMk : ∀ h ∈ S.Hs, ∀ τ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ ≤ Ck * (1 + |τ|) ^ (-k))
    (n : ℕ) :
    IntegrableOn (fun x => ‖S.B ψ₀ (F.ρ x) (F.t x)‖ ^ 2) (F.block S.T₁ n) F.ν ∧
      ∫ x in F.block S.T₁ n, ‖S.B ψ₀ (F.ρ x) (F.t x)‖ ^ 2 ∂F.ν ≤
        S.blockA Cls Eexc Cψ Cd C6 CGt k Ck n := by
  have hT1 := S.one_le_T₁
  match n with
  | 0 =>
    rw [F.block_zero]
    obtain ⟨hi, hb⟩ := S.J0_block ψ₀ F hLS hE
    have hpt : ∀ x ∈ F.ball 1, ‖S.B ψ₀ (F.ρ x) (F.t x)‖ ^ 2 ≤ S.m0 ψ₀ (F.ρ x) (F.t x) :=
      fun x _ => S.normSq_B_le_m0 ψ₀ (F.ρ x) (F.abs_im_le_half x)
    have hint : IntegrableOn (fun x => ‖S.B ψ₀ (F.ρ x) (F.t x)‖ ^ 2) (F.ball 1) F.ν := by
      refine hi.mono' (hBm.norm.pow_const 2).aestronglyMeasurable ?_
      refine (ae_restrict_iff' (F.measurableSet_ball 1)).2 (Eventually.of_forall fun x hx => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt x hx
    exact ⟨hint, (setIntegral_mono_on hint hi (F.measurableSet_ball 1) hpt).trans hb⟩
  | 1 =>
    have e : F.block S.T₁ 1 = F.annulus 1 S.T₁ := rfl
    rw [e]
    have h := S.annulus_sq_bound ψ₀ F hB hBm hC6 hM6 hGt (R := 1) (R₁ := S.T₁) le_rfl
      (S.J1_main_block ψ₀ F hLS hCψ hψ hCd hMd (Or.inl rfl))
      (S.J1_main_block ψ₀ F hLS hCψ hψ hCd hMd (Or.inr rfl))
      (S.rem_block ψ₀ F hLS hC6 hM6 hGt le_rfl hT1)
    refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
    simp only [blockA, boundMain, boundRem]
    ring
  | (m + 2) =>
    have e : F.block S.T₁ (m + 2) = F.annulus (2 ^ m * S.T₁) (2 ^ (m + 1) * S.T₁) := rfl
    rw [e]
    have hR : 1 ≤ 2 ^ m * S.T₁ :=
      le_trans (by norm_num) (mul_le_mul (one_le_pow₀ (by norm_num)) hT1 zero_le_one
        (by positivity))
    have hR₁ : 1 ≤ 2 ^ (m + 1) * S.T₁ :=
      le_trans (by norm_num) (mul_le_mul (one_le_pow₀ (by norm_num)) hT1 zero_le_one
        (by positivity))
    have h := S.annulus_sq_bound ψ₀ F hB hBm hC6 hM6 hGt hR
      (S.tail_block ψ₀ F hLS hk hCk hMk hR hR₁ (Or.inl rfl))
      (S.tail_block ψ₀ F hLS hk hCk hMk hR hR₁ (Or.inr rfl))
      (S.rem_block ψ₀ F hLS hC6 hM6 hGt hR hR₁)
    refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
    simp only [blockA, boundTail, boundRem]
    ring

set_option maxHeartbeats 1000000 in
/-- **The spectral side**: `∫ |B(ρ_t, t)| |U| ≤ ∑_n √(A_n) √(256/π T_n² P)`, given the
summability of the right-hand side (`summable_blocks`). -/
theorem spectral_side_of_summable (hB : BesselAssumptions) {Cls : ℝ → ℝ}
    (hLS : F.LS S.q Cls) {P : ℝ} (hHS : F.HS P)
    (hBm : Measurable fun x => S.B ψ₀ (F.ρ x) (F.t x)) {Eexc : ℝ}
    (hE : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∫ x in F.exc, S.V ^ (2 * (F.t x).im) *
      ‖S.Ssum ψ₀ (F.ρ x) s σ‖ ^ 2 ∂F.ν ≤ Eexc)
    {Cψ : ℝ} (hCψ : 0 ≤ Cψ) (hψ : ∀ y, |deriv ψ₀.ψ₀ y| ≤ Cψ) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hMd : ∀ h : ℝ, S.M ≤ h → h ≤ 2 * S.M → ∀ w : ℂ, w.re = 0 →
      DifferentiableAt ℝ (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h ∧
        ‖deriv (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h‖ ≤ Cd * S.X / S.K)
    {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {k Ck : ℝ} (hk : 0 ≤ k) (hCk : 0 ≤ Ck)
    (hMk : ∀ h ∈ S.Hs, ∀ τ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ ≤ Ck * (1 + |τ|) ^ (-k))
    (hsum : Summable fun n => Real.sqrt (S.blockA Cls Eexc Cψ Cd C6 CGt k Ck n) *
      Real.sqrt (256 / Real.pi * blockHi S.T₁ n ^ 2 * P)) :
    Integrable (fun x => ‖S.B ψ₀ (F.ρ x) (F.t x)‖ * ‖F.U x‖) F.ν ∧
      ∫ x, ‖S.B ψ₀ (F.ρ x) (F.t x)‖ * ‖F.U x‖ ∂F.ν ≤
        ∑' n, Real.sqrt (S.blockA Cls Eexc Cψ Cd C6 CGt k Ck n) *
          Real.sqrt (256 / Real.pi * blockHi S.T₁ n ^ 2 * P) := by
  have hT1 := S.one_le_T₁
  have hblk := S.block_sq_bound ψ₀ F hB hLS hBm hE hCψ hψ hCd hMd hC6 hM6 hGt hk hCk hMk
  have hU : ∀ n, ∫ x in F.block S.T₁ n, ‖F.U x‖ ^ 2 ∂F.ν ≤
      256 / Real.pi * blockHi S.T₁ n ^ 2 * P := by
    intro n
    refine (setIntegral_mono_set (F.intU (blockHi S.T₁ n))
      (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall (F.block_subset_ball S.T₁ n))).trans ?_
    exact hHS _ (one_le_blockHi hT1 n)
  have h := setIntegral_mul_le_tsum (μ := F.ν) (s := F.block S.T₁)
    (F.measurableSet_block S.T₁) (F.block_disjoint hT1)
    (f := fun x => ‖S.B ψ₀ (F.ρ x) (F.t x)‖) (g := fun x => ‖F.U x‖)
    (fun x => norm_nonneg _) (fun x => norm_nonneg _) hBm.norm.aestronglyMeasurable
    F.meas_U.norm.aestronglyMeasurable (fun n => (hblk n).1)
    (fun n => (F.intU (blockHi S.T₁ n)).mono_set (F.block_subset_ball S.T₁ n))
    (fun n => (hblk n).2) hU hsum
  rw [F.iUnion_block hT1, Measure.restrict_univ] at h
  exact ⟨integrableOn_univ.1 h.1, h.2⟩

end Setup

end Triples
